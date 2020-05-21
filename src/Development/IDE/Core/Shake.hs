-- Copyright (c) 2019 The DAML Authors. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ExplicitNamespaces         #-}

-- | A Shake implementation of the compiler service.
--
--   There are two primary locations where data lives, and both of
--   these contain much the same data:
--
-- * The Shake database (inside 'shakeDb') stores a map of shake keys
--   to shake values. In our case, these are all of type 'Q' to 'A'.
--   During a single run all the values in the Shake database are consistent
--   so are used in conjunction with each other, e.g. in 'uses'.
--
-- * The 'Values' type stores a map of keys to values. These values are
--   always stored as real Haskell values, whereas Shake serialises all 'A' values
--   between runs. To deserialise a Shake value, we just consult Values.
module Development.IDE.Core.Shake(
    IdeState, shakeExtras,
    ShakeExtras(..), getShakeExtras, getShakeExtrasRules,
    IdeRule, IdeResult, GetModificationTime(..),
    shakeOpen, shakeShut,
    shakeRun, shakeRunInternal, shakeRunInternalKill, shakeRunUser,
    shakeProfile,
    use, useWithStale, useNoFile, uses, usesWithStale, useWithStaleFast, delayedAction,
    useWithStaleFast', FastResult(..),
    use_, useNoFile_, uses_,
    define, defineEarlyCutoff, defineOnDisk, needOnDisk, needOnDisks,
    getDiagnostics, unsafeClearDiagnostics,
    getHiddenDiagnostics,
    IsIdeGlobal, addIdeGlobal, addIdeGlobalExtras, getIdeGlobalState, getIdeGlobalAction,
    garbageCollect,
    knownFiles,
    setPriority,
    sendEvent,
    ideLogger,
    actionLogger,
    FileVersion(..), modificationTime, newerFileVersion,
    Priority(..),
    updatePositionMapping, runAction, runActionSync,
    deleteValue,
    OnDiskRule(..),

    workerThread, delay, DelayedAction, mkDelayedAction,
    IdeAction(..), runIdeAction, askShake, mkUpdater,
    HieWriterChan
    ) where

import           Development.Shake hiding (ShakeValue, doesFileExist, Info)
import           Development.Shake.Database
import           Development.Shake.Classes
import           Development.Shake.Rule
import qualified Data.HashMap.Strict as HMap
import qualified Data.HashSet as HSet
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as BS
import           Data.Dynamic
import           Data.Maybe
import Data.Map.Strict (Map)
import           Data.List.Extra (partition, takeEnd)
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Tuple.Extra
import Data.Unique
import Development.IDE.Core.Debouncer
import Development.IDE.GHC.Compat ( NameCacheUpdater(..), upNameCache )
import Development.IDE.Core.RuleTypes
import Development.IDE.Core.PositionMapping
import Development.IDE.Types.Logger hiding (Priority)
import qualified Development.IDE.Types.Logger as Logger
import Language.Haskell.LSP.Diagnostics
import qualified Data.SortedList as SL
import           Development.IDE.Types.Diagnostics
import Development.IDE.Types.Location
import Development.IDE.Types.Options
import           Control.Concurrent.Async
import           Control.Concurrent.Extra
import           Control.Exception
import           Control.DeepSeq
import           System.Time.Extra
import           Data.Typeable
import qualified Language.Haskell.LSP.Messages as LSP
import qualified Language.Haskell.LSP.Types as LSP
import           System.FilePath hiding (makeRelative)
import qualified Development.Shake as Shake
import           Control.Monad.Extra
import           Data.Time
import           GHC.Generics
import           System.IO.Unsafe
import           Numeric.Extra
import Language.Haskell.LSP.Types
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import qualified Data.HashPSQ as PQ
import OpenTelemetry.Eventlog

import Data.IORef
import NameCache
import UniqSupply
import PrelInfo

import HieDb.Types

type HieWriterChan = Chan (HieDb -> IO ())

-- information we stash inside the shakeExtra field
data ShakeExtras = ShakeExtras
    {eventer :: LSP.FromServerMessage -> IO ()
    ,debouncer :: Debouncer NormalizedUri
    ,logger :: Logger
    ,globals :: Var (HMap.HashMap TypeRep Dynamic)
    ,state :: Var Values
    ,diagnostics :: Var DiagnosticStore
    ,hiddenDiagnostics :: Var DiagnosticStore
    ,publishedDiagnostics :: Var (HMap.HashMap NormalizedUri [Diagnostic])
    -- ^ This represents the set of diagnostics that we have published.
    -- Due to debouncing not every change might get published.
    ,positionMapping :: Var (HMap.HashMap NormalizedUri (Map TextDocumentVersion (PositionDelta, PositionMapping)))
    -- ^ Map from a text document version to a PositionMapping that describes how to map
    -- positions in a version of that document to positions in the latest version
    -- First mapping is delta from previous version and second one is an
    -- accumlation of all previous mappings.
    ,inProgress :: Var (HMap.HashMap NormalizedFilePath Int)
    -- ^ How many rules are running for each file
    , queue :: ShakeQueue
    , ideNc :: IORef NameCache
    , hiedb :: HieDb -- ^ Use only to read
    , hiedbChan :: HieWriterChan -- ^ use to write
    }

getShakeExtras :: Action ShakeExtras
getShakeExtras = do
    Just x <- getShakeExtra @ShakeExtras
    return x

getShakeExtrasRules :: Rules ShakeExtras
getShakeExtrasRules = do
    Just x <- getShakeExtraRules @ShakeExtras
    return x

class Typeable a => IsIdeGlobal a where

addIdeGlobal :: IsIdeGlobal a => a -> Rules ()
addIdeGlobal x = do
    extras <- getShakeExtrasRules
    liftIO $ addIdeGlobalExtras extras x

addIdeGlobalExtras :: IsIdeGlobal a => ShakeExtras -> a -> IO ()
addIdeGlobalExtras ShakeExtras{globals} x@(typeOf -> ty) =
    liftIO $ modifyVar_ globals $ \mp -> case HMap.lookup ty mp of
        Just _ -> error $ "Can't addIdeGlobal twice on the same type, got " ++ show ty
        Nothing -> return $! HMap.insert ty (toDyn x) mp


getIdeGlobalExtras :: forall a . IsIdeGlobal a => ShakeExtras -> IO a
getIdeGlobalExtras ShakeExtras{globals} = do
    Just x <- HMap.lookup (typeRep (Proxy :: Proxy a)) <$> readVar globals
    return $ fromDyn x $ error "Serious error, corrupt globals"

getIdeGlobalAction :: forall a . IsIdeGlobal a => Action a
getIdeGlobalAction = liftIO . getIdeGlobalExtras =<< getShakeExtras

getIdeGlobalState :: forall a . IsIdeGlobal a => IdeState -> IO a
getIdeGlobalState = getIdeGlobalExtras . shakeExtras


-- | The state of the all values.
type Values = HMap.HashMap (NormalizedFilePath, Key) (Value Dynamic)

-- | Key type
data Key = forall k . (Typeable k, Hashable k, Eq k, Show k) => Key k

instance Show Key where
  show (Key k) = show k

instance Eq Key where
    Key k1 == Key k2 | Just k2' <- cast k2 = k1 == k2'
                     | otherwise = False

instance Hashable Key where
    hashWithSalt salt (Key key) = hashWithSalt salt key

-- | The result of an IDE operation. Warnings and errors are in the Diagnostic,
--   and a value is in the Maybe. For operations that throw an error you
--   expect a non-empty list of diagnostics, at least one of which is an error,
--   and a Nothing. For operations that succeed you expect perhaps some warnings
--   and a Just. For operations that depend on other failing operations you may
--   get empty diagnostics and a Nothing, to indicate this phase throws no fresh
--   errors but still failed.
--

data Value v
    = Succeeded TextDocumentVersion v
    | Stale TextDocumentVersion v
    | Failed
    deriving (Functor, Generic, Show)

instance NFData v => NFData (Value v)

-- | Convert a Value to a Maybe. This will only return `Just` for
-- up2date results not for stale values.
currentValue :: Value v -> Maybe v
currentValue (Succeeded _ v) = Just v
currentValue (Stale _ _) = Nothing
currentValue Failed = Nothing

-- | Return the most recent, potentially stale, value and a PositionMapping
-- for the version of that value.
lastValueIO :: ShakeExtras -> NormalizedFilePath -> Value v -> IO (Maybe (v, PositionMapping))
lastValueIO ShakeExtras{positionMapping} file v = do
    allMappings <- liftIO $ readVar positionMapping
    pure $ case v of
        Succeeded ver v -> Just (v, mappingForVersion allMappings file ver)
        Stale ver v -> Just (v, mappingForVersion allMappings file ver)
        Failed -> Nothing

-- | Return the most recent, potentially stale, value and a PositionMapping
-- for the version of that value.
lastValue :: NormalizedFilePath -> Value v -> Action (Maybe (v, PositionMapping))
lastValue file v = do
    s <- getShakeExtras
    liftIO $ lastValueIO s file v

valueVersion :: Value v -> Maybe TextDocumentVersion
valueVersion = \case
    Succeeded ver _ -> Just ver
    Stale ver _ -> Just ver
    Failed -> Nothing

mappingForVersion
    :: HMap.HashMap NormalizedUri (Map TextDocumentVersion (a, PositionMapping))
    -> NormalizedFilePath
    -> TextDocumentVersion
    -> PositionMapping
mappingForVersion allMappings file ver =
    maybe zeroMapping snd $
    Map.lookup ver =<<
    HMap.lookup (filePathToUri' file) allMappings

type IdeRule k v =
  ( Shake.RuleResult k ~ v
  , Shake.ShakeValue k
  , Show v
  , Typeable v
  , NFData v
  )

-- | A Shake database plus persistent store. Can be thought of as storing
--   mappings from @(FilePath, k)@ to @RuleResult k@.
data IdeState = IdeState
    {shakeDb :: ShakeDatabase
    ,shakeAbort :: MVar (IO ()) -- close whoever was running last
    ,shakeClose :: IO ()
    ,shakeQueue :: ShakeQueue
    ,shakeExtras :: ShakeExtras
    ,shakeProfileDir :: Maybe FilePath
    }


data QPriority = QPriority { _retries :: Int
                           , _qid :: Int
                           , _qimportant :: Bool } deriving Eq

instance Ord QPriority where
    compare (QPriority r q i) (QPriority r' q' i') = compare i i' <> compare r r' <> compare q q'

-- A hashable Key with an integer to provide an Ord instance for use as a key in a priority queue.
data KeyWithId = KeyWithId Key Int deriving (Eq)

instance Hashable KeyWithId where
  hashWithSalt salt (KeyWithId k _) = hashWithSalt salt k

instance Ord KeyWithId where
    compare (KeyWithId _h1 i1) (KeyWithId _h2 i2) = i1 `compare` i2


type PriorityMap =  PQ.HashPSQ KeyWithId QPriority DelayedActionInternal

-- | Actions we want to run on the shake database are queued up and batched together.
-- A batch can be killed when a file is modified as we assume it will invalidate it.
data ShakeQueue = ShakeQueue
                { qactions :: Var PriorityMap
                -- An action which cancels the currently running batch and
                -- requeues the participants.
                , qabort :: Var (IO () -> IO ())
                -- A monotonically increasing integer to give each request
                -- a unique identifier.
                , qcount :: Var Int
                -- The worker takes this MVar when the actions are empty, it is filled
                -- when an action is written to the map which allows the
                -- worker to continue.
                , qTrigger :: MVar ()
                }

-- This is stuff we make up and add onto the information the user
-- provided.
data DelayedActionExtra = DelayedActionExtra { _actionInternalId :: Int
                                             , _actionInternalQPriority :: QPriority
                                             , _actionInternalFinished :: IO Bool
                                             , _actionInternal :: Action ()
                                             }

type DelayedAction a = DelayedActionX (Action a)
type DelayedActionInternal = DelayedActionX DelayedActionExtra

{-# COMPLETE DelayedActionInternal#-}
pattern DelayedActionInternal :: String -> Key -> Logger.Priority -> Action () -> Int -> QPriority -> IO Bool -> DelayedActionX DelayedActionExtra
pattern DelayedActionInternal {actionInternalName, actionInternalKey, actionInternalPriority, getAction
                              , actionId, actionQPriority, actionFinished}
                              = DelayedActionX actionInternalName actionInternalKey actionInternalPriority
                                    (DelayedActionExtra actionId actionQPriority actionFinished getAction)

{-# COMPLETE DelayedAction#-}
pattern DelayedAction :: String -> Key -> Logger.Priority -> Action a -> DelayedAction a
pattern DelayedAction a b c d = DelayedActionX a b c d

mkDelayedAction :: (Show k, Typeable k, Hashable k, Eq k)
                => String -> k -> Logger.Priority -> Action a -> DelayedAction a
mkDelayedAction s k = DelayedAction s (Key k)

data DelayedActionX a = DelayedActionX { actionName :: String -- Name we show to the user
                                      , actionKey :: Key
                                      -- The queue only contrains entries for
                                      -- unique key values.
                                      , actionPriority :: Logger.Priority
                                      -- An action which can be called to see
                                      -- if the action has finished yet.
                                      , _actionExtra :: a
                                      }

instance Show (DelayedActionX a) where
    show d = "DelayedAction: " ++ actionName d

finishedBarrier :: Barrier a -> IO Bool
finishedBarrier b = isJust <$> waitBarrierMaybe b

freshId :: ShakeQueue -> IO Int
freshId (ShakeQueue{qcount}) = do
    modifyVar qcount (\n -> return (n + 1, n))

-- Could replace this argument with a parameterised version of
-- DelayedAction.
queueAction :: [DelayedAction a]
               -> ShakeQueue
               -> IO [Barrier a]
queueAction as sq = do
    (bs, ds) <- unzip <$> mapM (instantiateDelayedAction sq) as
    modifyVar_ (qactions sq) (return . insertMany ds)
    -- Wake up the worker if necessary
    void $ tryPutMVar (qTrigger sq) ()
    return bs

insertMany :: [DelayedActionInternal] -> PriorityMap -> PriorityMap
insertMany ds pm = foldr (\d pm' -> PQ.insert (mkKid d) (getPriority d) d pm') pm ds


mkKid :: DelayedActionX DelayedActionExtra -> KeyWithId
mkKid d = KeyWithId (actionKey d) (actionId d)

queueDelayedAction :: DelayedActionInternal -> ShakeQueue -> IO ()
queueDelayedAction d sq = do
    modifyVar_ (qactions sq) (return . PQ.insert (mkKid d) (getPriority d) d)
    -- Wake up the worker if necessary
    void $ tryPutMVar (qTrigger sq) ()

getPriority :: DelayedActionInternal -> QPriority
getPriority = actionQPriority

instantiateDelayedAction :: ShakeQueue -> DelayedAction a -> IO (Barrier a, DelayedActionInternal)
instantiateDelayedAction sq (DelayedAction s k p a) = do
    b <- newBarrier
    i <- freshId sq
    let a' = do r <- a
                liftIO $ signalBarrier b r
    let d = DelayedActionInternal s k p a' i (QPriority 0 i False) (finishedBarrier b)
    return (b, d)


newShakeQueue :: IO ShakeQueue
newShakeQueue = do
    ShakeQueue <$> newVar (PQ.empty) <*> (newVar id) <*> newVar 0 <*> newEmptyMVar

requeueIfCancelled :: ShakeQueue -> DelayedActionInternal -> IO ()
requeueIfCancelled sq d@(DelayedActionInternal{..}) = do
    is_finished <- actionFinished
    unless is_finished (queueDelayedAction d sq)

logDelayedAction :: Logger -> DelayedActionInternal -> Action ()
logDelayedAction l d  = do
    start <- liftIO $ offsetTime
    -- These traces go to the eventlog and can be interpreted with the opentelemetry library.
    actionBracket (beginSpan (show $ actionKey d)) endSpan (const $ getAction d)
    runTime <- liftIO $ start
    return ()
    liftIO $ logPriority l (actionPriority d) $ T.pack $
        "finish: " ++ (actionName d) ++ " (took " ++ showDuration runTime ++ ")"

-- | Retrieve up to k values from the map and return the modified map
smallestK :: Int -> PriorityMap -> (PriorityMap, [DelayedActionInternal])
smallestK 0 p = (p, [])
smallestK n p = case PQ.minView p of
                    Nothing -> (p, [])
                    Just (_, _, v, p') ->
                        let (p'', ds) = smallestK (n - 1) p'
                        in (p'', v:ds)

type QueueInfo = (Int, Int)

getWork :: Int -> PriorityMap -> (PriorityMap, (QueueInfo, [DelayedActionInternal]))
getWork n p =
    let before_size = PQ.size p
        (p', as) = smallestK n p
        after_size = PQ.size p'
    in (p', ((before_size, after_size), as))

-- | A thread which continually reads from the queue running shake actions
workerThread :: IdeState -> IO ()
workerThread i@IdeState{shakeQueue=sq@ShakeQueue{..},..} = do
    -- I choose 20 here but may be better to just chuck the whole thing to shake as it will paralellise the work itself.
    (info, ds) <- modifyVar qactions (return . getWork 500)
    case ds of
        -- Nothing to do, wait until some work is available.
        [] -> takeMVar qTrigger
        _ -> do
            logDebug (logger shakeExtras) (T.pack $ "Starting: " ++ show info ++ ":" ++ show ds)
            (cancel, wait) <- shakeRun Debug "batch" i (map (logDelayedAction (logger shakeExtras)) ds)
            writeVar qabort (\k -> do
                k
                cancel
                mapM_ (requeueIfCancelled sq) ds)
            res <- try wait
            case res of
                -- Really don't want an exception to kill this thread but not sure where it should go
                Left (_e :: SomeException) -> return ()
                Right _r -> return ()
            -- Action finished, nothing to abort now
            writeVar qabort id
            return ()

-- Write a profile of the last action to be completed
shakeWriteProfile :: String -> ShakeDatabase -> Seconds -> FilePath -> IO FilePath
shakeWriteProfile herald shakeDb time dir = do
     count <- modifyVar profileCounter $ \x -> let !y = x+1 in return (y,y)
     let file = herald ++ "-ide-" ++ profileStartTime ++ "-" ++ takeEnd 5 ("0000" ++ show count) ++ "-" ++ showDP 2 time <.> "html"
     shakeProfileDatabase shakeDb $ dir </> file
     return (dir </> file)

{-# NOINLINE profileStartTime #-}
profileStartTime :: String
profileStartTime = unsafePerformIO $ formatTime defaultTimeLocale "%Y%m%d-%H%M%S" <$> getCurrentTime

{-# NOINLINE profileCounter #-}
profileCounter :: Var Int
profileCounter = unsafePerformIO $ newVar 0

setValues :: IdeRule k v
          => Var Values
          -> k
          -> NormalizedFilePath
          -> Value v
          -> IO ()
setValues state key file val = modifyVar_ state $ \vals -> do
    -- Force to make sure the old HashMap is not retained
    --let size = HMap.size vals
    --traceEventIO ("METRIC:" ++ show size)
    evaluate $ HMap.insert (file, Key key) (fmap toDyn val) vals

-- | Delete the value stored for a given ide build key
deleteValue
  :: (Typeable k, Hashable k, Eq k, Show k)
  => IdeState
  -> k
  -> NormalizedFilePath
  -> IO ()
deleteValue IdeState{shakeExtras = ShakeExtras{state}} key file = modifyVar_ state $ \vals ->
    evaluate $ HMap.delete (file, Key key) vals

-- | We return Nothing if the rule has not run and Just Failed if it has failed to produce a value.
getValues :: forall k v. IdeRule k v => Var Values -> k -> NormalizedFilePath -> IO (Maybe (Value v))
getValues state key file = do
    vs <- readVar state
    case HMap.lookup (file, Key key) vs of
        Nothing -> pure Nothing
        Just v -> do
            let r = fmap (fromJust . fromDynamic @v) v
            -- Force to make sure we do not retain a reference to the HashMap
            -- and we blow up immediately if the fromJust should fail
            -- (which would be an internal error).
            evaluate (r `seqValue` Just r)

-- Consult the Values hashmap to get a list of all the files we care about
-- in a project
-- MP: This may be quite inefficient if the Values table is very big but
-- simplest implementation first.
knownFilesIO :: Var Values -> IO (HSet.HashSet NormalizedFilePath)
knownFilesIO v = do
  vs <- readVar v
  return $ HSet.map fst $ HSet.filter (\(_, k) -> k == Key GetHiFile) (HMap.keysSet vs)

knownFiles :: Action (HSet.HashSet NormalizedFilePath)
knownFiles = do
  ShakeExtras{state} <- getShakeExtras
  liftIO $ knownFilesIO state




-- | Seq the result stored in the Shake value. This only
-- evaluates the value to WHNF not NF. We take care of the latter
-- elsewhere and doing it twice is expensive.
seqValue :: Value v -> b -> b
seqValue v b = case v of
    Succeeded ver v -> rnf ver `seq` v `seq` b
    Stale ver v -> rnf ver `seq` v `seq` b
    Failed -> b

-- | Open a 'IdeState', should be shut using 'shakeShut'.
shakeOpen :: IO LSP.LspId
          -> (LSP.FromServerMessage -> IO ()) -- ^ diagnostic handler
          -> Logger
          -> Debouncer NormalizedUri
          -> Maybe FilePath
          -> IdeReportProgress
          -> HieDb
          -> Chan (HieDb -> IO ())
          -> ShakeOptions
          -> Rules ()
          -> IO IdeState
shakeOpen getLspId eventer logger debouncer shakeProfileDir (IdeReportProgress reportProgress) hiedb hiedbChan opts rules = do
    inProgress <- newVar HMap.empty
    shakeAbort <- newMVar $ return ()
    shakeQueue <- newShakeQueue
    us <- mkSplitUniqSupply 'r'
    ideNc <- newIORef (initNameCache us knownKeyNames)
    shakeExtras <- do
        globals <- newVar HMap.empty
        state <- newVar HMap.empty
        diagnostics <- newVar mempty
        hiddenDiagnostics <- newVar mempty
        publishedDiagnostics <- newVar mempty
        positionMapping <- newVar HMap.empty
        let queue = shakeQueue
        pure ShakeExtras{..}
    (shakeDb, shakeClose) <-
        shakeOpenDatabase
            opts
                { shakeExtra = addShakeExtra shakeExtras $ shakeExtra opts
                -- we don't actually use the progress value, but Shake conveniently spawns/kills this thread whenever
                -- we call into Shake, so abuse it for that purpose
                , shakeProgress = const $ if reportProgress then lspShakeProgress getLspId eventer inProgress else pure ()
                }
            rules
    shakeDb <- shakeDb
    return IdeState{..}

lspShakeProgress :: Hashable a => IO LSP.LspId -> (LSP.FromServerMessage -> IO ()) -> Var (HMap.HashMap a Int) -> IO ()
lspShakeProgress getLspId sendMsg inProgress = do
    -- first sleep a bit, so we only show progress messages if it's going to take
    -- a "noticable amount of time" (we often expect a thread kill to arrive before the sleep finishes)
    sleep 0.1
    lspId <- getLspId
    u <- ProgressTextToken . T.pack . show . hashUnique <$> newUnique
    sendMsg $ LSP.ReqWorkDoneProgressCreate $ LSP.fmServerWorkDoneProgressCreateRequest
      lspId $ LSP.WorkDoneProgressCreateParams
      { _token = u }
    bracket_ (start u) (stop u) (loop u Nothing)
    where
        start id = sendMsg $ LSP.NotWorkDoneProgressBegin $ LSP.fmServerWorkDoneProgressBeginNotification
            LSP.ProgressParams
                { _token = id
                , _value = WorkDoneProgressBeginParams
                  { _title = "Processing"
                  , _cancellable = Nothing
                  , _message = Nothing
                  , _percentage = Nothing
                  }
                }
        stop id = sendMsg $ LSP.NotWorkDoneProgressEnd $ LSP.fmServerWorkDoneProgressEndNotification
            LSP.ProgressParams
                { _token = id
                , _value = WorkDoneProgressEndParams
                  { _message = Nothing
                  }
                }
        sample = 0.1
        loop id prev = do
            sleep sample
            current <- readVar inProgress
            let done = length $ filter (== 0) $ HMap.elems current
            let todo = HMap.size current
            let next = Just $ T.pack $ show done <> "/" <> show todo
            when (next /= prev) $
                sendMsg $ LSP.NotWorkDoneProgressReport $ LSP.fmServerWorkDoneProgressReportNotification
                    LSP.ProgressParams
                        { _token = id
                        , _value = LSP.WorkDoneProgressReportParams
                        { _cancellable = Nothing
                        , _message = next
                        , _percentage = Nothing
                        }
                        }
            loop id next

shakeProfile :: IdeState -> FilePath -> IO ()
shakeProfile IdeState{..} = shakeProfileDatabase shakeDb

shakeShut :: IdeState -> IO ()
shakeShut IdeState{..} = withMVar shakeAbort $ \stop -> do
    -- Shake gets unhappy if you try to close when there is a running
    -- request so we first abort that.
    stop
    shakeClose

-- | These actions are run asynchronously after the current action is
-- finished running. For example, to trigger a key build after a rule
-- has already finished as is the case with useWithStaleFast
delayedAction :: DelayedAction () -> IdeAction ()
delayedAction a = do
  sq <- shakeQueue <$> ask
  void $ liftIO $ queueAction [a] sq

-- | A varient of delayedAction for the Action monad
-- The supplied action *will* be run but at least not until the current action has finished.
delay :: (Typeable k, Show k, Hashable k, Eq k)
      => String -> k -> Action () -> Action ()
delay herald k a = do
    ShakeExtras{queue} <- getShakeExtras
    let da = mkDelayedAction herald (Key k) Info a
    -- Do not wait for the action to return
    void $ liftIO $ queueAction [da] queue

-- | Running an action which DIRECTLY corresponds to something a user did,
-- for example computing hover information.
shakeRunUser :: IdeState -> [DelayedAction a] -> IO ([IO a])
shakeRunUser ide as = do
    bs <- queueAction as (shakeQueue ide)
    return $ map waitBarrier bs
-- | Running an action which is INTERNAL to shake, for example, a file has
-- been modified, basically any use of shakeRun which is not blocking (ie
-- which is not called via runAction).
shakeRunInternal :: IdeState -> [DelayedAction a] -> IO ()
shakeRunInternal ide as = void $ queueAction as (shakeQueue ide)

-- | Like shakeRun internal but kill ongoing work first
shakeRunInternalKill :: IdeState -> [DelayedAction a] -> IO ()
shakeRunInternalKill ide as = do
    -- TODO: There is a race here if the actions get queued
    -- and start to run before the kill, sh
    let k = shakeRunInternal ide as
    kill <- readVar (qabort (shakeQueue ide))
    kill k


-- | Spawn immediately. If you are already inside a call to shakeRun that will be aborted with an exception.
shakeRun :: Logger.Priority
         -> String  -- A name for the action and at which logging priority it should be displayed.
                                -- Some requests are very internal to shake
                                -- and don't make much sense to normal
                                -- users.
         -> IdeState -> [Action a] -> IO (IO (), IO [a])
shakeRun p herald IdeState{shakeExtras=ShakeExtras{..},..} acts  =
        -- It is crucial to be masked here, otherwise we can get killed
        -- between spawning the new thread and updating shakeAbort.
        -- See https://github.com/digital-asset/ghcide/issues/79
        (do
              aThread <- asyncWithUnmask $ \restore -> do
                    -- Try to run the action and record how long it took
                   (runTime, res) <- duration $ try (restore $ shakeRunDatabase shakeDb acts)

                   -- Write a profile when the action completed normally
                   profile <- case res of
                     Left {}  -> return ""
                     Right {} -> do
                      mfp <- forM shakeProfileDir (shakeWriteProfile herald shakeDb runTime)
                      case mfp of
                        Just fp ->  return $
                          let link = case filePathToUri' $ toNormalizedFilePath' fp of
                                                NormalizedUri _ x -> x
                          in ", profile saved at " <> T.unpack link
                        Nothing -> return ""

                   let res' = case res of
                            Left e -> "exception: " <> displayException e
                            Right _ -> "completed"
                   logPriority logger p $ T.pack $
                        "finish shakeRun: " ++ herald ++ " (took " ++ showDuration runTime ++ ", " ++ res' ++ profile ++ ")"
                   return res
              let wrapUp res = either (throwIO @SomeException) return res
              -- An action which can be used to block on the result of
              -- shakeRun returning
              let k = do
                        (res, as) <- (wrapUp =<< wait aThread)
                        sequence_ as
                        return res
              pure (cancel aThread, k))

getDiagnostics :: IdeState -> IO [FileDiagnostic]
getDiagnostics IdeState{shakeExtras = ShakeExtras{diagnostics}} = do
    val <- readVar diagnostics
    return $ getAllDiagnostics val

getHiddenDiagnostics :: IdeState -> IO [FileDiagnostic]
getHiddenDiagnostics IdeState{shakeExtras = ShakeExtras{hiddenDiagnostics}} = do
    val <- readVar hiddenDiagnostics
    return $ getAllDiagnostics val

-- | FIXME: This function is temporary! Only required because the files of interest doesn't work
unsafeClearDiagnostics :: IdeState -> IO ()
unsafeClearDiagnostics IdeState{shakeExtras = ShakeExtras{diagnostics}} =
    writeVar diagnostics mempty

-- | Clear the results for all files that do not match the given predicate.
garbageCollect :: (NormalizedFilePath -> Bool) -> Action ()
garbageCollect keep = do
    ShakeExtras{state, diagnostics,hiddenDiagnostics,publishedDiagnostics,positionMapping} <- getShakeExtras
    liftIO $
        do newState <- modifyVar state $ \values -> do
               values <- evaluate $ HMap.filterWithKey (\(file, _) _ -> keep file) values
               return $! dupe values
           modifyVar_ diagnostics $ \diags -> return $! filterDiagnostics keep diags
           modifyVar_ hiddenDiagnostics $ \hdiags -> return $! filterDiagnostics keep hdiags
           modifyVar_ publishedDiagnostics $ \diags -> return $! HMap.filterWithKey (\uri _ -> keep (fromUri uri)) diags
           let versionsForFile =
                   HMap.fromListWith Set.union $
                   mapMaybe (\((file, _key), v) -> (filePathToUri' file,) . Set.singleton <$> valueVersion v) $
                   HMap.toList newState
           modifyVar_ positionMapping $ \mappings -> return $! filterVersionMap versionsForFile mappings
define
    :: IdeRule k v
    => (k -> NormalizedFilePath -> Action (IdeResult v)) -> Rules ()
define op = defineEarlyCutoff $ \k v -> (Nothing,) <$> op k v

use :: IdeRule k v
    => k -> NormalizedFilePath -> Action (Maybe v)
use key file = head <$> uses key [file]

useWithStale :: IdeRule k v
    => k -> NormalizedFilePath -> Action (Maybe (v, PositionMapping))
useWithStale key file = head <$> usesWithStale key [file]

newtype IdeAction a = IdeAction { runIdeActionT  :: (ReaderT IdeState IO) a }
    deriving (MonadReader IdeState, MonadIO, Functor, Applicative, Monad)

runIdeAction :: String -> IdeState -> IdeAction a -> IO a
runIdeAction _herald s i = do
    res <- runReaderT (runIdeActionT i) s
    return res

askShake :: IdeAction ShakeExtras
askShake = shakeExtras <$> ask

mkUpdater :: MaybeT IdeAction NameCacheUpdater
mkUpdater = do
  ref <- lift $ ideNc <$> askShake
  pure $ NCU (upNameCache ref)

-- A (maybe) stale result now, and an up to date one later
data FastResult a = FastResult { stale :: Maybe (a,PositionMapping), uptoDate :: Barrier (Maybe a)  }

useWithStaleFast' :: IdeRule k v => k -> NormalizedFilePath -> IdeAction (FastResult v)
useWithStaleFast' key file = do
  final_res <-  do
    -- This lookup directly looks up the key in the shake database and
    -- returns the last value that was computed for this key without
    -- checking freshness.

    s@ShakeExtras{state} <- askShake
    r <- liftIO $ getValues state key file
    case r of
      Nothing -> do
        -- Perhaps for Hover this should return Nothing immediatey but for
        -- completions it should block? Not for MP to decide, need AZ and
        -- F to comment
        return Nothing
        --useWithStale key file
      -- Otherwise, use the computed value even if it's out of date.
      Just v -> do
        liftIO $ lastValueIO s file v
  -- Then async trigger the key to be built anyway because we want to
  -- keep updating the value in the key.
  --shakeRunInternal ("C:" ++ (show key)) ide [use key file]
  b <- liftIO $ newBarrier
  delayedAction (mkDelayedAction ("C:" ++ (show key)) (key, file) Debug (use key file >>= liftIO . signalBarrier b))
  return (FastResult final_res b)

useWithStaleFast :: IdeRule k v => k -> NormalizedFilePath -> IdeAction (Maybe (v, PositionMapping))
useWithStaleFast key file = stale <$> useWithStaleFast' key file

-- MattP: Removed the distinction between runAction and runActionSync
-- as it is no longer necessary now the are no `action` rules. This is how
-- it should remain as they add a lot of overhead for hover for example if
-- you run them every time.
-- There is only one use of runAction left in the whole code base (apart from exe/Main.hs)
-- In CodeAction where we probably want to remove it.
runAction :: String -> IdeState -> Action a -> IO a
runAction herald ide action = runActionSync herald ide action

runActionSync :: String -> IdeState -> Action a -> IO a
runActionSync herald s act = fmap head $ join $ sequence <$> shakeRunUser s [mkDelayedAction herald herald Info act]

useNoFile :: IdeRule k v => k -> Action (Maybe v)
useNoFile key = use key emptyFilePath

use_ :: IdeRule k v => k -> NormalizedFilePath -> Action v
use_ key file = head <$> uses_ key [file]

useNoFile_ :: IdeRule k v => k -> Action v
useNoFile_ key = use_ key emptyFilePath

uses_ :: IdeRule k v => k -> [NormalizedFilePath] -> Action [v]
uses_ key files = do
    res <- uses key files
    case sequence res of
        Nothing -> liftIO $ throwIO $ BadDependency (show key)
        Just v -> return v


-- | When we depend on something that reported an error, and we fail as a direct result, throw BadDependency
--   which short-circuits the rest of the action
data BadDependency = BadDependency String deriving Show
instance Exception BadDependency

isBadDependency :: SomeException -> Bool
isBadDependency x
    | Just (x :: ShakeException) <- fromException x = isBadDependency $ shakeExceptionInner x
    | Just (_ :: BadDependency) <- fromException x = True
    | otherwise = False

newtype Q k = Q (k, NormalizedFilePath)
    deriving (Eq,Hashable,NFData, Generic)

instance Binary k => Binary (Q k)

instance Show k => Show (Q k) where
    show (Q (k, file)) = show k ++ "; " ++ fromNormalizedFilePath file

-- | Invariant: the 'v' must be in normal form (fully evaluated).
--   Otherwise we keep repeatedly 'rnf'ing values taken from the Shake database
-- Note (MK) I am not sure why we need the ShakeValue here, maybe we
-- can just remove it?
data A v = A (Value v) ShakeValue
    deriving Show

instance NFData (A v) where rnf (A v x) = v `seq` rnf x

-- In the Shake database we only store one type of key/result pairs,
-- namely Q (question) / A (answer).
type instance RuleResult (Q k) = A (RuleResult k)


-- | Return up2date results. Stale results will be ignored.
uses :: IdeRule k v
    => k -> [NormalizedFilePath] -> Action [Maybe v]
uses key files = map (\(A value _) -> currentValue value) <$> apply (map (Q . (key,)) files)

-- | Return the last computed result which might be stale.
usesWithStale :: IdeRule k v
    => k -> [NormalizedFilePath] -> Action [Maybe (v, PositionMapping)]
usesWithStale key files = do
    values <- map (\(A value _) -> value) <$> apply (map (Q . (key,)) files)
    zipWithM lastValue files values


withProgress :: (Eq a, Hashable a) => Var (HMap.HashMap a Int) -> a -> Action b -> Action b
withProgress var file = actionBracket (f succ) (const $ f pred) . const
    where f shift = modifyVar_ var $ \x -> return (HMap.alter (\x -> Just (shift (fromMaybe 0 x))) file x)


defineEarlyCutoff
    :: IdeRule k v
    => (k -> NormalizedFilePath -> Action (Maybe BS.ByteString, IdeResult v))
    -> Rules ()
defineEarlyCutoff op = addBuiltinRule noLint noIdentity $ \(Q (key, file)) (old :: Maybe BS.ByteString) mode -> do
    extras@ShakeExtras{state, inProgress} <- getShakeExtras
    -- don't do progress for GetFileExists, as there are lots of non-nodes for just that one key
    (if show key == "GetFileExists" then id else withProgress inProgress file) $ do
        val <- case old of
            Just old | mode == RunDependenciesSame -> do
                v <- liftIO $ getValues state key file
                case v of
                    -- No changes in the dependencies and we have
                    -- an existing result.
                    Just v -> return $ Just $ RunResult ChangedNothing old $ A v (decodeShakeValue old)
                    _ -> return Nothing
            _ -> return Nothing
        case val of
            Just res -> return res
            Nothing -> do
                (bs, (diags, res)) <- actionCatch
                    (do v <- op key file; liftIO $ evaluate $ force v) $
                    \(e :: SomeException) -> pure (Nothing, ([ideErrorText file $ T.pack $ show e | not $ isBadDependency e],Nothing))
                modTime <- liftIO $ (currentValue =<<) <$> getValues state GetModificationTime file
                (bs, res) <- case res of
                    Nothing -> do
                        staleV <- liftIO $ getValues state key file
                        pure $ case staleV of
                            Nothing -> (toShakeValue ShakeResult bs, Failed)
                            Just v -> case v of
                                Succeeded ver v -> (toShakeValue ShakeStale bs, Stale ver v)
                                Stale ver v -> (toShakeValue ShakeStale bs, Stale ver v)
                                Failed -> (toShakeValue ShakeResult bs, Failed)
                    Just v -> pure (maybe ShakeNoCutoff ShakeResult bs, Succeeded (vfsVersion =<< modTime) v)
                liftIO $ setValues state key file res
                updateFileDiagnostics file (Key key) extras $ map (\(_,y,z) -> (y,z)) diags
                let eq = case (bs, fmap decodeShakeValue old) of
                        (ShakeResult a, Just (ShakeResult b)) -> a == b
                        (ShakeStale a, Just (ShakeStale b)) -> a == b
                        -- If we do not have a previous result
                        -- or we got ShakeNoCutoff we always return False.
                        _ -> False
                return $ RunResult
                    (if eq then ChangedRecomputeSame else ChangedRecomputeDiff)
                    (encodeShakeValue bs) $
                    A res bs


-- | Rule type, input file
data QDisk k = QDisk k NormalizedFilePath
  deriving (Eq, Generic)

instance Hashable k => Hashable (QDisk k)

instance NFData k => NFData (QDisk k)

instance Binary k => Binary (QDisk k)

instance Show k => Show (QDisk k) where
    show (QDisk k file) =
        show k ++ "; " ++ fromNormalizedFilePath file

type instance RuleResult (QDisk k) = Bool

data OnDiskRule = OnDiskRule
  { getHash :: Action BS.ByteString
  -- This is used to figure out if the state on disk corresponds to the state in the Shake
  -- database and we can therefore avoid rerunning. Often this can just be the file hash but
  -- in some cases we can be more aggressive, e.g., for GHC interface files this can be the ABI hash which
  -- is more stable than the hash of the interface file.
  -- An empty bytestring indicates that the state on disk is invalid, e.g., files are missing.
  -- We do not use a Maybe since we have to deal with encoding things into a ByteString anyway in the Shake DB.
  , runRule :: Action (IdeResult BS.ByteString)
  -- The actual rule code which produces the new hash (or Nothing if the rule failed) and the diagnostics.
  }

-- This is used by the DAML compiler for incremental builds. Right now this is not used by
-- ghcide itself but that might change in the future.
-- The reason why this code lives in ghcide and in particular in this module is that it depends quite heavily on
-- the internals of this module that we do not want to expose.
defineOnDisk
  :: (Shake.ShakeValue k, RuleResult k ~ ())
  => (k -> NormalizedFilePath -> OnDiskRule)
  -> Rules ()
defineOnDisk act = addBuiltinRule noLint noIdentity $
  \(QDisk key file) (mbOld :: Maybe BS.ByteString) mode -> do
      extras <- getShakeExtras
      let OnDiskRule{..} = act key file
      let validateHash h
              | BS.null h = Nothing
              | otherwise = Just h
      let runAct = actionCatch runRule $
              \(e :: SomeException) -> pure ([ideErrorText file $ T.pack $ displayException e | not $ isBadDependency e], Nothing)
      case mbOld of
          Nothing -> do
              (diags, mbHash) <- runAct
              updateFileDiagnostics file (Key key) extras $ map (\(_,y,z) -> (y,z)) diags
              pure $ RunResult ChangedRecomputeDiff (fromMaybe "" mbHash) (isJust mbHash)
          Just old -> do
              current <- validateHash <$> (actionCatch getHash $ \(_ :: SomeException) -> pure "")
              if mode == RunDependenciesSame && Just old == current && not (BS.null old)
                  then
                    -- None of our dependencies changed, we’ve had a successful run before and
                    -- the state on disk matches the state in the Shake database.
                    pure $ RunResult ChangedNothing (fromMaybe "" current) (isJust current)
                  else do
                    (diags, mbHash) <- runAct
                    updateFileDiagnostics file (Key key) extras $ map (\(_,y,z) -> (y,z)) diags
                    let change
                          | mbHash == Just old = ChangedRecomputeSame
                          | otherwise = ChangedRecomputeDiff
                    pure $ RunResult change (fromMaybe "" mbHash) (isJust mbHash)

needOnDisk :: (Shake.ShakeValue k, RuleResult k ~ ()) => k -> NormalizedFilePath -> Action ()
needOnDisk k file = do
    successfull <- apply1 (QDisk k file)
    liftIO $ unless successfull $ throwIO $ BadDependency (show k)

needOnDisks :: (Shake.ShakeValue k, RuleResult k ~ ()) => k -> [NormalizedFilePath] -> Action ()
needOnDisks k files = do
    successfulls <- apply $ map (QDisk k) files
    liftIO $ unless (and successfulls) $ throwIO $ BadDependency (show k)

toShakeValue :: (BS.ByteString -> ShakeValue) -> Maybe BS.ByteString -> ShakeValue
toShakeValue = maybe ShakeNoCutoff

data ShakeValue
    = ShakeNoCutoff
    -- ^ This is what we use when we get Nothing from
    -- a rule.
    | ShakeResult !BS.ByteString
    -- ^ This is used both for `Failed`
    -- as well as `Succeeded`.
    | ShakeStale !BS.ByteString
    deriving (Generic, Show)

instance NFData ShakeValue

encodeShakeValue :: ShakeValue -> BS.ByteString
encodeShakeValue = \case
    ShakeNoCutoff -> BS.empty
    ShakeResult r -> BS.cons 'r' r
    ShakeStale r -> BS.cons 's' r

decodeShakeValue :: BS.ByteString -> ShakeValue
decodeShakeValue bs = case BS.uncons bs of
    Nothing -> ShakeNoCutoff
    Just (x, xs)
      | x == 'r' -> ShakeResult xs
      | x == 's' -> ShakeStale xs
      | otherwise -> error $ "Failed to parse shake value " <> show bs


updateFileDiagnostics :: MonadIO m
  => NormalizedFilePath
  -> Key
  -> ShakeExtras
  -> [(ShowDiagnostic,Diagnostic)] -- ^ current results
  -> m ()
updateFileDiagnostics fp k ShakeExtras{diagnostics, hiddenDiagnostics, publishedDiagnostics, state, debouncer, eventer} current = liftIO $ do
    modTime <- (currentValue =<<) <$> getValues state GetModificationTime fp
    let (currentShown, currentHidden) = partition ((== ShowDiag) . fst) current
    mask_ $ do
        -- Mask async exceptions to ensure that updated diagnostics are always
        -- published. Otherwise, we might never publish certain diagnostics if
        -- an exception strikes between modifyVar but before
        -- publishDiagnosticsNotification.
        newDiags <- modifyVar diagnostics $ \old -> do
            let newDiagsStore = setStageDiagnostics fp (vfsVersion =<< modTime)
                                  (T.pack $ show k) (map snd currentShown) old
            let newDiags = getFileDiagnostics fp newDiagsStore
            _ <- evaluate newDiagsStore
            _ <- evaluate newDiags
            pure (newDiagsStore, newDiags)
        modifyVar_ hiddenDiagnostics $ \old -> do
            let newDiagsStore = setStageDiagnostics fp (vfsVersion =<< modTime)
                                  (T.pack $ show k) (map snd currentHidden) old
            let newDiags = getFileDiagnostics fp newDiagsStore
            _ <- evaluate newDiagsStore
            _ <- evaluate newDiags
            return newDiagsStore
        let uri = filePathToUri' fp
        let delay = if null newDiags then 0.1 else 0
        registerEvent debouncer delay uri $ do
             mask_ $ modifyVar_ publishedDiagnostics $ \published -> do
                 let lastPublish = HMap.lookupDefault [] uri published
                 when (lastPublish /= newDiags) $
                     eventer $ publishDiagnosticsNotification (fromNormalizedUri uri) newDiags
                 pure $! HMap.insert uri newDiags published

publishDiagnosticsNotification :: Uri -> [Diagnostic] -> LSP.FromServerMessage
publishDiagnosticsNotification uri diags =
    LSP.NotPublishDiagnostics $
    LSP.NotificationMessage "2.0" LSP.TextDocumentPublishDiagnostics $
    LSP.PublishDiagnosticsParams uri (List diags)

newtype Priority = Priority Double

setPriority :: Priority -> Action ()
setPriority (Priority p) = deprioritize p

sendEvent :: LSP.FromServerMessage -> Action ()
sendEvent e = do
    ShakeExtras{eventer} <- getShakeExtras
    liftIO $ eventer e

ideLogger :: IdeState -> Logger
ideLogger IdeState{shakeExtras=ShakeExtras{logger}} = logger

actionLogger :: Action Logger
actionLogger = do
    ShakeExtras{logger} <- getShakeExtras
    return logger


data GetModificationTime = GetModificationTime
    deriving (Eq, Show, Generic)
instance Hashable GetModificationTime
instance NFData   GetModificationTime
instance Binary   GetModificationTime

-- | Get the modification time of a file.
type instance RuleResult GetModificationTime = FileVersion

data FileVersion
    = VFSVersion Int
    | ModificationTime
      !Int   -- ^ Large unit (platform dependent, do not make assumptions)
      !Int   -- ^ Small unit (platform dependent, do not make assumptions)
    deriving (Show, Generic)

instance NFData FileVersion

vfsVersion :: FileVersion -> Maybe Int
vfsVersion (VFSVersion i) = Just i
vfsVersion ModificationTime{} = Nothing

-- | A comparision function where any VFS version is newer than an ondisk version
newerFileVersion :: FileVersion -> FileVersion -> Bool
newerFileVersion (VFSVersion i) (VFSVersion j) = i > j
newerFileVersion (VFSVersion {}) (ModificationTime {}) = True
newerFileVersion m1 m2 = modificationTime m1 > modificationTime m2

modificationTime :: FileVersion -> Maybe (Int, Int)
modificationTime VFSVersion{} = Nothing
modificationTime (ModificationTime large small) = Just (large, small)

getDiagnosticsFromStore :: StoreItem -> [Diagnostic]
getDiagnosticsFromStore (StoreItem _ diags) = concatMap SL.fromSortedList $ Map.elems diags


-- | Sets the diagnostics for a file and compilation step
--   if you want to clear the diagnostics call this with an empty list
setStageDiagnostics
    :: NormalizedFilePath
    -> TextDocumentVersion -- ^ the time that the file these diagnostics originate from was last edited
    -> T.Text
    -> [LSP.Diagnostic]
    -> DiagnosticStore
    -> DiagnosticStore
setStageDiagnostics fp timeM stage diags ds  =
    updateDiagnostics ds uri timeM diagsBySource
    where
        diagsBySource = Map.singleton (Just stage) (SL.toSortedList diags)
        uri = filePathToUri' fp

getAllDiagnostics ::
    DiagnosticStore ->
    [FileDiagnostic]
getAllDiagnostics =
    concatMap (\(k,v) -> map (fromUri k,ShowDiag,) $ getDiagnosticsFromStore v) . HMap.toList

getFileDiagnostics ::
    NormalizedFilePath ->
    DiagnosticStore ->
    [LSP.Diagnostic]
getFileDiagnostics fp ds =
    maybe [] getDiagnosticsFromStore $
    HMap.lookup (filePathToUri' fp) ds

filterDiagnostics ::
    (NormalizedFilePath -> Bool) ->
    DiagnosticStore ->
    DiagnosticStore
filterDiagnostics keep =
    HMap.filterWithKey (\uri _ -> maybe True (keep . toNormalizedFilePath') $ uriToFilePath' $ fromNormalizedUri uri)

filterVersionMap
    :: HMap.HashMap NormalizedUri (Set.Set TextDocumentVersion)
    -> HMap.HashMap NormalizedUri (Map TextDocumentVersion a)
    -> HMap.HashMap NormalizedUri (Map TextDocumentVersion a)
filterVersionMap =
    HMap.intersectionWith $ \versionsToKeep versionMap -> Map.restrictKeys versionMap versionsToKeep

updatePositionMapping :: IdeState -> VersionedTextDocumentIdentifier -> List TextDocumentContentChangeEvent -> IO ()
updatePositionMapping IdeState{shakeExtras = ShakeExtras{positionMapping}} VersionedTextDocumentIdentifier{..} (List changes) = do
    modifyVar_ positionMapping $ \allMappings -> do
        let uri = toNormalizedUri _uri
        let mappingForUri = HMap.lookupDefault Map.empty uri allMappings
        let (_, updatedMapping) =
                -- Very important to use mapAccum here so that the tails of
                -- each mapping can be shared, otherwise quadratic space is
                -- used which is evident in long running sessions.
                Map.mapAccumRWithKey (\acc _k (delta, _) -> let new = addDelta delta acc in (new, (delta, acc)))
                  zeroMapping
                  (Map.insert _version (shared_change, zeroMapping) mappingForUri)
        pure $! HMap.insert uri updatedMapping allMappings
  where
    shared_change = mkDelta changes

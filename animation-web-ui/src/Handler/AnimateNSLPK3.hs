{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{- RandNTypes is required for the type signature of getNextEventsDB, otherwise
animation-web-ui>     • Illegal polymorphic type:
animation-web-ui>         forall (m :: * -> *). MonadUnliftIO m => ReaderT SqlBackend m Int
animation-web-ui>       Perhaps you intended to use RankNTypes
animation-web-ui>     • In the expansion of type synonym ‘DB’
animation-web-ui>       In the type signature: getNextEventsDB :: DB Int -> [Entity Trees]
animation-web-ui>     |
animation-web-ui> 210 | getNextEventsDB :: DB Int -> [Entity Trees]
-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Handler.AnimateNSLPK3 where

import Import
import Data.Monoid (All(getAll))
import qualified Data.Text as T (unlines, pack, unpack, intercalate)
import Handler.Common
import Handler.Session ( sessionAddForm, getSessionId)
-- import NSLPK3 ()
import NSPK3_Animate (explore_tree_NSLPK3, 
  EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  NSLPK3_TEvent(..), NSLPK3_EventTree(..), formatEvents, formatTEvent, formatTEvents, getChannelList, getChannelList4Property
  )

import qualified Data.Map as M
import qualified Web.ServerSession.Frontend.Yesod as SS
import Yesod.Form.Bootstrap3
import Import (redirect, get404, setSession)
import Text.Read (readMaybe, read)
import Data.Graph (reachable)

getAnimateNSLPK3R :: Handler Html
getAnimateNSLPK3R = do
    -- Check if the event tree is already in the DB by looking for the ROOT event
    rootEventDB <- runDB $ getRootEventDB 
    -- liftIO $ print $ "rootEventDB" <> T.pack (show rootEventDB)
    case rootEventDB of
      [] -> liftHandler $ initInsertEventTreeToDB 
      _ -> return () -- So the tree is already in the DB

    maybeProtocol <- lookupSession $ sessionProtocolNameKey
    case maybeProtocol of
      -- We don't need to set the protocol name if it is already NSLPK3
      Just "NSLPK3" -> return ()
      -- Otherwise, clear the session and set the protocol name to NSLPK3 
      _ -> do
        clearSession
        setSession sessionProtocolNameKey "NSLPK3"

    msid <- getSessionId
    vars <- M.toAscList <$> getSession
    allEvents <- getAllNextEventsFromDB
    -- liftIO $ print $ "allEvents" <> T.pack (show allEvents)

    (manFormWidget, manFormEnctype) <- generateFormPost $ manualInputForm allEvents
--    (sessionAddFormWidget, sessionAddFormEnctype) <- generateFormPost sessionAddForm
    (autoFormWidget, autoFormEnctype) <- generateFormPost $ autoAnimationForm getChannelListPair 
    let submission = Nothing :: Maybe ManualInputForm 
        handlerName = "getAnimateNSLPK3R" :: Text
        -- allEvents = getAllEvents 
        -- allEvents = getAllIndexedEvents 

    nslpk3_plantumlinput <- plantUMLTextNSLPK3
    nslpk3_diagram <- getPlantUMLDiagram nslpk3_plantumlinput 
    nslpk3_plantumlinput_no_attack <- plantUMLTextNSLPK3_no_attack
    nslpk3_diagram_no_attack <- getPlantUMLDiagram nslpk3_plantumlinput_no_attack 

    plantUMLInput <- plantUMLInput4Animation
    diagram <- getPlantUMLDiagram plantUMLInput

    counterexample_input <- plantUMLInput4Counterexample 
    counterexample_diagram <- getPlantUMLDiagram counterexample_input 

    autoRes <- getCounterexamplesFromSessionPP

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Verification of the original Needham-Schroeder Public Key Protocol (the simplified 3-message version)"
        $(widgetFile "nslpk3")

postAnimateNSLPK3R :: Handler Html
postAnimateNSLPK3R = do
    msid <- getSessionId
    vars <- M.toAscList <$> getSession
    allEvents <-  getAllNextEventsFromDB 

    ((manualResult, manFormWidget), manFormEnctype) <- runFormPost $ identifyForm "manualInputForm" $ manualInputForm allEvents
    (autoFormWidget, autoFormEnctype) <- generateFormPost $ autoAnimationForm getChannelListPair
    let handlerName = "postAnimateNSLPK3R" :: Text
        submission = Nothing :: Maybe ManualInputForm

    case manualResult of
      FormSuccess res ->
            let (eid, ch, src, dest, msg) = manualSelectedEventId res
            in do 
              setSession "next" eid 
              liftIO $ print "Manual animation"
              appendEventInSession eid 
              appendPlantUMLInSession (src, dest, ch <> "." <> msg)
              return ()
      FormFailure _ -> do
          liftIO $ print "Manual form failure"
          return ()
      FormMissing -> do
          liftIO $ print "Manual form missing"
          return ()

    autoRes <- getCounterexamplesFromSessionPP

    nslpk3_plantumlinput <- plantUMLTextNSLPK3
    nslpk3_diagram <- getPlantUMLDiagram nslpk3_plantumlinput 
    nslpk3_plantumlinput_no_attack <- plantUMLTextNSLPK3_no_attack
    nslpk3_diagram_no_attack <- getPlantUMLDiagram nslpk3_plantumlinput_no_attack 

    plantUMLInput <- plantUMLInput4Animation
    diagram <- getPlantUMLDiagram plantUMLInput

    counterexample_input <- plantUMLInput4Counterexample 
    counterexample_diagram <- getPlantUMLDiagram counterexample_input 

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Verification of the original Needham-Schroeder Public Key Protocol (the simplified 3-message version)"
        $(widgetFile "nslpk3")

    redirect $ AnimateNSLPK3R :#: ("animation_forms" :: Text)

postAnimateNSLPK3AutoR :: Handler () 
postAnimateNSLPK3AutoR = do
  processForm "Automatic check form" (autoAnimationForm getChannelListPair) $ autoFormHandler 

autoFormHandler :: AutoInputForm -> Handler String
autoFormHandler autoFormRes = do 
      clearSessionForCounterexamples
      res <- autoCheck reach ch1 msg1 ch2 msg2
      -- setMessage $ toHtml $ "Automatic reachability check counterexamples: " ++ show (length res) ++ "."
      liftIO $ print ("Automatic reachability check counterexamples: " ++ show (length res) ++ ".")
      addCounterexamplesToSession res
      return $ concat
        [ "Automatic checking ["
        , show ch2 
        , "/ "
        , show msg2
        , "] with event for monitor ["
        , show ch1 
        , "/ "
        , show msg1
        , "]." ]
    where 
      reach = autoReach autoFormRes 
      ch1 = autoMonitorChannel autoFormRes 
      msg1 = autoMonitorMsg autoFormRes 
      ch2 = autoCheckChannel autoFormRes 
      msg2 = autoCheckMsg autoFormRes 

-- | Update the session to a corresponding selected counterexample and produce its PlantUML text input
postViewNSLPK3CounterExampleR :: Int -> Handler () 
postViewNSLPK3CounterExampleR no = do
  maybeTrace <- lookupSession $ sessionCounterexampleKey ++ (T.pack $ show no) 
  case maybeTrace of 
    Nothing -> return () 
    Just tr -> do 
      let eventIdListStr = splitOn ',' (T.unpack tr)  
          eventIdList = map read eventIdListStr
      -- (eid, (ch, src, dest, msg))
      eventListTuples <- getEventsFromDB eventIdList 
      liftIO $ print $ "eventListTuples" <> (events2PlantUMLInput eventListTuples)
      setSession sessionCntExPlantumlInputKey $ events2PlantUMLInput eventListTuples
      return ()
  redirect $ AnimateNSLPK3R :#: ("counterexample" :: Text)

postAnimateNSLPK3ResetR :: Handler () 
postAnimateNSLPK3ResetR = do 
  clearSession
  redirect $ AnimateNSLPK3R :#: ("animation_forms" :: Text)

-- | Initialise the database with explored tree and insert all events into the DB
initInsertEventTreeToDB :: Handler ()
initInsertEventTreeToDB = do
    -- liftIO $ print "initInsertEventTreeToDB"
    (depth, internal_depth) <- getEventTreeDepth
    case explore_tree_NSLPK3 depth internal_depth of
      ETNode (TEP 0 0 Root) trees -> do 
        -- insert the ROOT event with its parent id set to -1
        runDB $ do insert_ $ NSLPK3Trees "NSLPK3" 0 0 0 (-1) (NSLPK3_TEvent Root)
        case trees of
          [] -> return ()
          (xs) -> do 
            -- liftIO $ print "initInsertEventTreeToDB" 
            eid <- traverseTree (map NSLPK3_EventTree xs) 0 0
            return ()
      _ -> return ()

-- | Traverse a list of event trees based on current event id and parent
traverseTree :: [NSLPK3_EventTree] -> Int -> Int -> Handler Int 
traverseTree [] eid parent = return eid
traverseTree (x:xs) eid parent = case x of 
  NSLPK3_EventTree (ETNode et@(TEP d n e) trees) -> do
        -- logInfo $ "Insert: " <> T.pack (show e)
        runDB $ do insert_ $ NSLPK3Trees "NSLPK3" (eid+1) d n parent (NSLPK3_TEvent e)
        eid1 <- traverseTree (map NSLPK3_EventTree trees) (eid+1) (eid+1)
        eid2 <- traverseTree xs eid1 parent
        return eid2 
--  _ -> return ()

-- | Get the ROOT event from the database
getRootEventDB :: DB [Entity NSLPK3Trees]
-- The ROOT event
getRootEventDB = selectList [NSLPK3TreesDepth ==. 0, NSLPK3TreesNumber ==. 0, NSLPK3TreesEvent ==. (NSLPK3_TEvent Root)] [Asc NSLPK3TreesId]
-- Check f the next (1st level) events are already in the DB
-- getRootEventDB = selectList [NSLPK3TreesDepth ==. 1] [Asc NSLPK3TreesId]

-- | Get the next events for animation from current chosen event 
getNextEventsDB :: Int -> DB [Entity NSLPK3Trees]
getNextEventsDB parent_eid = selectList [NSLPK3TreesParent ==. parent_eid] [Asc NSLPK3TreesId]

-- | Convert a list of tree entities to a list of event tuples, indexed by the depth number 
entities2EventListIndexedByDepthNumber:: [Entity NSLPK3Trees] -> [(Text, (Text, Text, Text, Text, Text))]
entities2EventListIndexedByDepthNumber [] = []
entities2EventListIndexedByDepthNumber (x:xs) = case x of 
  Entity _ (NSLPK3Trees protocol eid depth number parent event) -> case event of 
    NSLPK3_TEvent Root -> (T.pack $ show number, (T.pack $ show eid, "ROOT", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumber xs
    NSLPK3_TEvent Deadlocked -> (T.pack $ show number, (T.pack $ show eid, "Deadlocked", "Sys", "Env", "") ) : entities2EventListIndexedByDepthNumber xs
    NSLPK3_TEvent Terminated -> (T.pack $ show number, (T.pack $ show eid, "Terminated", "Sys", "Env", "") ) : entities2EventListIndexedByDepthNumber xs
    NSLPK3_TEvent Divergent -> (T.pack $ show number, (T.pack $ show eid, "Divergent", "Sys", "Env", "") ) : entities2EventListIndexedByDepthNumber xs
    NSLPK3_TEvent (EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ formatEvents e in 
      (T.pack $ show number, (T.pack $ show eid, T.pack $ ch, T.pack $ src, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByDepthNumber xs

-- | Convert a list of tree entities to a list of event tuples, indexed by the eid number 
entities2EventListIndexedByEid :: [Entity NSLPK3Trees] -> [(Text, (Text, Text, Text, Text))]
entities2EventListIndexedByEid [] = []
entities2EventListIndexedByEid (x:xs) = case x of 
  Entity _ (NSLPK3Trees protocol eid depth number parent event) -> case event of 
    NSLPK3_TEvent Root -> (T.pack $ show eid, ("ROOT", "Env", "Env", "") ) : entities2EventListIndexedByEid xs
    NSLPK3_TEvent Deadlocked -> (T.pack $ show eid, ("Deadlocked", "Sys", "Env", "") ) : entities2EventListIndexedByEid xs
    NSLPK3_TEvent Terminated -> (T.pack $ show eid, ("Terminated", "Sys", "Env", "") ) : entities2EventListIndexedByEid xs
    NSLPK3_TEvent Divergent -> (T.pack $ show eid, ("Divergent", "Sys", "Env", "") ) : entities2EventListIndexedByEid xs
    NSLPK3_TEvent (EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ formatEvents e in 
      (T.pack $ show eid, (T.pack $ ch, T.pack $ src, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByEid xs

-- | Get all events to be shown and animated
getAllNextEventsFromDB :: Handler [(Text, (Text, Text, Text, Text, Text))]
getAllNextEventsFromDB = do 
    -- We use the 'next' key to store the current explored event (eid), whose children we want to animate
    maybeNext <- lookupSession "next"
    -- Here we get all events to be shown and animated
    allEvents <- case maybeNext of
      Nothing -> do 
        setSession "next" "0"
        nextEvents <- runDB $ (getNextEventsDB 0)
        return $ entities2EventListIndexedByDepthNumber nextEvents
      Just str_parent_eid -> case (readMaybe $ T.unpack str_parent_eid) of
        Nothing -> do 
          setSession "next" "0"
          nextEvents <- runDB $ (getNextEventsDB 0)
          return $ entities2EventListIndexedByDepthNumber nextEvents
        Just parent_eid -> do
          nextEvents <- runDB $ getNextEventsDB parent_eid 
          return $ entities2EventListIndexedByDepthNumber nextEvents
    return allEvents

-- | Append the selected event to the trace (or the counterexample if security is violated)
appendEventInSession :: Text -> Handler () 
appendEventInSession eid = do 
  maybeNext <- lookupSession "trace"
  case maybeNext of
    Nothing -> do 
      setSession "trace" (eid)
    Just str_trace -> do 
      setSession "trace" (str_trace ++ ";" ++ eid )

-- | Append the selected event to the trace (or the counterexample if security is violated)
appendPlantUMLInSession :: (Text, Text, Text) -> Handler () 
appendPlantUMLInSession (src, dst, ch_msg) = do 
  maybeNext <- lookupSession "plantuml_input"
  case maybeNext of
    Nothing -> do 
      setSession "plantuml_input" (formatPlantUMLInput (src, dst, ch_msg))
    Just str_trace -> do 
      setSession "plantuml_input" (str_trace ++ "\n" ++ formatPlantUMLInput (src, dst, ch_msg))

getChannelListPair :: [(Text, Text)]
getChannelListPair = map (\x -> (T.pack $ x, T.pack $ x)) getChannelList4Property

isMessageMatchAll :: Maybe Text -> Bool
isMessageMatchAll msg = (msg == Just "") || (msg == Just "*") || (msg == Nothing)

isMessageMatch :: Maybe Text -> Text -> Bool
isMessageMatch msg msg1 = case msg of 
  Nothing -> False 
  Just msg_body -> msg1 == msg_body 
 
isMessageMatch' :: Text -> Maybe Text -> (Text, Text, Text, Text) -> Bool
isMessageMatch' chIn maybeMsgIn (ch, src, dest, msg) = case maybeMsgIn of 
  Nothing -> (chIn == ch)
  Just msgIn -> (chIn <> msgIn) == formatEventForDisplay ch src dest msg 

isMatchedEvent :: Text -> Maybe Text -> NSLPK3_TEvent -> Bool
isMatchedEvent chIn msgIn event = 
  if chIn == "" then False else
    case event of  
      NSLPK3_TEvent Root -> (chIn == "ROOT") && (isMessageMatchAll msgIn)
      NSLPK3_TEvent Deadlocked -> (chIn == "Deadlocked") && (isMessageMatchAll msgIn)
      NSLPK3_TEvent Terminated -> (chIn == "Terminated") && (isMessageMatchAll msgIn) 
      NSLPK3_TEvent Divergent -> (chIn == "Divergent") && (isMessageMatchAll msgIn)
      NSLPK3_TEvent (EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ formatEvents e in 
        isMessageMatch' chIn msgIn (T.pack ch, T.pack src, T.pack dest, T.pack msg)

-- | Automatically reachability check with events for monitoring 
autoCheck :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text -> Handler [[Int]]
autoCheck reach chMonitor msgMonitor chCheck msgCheck = do 
    maybeNext <- lookupSession "next"
    case maybeNext of
      Nothing -> return [[]] 
      Just str_parent_eid -> case (readMaybe $ T.unpack str_parent_eid) of
        Nothing -> return [[]] 
        Just parent_eid -> do
          nextEvents <- runDB $ getNextEventsDB parent_eid 
          -- Current trace should be the value of "trace" in session, but it is String. Here we need a TEvent.
          -- So we set it to empty list and let higher layer combine them.
          exhaustiveSearch reach chMonitor msgMonitor chCheck msgCheck [] 0 nextEvents

-- | Automatically reachability check with events for monitoring
exhaustiveSearch :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text 
  -> [Int] -- current trace
  -> Int -- the number of times that the event for monitoring occurred
  -> [Entity NSLPK3Trees] 
  -> Handler [[Int]] -- all counterexamples
exhaustiveSearch reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore [] = return []
exhaustiveSearch reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore (x:xs) = do
  xsRes <- exhaustiveSearch reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore xs
  case x of 
    Entity _ (NSLPK3Trees protocol eid depth number parent event) -> 
      case isMatchedEvent chMonitor msgMonitor event of
        True -> do 
          nextEvents <- runDB $ getNextEventsDB eid 
          xRes <- exhaustiveSearch reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) (monitoredBefore + 1) nextEvents 
          return (xsRes ++ xRes)
        False -> 
          case isMatchedEvent chCheck msgCheck event of
            -- If the event for checking matches, finish the search along this path, and add the current trace to the counterexamples 
            True -> case reach of 
              Correspondence -> do -- If checking for reachability, check if the event for monitoring is reachable
                if monitoredBefore > 0 then 
                  return xsRes  -- this is not a counterexample
                else
                  return ([currentTrace ++ [eid]] ++ xsRes) -- this is a counterexample
              Injective_Correspondence -> do
                if monitoredBefore == 1 then 
                  return xsRes  -- this is not a counterexample
                else
                  return ([currentTrace ++ [eid]] ++ xsRes) -- this is a counterexample
              Secrecy -> -- If checking for secrecy, this is the counterexample 
                return ([currentTrace ++ [eid]] ++ xsRes)
            False -> do
              nextEvents <- runDB $ getNextEventsDB eid 
              xRes <- exhaustiveSearch reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) monitoredBefore nextEvents 
              return (xsRes ++ xRes)

-- | A session key "number_of_counterexamples" to store the number of counterexamples
--   and additional n session variables "counterexample_i" to store the trace of the i-th counterexample 
clearSessionForCounterexamples :: Handler ()
clearSessionForCounterexamples = do 
  deleteSession sessionCntExPlantumlInputKey
  maybeNumber <- lookupSession sessionNumberOfCounterexamplesKey
  case maybeNumber of 
    Nothing -> -- add this session variable 
      setSession sessionNumberOfCounterexamplesKey "0" 
    Just str_n -> case (readMaybe $ T.unpack str_n) of
      Nothing -> setSession sessionNumberOfCounterexamplesKey "0" 
      Just n -> do
        deleteAllCounterexamples n 
        return ()
        where 
          deleteAllCounterexamples :: Int -> Handler ()
          deleteAllCounterexamples m = if m == 0 then return () else do 
            deleteSession $ "counterexample_" ++ (T.pack $ show m)
            deleteAllCounterexamples (m - 1) 

-- | Add counterexamples to sessions
addCounterexamplesToSession :: [[Int]] -> Handler ()
addCounterexamplesToSession xs = do 
  setSession sessionNumberOfCounterexamplesKey (T.pack $ show $ length xs)
  addCounterexamplesToSession' xs 1
  where 
    addCounterexamplesToSession' :: [[Int]] -> Int -> Handler ()
    addCounterexamplesToSession' [] _ = return ()
    addCounterexamplesToSession' (m:ms) i = do 
      -- setSession ("counterexample_" ++ (T.pack $ show i)) (T.pack $ show m)
      -- set "counterexample_i" to "23, 24, 61, ..."
      setSession ("counterexample_" ++ (T.pack $ show i)) (T.pack $ intercalate "," (map show m))
      addCounterexamplesToSession' ms (i + 1)

-- | A session key "number_of_counterexamples" to store the number of counterexamples
--   and additional n session variables "counterexample_i" to store the trace of the i-th counterexample 
--   What this function returns is the index of the counterexample and the trace of the counterexample in terms of eid,
--   like [(1, "23, 24, 61, ..."), ...]
getCounterexamplesFromSession :: Handler [(Int, Text)]
getCounterexamplesFromSession = do 
  maybeNumber <- lookupSession sessionNumberOfCounterexamplesKey
  case maybeNumber of 
    Nothing -> return [] 
    Just str_n -> case (readMaybe $ T.unpack str_n) of
      Nothing -> return [] 
      Just n -> do
        ns <- getCounterexamples n 
        return ns
        where 
          getCounterexamples :: Int -> Handler [(Int, Text)]
          getCounterexamples m = if m == 0 then return [] else do 
            ms <- getCounterexamples (m - 1) 
            maybeTrace <- lookupSession $ sessionCounterexampleKey ++ (T.pack $ show m)
            case maybeTrace of
              Nothing -> return ms
              Just tr -> return $ ms ++ [(m, tr)]

-- | A function to turn a list of eid in form of "23, 24, 61, ..." into a list of pretty printed events
--  like 
eidsToPrettyEvents :: Text -> Handler [Text]
eidsToPrettyEvents events = do
      let eventIdListStr = splitOn ',' (T.unpack events)  
          eventIdList = map read eventIdListStr
      -- (eid, (ch, src, dest, msg))
      eventListTuples <- getEventsFromDB eventIdList 
      return $ map (\(eid, (ch, src, dst, msg)) -> formatEventForDisplay ch src dst msg) eventListTuples

-- | A session key "number_of_counterexamples" to store the number of counterexamples
--   and additional n session variables "counterexample_i" to store the trace of the i-th counterexample 
--   What this function returns is the index of the counterexample and the trace of the i-th counterexample in terms of pretty printed events, 
--   like [(1, "[Sig]ClaimSecret[Alice-->Intruder].N_Alice ; Send[Alice-->Intruder].{<N_Alice, Alice>}^a_PK_Intruder ; ..."), ...]
getCounterexamplesFromSessionPP :: Handler [(Int, Text)]
getCounterexamplesFromSessionPP = do 
  maybeNumber <- lookupSession sessionNumberOfCounterexamplesKey
  case maybeNumber of 
    Nothing -> return [] 
    Just str_n -> case (readMaybe $ T.unpack str_n) of
      Nothing -> return [] 
      Just n -> do
        ns <- getCounterexamples n 
        return ns
        where 
          getCounterexamples :: Int -> Handler [(Int, Text)]
          getCounterexamples m = if m == 0 then return [] else do 
            ms <- getCounterexamples (m - 1) 
            maybeTrace <- lookupSession $ sessionCounterexampleKey ++ (T.pack $ show m)
            case maybeTrace of
              Nothing -> return ms
              Just tr -> do
                events <- eidsToPrettyEvents tr
                let tr = T.intercalate "  #  " events
                return $ ms ++ [(m, tr)]

-- | Helper function for form processing handlers.
processForm :: String -> Form a -> (a -> Handler String) -> Handler ()
processForm formName form act = do
  ((result, _), _) <- runFormPost form
  (>>= setMessage . toHtml) $
    case result of
      FormSuccess ret  -> act ret
      FormFailure errs -> return $ formName ++ " has errors: " ++ show errs ++ "."
      FormMissing      -> return $ formName ++ " is missing."
  -- redirect AnimateNSLPK3R 
  redirect $ AnimateNSLPK3R :#: ("automatic_animation" :: Text)

-- | Our definition of horizontal form.
horizontal :: BootstrapFormLayout
horizontal = BootstrapHorizontalForm (ColSm 0) (ColSm 4) (ColSm 0) (ColSm 6)

getEventFromDB :: Int -> Handler (Maybe NSLPK3_TEvent)
getEventFromDB eid = do 
  maybeEvent <- runDB $ getBy $ UniqueTrees_NSLPK3 eid 
  case maybeEvent of 
    Nothing -> return Nothing 
    Just (Entity _ (NSLPK3Trees protocol eid depth number parent event)) -> 
      return $ Just event

-- | Get a list of events from the database in a form of (eid, (channel, src, dest, msg))
getEventsFromDB :: [Int] -> Handler [(Text, (Text, Text, Text, Text))]
getEventsFromDB eventIds = do 
  events <- runDB $ selectList [NSLPK3TreesEid <-. eventIds] [Asc NSLPK3TreesId]
  return $ entities2EventListIndexedByEid events

-- | Convert a list of events to a PlantUML input
events2PlantUMLInput :: [(Text, (Text, Text, Text, Text))] -> Text
events2PlantUMLInput [] = ""
events2PlantUMLInput ((_, (ch, src, dst, msg)):xs) = do
  formatPlantUMLInput (src, dst, ch <> "." <> msg) ++ "\n" ++ events2PlantUMLInput xs

formatAgentName :: String -> String
formatAgentName "A0" = "Alice"
formatAgentName "A1" = "Bob"
formatAgentName "I" = "Intruder"
formatAgentName n = n  

-- | Convert Agent names to Alice and Bob etc.
convertAgentName :: (String, String, String, String, String) -> (String, String, String, String, String)
convertAgentName (ch, src, mid, dst, msg) = case (src, mid) of
  ("I", "I") -> (ch, formatAgentName src, formatAgentName mid, formatAgentName dst, msg)
  (_, "I") -> (ch, formatAgentName src, formatAgentName mid, formatAgentName mid, msg)
  (_, _) -> (ch, formatAgentName src, formatAgentName mid, formatAgentName dst, msg)

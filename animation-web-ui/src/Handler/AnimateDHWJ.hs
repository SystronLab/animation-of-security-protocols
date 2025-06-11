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

module Handler.AnimateDHWJ where

import Import
import Data.Monoid (All(getAll))
import qualified Data.Text as T (unlines, pack, unpack, intercalate)
import Handler.Common
--    ( ManualInputForm(manualSelectedEventId),
--      getPlantUMLDiagram,
--      formatPlantUMLInput,
--      plantUMLInput4Animation,
--      manualInputForm,
--      autoAnimationForm,
--      AutoInputForm(autoReach, autoMonitorChannel, autoMonitorMsg, autoCheckChannel, autoCheckMsg),
--      getEventTreeDepth,
--      formatTEvent,
--      formatTEvents, plantUMLTextEmpty, sessionCounterexampleKey, sessionCntExPlantumlInputKey,
--      splitOn, plantUMLInput4Counterexample,  
--    )
import Handler.Session ( sessionAddForm, getSessionId)
import DHWJ_config (Deve(..), equal_deve)
-- import DHWJ_wbplsec (dHWJ_active)
import qualified DHWJ_Animate as NSA (explore_tree_DHWJ, 
  EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  DHWJ_TEvent(..), DHWJ_EventTree(..), formatEvents, formatTEvent, formatTEvents, getChannelList, getChannelList4Property
  )

import qualified Data.Map as M
import qualified Web.ServerSession.Frontend.Yesod as SS
import Yesod.Form.Bootstrap3
import Import (redirect, get404, setSession)
import Text.Read (readMaybe, read)
import Data.Graph (reachable)

getAnimateDHWJR :: Handler Html
getAnimateDHWJR = do
    -- Check if the event tree is already in the DB by looking for the ROOT event
    rootEventDBEve1 <- runDB $ getRootEventDBEve1 
    -- liftIO $ print $ "rootEventDB" <> T.pack (show rootEventDB)
    case rootEventDBEve1 of
      [] -> liftHandler $ initInsertEventTreeToDB Eve1
      _ -> return () -- So the tree is already in the DB

    rootEventDBEve2 <- runDB $ getRootEventDBEve2 
    case rootEventDBEve2 of
      [] -> liftHandler $ initInsertEventTreeToDB Eve2 
      _ -> return () -- So the tree is already in the DB

    rootEventDBEve3 <- runDB $ getRootEventDBEve3 
    case rootEventDBEve3 of
      [] -> liftHandler $ initInsertEventTreeToDB Eve3 
      _ -> return () -- So the tree is already in the DB

    rootEventDBEve4 <- runDB $ getRootEventDBEve4 
    case rootEventDBEve4 of
      [] -> liftHandler $ initInsertEventTreeToDB Eve4 
      _ -> return () -- So the tree is already in the DB

    maybeProtocol <- lookupSession $ sessionProtocolNameKey
    case maybeProtocol of
      -- We don't need to set the protocol name if it is already DHWJ
      Just "DHWJEve1" -> return ()
      Just "DHWJEve2" -> return ()
      Just "DHWJEve3" -> return ()
      Just "DHWJEve4" -> return ()
      -- Otherwise, clear the session and set the protocol name to DHWJ 
      _ -> do
        clearSession
        setSession sessionProtocolNameKey "DHWJEve3"

    maybeEve <- currentEveScenario
    (eveFormWidget, eveFormEnctype) <- 
      case maybeEve of
        Just Eve1 -> generateFormPost $ eveScenarioForm Eve1
        Just Eve2 -> generateFormPost $ eveScenarioForm Eve2
        Just Eve3 -> generateFormPost $ eveScenarioForm Eve3
        Just Eve4 -> generateFormPost $ eveScenarioForm Eve4
        _ -> do 
          clearSession
          setSession sessionProtocolNameKey "DHWJEve3"
          generateFormPost $ eveScenarioForm Eve3

    msid <- getSessionId
    vars <- M.toAscList <$> getSession
    allEvents <- getAllNextEventsFromDB

    (manFormWidget, manFormEnctype) <- generateFormPost $ manualInputForm $ discardMid allEvents
--    (sessionAddFormWidget, sessionAddFormEnctype) <- generateFormPost sessionAddForm
    (autoFormWidget, autoFormEnctype) <- generateFormPost $ autoAnimationForm getChannelListPair 

    let submission = Nothing :: Maybe ManualInputForm 
        handlerName = "getAnimateDHWJR" :: Text
        -- allEvents = getAllEvents 
        -- allEvents = getAllIndexedEvents 

    dhwj_plantumlinput <- plantUMLTextDHWJ
    dhwj_diagram <- getPlantUMLDiagram dhwj_plantumlinput 
    dhwj_plantumlinput_no_attack <- plantUMLTextDHWJ_no_attack
    dhwj_diagram_no_attack <- getPlantUMLDiagram dhwj_plantumlinput_no_attack 

    plantUMLInput <- plantUMLInput4Animation
    diagram <- getPlantUMLDiagram plantUMLInput

    counterexample_input <- plantUMLInput4Counterexample 
    counterexample_diagram <- getPlantUMLDiagram counterexample_input 

    autoRes <- getCounterexamplesFromSessionPP

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Verification of the original Needham-Schroeder Public Key Protocol (the simplified 3-message version)"
        $(widgetFile "dhwj")

postAnimateDHWJR :: Handler Html
postAnimateDHWJR = do
    msid <- getSessionId
    vars <- M.toAscList <$> getSession
    allEvents <-  getAllNextEventsFromDB 

    ((manualResult, manFormWidget), manFormEnctype) <- runFormPost $ identifyForm "manualInputForm" $ manualInputForm $ discardMid allEvents
    (autoFormWidget, autoFormEnctype) <- generateFormPost $ autoAnimationForm getChannelListPair
    (eveFormWidget, eveFormEnctype) <- generateFormPost $ eveScenarioForm Eve3
    let handlerName = "postAnimateDHWJR" :: Text
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

    dhwj_plantumlinput <- plantUMLTextDHWJ
    dhwj_diagram <- getPlantUMLDiagram dhwj_plantumlinput 
    dhwj_plantumlinput_no_attack <- plantUMLTextDHWJ_no_attack
    dhwj_diagram_no_attack <- getPlantUMLDiagram dhwj_plantumlinput_no_attack 

    plantUMLInput <- plantUMLInput4Animation
    diagram <- getPlantUMLDiagram plantUMLInput

    counterexample_input <- plantUMLInput4Counterexample 
    counterexample_diagram <- getPlantUMLDiagram counterexample_input 

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Verification of the original Needham-Schroeder Public Key Protocol (the simplified 3-message version)"
        $(widgetFile "dhwj")

    redirect $ AnimateDHWJR :#: ("animation_forms" :: Text)

postAnimateDHWJAutoR :: Handler () 
postAnimateDHWJAutoR = do
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
postViewDHWJCounterExampleR :: Int -> Handler () 
postViewDHWJCounterExampleR no = do
  maybeTrace <- lookupSession $ sessionCounterexampleKey ++ (T.pack $ show no) 
  case maybeTrace of 
    Nothing -> return () 
    Just tr -> do 
      let eventIdListStr = splitOn ',' (T.unpack tr)  
          eventIdList = map read eventIdListStr
      -- (eid, (ch, src, dest, msg))
      maybeEve <- currentEveScenario
      eventListTuples <- 
        case maybeEve of
          Just Eve1 -> getEventsFromDBEve1 eventIdList 
          Just Eve2 -> getEventsFromDBEve2 eventIdList 
          Just Eve3 -> getEventsFromDBEve3 eventIdList 
          Just Eve4 -> getEventsFromDBEve4 eventIdList 
          _ -> return $ [] 
      liftIO $ print $ "eventListTuples" <> (events2PlantUMLInput eventListTuples)
      setSession sessionCntExPlantumlInputKey $ events2PlantUMLInput eventListTuples
      return ()
  redirect $ AnimateDHWJR :#: ("counterexample" :: Text)

postAnimateDHWJResetR :: Handler () 
postAnimateDHWJResetR = do 
  clearSession
  redirect $ AnimateDHWJR :#: ("animation_forms" :: Text)

postChangeDHWJProtocolR :: Handler () 
postChangeDHWJProtocolR = do
  processForm "Change the location of Eavesdropper" (eveScenarioForm Eve3) $ eveFormHandler 

eveFormHandler :: EveInputForm -> Handler String
eveFormHandler eveInput = do 
  case eve eveInput of 
    Eve1 -> setSession sessionProtocolNameKey "DHWJEve1"
    Eve2 -> setSession sessionProtocolNameKey "DHWJEve2"
    Eve3 -> setSession sessionProtocolNameKey "DHWJEve3" 
    Eve4 -> setSession sessionProtocolNameKey "DHWJEve4" 
    _ -> setSession sessionProtocolNameKey "DHWJEve3"

  return $ concat
        [ "Set the Eavesdropper location scenario to: "
        , show (eve eveInput) 
        , "." ]

  redirect $ AnimateDHWJR 

-- | Initialise the database with explored tree and insert all events into the DB
initInsertEventTreeToDB :: Deve -> Handler ()
initInsertEventTreeToDB eve = do
    -- liftIO $ print "initInsertEventTreeToDB"
    (depth, internal_depth) <- getEventTreeDepth
    case eve of
      Eve1 -> 
        case NSA.explore_tree_DHWJ depth internal_depth Eve1 of
          NSA.ETNode (NSA.TEP 0 0 NSA.Root) trees -> do 
            -- insert the ROOT event with its parent id set to -1
            runDB $ do insert_ $ DHWJTreesEve1 "DHWJEve1" 0 0 0 (-1) (NSA.DHWJ_TEvent NSA.Root)
            case trees of
              [] -> return ()
              (xs) -> do 
                -- liftIO $ print "initInsertEventTreeToDB" 
                eid <- traverseTree (map NSA.DHWJ_EventTree xs) 0 0 eve
                return ()
          _ -> return ()
      Eve2 -> 
        case NSA.explore_tree_DHWJ depth internal_depth Eve2 of
          NSA.ETNode (NSA.TEP 0 0 NSA.Root) trees -> do 
            -- insert the ROOT event with its parent id set to -1
            runDB $ do insert_ $ DHWJTreesEve2 "DHWJEve2" 0 0 0 (-1) (NSA.DHWJ_TEvent NSA.Root)
            case trees of
              [] -> return ()
              (xs) -> do 
                -- liftIO $ print "initInsertEventTreeToDB" 
                eid <- traverseTree (map NSA.DHWJ_EventTree xs) 0 0 eve
                return ()
          _ -> return ()
      Eve3 -> 
        case NSA.explore_tree_DHWJ depth internal_depth Eve3 of
          NSA.ETNode (NSA.TEP 0 0 NSA.Root) trees -> do 
            -- insert the ROOT event with its parent id set to -1
            runDB $ do insert_ $ DHWJTreesEve3 "DHWJEve3" 0 0 0 (-1) (NSA.DHWJ_TEvent NSA.Root)
            case trees of
              [] -> return ()
              (xs) -> do 
                -- liftIO $ print "initInsertEventTreeToDB" 
                eid <- traverseTree (map NSA.DHWJ_EventTree xs) 0 0 eve
                return ()
          _ -> return ()
      Eve4 -> 
        case NSA.explore_tree_DHWJ depth internal_depth Eve4 of
          NSA.ETNode (NSA.TEP 0 0 NSA.Root) trees -> do 
            -- insert the ROOT event with its parent id set to -1
            runDB $ do insert_ $ DHWJTreesEve4 "DHWJEve4" 0 0 0 (-1) (NSA.DHWJ_TEvent NSA.Root)
            case trees of
              [] -> return ()
              (xs) -> do 
                -- liftIO $ print "initInsertEventTreeToDB" 
                eid <- traverseTree (map NSA.DHWJ_EventTree xs) 0 0 eve
                return ()
          _ -> return ()
      _ -> return ()

-- | Traverse a list of event trees based on current event id and parent
traverseTree :: [NSA.DHWJ_EventTree] -> Int -> Int -> Deve -> Handler Int 
traverseTree [] eid parent deve = return eid
traverseTree (x:xs) eid parent deve = case x of 
  NSA.DHWJ_EventTree (NSA.ETNode et@(NSA.TEP d n e) trees) -> 
    case deve of
      Eve1 -> do
        -- logInfo $ "Insert: " <> T.pack (show e)
        runDB $ do insert_ $ DHWJTreesEve1 "DHWJEve1" (eid+1) d n parent (NSA.DHWJ_TEvent e)
        eid1 <- traverseTree (map NSA.DHWJ_EventTree trees) (eid+1) (eid+1) deve
        eid2 <- traverseTree xs eid1 parent deve
        return eid2 
      Eve2 -> do
        -- logInfo $ "Insert: " <> T.pack (show e)
        runDB $ do insert_ $ DHWJTreesEve2 "DHWJEve2" (eid+1) d n parent (NSA.DHWJ_TEvent e)
        eid1 <- traverseTree (map NSA.DHWJ_EventTree trees) (eid+1) (eid+1) deve
        eid2 <- traverseTree xs eid1 parent deve
        return eid2 
      Eve3 -> do
        -- logInfo $ "Insert: " <> T.pack (show e)
        runDB $ do insert_ $ DHWJTreesEve3 "DHWJEve3" (eid+1) d n parent (NSA.DHWJ_TEvent e)
        eid1 <- traverseTree (map NSA.DHWJ_EventTree trees) (eid+1) (eid+1) deve
        eid2 <- traverseTree xs eid1 parent deve
        return eid2
      Eve4 -> do
        -- logInfo $ "Insert: " <> T.pack (show e)
        runDB $ do insert_ $ DHWJTreesEve4 "DHWJEve4" (eid+1) d n parent (NSA.DHWJ_TEvent e)
        eid1 <- traverseTree (map NSA.DHWJ_EventTree trees) (eid+1) (eid+1) deve
        eid2 <- traverseTree xs eid1 parent deve
        return eid2

-- | Get the ROOT event from the database
getRootEventDBEve1 :: DB [Entity DHWJTreesEve1]
-- The ROOT event
getRootEventDBEve1 = selectList [DHWJTreesEve1Depth ==. 0, DHWJTreesEve1Number ==. 0, DHWJTreesEve1Event ==. (NSA.DHWJ_TEvent NSA.Root)] [Asc DHWJTreesEve1Id]
-- Check f the next (1st level) events are already in the DB
-- getRootEventDB = selectList [DHWJTreesDepth ==. 1] [Asc DHWJTreesId]

getRootEventDBEve2 :: DB [Entity DHWJTreesEve2]
getRootEventDBEve2 = selectList [DHWJTreesEve2Depth ==. 0, DHWJTreesEve2Number ==. 0, DHWJTreesEve2Event ==. (NSA.DHWJ_TEvent NSA.Root)] [Asc DHWJTreesEve2Id]

getRootEventDBEve3 :: DB [Entity DHWJTreesEve3]
getRootEventDBEve3 = selectList [DHWJTreesEve3Depth ==. 0, DHWJTreesEve3Number ==. 0, DHWJTreesEve3Event ==. (NSA.DHWJ_TEvent NSA.Root)] [Asc DHWJTreesEve3Id]

getRootEventDBEve4 :: DB [Entity DHWJTreesEve4]
getRootEventDBEve4 = selectList [DHWJTreesEve4Depth ==. 0, DHWJTreesEve4Number ==. 0, DHWJTreesEve4Event ==. (NSA.DHWJ_TEvent NSA.Root)] [Asc DHWJTreesEve4Id]

-- | Get the next events for animation from current chosen event 
getNextEventsDBEve1 :: Int -> DB [Entity DHWJTreesEve1]
getNextEventsDBEve1 parent_eid = selectList [DHWJTreesEve1Parent ==. parent_eid] [Asc DHWJTreesEve1Id]

getNextEventsDBEve2 :: Int -> DB [Entity DHWJTreesEve2]
getNextEventsDBEve2 parent_eid = selectList [DHWJTreesEve2Parent ==. parent_eid] [Asc DHWJTreesEve2Id]

getNextEventsDBEve3 :: Int -> DB [Entity DHWJTreesEve3]
getNextEventsDBEve3 parent_eid = selectList [DHWJTreesEve3Parent ==. parent_eid] [Asc DHWJTreesEve3Id]

getNextEventsDBEve4 :: Int -> DB [Entity DHWJTreesEve4]
getNextEventsDBEve4 parent_eid = selectList [DHWJTreesEve4Parent ==. parent_eid] [Asc DHWJTreesEve4Id]

-- | Convert a list of tree entities to a list of event tuples, indexed by the depth number 
entities2EventListIndexedByDepthNumberEve1:: [Entity DHWJTreesEve1] -> [(Text, (Text, Text, Text, Text, Text, Text))]
entities2EventListIndexedByDepthNumberEve1 [] = []
entities2EventListIndexedByDepthNumberEve1 (x:xs) = case x of 
  Entity _ (DHWJTreesEve1 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show number, (T.pack $ show eid, "ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve1 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show number, (T.pack $ show eid, "Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve1 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show number, (T.pack $ show eid, "Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve1 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show number, (T.pack $ show eid, "Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve1 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show number, (T.pack $ show eid, T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByDepthNumberEve1 xs

entities2EventListIndexedByDepthNumberEve2:: [Entity DHWJTreesEve2] -> [(Text, (Text, Text, Text, Text, Text, Text))]
entities2EventListIndexedByDepthNumberEve2 [] = []
entities2EventListIndexedByDepthNumberEve2 (x:xs) = case x of 
  Entity _ (DHWJTreesEve2 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show number, (T.pack $ show eid, "ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve2 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show number, (T.pack $ show eid, "Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve2 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show number, (T.pack $ show eid, "Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve2 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show number, (T.pack $ show eid, "Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve2 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show number, (T.pack $ show eid, T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByDepthNumberEve2 xs

entities2EventListIndexedByDepthNumberEve3:: [Entity DHWJTreesEve3] -> [(Text, (Text, Text, Text, Text, Text, Text))]
entities2EventListIndexedByDepthNumberEve3 [] = []
entities2EventListIndexedByDepthNumberEve3 (x:xs) = case x of 
  Entity _ (DHWJTreesEve3 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show number, (T.pack $ show eid, "ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve3 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show number, (T.pack $ show eid, "Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve3 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show number, (T.pack $ show eid, "Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve3 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show number, (T.pack $ show eid, "Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve3 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show number, (T.pack $ show eid, T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByDepthNumberEve3 xs

entities2EventListIndexedByDepthNumberEve4:: [Entity DHWJTreesEve4] -> [(Text, (Text, Text, Text, Text, Text, Text))]
entities2EventListIndexedByDepthNumberEve4 [] = []
entities2EventListIndexedByDepthNumberEve4 (x:xs) = case x of 
  Entity _ (DHWJTreesEve4 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show number, (T.pack $ show eid, "ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve4 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show number, (T.pack $ show eid, "Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve4 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show number, (T.pack $ show eid, "Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve4 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show number, (T.pack $ show eid, "Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByDepthNumberEve4 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show number, (T.pack $ show eid, T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByDepthNumberEve4 xs

-- | Convert a list of tree entities to a list of event tuples, indexed by the eid number 
entities2EventListIndexedByEidEve1 :: [Entity DHWJTreesEve1] -> [(Text, (Text, Text, Text, Text, Text))]
entities2EventListIndexedByEidEve1 [] = []
entities2EventListIndexedByEidEve1 (x:xs) = case x of 
  Entity _ (DHWJTreesEve1 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show eid, ("ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByEidEve1 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show eid, ("Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve1 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show eid, ("Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve1 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show eid, ("Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve1 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show eid, (T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByEidEve1 xs

-- | Convert a list of tree entities to a list of event tuples, indexed by the eid number 
entities2EventListIndexedByEidEve2 :: [Entity DHWJTreesEve2] -> [(Text, (Text, Text, Text, Text, Text))]
entities2EventListIndexedByEidEve2 [] = []
entities2EventListIndexedByEidEve2 (x:xs) = case x of 
  Entity _ (DHWJTreesEve2 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show eid, ("ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByEidEve2 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show eid, ("Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve2 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show eid, ("Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve2 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show eid, ("Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve2 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show eid, (T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByEidEve2 xs

entities2EventListIndexedByEidEve3 :: [Entity DHWJTreesEve3] -> [(Text, (Text, Text, Text, Text, Text))]
entities2EventListIndexedByEidEve3 [] = []
entities2EventListIndexedByEidEve3 (x:xs) = case x of 
  Entity _ (DHWJTreesEve3 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show eid, ("ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByEidEve3 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show eid, ("Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve3 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show eid, ("Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve3 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show eid, ("Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve3 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show eid, (T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByEidEve3 xs

entities2EventListIndexedByEidEve4 :: [Entity DHWJTreesEve4] -> [(Text, (Text, Text, Text, Text, Text))]
entities2EventListIndexedByEidEve4 [] = []
entities2EventListIndexedByEidEve4 (x:xs) = case x of 
  Entity _ (DHWJTreesEve4 protocol eid depth number parent event) -> case event of 
    NSA.DHWJ_TEvent NSA.Root -> (T.pack $ show eid, ("ROOT", "Env", "Env", "Env", "") ) : entities2EventListIndexedByEidEve4 xs
    NSA.DHWJ_TEvent NSA.Deadlocked -> (T.pack $ show eid, ("Deadlocked", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve4 xs
    NSA.DHWJ_TEvent NSA.Terminated -> (T.pack $ show eid, ("Terminated", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve4 xs
    NSA.DHWJ_TEvent NSA.Divergent -> (T.pack $ show eid, ("Divergent", "Sys", "Env", "Env", "") ) : entities2EventListIndexedByEidEve4 xs
    NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
      (T.pack $ show eid, (T.pack $ ch, T.pack $ src, T.pack $ mid, T.pack $ dest, T.pack $ msg)) : entities2EventListIndexedByEidEve4 xs

-- | Get all events to be shown and animated
getAllNextEventsFromDB :: Handler [(Text, (Text, Text, Text, Text, Text, Text))]
getAllNextEventsFromDB = do 
    -- We use the 'next' key to store the current explored event (eid), whose children we want to animate
    maybeNext <- lookupSession "next"
    maybeEve <- currentEveScenario
    -- Here we get all events to be shown and animated
    allEvents <- case maybeNext of
      Nothing -> do 
        setSession "next" "0"
        case maybeEve of 
          Just Eve1 -> do 
            nextEvents <- runDB $ (getNextEventsDBEve1 0)
            return $ entities2EventListIndexedByDepthNumberEve1 nextEvents
          Just Eve2 -> do 
            nextEvents <- runDB $ (getNextEventsDBEve2 0)
            return $ entities2EventListIndexedByDepthNumberEve2 nextEvents
          Just Eve3 -> do 
            nextEvents <- runDB $ (getNextEventsDBEve3 0)
            return $ entities2EventListIndexedByDepthNumberEve3 nextEvents
          Just Eve4 -> do 
            nextEvents <- runDB $ (getNextEventsDBEve4 0)
            return $ entities2EventListIndexedByDepthNumberEve4 nextEvents
          _ -> return [] 
      Just str_parent_eid -> case (readMaybe $ T.unpack str_parent_eid) of
        Nothing -> do 
          setSession "next" "0"
          case maybeEve of 
            Just Eve1 -> do 
              nextEvents <- runDB $ (getNextEventsDBEve1 0)
              return $ entities2EventListIndexedByDepthNumberEve1 nextEvents
            Just Eve2 -> do 
              nextEvents <- runDB $ (getNextEventsDBEve2 0)
              return $ entities2EventListIndexedByDepthNumberEve2 nextEvents
            Just Eve3 -> do 
              nextEvents <- runDB $ (getNextEventsDBEve3 0)
              return $ entities2EventListIndexedByDepthNumberEve3 nextEvents
            Just Eve4 -> do 
              nextEvents <- runDB $ (getNextEventsDBEve4 0)
              return $ entities2EventListIndexedByDepthNumberEve4 nextEvents
            _ -> return []
        Just parent_eid -> do
          case maybeEve of
            Just Eve1 -> do 
              nextEvents <- runDB $ getNextEventsDBEve1 parent_eid 
              return $ entities2EventListIndexedByDepthNumberEve1 nextEvents
            Just Eve2 -> do 
              nextEvents <- runDB $ getNextEventsDBEve2 parent_eid 
              return $ entities2EventListIndexedByDepthNumberEve2 nextEvents
            Just Eve3 -> do 
              nextEvents <- runDB $ getNextEventsDBEve3 parent_eid 
              return $ entities2EventListIndexedByDepthNumberEve3 nextEvents
            Just Eve4 -> do 
              nextEvents <- runDB $ getNextEventsDBEve4 parent_eid 
              return $ entities2EventListIndexedByDepthNumberEve4 nextEvents
            _ -> return []
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
getChannelListPair = map (\x -> (T.pack $ x, T.pack $ x)) NSA.getChannelList4Property

isMessageMatchAll :: Maybe Text -> Bool
isMessageMatchAll msg = (msg == Just "") || (msg == Just "*") || (msg == Nothing)

isMessageMatch :: Maybe Text -> Text -> Bool
isMessageMatch msg msg1 = case msg of 
  Nothing -> False 
  Just msg_body -> msg1 == msg_body 
 
isMessageMatch' :: Text -> Maybe Text -> (Text, Text, Text, Text, Text) -> Bool
isMessageMatch' chIn maybeMsgIn (ch, src, mid, dest, msg) = case maybeMsgIn of 
  Nothing -> (chIn == ch)
  Just msgIn -> (chIn <> msgIn) == formatEventForDisplay ch src dest msg 

isMatchedEvent :: Text -> Maybe Text -> NSA.DHWJ_TEvent -> Bool
isMatchedEvent chIn msgIn event = 
  if chIn == "" then False else
    case event of  
      NSA.DHWJ_TEvent NSA.Root -> (chIn == "ROOT") && (isMessageMatchAll msgIn)
      NSA.DHWJ_TEvent NSA.Deadlocked -> (chIn == "Deadlocked") && (isMessageMatchAll msgIn)
      NSA.DHWJ_TEvent NSA.Terminated -> (chIn == "Terminated") && (isMessageMatchAll msgIn) 
      NSA.DHWJ_TEvent NSA.Divergent -> (chIn == "Divergent") && (isMessageMatchAll msgIn)
      NSA.DHWJ_TEvent (NSA.EChan e) -> let (ch, src, mid, dest, msg) = convertAgentName $ NSA.formatEvents e in 
        isMessageMatch' chIn msgIn (T.pack ch, T.pack src, T.pack mid, T.pack dest, T.pack msg)

-- | Automatically reachability check with events for monitoring 
autoCheck :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text -> Handler [[Int]]
autoCheck reach chMonitor msgMonitor chCheck msgCheck = do 
    maybeNext <- lookupSession "next"
    case maybeNext of
      Nothing -> return [[]] 
      Just str_parent_eid -> case (readMaybe $ T.unpack str_parent_eid) of
        Nothing -> return [[]] 
        Just parent_eid -> do
          maybeEve <- currentEveScenario
          case maybeEve of 
            Just Eve1 -> do 
              nextEvents <- runDB $ getNextEventsDBEve1 parent_eid 
              -- Current trace should be the value of "trace" in session, but it is String. Here we need a TEvent.
              -- So we set it to empty list and let higher layer combine them.
              exhaustiveSearchEve1 reach chMonitor msgMonitor chCheck msgCheck [] 0 nextEvents
            Just Eve2 -> do 
              nextEvents <- runDB $ getNextEventsDBEve2 parent_eid 
              -- Current trace should be the value of "trace" in session, but it is String. Here we need a TEvent.
              -- So we set it to empty list and let higher layer combine them.
              exhaustiveSearchEve2 reach chMonitor msgMonitor chCheck msgCheck [] 0 nextEvents
            Just Eve3 -> do 
              nextEvents <- runDB $ getNextEventsDBEve3 parent_eid 
              -- Current trace should be the value of "trace" in session, but it is String. Here we need a TEvent.
              -- So we set it to empty list and let higher layer combine them.
              exhaustiveSearchEve3 reach chMonitor msgMonitor chCheck msgCheck [] 0 nextEvents
            Just Eve4 -> do 
              nextEvents <- runDB $ getNextEventsDBEve4 parent_eid 
              -- Current trace should be the value of "trace" in session, but it is String. Here we need a TEvent.
              -- So we set it to empty list and let higher layer combine them.
              exhaustiveSearchEve4 reach chMonitor msgMonitor chCheck msgCheck [] 0 nextEvents
            _ -> return [[]]

-- | Automatically reachability check with events for monitoring
exhaustiveSearchEve1 :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text 
  -> [Int] -- current trace
  -> Int -- the number of times that the event for monitoring occurred
  -> [Entity DHWJTreesEve1] 
  -> Handler [[Int]] -- all counterexamples
exhaustiveSearchEve1 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore [] = return []
exhaustiveSearchEve1 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore (x:xs) = do
  xsRes <- exhaustiveSearchEve1 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore xs
  case x of 
    Entity _ (DHWJTreesEve1 protocol eid depth number parent event) -> 
      case isMatchedEvent chMonitor msgMonitor event of
        True -> do 
          nextEvents <- runDB $ getNextEventsDBEve1 eid 
          xRes <- exhaustiveSearchEve1 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) (monitoredBefore + 1) nextEvents 
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
              nextEvents <- runDB $ getNextEventsDBEve1 eid 
              xRes <- exhaustiveSearchEve1 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) monitoredBefore nextEvents 
              return (xsRes ++ xRes)

exhaustiveSearchEve2 :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text 
  -> [Int] -- current trace
  -> Int -- the number of times that the event for monitoring occurred
  -> [Entity DHWJTreesEve2] 
  -> Handler [[Int]] -- all counterexamples
exhaustiveSearchEve2 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore [] = return []
exhaustiveSearchEve2 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore (x:xs) = do
  xsRes <- exhaustiveSearchEve2 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore xs
  case x of 
    Entity _ (DHWJTreesEve2 protocol eid depth number parent event) -> 
      case isMatchedEvent chMonitor msgMonitor event of
        True -> do 
          nextEvents <- runDB $ getNextEventsDBEve2 eid 
          xRes <- exhaustiveSearchEve2 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) (monitoredBefore + 1) nextEvents 
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
              nextEvents <- runDB $ getNextEventsDBEve2 eid 
              xRes <- exhaustiveSearchEve2 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) monitoredBefore nextEvents 
              return (xsRes ++ xRes)
          
exhaustiveSearchEve3 :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text 
  -> [Int] -- current trace
  -> Int -- the number of times that the event for monitoring occurred
  -> [Entity DHWJTreesEve3] 
  -> Handler [[Int]] -- all counterexamples
exhaustiveSearchEve3 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore [] = return []
exhaustiveSearchEve3 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore (x:xs) = do
  xsRes <- exhaustiveSearchEve3 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore xs
  case x of 
    Entity _ (DHWJTreesEve3 protocol eid depth number parent event) -> 
      case isMatchedEvent chMonitor msgMonitor event of
        True -> do 
          nextEvents <- runDB $ getNextEventsDBEve3 eid 
          xRes <- exhaustiveSearchEve3 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) (monitoredBefore + 1) nextEvents 
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
              nextEvents <- runDB $ getNextEventsDBEve3 eid 
              xRes <- exhaustiveSearchEve3 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) monitoredBefore nextEvents 
              return (xsRes ++ xRes)

exhaustiveSearchEve4 :: CheckMode -> Text -> Maybe Text -> Text -> Maybe Text 
  -> [Int] -- current trace
  -> Int -- the number of times that the event for monitoring occurred
  -> [Entity DHWJTreesEve4] 
  -> Handler [[Int]] -- all counterexamples
exhaustiveSearchEve4 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore [] = return []
exhaustiveSearchEve4 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore (x:xs) = do
  xsRes <- exhaustiveSearchEve4 reach chMonitor msgMonitor chCheck msgCheck currentTrace monitoredBefore xs
  case x of 
    Entity _ (DHWJTreesEve4 protocol eid depth number parent event) -> 
      case isMatchedEvent chMonitor msgMonitor event of
        True -> do 
          nextEvents <- runDB $ getNextEventsDBEve4 eid 
          xRes <- exhaustiveSearchEve4 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) (monitoredBefore + 1) nextEvents 
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
              nextEvents <- runDB $ getNextEventsDBEve4 eid 
              xRes <- exhaustiveSearchEve4 reach chMonitor msgMonitor chCheck msgCheck (currentTrace ++ [eid]) monitoredBefore nextEvents 
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
      maybeEve <- currentEveScenario
      -- liftIO $ print $ "maybeEve in eidsToPrettyEvents" <> T.pack (show maybeEve)
      case maybeEve of 
        Nothing -> return []
        Just Eve1 -> do
          eventListTuples <- getEventsFromDBEve1 eventIdList 
          return $ map (\(eid, (ch, src, mid, dst, msg)) -> formatEventForDisplay ch src dst msg) eventListTuples
        Just Eve2 -> do
          eventListTuples <- getEventsFromDBEve2 eventIdList 
          return $ map (\(eid, (ch, src, mid, dst, msg)) -> formatEventForDisplay ch src dst msg) eventListTuples
        Just Eve3 -> do
          eventListTuples <- getEventsFromDBEve3 eventIdList 
          return $ map (\(eid, (ch, src, mid, dst, msg)) -> formatEventForDisplay ch src dst msg) eventListTuples 
        Just Eve4 -> do
          eventListTuples <- getEventsFromDBEve4 eventIdList 
          return $ map (\(eid, (ch, src, mid, dst, msg)) -> formatEventForDisplay ch src dst msg) eventListTuples 

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
  -- redirect AnimateDHWJR 
  redirect $ AnimateDHWJR :#: ("automatic_animation" :: Text)

-- | Our definition of horizontal form.
horizontal :: BootstrapFormLayout
horizontal = BootstrapHorizontalForm (ColSm 0) (ColSm 4) (ColSm 0) (ColSm 6)

getEventFromDBEve1 :: Int -> Handler (Maybe NSA.DHWJ_TEvent)
getEventFromDBEve1 eid = do 
  maybeEvent <- runDB $ getBy $ UniqueTrees_DHWJEve1 eid 
  case maybeEvent of 
    Nothing -> return Nothing 
    Just (Entity _ (DHWJTreesEve1 protocol eid depth number parent event)) -> 
      return $ Just event

-- | Get a list of events from the database in a form of (eid, (channel, src, dest, msg))
getEventsFromDBEve1 :: [Int] -> Handler [(Text, (Text, Text, Text, Text, Text))]
getEventsFromDBEve1 eventIds = do 
  events <- runDB $ selectList [DHWJTreesEve1Eid <-. eventIds] [Asc DHWJTreesEve1Id]
  return $ entities2EventListIndexedByEidEve1 events

getEventsFromDBEve2 :: [Int] -> Handler [(Text, (Text, Text, Text, Text, Text))]
getEventsFromDBEve2 eventIds = do 
  events <- runDB $ selectList [DHWJTreesEve2Eid <-. eventIds] [Asc DHWJTreesEve2Id]
  return $ entities2EventListIndexedByEidEve2 events

getEventsFromDBEve3 :: [Int] -> Handler [(Text, (Text, Text, Text, Text, Text))]
getEventsFromDBEve3 eventIds = do 
  events <- runDB $ selectList [DHWJTreesEve3Eid <-. eventIds] [Asc DHWJTreesEve3Id]
  return $ entities2EventListIndexedByEidEve3 events

getEventsFromDBEve4 :: [Int] -> Handler [(Text, (Text, Text, Text, Text, Text))]
getEventsFromDBEve4 eventIds = do 
  events <- runDB $ selectList [DHWJTreesEve4Eid <-. eventIds] [Asc DHWJTreesEve4Id]
  return $ entities2EventListIndexedByEidEve4 events

-- | Convert a list of events to a PlantUML input
events2PlantUMLInput :: [(Text, (Text, Text, Text, Text, Text))] -> Text
events2PlantUMLInput [] = ""
events2PlantUMLInput ((_, (ch, src, mid, dst, msg)):xs) = do
  formatPlantUMLInput (src, dst, ch <> "." <> msg) ++ "\n" ++ events2PlantUMLInput xs

plantUMLTextDHWJ :: Handler Text
plantUMLTextDHWJ = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "actor Bob #red",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextDHWJ_no_attack :: Handler Text
plantUMLTextDHWJ_no_attack = return $ T.unlines $ [
  "@startuml",
  "title",
  "  Assume all participants know each other's <u>public keys</u>",
  "end title",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "entity \"Intruder <:spider:>\" as Intruder #green ",
  "actor Bob #red",
  "Alice -> Intruder: (na, Alice) <:1f510:> pkIntruder",
  "note left Intruder: Intruder decrypts and \\nthen re-encrypts it",
  "Intruder -[#red]> Bob : (na, Alice) <:1f510:> pkBob",
  "Bob -> Intruder: (na, nb, <font color=red><b>Bob</font>) <:1f510:> pkAlice",
  "note left Intruder: Intruder cannot decrypt it \\nand so just forward it",
  "Intruder -[#red]> Alice: (na, nb, Bob) <:1f510:> pkAlice",
  "note left Alice: Alice expects the message from Intruder \\n but it is from <font color=red><b>Bob</font>",
  "Caption No man-in-the-middle attack",
  "@enduml"
  ]

discardMid :: [(Text, (Text, Text, Text, Text, Text, Text))] -> [(Text, (Text, Text, Text, Text, Text))]
discardMid [] = [] 
discardMid ((no, (id, ch, src, mid, dst, msg)):xs) = (no, (id, ch, src, dst, msg)):discardMid xs

currentEveScenario :: Handler (Maybe Deve)
currentEveScenario = do
    maybeProtocol <- lookupSession $ sessionProtocolNameKey
    case maybeProtocol of
      -- We don't need to set the protocol name if it is already DHWJ
      Just "DHWJEve1" -> return $ Just Eve1
      Just "DHWJEve2" -> return $ Just Eve2
      Just "DHWJEve3" -> return $ Just Eve3
      Just "DHWJEve4" -> return $ Just Eve4
      _ -> return $ Just Eve3 

data EveInputForm = EveInputForm 
    { -- manualInput :: Int 
      eve :: Deve 
    } deriving (Eq, Show)

eveScenarioForm :: Deve -> Form EveInputForm 
eveScenarioForm eve = 
  identifyForm "eveScenarioForm" $
  renderBootstrap3 (BootstrapHorizontalForm (ColSm 0) (ColSm 3) (ColSm 0) (ColSm 8)) $ EveInputForm
    <$> areq (radioFieldList reachFieldList) "Eve location: " (Just eve) 
    <* submit "Select Eve location"
    -- Add attributes like the placeholder and CSS classes.
    where
        reachFieldList :: [(Text, Deve)]
        reachFieldList = 
            [ ("Eve1 - Within Alice's Jamming Range but not Bob's", Eve1)
            , ("Eve2 - Within Bob's Jamming Range but not Alice's", Eve2)
            , ("Eve3 - Within Both Alice's and Bob's Jamming Ranges", Eve3)
            , ("Eve4 - Not within Both Alice's and Bob's Jamming Ranges", Eve4)
            ] 

formatAgentName :: String -> String
formatAgentName "A0" = "Alice"
formatAgentName "A1" = "Bob"
formatAgentName "I" = "Intruder"
formatAgentName n = n  

-- | Convert Agent names to Alice and Bob etc.
convertAgentName :: (String, String, String, String, String) -> (String, String, String, String, String)
convertAgentName (ch, src, mid, dst, msg) = case (ch, src, mid) of
  ("Send", _, "I") -> (ch, formatAgentName src, formatAgentName mid, formatAgentName mid, msg)
  ("Recv", _, "I") -> (ch, formatAgentName mid, formatAgentName mid, formatAgentName dst, msg)
  (_, _, _) -> (ch, formatAgentName src, formatAgentName mid, formatAgentName dst, msg)

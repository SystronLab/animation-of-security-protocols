{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}

-- | Common handler functions.
module Handler.Common where

import Data.FileEmbed (embedFile)
import Yesod.Form.Bootstrap3 -- (BootstrapFormLayout (..), renderBootstrap3, BootstrapGridOptions(..), bootstrapSubmit, BootstrapSubmit) 
import Import
import Network.HTTP.Simple
import Data.Text           as T
import Data.Text.Encoding  as T
import Data.Text.IO        as T
import qualified Data.List as DL (dropWhile, dropWhileEnd, intersect, head, tail, elemIndex, uncons);
import Data.ByteString.UTF8 as B
import Data.ByteString.Lazy.UTF8 as LB
import Text.Blaze.Internal as TBI
import "nspk3-animator" Simulate as NSPK3_Simulate
import NSPK3_Animate (explore_tree_NSPK3, 
  explore_tree_NSLPK3, EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  )

-- These handlers embed files in the executable at compile time to avoid a
-- runtime dependency, and for efficiency.

getFaviconR :: Handler TypedContent
getFaviconR = do cacheSeconds $ 60 * 60 * 24 * 30 -- cache for a month
                 return $ TypedContent "image/x-icon"
                        $ toContent $(embedFile "config/favicon.ico")

getRobotsR :: Handler TypedContent
getRobotsR = return $ TypedContent typePlain
                    $ toContent $(embedFile "config/robots.txt")

data CheckMode = Secrecy |Correspondence | Injective_Correspondence 
  deriving (Eq, Show)

fst4 :: (a, b, c, d) -> a
fst4 (a, _, _, _) = a

snd4 :: (a, b, c, d) -> b
snd4 (_, b, _, _) = b

thd4 :: (a, b, c, d) -> c
thd4 (_, _, c, _) = c

fth4 :: (a, b, c, d) -> d
fth4 (_, _, _, d) = d 

fst5 :: (a, b, c, d, e) -> a
fst5 (a, _, _, _, _) = a

snd5 :: (a, b, c, d, e) -> b
snd5 (_, b, _, _, _) = b

thd5 :: (a, b, c, d, e) -> c
thd5 (_, _, c, _, _) = c

fth5 :: (a, b, c, d, e) -> d
fth5 (_, _, _, d, _) = d

fifth5 :: (a, b, c, d, e) -> e
fifth5 (_, _, _, _, e) = e

getPlantUMLDiagram :: Text -> Handler TBI.Markup 
getPlantUMLDiagram plantUmlCode = do 
    -- Define PlantUML diagram text
    -- let plantUmlCode = T.unlines
    --         [ "@startuml"
    --         , "Alice -> Bob: Hello"
    --         , "Bob --> Alice: Hi"
    --         , "@enduml"
    --         ]
    
    -- Define PlantUML server endpoint (use localhost or public server)
    -- let url = "http://localhost:8080/plantuml/svg"
    url <- T.unpack <$> getPlantUMLURL 

    -- Create a POST request with the diagram as body
    let request = setRequestBodyLBS (LB.fromString $ T.unpack plantUmlCode) $
                  setRequestMethod "POST" $
                  parseRequest_ url

    -- Send the request and get the response
    response <- httpBS request

    -- Save the response body (the generated SVG) to a file
    return $ preEscapedToMarkup $ B.toString $ getResponseBody response

getPlantUMLURL :: Handler Text 
getPlantUMLURL = do 
    -- Get the foundation (App)
    app <- getYesod

    -- Access appSettings from the foundation
    let settings = appSettings app

    -- Extract specific settings, e.g., appTitle
    return $ appPlantUmlUrl settings

{-
  plantUMLHeader ++ [
  "Env -> Alice: Intruder", 
  "Alice -> Alice: ClaimSecret (N Alice) {Intruder}", 
  "Alice -> Intruder: {<N Alice, Alice>}_{PK Intruder}", 
  "Intruder -> Bob: {<N Alice, Alice>}_{PK Bob}", 
  "Bob -> Bob: ClaimSecret (N Bob) {Alice}", 
  "Bob -> Bob: StartProt Bob Alice (N Alice) (N Bob) ", 
  "Bob -> Intruder: {<N Alice, N Bob>}_{PK Alice}", 
  "Intruder -> Alice: {<N Alice, N Bob>}_{PK Alice}", 
  "Alice -> Alice: StartProt Alice Intruder (N Alice) (N Bob)", 
  "Alice -> Intruder: {<N Bob>}_{PK Intruder}", 
  "Intruder -[#red]> Intruder: Leak (N Bob) ", 
  "@enduml"
  ]
-}

formatPlantUMLInput :: (Text, Text, Text) -> Text
formatPlantUMLInput (src, dst, ch_msg) = 
  src <> " -> " <> dst <> ": " <> ch_msg

plantUMLHeader :: [Text]
plantUMLHeader = [
  "@startuml",
  "autonumber \"[00]\"",
  "entity Env",
  "boundary Sys #green",
  "box \"Protocol\" #Snow", 
  "actor Alice #blue",
  "participant Intruder #yellow",
  "actor Bob #red",
  "end box"
  ] 

plantUMLTail :: [Text]
plantUMLTail = [ "@enduml" ] 

plantUMLInput4Animation :: Handler Text
plantUMLInput4Animation = do
  maybeNext <- lookupSession "plantuml_input"
  case maybeNext of
    Nothing -> return $ T.unlines $ 
      plantUMLHeader ++ plantUMLTail
    Just str_trace -> return $ T.unlines $ 
      plantUMLHeader ++ [str_trace] ++ plantUMLTail

plantUMLInput4Counterexample :: Handler Text
plantUMLInput4Counterexample = do
  maybeNext <- lookupSession sessionCntExPlantumlInputKey
  case maybeNext of
    Nothing -> return $ T.unlines $ 
      plantUMLHeader ++ plantUMLTail
    Just str_trace -> return $ T.unlines $ 
      plantUMLHeader ++ [str_trace] ++ plantUMLTail

plantUMLTextEmpty :: Handler Text
plantUMLTextEmpty = return $ T.unlines $ 
      plantUMLHeader ++ plantUMLTail

plantUMLTextNSPK7 :: Handler Text
plantUMLTextNSPK7 = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "database Server #green",
  "actor Bob #red",
  "Alice -> Server : (Alice, Bob)",
  "Server -> Alice : (pk(Bob), Bob) <:1f510:> skServer",
  "Alice -> Alice: <:1f513:> pkServer",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Bob: <:1f513:> skBob",
  "Bob -> Server: (Bob, Alice)",
  "Server -> Bob : (pkAlice, Alice) <:1f510:> skServer",
  "Bob -> Bob: <:1f513:> pkServer",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Alice: <:1f513:> skAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "Bob -> Bob: <:1f513:> skBob",
  "@enduml"
  ]

plantUMLTextNSPK7_dot :: Handler Text
plantUMLTextNSPK7_dot = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "database Server #green",
  "actor Bob #red",
  "Alice -[#0000FF]-> Server : (Alice, Bob)",
  "Server -[#0000FF]-> Alice : (pk(Bob), Bob) <:1f510:> skServer",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -[#0000FF]-> Server: (Bob, Alice)",
  "Server -[#0000FF]-> Bob : (pkAlice, Alice) <:1f510:> skServer",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextNSPK3 :: Handler Text
plantUMLTextNSPK3 = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "actor Bob #red",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextNSLPK3 :: Handler Text
plantUMLTextNSLPK3 = return $ T.unlines $ [
  "@startuml",
  "autonumber \"[00]\"",
  "actor Alice #blue",
  "actor Bob #red",
  "Alice -> Bob: (na, Alice) <:1f510:> pkBob",
  "Bob -> Alice: (na, nb, <font color=red><b>Bob</font>) <:1f510:> pkAlice",
  "Alice -> Bob: nb <:1f510:> pkBob",
  "@enduml"
  ]

plantUMLTextNSPK3_attack :: Handler Text
plantUMLTextNSPK3_attack = return $ T.unlines $ [
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
  "Bob -> Intruder: (na, nb) <:1f510:> pkAlice",
  "note left Intruder: Intruder cannot decrypt it \\nand so just forward it",
  "Intruder -[#red]> Alice: (na, nb) <:1f510:> pkAlice",
  "Alice -> Intruder: nb <:1f510:> pkIntruder",
  "note left Intruder: Intruder \\nknows <font color=red><b>nb</font>",
  "Intruder -[#red]> Bob: nb <:1f510:> pkBob",
  "note left Bob: But Bob <font color=red><b>doesn't realise</font>",
  "Caption The man-in-the-middle attack",
  "@enduml"
  ]

plantUMLTextNSLPK3_no_attack :: Handler Text
plantUMLTextNSLPK3_no_attack = return $ T.unlines $ [
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
-- Define our data that will be used for creating the form.
data ManualInputForm = ManualInputForm
    { -- manualInput :: Int 
      manualSelectedEventId :: (Text, Text, Text, Text, Text)
    } deriving (Eq, Show)

-- User input for automatic reachability check: an event for monitoring and an event for checking
data AutoInputForm = AutoInputForm
    { 
      autoReach :: CheckMode, 
      autoMonitorChannel :: Text,
      autoMonitorMsg :: Maybe Text,
      autoCheckChannel :: Text,
      autoCheckMsg :: Maybe Text
    } deriving (Eq, Show)

manualInputForm :: [(Text, (Text, Text, Text, Text, Text))] -> Form ManualInputForm
manualInputForm eventList = 
  identifyForm "manualInputForm" $
  renderDivs $ ManualInputForm
    <$> areq (selectFieldList (eventList)) "Which event to animate?   " Nothing 

{-
autoAnimationForm :: [(Text, Text)] -> Form AutoInputForm
autoAnimationForm channelList = renderTable $ AutoInputForm
    <$> areq (selectFieldList channelList) "Choose a channel\t: \t" Nothing 
    <*> aopt textField "Type a message to check (optional)\t:\t " Nothing 
-}

{-
autoAnimationForm :: [(Text, Text)] -> Form AutoInputForm
autoAnimationForm channelList = renderTable $ AutoInputForm
    <$> areq (selectFieldList channelList) "Choose a channel\t: \t" Nothing 
    <*> aopt textField "Type a message to check (optional)\t:\t " Nothing
-}

autoAnimationForm :: [(Text, Text)] -> Form AutoInputForm
autoAnimationForm channelList = 
  identifyForm "autoAnimationForm" $
  renderBootstrap3 (BootstrapHorizontalForm (ColSm 0) (ColSm 5) (ColSm 0) (ColSm 6)) $ AutoInputForm
    <$> areq (radioFieldList reachFieldList) "Security check: " (Just Secrecy) 
    <*> areq (selectFieldList ([("", "")] ++ channelList)) "Choose a channel for monitoring: " (Just "")
    <*> aopt textField (textSettings "Type a message for monitoring (optional):") Nothing
    <*> areq (selectFieldList channelList) "Choose a channel for checking: " Nothing 
    <*> aopt textField (textSettings "Type a message for checking (optional):") Nothing
    <* submit "Automatic checking"
    -- Add attributes like the placeholder and CSS classes.
    where
        reachFieldList :: [(Text, CheckMode)]
        reachFieldList = 
            [ ("Secrecy/Reachability check - should not be reached", Secrecy)
            , ("Correspondence check - event 1 occurs before event 2", Correspondence)
            , ("Injective correspondence check - exactly one event 1 occurs before event 2", Injective_Correspondence)
            ] 
        textSettings label = FieldSettings
            { fsLabel = label 
            , fsTooltip = Nothing
            , fsId = Nothing
            , fsName = Nothing
            , fsAttrs =
                [ ("class", "form-control")
                , ("placeholder", "Message")
                ]
            }

{-
autoAnimationAForm :: [(Text, Text)] -> AForm Handler AutoInputForm
autoAnimationAForm channelList = AutoInputForm
    <$> areq (selectFieldList channelList) "Choose a channel\t: \t" Nothing 
    <*> aopt textField "Type a message to check (optional)\t:\t " (Just "*")

autoAnimationForm :: [(Text, Text)] -> Html -> Handler (FormResult AutoInputForm, Widget)
autoAnimationForm channelList = renderTable (autoAnimationAForm channelList)
-}

getEventTreeDepth :: Handler (Int, Int)
getEventTreeDepth = do 
    -- Get the foundation (App)
    app <- getYesod

    -- Access appSettings from the foundation
    let settings = appSettings app

    -- Extract specific settings, e.g., appTitle
    return $ (appEventTreeDepth settings, appEventTreeInternalDepth settings)


-- | Our definition of submit button.
submit :: MonadHandler m => Text -> AForm m ()
submit t = bootstrapSubmit (BootstrapSubmit t "btn-primary" [])

splitWhen' :: (Char -> Bool) -> String -> [String]
splitWhen' p s =  case DL.dropWhile p s of
   "" -> []
   s' -> w : splitWhen' p s''
         where (w, s'') = Import.break p s'

splitOn :: Char -> String -> [String]
splitOn c = splitWhen' (== c)

-- | The session key for protocol name 
sessionProtocolNameKey :: Text
sessionProtocolNameKey = "protocol"

-- | The session key for indexed counterexamples
sessionCounterexampleKey :: Text
sessionCounterexampleKey = "counterexample_"

-- | The session key for number of counterexamples
sessionNumberOfCounterexamplesKey :: Text
sessionNumberOfCounterexamplesKey = "number_of_counterexamples"

-- | The session key for PlantUML input for a chosen counterexample to view
sessionCntExPlantumlInputKey :: Text
sessionCntExPlantumlInputKey = "plantuml_input_cntex"

-- | Format an event for display by using the following pattern:
--   ch[src-->desc].msg
formatEventForDisplay :: Text -> Text -> Text -> Text -> Text
formatEventForDisplay ch src desc msg = ch <> "[" <> src <> "-->" <> desc <> "]" <> "." <> msg

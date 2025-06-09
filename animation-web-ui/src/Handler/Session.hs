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

module Handler.Session where

import Import
import Data.Monoid (All(getAll))
import qualified Data.Text as T (pack, unpack)
import Handler.Common
-- import Interaction_Trees;
-- import Sec_Messages;
-- import NSPK3
-- import NSPK3_Animate (animate_manual, eventList, eventTreeList, formatEvents, explore_tree_NSPK3, 
--   explore_tree_NSLPK3, EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan))

import qualified Data.Map as M
import qualified Web.ServerSession.Frontend.Yesod as SS
import Yesod.Form.Bootstrap3
import Import (redirect, get404, setSession)
import Text.Read (readMaybe, read)
import Data.Text as T (unlines)

getSessionR :: Handler Html
getSessionR = do
    msid <- getSessionId
    vars <- M.toAscList <$> getSession

    (sessionAddFormWidget, sessionAddFormEnctype) <- generateFormPost sessionAddForm

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "View and modify session variables"
        $(widgetFile "session")

postSessionR :: Handler Html
postSessionR = do
    msid <- getSessionId
    vars <- M.toAscList <$> getSession

    (sessionAddFormWidget, sessionAddFormEnctype) <- generateFormPost sessionAddForm

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "View and modify session variables"
        $(widgetFile "session")

-- | Add (or modify) a session variable.
postSessionAddR :: Handler ()
postSessionAddR = do   
  processForm "Add session form" sessionAddForm $ \(key, val) -> do
    setSession key val
    return $ concat
      [ "Set session key "
      , show key
      , " to value "
      , show val
      , "." ]

-- | Delete a session variable.
postSessionDeleteR :: Text -> Handler ()
postSessionDeleteR key = do
  deleteSession key
  setMessage $ toHtml $ "Deleted session key " ++ show key ++ "."
  redirect SessionR 

postSessionClearR :: Handler ()
postSessionClearR = do
  clearSession
  setMessage $ toHtml $ ("Cleared all session variables." :: Text)
  redirect SessionR

-- | Form for adding or modifying session variables.
sessionAddForm :: Form (Text, Text)
sessionAddForm =
  identifyForm "sessionAddForm" $
  renderBootstrap3 horizontal $
    (,)
      <$> areq textField "My Session key"   Nothing
      <*> areq textField "My Session value" Nothing
      <* submit "Add/modify session variable"

-- | Retrieve the session ID from the cookie.
getSessionId :: Handler (Maybe Text)
getSessionId = lookupCookie sessionCookieName

-- | Helper function for form processing handlers.
processForm :: String -> Form a -> (a -> Handler String) -> Handler ()
processForm formName form act = do
  ((result, _), _) <- runFormPost form
  (>>= setMessage . toHtml) $
    case result of
      FormSuccess ret  -> act ret
      FormFailure errs -> return $ formName ++ " has errors: " ++ show errs ++ "."
      FormMissing      -> return $ formName ++ " is missing."
  redirect SessionR 

-- | Our definition of horizontal form.
horizontal :: BootstrapFormLayout
horizontal = BootstrapHorizontalForm (ColSm 0) (ColSm 4) (ColSm 0) (ColSm 6)

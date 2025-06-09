{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PackageImports #-}

module Model where

import ClassyPrelude.Yesod
import Database.Persist.Quasi
import "nspk3-animator" Interaction_Trees
import "nspk3-animator" Sec_Messages
import "nspk3-animator" NSPK3
import "nspk3-animator" NSPK3_Animate

import "nswj3-animator" Interaction_Trees as NSWJ3_Interaction_Trees
import "nswj3-animator" Sec_Messages as NSWJ3_Sec_Messages
import "nswj3-animator" NSWJ3_wbplsec
import "nswj3-animator" NSWJ3_Animate 


-- In order for TEvent to be a persistent entity
derivePersistField "NSPK3_Animate.NSPK3_TEvent"
derivePersistField "NSPK3_Animate.NSLPK3_TEvent"
derivePersistField "NSWJ3_Animate.NSWJ3_TEvent"

-- You can define all of your database entities in the entities file.
-- You can find more information on persistent and how to declare entities
-- at:
-- http://www.yesodweb.com/book/persistent/
-- share [mkPersist sqlSettings, mkMigrate "migrateAll"]
--    $(persistFileWith lowerCaseSettings "config/models.persistentmodels")

share [mkPersist sqlSettings, mkEntityDefList "entityDefs"]
    $(persistFileWith lowerCaseSettings "config/models.persistentmodels")

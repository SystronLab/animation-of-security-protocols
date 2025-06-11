{-|
Module      :  Animate
Copyright   :  (c) Kangfeng Ye, 2025 
License     :  BSD3

Maintainer  :  Kangfeng Ye <kangfeng.ye@york.ac.uk>
Stability   :  experimental

This module provides functions to animate the interaction trees. 
-}

module DHWJ_Animate (explore_tree_DHWJ, 
  EventTree(ETNode), TEventPos(TEP), TEvent(Root, Deadlocked, Terminated, Divergent, EChan),
  DHWJ_TEvent(..), DHWJ_EventTree(..), eventList, eventTreeList, formatEvents, formatTEvent, formatTEvents, 
  getChannelList, getChannelList4Property
  ) where
import Interaction_Trees ( Itree(..), Pfun(Pfun_of_alist, Pfun_of_map, Pfun_entries), pfun_app );
import Prelude;
import Text.Read (get);
import Text.Show.Pretty ( ppShow );
import System.IO ();
import Arith ( Nat(Nat) );
import qualified Set;
import Sec_Messages ( Chan(..), Dmsg(..), Dsig(..), Dagent(Agent), Dkey(Kp, Ks));
import qualified Numeral_Type;
import qualified Type_Length;
-- import qualified Data.List (dropWhile, dropWhileEnd, intersect, head, tail, elemIndex, uncons);
-- import Control.Monad (forM_, when);
-- import System.Exit (exitWith, ExitCode( ExitSuccess ));
-- import System.Random.Stateful ();
-- import Data.Char (isSpace); 
import Simulate (ppAgent, ppMsg, ppSig, ppK, ppG, ppNmk, ppNonce, ppSet, ppList, ppTrace, ppTraceApp, 
  format_events, format_reach, simulate_cnt, eventList, eventTreeList, formatEvents,
  TEvent(..), TEventPos(..), EventTree(..), formatTEvent, formatTEvents, explore_tree_cnt, getChannelList, getChannelList4Property);
import DHWJ_config (Deve(..), equal_deve, mkbma)
import DHWJ_wbplsec (dHWJ_active)

newtype DHWJ_TEvent = DHWJ_TEvent (TEvent 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 
  (Numeral_Type.Bit1 Numeral_Type.Num1)
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  )
  deriving (Eq, Read, Show);

newtype DHWJ_EventTree = DHWJ_EventTree (EventTree 
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 
  (Numeral_Type.Bit1 Numeral_Type.Num1)
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  )
  deriving (Eq, Read, Show);

instance Eq Deve where {
  a == b = equal_deve a b;
};

-- | A top-level function to explore an ITree for given steps of external events and internal events 
explore_tree_DHWJ ::  Int -> Int -> Deve -> EventTree
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1))
  Numeral_Type.Num1 
  (Numeral_Type.Bit1 Numeral_Type.Num1)
  (Numeral_Type.Bit0 Numeral_Type.Num1)
  ;
explore_tree_DHWJ steps tau_steps eve = ETNode (TEP 0 0 Root) (explore_tree_cnt (dHWJ_active eve) steps 1 tau_steps tau_steps)
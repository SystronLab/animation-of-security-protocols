{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Sec_Messages(Dagent(..), equal_dagent, Dsig(..), equal_dsig, Dbitmask(..),
                equal_dbitmask, Dkey(..), equal_dkey, Dmsg(..), equal_dmsg,
                Chan(..), equal_chan, last4, pKsLst, sKsLst, atomic, is_MWat,
                mwb, break_lst, atomics, breakm, ks, ma, mn, sn, sp, un_env_C,
                is_env_C, env, un_sig_C, is_sig_C, sig, mc1, mc2, mem, pk_of_sk,
                agentsLst, noncesLst, buildable, un_leak_C, is_leak_C, leak,
                un_recv_C, is_recv_C, recv, un_send_C, is_send_C, send,
                un_terminate_C, is_terminate_C, terminate, filter_buildable)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified Channel_Type;
import qualified Prisms;
import qualified HOL;
import qualified List;
import qualified Set;
import qualified FSNat;
import qualified Typerep;
import qualified Type_Length;

data Dagent a = Agent (FSNat.Fsnat a) | Intruder | Server
  deriving (Prelude.Read, Prelude.Show);

equal_dagent :: forall a. (Type_Length.Len a) => Dagent a -> Dagent a -> Bool;
equal_dagent Intruder Server = False;
equal_dagent Server Intruder = False;
equal_dagent (Agent x1) Server = False;
equal_dagent Server (Agent x1) = False;
equal_dagent (Agent x1) Intruder = False;
equal_dagent Intruder (Agent x1) = False;
equal_dagent (Agent x1) (Agent y1) = FSNat.equal_fsnat x1 y1;
equal_dagent Server Server = True;
equal_dagent Intruder Intruder = True;

data Dsig a b = ClaimSecret (Dagent a) (FSNat.Fsnat b) (Set.Set (Dagent a))
  | StartProt (Dagent a) (Dagent a) (FSNat.Fsnat b) (FSNat.Fsnat b)
  | EndProt (Dagent a) (Dagent a) (FSNat.Fsnat b) (FSNat.Fsnat b)
  deriving (Prelude.Read, Prelude.Show);

instance (Type_Length.Len a) => Eq (Dagent a) where {
  a == b = equal_dagent a b;
};

equal_dsig ::
  forall a b.
    (Type_Length.Len a, Type_Length.Len b) => Dsig a b -> Dsig a b -> Bool;
equal_dsig (StartProt x21 x22 x23 x24) (EndProt x31 x32 x33 x34) = False;
equal_dsig (EndProt x31 x32 x33 x34) (StartProt x21 x22 x23 x24) = False;
equal_dsig (ClaimSecret x11 x12 x13) (EndProt x31 x32 x33 x34) = False;
equal_dsig (EndProt x31 x32 x33 x34) (ClaimSecret x11 x12 x13) = False;
equal_dsig (ClaimSecret x11 x12 x13) (StartProt x21 x22 x23 x24) = False;
equal_dsig (StartProt x21 x22 x23 x24) (ClaimSecret x11 x12 x13) = False;
equal_dsig (EndProt x31 x32 x33 x34) (EndProt y31 y32 y33 y34) =
  equal_dagent x31 y31 &&
    equal_dagent x32 y32 &&
      FSNat.equal_fsnat x33 y33 && FSNat.equal_fsnat x34 y34;
equal_dsig (StartProt x21 x22 x23 x24) (StartProt y21 y22 y23 y24) =
  equal_dagent x21 y21 &&
    equal_dagent x22 y22 &&
      FSNat.equal_fsnat x23 y23 && FSNat.equal_fsnat x24 y24;
equal_dsig (ClaimSecret x11 x12 x13) (ClaimSecret y11 y12 y13) =
  equal_dagent x11 y11 && FSNat.equal_fsnat x12 y12 && Set.equal_set x13 y13;

data Dbitmask a = Null | Bm (FSNat.Fsnat a)
  deriving (Prelude.Read, Prelude.Show);

equal_dbitmask ::
  forall a. (Type_Length.Len a) => Dbitmask a -> Dbitmask a -> Bool;
equal_dbitmask Null (Bm x2) = False;
equal_dbitmask (Bm x2) Null = False;
equal_dbitmask (Bm x2) (Bm y2) = FSNat.equal_fsnat x2 y2;
equal_dbitmask Null Null = True;

data Dkey a b = Kp (FSNat.Fsnat a) | Ks (FSNat.Fsnat b)
  deriving (Prelude.Read, Prelude.Show);

equal_dkey ::
  forall a b.
    (Type_Length.Len a, Type_Length.Len b) => Dkey a b -> Dkey a b -> Bool;
equal_dkey (Kp x1) (Ks x2) = False;
equal_dkey (Ks x2) (Kp x1) = False;
equal_dkey (Ks x2) (Ks y2) = FSNat.equal_fsnat x2 y2;
equal_dkey (Kp x1) (Kp y1) = FSNat.equal_fsnat x1 y1;

data Dmsg a b c d e f = MAg (Dagent a) | MNon (FSNat.Fsnat b) | MK (Dkey c d)
  | MPair (Dmsg a b c d e f) (Dmsg a b c d e f)
  | MAEnc (Dmsg a b c d e f) (Dmsg a b c d e f)
  | MSig (Dmsg a b c d e f) (Dmsg a b c d e f)
  | MSEnc (Dmsg a b c d e f) (Dmsg a b c d e f) | MExpg (FSNat.Fsnat e)
  | MModExp (Dmsg a b c d e f) (Dmsg a b c d e f) | MBitm (Dbitmask f)
  | MWat (Dmsg a b c d e f) (Dmsg a b c d e f)
  | MJam (Dmsg a b c d e f) (Dmsg a b c d e f)
  deriving (Prelude.Read, Prelude.Show);

equal_dmsg ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f -> Dmsg a b c d e f -> Bool;
equal_dmsg (MWat x111 x112) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MWat x111 x112) = False;
equal_dmsg (MBitm x10) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MBitm x10) = False;
equal_dmsg (MModExp x91 x92) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MModExp x91 x92) = False;
equal_dmsg (MExpg x8) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MExpg x8) = False;
equal_dmsg (MSEnc x71 x72) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MSEnc x71 x72) = False;
equal_dmsg (MSig x61 x62) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MSig x61 x62) = False;
equal_dmsg (MAEnc x51 x52) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MAEnc x51 x52) = False;
equal_dmsg (MPair x41 x42) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MPair x41 x42) = False;
equal_dmsg (MK x3) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MK x3) = False;
equal_dmsg (MK x3) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MK x3) = False;
equal_dmsg (MK x3) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MK x3) = False;
equal_dmsg (MK x3) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MK x3) = False;
equal_dmsg (MK x3) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MK x3) = False;
equal_dmsg (MK x3) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MK x3) = False;
equal_dmsg (MK x3) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MK x3) = False;
equal_dmsg (MK x3) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MK x3) = False;
equal_dmsg (MK x3) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MK x3) = False;
equal_dmsg (MNon x2) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MNon x2) = False;
equal_dmsg (MNon x2) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MNon x2) = False;
equal_dmsg (MNon x2) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MNon x2) = False;
equal_dmsg (MNon x2) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MNon x2) = False;
equal_dmsg (MNon x2) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MNon x2) = False;
equal_dmsg (MNon x2) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MNon x2) = False;
equal_dmsg (MNon x2) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MNon x2) = False;
equal_dmsg (MNon x2) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MNon x2) = False;
equal_dmsg (MNon x2) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MNon x2) = False;
equal_dmsg (MNon x2) (MK x3) = False;
equal_dmsg (MK x3) (MNon x2) = False;
equal_dmsg (MAg x1) (MJam x121 x122) = False;
equal_dmsg (MJam x121 x122) (MAg x1) = False;
equal_dmsg (MAg x1) (MWat x111 x112) = False;
equal_dmsg (MWat x111 x112) (MAg x1) = False;
equal_dmsg (MAg x1) (MBitm x10) = False;
equal_dmsg (MBitm x10) (MAg x1) = False;
equal_dmsg (MAg x1) (MModExp x91 x92) = False;
equal_dmsg (MModExp x91 x92) (MAg x1) = False;
equal_dmsg (MAg x1) (MExpg x8) = False;
equal_dmsg (MExpg x8) (MAg x1) = False;
equal_dmsg (MAg x1) (MSEnc x71 x72) = False;
equal_dmsg (MSEnc x71 x72) (MAg x1) = False;
equal_dmsg (MAg x1) (MSig x61 x62) = False;
equal_dmsg (MSig x61 x62) (MAg x1) = False;
equal_dmsg (MAg x1) (MAEnc x51 x52) = False;
equal_dmsg (MAEnc x51 x52) (MAg x1) = False;
equal_dmsg (MAg x1) (MPair x41 x42) = False;
equal_dmsg (MPair x41 x42) (MAg x1) = False;
equal_dmsg (MAg x1) (MK x3) = False;
equal_dmsg (MK x3) (MAg x1) = False;
equal_dmsg (MAg x1) (MNon x2) = False;
equal_dmsg (MNon x2) (MAg x1) = False;
equal_dmsg (MJam x121 x122) (MJam y121 y122) =
  equal_dmsg x121 y121 && equal_dmsg x122 y122;
equal_dmsg (MWat x111 x112) (MWat y111 y112) =
  equal_dmsg x111 y111 && equal_dmsg x112 y112;
equal_dmsg (MBitm x10) (MBitm y10) = equal_dbitmask x10 y10;
equal_dmsg (MModExp x91 x92) (MModExp y91 y92) =
  equal_dmsg x91 y91 && equal_dmsg x92 y92;
equal_dmsg (MExpg x8) (MExpg y8) = FSNat.equal_fsnat x8 y8;
equal_dmsg (MSEnc x71 x72) (MSEnc y71 y72) =
  equal_dmsg x71 y71 && equal_dmsg x72 y72;
equal_dmsg (MSig x61 x62) (MSig y61 y62) =
  equal_dmsg x61 y61 && equal_dmsg x62 y62;
equal_dmsg (MAEnc x51 x52) (MAEnc y51 y52) =
  equal_dmsg x51 y51 && equal_dmsg x52 y52;
equal_dmsg (MPair x41 x42) (MPair y41 y42) =
  equal_dmsg x41 y41 && equal_dmsg x42 y42;
equal_dmsg (MK x3) (MK y3) = equal_dkey x3 y3;
equal_dmsg (MNon x2) (MNon y2) = FSNat.equal_fsnat x2 y2;
equal_dmsg (MAg x1) (MAg y1) = equal_dagent x1 y1;

data Chan a b c d e f = Env_C (Dagent a, Dagent a)
  | Send_C (Dagent a, (Dagent a, (Dagent a, Dmsg a b c d e f)))
  | Cjam_C (Dmsg a b c d e f) | Cdejam_C (Dmsg a b c d e f)
  | Recv_C (Dagent a, (Dagent a, (Dagent a, Dmsg a b c d e f)))
  | Leak_C (Dmsg a b c d e f) | Sig_C (Dsig a b) | Terminate_C ()
  deriving (Prelude.Read, Prelude.Show);

instance (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
           Type_Length.Len d, Type_Length.Len e,
           Type_Length.Len f) => Eq (Dmsg a b c d e f) where {
  a == b = equal_dmsg a b;
};

equal_chan ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Chan a b c d e f -> Chan a b c d e f -> Bool;
equal_chan (Sig_C x7) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Sig_C x7) = False;
equal_chan (Leak_C x6) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Leak_C x6) = False;
equal_chan (Recv_C x5) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Recv_C x5) = False;
equal_chan (Cdejam_C x4) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Cdejam_C x4) = False;
equal_chan (Cjam_C x3) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Cjam_C x3) = False;
equal_chan (Send_C x2) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Send_C x2) = False;
equal_chan (Send_C x2) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Send_C x2) = False;
equal_chan (Send_C x2) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Send_C x2) = False;
equal_chan (Send_C x2) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Send_C x2) = False;
equal_chan (Send_C x2) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Send_C x2) = False;
equal_chan (Send_C x2) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Send_C x2) = False;
equal_chan (Env_C x1) (Terminate_C x8) = False;
equal_chan (Terminate_C x8) (Env_C x1) = False;
equal_chan (Env_C x1) (Sig_C x7) = False;
equal_chan (Sig_C x7) (Env_C x1) = False;
equal_chan (Env_C x1) (Leak_C x6) = False;
equal_chan (Leak_C x6) (Env_C x1) = False;
equal_chan (Env_C x1) (Recv_C x5) = False;
equal_chan (Recv_C x5) (Env_C x1) = False;
equal_chan (Env_C x1) (Cdejam_C x4) = False;
equal_chan (Cdejam_C x4) (Env_C x1) = False;
equal_chan (Env_C x1) (Cjam_C x3) = False;
equal_chan (Cjam_C x3) (Env_C x1) = False;
equal_chan (Env_C x1) (Send_C x2) = False;
equal_chan (Send_C x2) (Env_C x1) = False;
equal_chan (Terminate_C x8) (Terminate_C y8) = x8 == y8;
equal_chan (Sig_C x7) (Sig_C y7) = equal_dsig x7 y7;
equal_chan (Leak_C x6) (Leak_C y6) = equal_dmsg x6 y6;
equal_chan (Recv_C x5) (Recv_C y5) = x5 == y5;
equal_chan (Cdejam_C x4) (Cdejam_C y4) = equal_dmsg x4 y4;
equal_chan (Cjam_C x3) (Cjam_C y3) = equal_dmsg x3 y3;
equal_chan (Send_C x2) (Send_C y2) = x2 == y2;
equal_chan (Env_C x1) (Env_C y1) = x1 == y1;

instance (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b,
           Typerep.Typerep b, Type_Length.Len c, Typerep.Typerep c,
           Type_Length.Len d, Typerep.Typerep d, Type_Length.Len e,
           Typerep.Typerep e, Type_Length.Len f,
           Typerep.Typerep f) => Eq (Chan a b c d e f) where {
  a == b = equal_chan a b;
};

last4 :: forall a b c d. (a, (b, (c, d))) -> d;
last4 x = snd (snd (snd x));

pKsLst ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f) => [Dkey a b] -> [Dmsg c d a b e f];
pKsLst pks = map MK pks;

sKsLst ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f) => [Dkey a b] -> [Dmsg c d a b e f];
sKsLst sks = map MK sks;

atomic ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f -> [Dmsg a b c d e f];
atomic (MAg m) = [MAg m];
atomic (MNon m) = [MNon m];
atomic (MK m) = [MK m];
atomic (MPair m1 m2) = List.union (atomic m1) (atomic m2);
atomic (MAEnc m k) = atomic m;
atomic (MSig m k) = atomic m;
atomic (MSEnc m k) = atomic m;
atomic (MExpg m) = [MExpg m];
atomic (MModExp m k) = atomic m;
atomic (MBitm b) = [MBitm b];
atomic (MWat m k) = atomic m;
atomic (MJam m k) = atomic m;

is_MWat ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f) => Dmsg a b c d e f -> Bool;
is_MWat (MAg x1) = False;
is_MWat (MNon x2) = False;
is_MWat (MK x3) = False;
is_MWat (MPair x41 x42) = False;
is_MWat (MAEnc x51 x52) = False;
is_MWat (MSig x61 x62) = False;
is_MWat (MSEnc x71 x72) = False;
is_MWat (MExpg x8) = False;
is_MWat (MModExp x91 x92) = False;
is_MWat (MBitm x10) = False;
is_MWat (MWat x111 x112) = True;
is_MWat (MJam x121 x122) = False;

mwb ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f -> Dmsg a b c d e f;
mwb (MWat x111 x112) = x112;

break_lst ::
  forall a b c d e.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e) => [Dmsg a b c c d e] ->
                              [Dmsg a b c c d e] ->
                                Set.Set (Dmsg a b c c d e) ->
                                  [Dmsg a b c c d e];
break_lst [] ams asa = ams;
break_lst (MK k : xs) ams asa = break_lst xs (List.insert (MK k) ams) asa;
break_lst (MAg a : xs) ams asa = break_lst xs (List.insert (MAg a) ams) asa;
break_lst (MNon a : xs) ams asa = break_lst xs (List.insert (MNon a) ams) asa;
break_lst (MPair a b : xs) ams asa =
  break_lst xs
    (List.remdups (break_lst [a] ams asa ++ break_lst [b] ams asa ++ ams)) asa;
break_lst (MAEnc a (MK (Kp k)) : xs) ams asa =
  (if Set.member (MK (Ks k)) asa
    then (if List.member ams (MK (Ks k))
           then break_lst (a : xs) (List.insert (MAEnc a (MK (Kp k))) ams) asa
           else let {
                  rams = break_lst xs ams asa;
                } in (if List.member rams (MK (Ks k))
                       then break_lst (a : xs)
                              (List.insert (MAEnc a (MK (Kp k))) ams) asa
                       else break_lst xs (List.insert (MAEnc a (MK (Kp k))) ams)
                              asa))
    else break_lst xs (List.insert (MAEnc a (MK (Kp k))) ams) asa);
break_lst (MSig a (MK (Ks k)) : xs) ams asa =
  (if Set.member (MK (Kp k)) asa
    then (if List.member ams (MK (Kp k))
           then break_lst (a : xs) (List.insert (MSig a (MK (Ks k))) ams) asa
           else let {
                  rams = break_lst xs ams asa;
                } in (if List.member rams (MK (Kp k))
                       then break_lst (a : xs)
                              (List.insert (MSig a (MK (Ks k))) ams) asa
                       else break_lst xs (List.insert (MSig a (MK (Ks k))) ams)
                              asa))
    else break_lst xs (List.insert (MSig a (MK (Ks k))) ams) asa);
break_lst (MSEnc m k : xs) ams asa =
  (case k of {
    MAg _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MNon _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MK (Kp _) -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MK (Ks ka) ->
      (if Set.member (MK (Ks ka)) asa
        then (if List.member ams (MK (Ks ka))
               then break_lst (m : xs) (List.insert (MSEnc m (MK (Ks ka))) ams)
                      asa
               else let {
                      rams = break_lst xs ams asa;
                    } in (if List.member rams (MK (Ks ka))
                           then break_lst (m : xs)
                                  (List.insert (MAEnc m (MK (Ks ka))) ams) asa
                           else break_lst xs
                                  (List.insert (MAEnc m (MK (Ks ka))) ams) asa))
        else break_lst xs (List.insert (MAEnc m (MK (Ks ka))) ams) asa);
    MPair _ _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MAEnc _ _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MSig _ _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MSEnc _ _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MExpg _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MAg _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MNon _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MK _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MPair _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MAEnc _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MSig _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MSEnc _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MExpg _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MAg _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MNon _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MK _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MPair _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MAEnc _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MSig _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MSEnc _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MExpg gn) a) b ->
      (if List.member ams (MModExp (MExpg gn) a) && List.member ams b ||
            (List.member ams (MModExp (MExpg gn) b) && List.member ams a ||
              List.member ams (MExpg gn) &&
                List.member ams a && List.member ams b)
        then break_lst (m : xs) (List.insert (MSEnc m k) ams) asa
        else let {
               rams = break_lst xs ams asa;
             } in (if List.member rams (MModExp (MExpg gn) a) &&
                        List.member rams b ||
                        (List.member rams (MModExp (MExpg gn) b) &&
                           List.member rams a ||
                          List.member rams (MExpg gn) &&
                            List.member rams a && List.member rams b)
                    then break_lst (m : xs) (List.insert (MSEnc m k) ams) asa
                    else break_lst xs (List.insert (MSEnc m k) ams) asa));
    MModExp (MModExp (MModExp _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MBitm _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MWat _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MModExp (MJam _ _) _) _ ->
      break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MBitm _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MWat _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MModExp (MJam _ _) _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MBitm _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MWat _ _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
    MJam _ _ -> break_lst xs (List.insert (MSEnc m k) ams) asa;
  });
break_lst (MExpg a : xs) ams asa = break_lst xs (List.insert (MExpg a) ams) asa;
break_lst (MModExp a b : xs) ams asa =
  break_lst xs (List.insert (MModExp a b) ams) asa;
break_lst (MBitm b : xs) ams asa = break_lst xs (List.insert (MBitm b) ams) asa;
break_lst (MWat m b : xs) ams asa = break_lst xs (List.insert m ams) asa;
break_lst (MJam m (MBitm b) : xs) ams asa =
  (if not (equal_dbitmask b Null)
    then (if is_MWat m &&
               equal_dmsg (mwb m) (MBitm b) && Set.member (MBitm b) asa
           then (if List.member ams (MBitm b)
                  then break_lst (m : xs) (List.insert (MJam m (MBitm b)) ams)
                         asa
                  else let {
                         rams = break_lst xs ams asa;
                       } in (if List.member rams (MBitm b)
                              then break_lst (m : xs)
                                     (List.insert (MJam m (MBitm b)) ams) asa
                              else break_lst xs
                                     (List.insert (MJam m (MBitm b)) ams) asa))
           else break_lst xs (List.insert (MJam m (MBitm b)) ams) asa)
    else break_lst (m : xs) (List.insert (MJam m (MBitm b)) ams) asa);
break_lst (MAEnc v (MAg vb) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MAg vb)) ams) asa;
break_lst (MAEnc v (MNon vb) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MNon vb)) ams) asa;
break_lst (MAEnc v (MK (Ks vc)) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MK (Ks vc))) ams) asa;
break_lst (MAEnc v (MPair vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MPair vb vc)) ams) asa;
break_lst (MAEnc v (MAEnc vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MAEnc vb vc)) ams) asa;
break_lst (MAEnc v (MSig vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MSig vb vc)) ams) asa;
break_lst (MAEnc v (MSEnc vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MSEnc vb vc)) ams) asa;
break_lst (MAEnc v (MExpg vb) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MExpg vb)) ams) asa;
break_lst (MAEnc v (MModExp vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MModExp vb vc)) ams) asa;
break_lst (MAEnc v (MBitm vb) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MBitm vb)) ams) asa;
break_lst (MAEnc v (MWat vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MWat vb vc)) ams) asa;
break_lst (MAEnc v (MJam vb vc) : xs) ams asa =
  break_lst xs (List.insert (MAEnc v (MJam vb vc)) ams) asa;
break_lst (MSig v (MAg vb) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MAg vb)) ams) asa;
break_lst (MSig v (MNon vb) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MNon vb)) ams) asa;
break_lst (MSig v (MK (Kp vc)) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MK (Kp vc))) ams) asa;
break_lst (MSig v (MPair vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MPair vb vc)) ams) asa;
break_lst (MSig v (MAEnc vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MAEnc vb vc)) ams) asa;
break_lst (MSig v (MSig vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MSig vb vc)) ams) asa;
break_lst (MSig v (MSEnc vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MSEnc vb vc)) ams) asa;
break_lst (MSig v (MExpg vb) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MExpg vb)) ams) asa;
break_lst (MSig v (MModExp vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MModExp vb vc)) ams) asa;
break_lst (MSig v (MBitm vb) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MBitm vb)) ams) asa;
break_lst (MSig v (MWat vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MWat vb vc)) ams) asa;
break_lst (MSig v (MJam vb vc) : xs) ams asa =
  break_lst xs (List.insert (MSig v (MJam vb vc)) ams) asa;
break_lst (MJam v (MAg vb) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MAg vb)) ams) asa;
break_lst (MJam v (MNon vb) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MNon vb)) ams) asa;
break_lst (MJam v (MK vb) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MK vb)) ams) asa;
break_lst (MJam v (MPair vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MPair vb vc)) ams) asa;
break_lst (MJam v (MAEnc vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MAEnc vb vc)) ams) asa;
break_lst (MJam v (MSig vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MSig vb vc)) ams) asa;
break_lst (MJam v (MSEnc vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MSEnc vb vc)) ams) asa;
break_lst (MJam v (MExpg vb) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MExpg vb)) ams) asa;
break_lst (MJam v (MModExp vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MModExp vb vc)) ams) asa;
break_lst (MJam v (MWat vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MWat vb vc)) ams) asa;
break_lst (MJam v (MJam vb vc) : xs) ams asa =
  break_lst xs (List.insert (MJam v (MJam vb vc)) ams) asa;

atomics ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => [Dmsg a b c d e f] -> [Dmsg a b c d e f];
atomics xs = concatMap atomic xs;

breakm ::
  forall a b c d e.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e) => [Dmsg a b c c d e] -> [Dmsg a b c c d e];
breakm xs = let {
              asa = Set.Set (atomics xs);
              ys = break_lst xs [] asa;
            } in break_lst ys [] asa;

ks :: forall a b.
        (Type_Length.Len a, Type_Length.Len b) => Dkey a b -> FSNat.Fsnat b;
ks (Ks x2) = x2;

ma :: forall a b c d e f.
        (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
          Type_Length.Len d, Type_Length.Len e,
          Type_Length.Len f) => Dmsg a b c d e f -> Dagent a;
ma (MAg x1) = x1;

mn :: forall a b c d e f.
        (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c,
          Type_Length.Len d, Type_Length.Len e,
          Type_Length.Len f) => Dmsg a b c d e f -> FSNat.Fsnat b;
mn (MNon x2) = x2;

sn :: forall a b.
        (Type_Length.Len a, Type_Length.Len b) => Dsig a b -> FSNat.Fsnat b;
sn (ClaimSecret x11 x12 x13) = x12;

sp :: forall a b.
        (Type_Length.Len a,
          Type_Length.Len b) => Dsig a b -> Set.Set (Dagent a);
sp (ClaimSecret x11 x12 x13) = x13;

un_env_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Chan a b c d e f -> (Dagent a, Dagent a);
un_env_C (Env_C x1) = x1;

is_env_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Bool;
is_env_C (Env_C x1) = True;
is_env_C (Send_C x2) = False;
is_env_C (Cjam_C x3) = False;
is_env_C (Cdejam_C x4) = False;
is_env_C (Recv_C x5) = False;
is_env_C (Leak_C x6) = False;
is_env_C (Sig_C x7) = False;
is_env_C (Terminate_C x8) = False;

env ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Prisms.Prism_ext (Dagent a, Dagent a)
                              (Chan a b c d e f) ();
env = Channel_Type.ctor_prism Env_C is_env_C un_env_C;

un_sig_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Dsig a b;
un_sig_C (Sig_C x7) = x7;

is_sig_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Bool;
is_sig_C (Env_C x1) = False;
is_sig_C (Send_C x2) = False;
is_sig_C (Cjam_C x3) = False;
is_sig_C (Cdejam_C x4) = False;
is_sig_C (Recv_C x5) = False;
is_sig_C (Leak_C x6) = False;
is_sig_C (Sig_C x7) = True;
is_sig_C (Terminate_C x8) = False;

sig ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Prisms.Prism_ext (Dsig a b) (Chan a b c d e f) ();
sig = Channel_Type.ctor_prism Sig_C is_sig_C un_sig_C;

mc1 ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f -> Dmsg a b c d e f;
mc1 (MPair x41 x42) = x41;

mc2 ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f -> Dmsg a b c d e f;
mc2 (MPair x41 x42) = x42;

mem ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f -> Dmsg a b c d e f;
mem (MAEnc x51 x52) = x51;

pk_of_sk ::
  forall a b c.
    (Type_Length.Len a, Type_Length.Len b,
      Type_Length.Len c) => Dkey a b -> Dkey b c;
pk_of_sk pk = Kp (ks pk);

agentsLst ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e, Type_Length.Len f) => [Dagent a] -> [Dmsg a b c d e f];
agentsLst asa = map MAg asa;

noncesLst ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => [FSNat.Fsnat a] -> [Dmsg b a c d e f];
noncesLst xs = map MNon xs;

buildable ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => Dmsg a b c d e f ->
                              Set.Set (Dmsg a b c d e f) -> Bool;
buildable m ms =
  (if Set.member m ms then True
    else (case m of {
           MAg _ -> False;
           MNon _ -> False;
           MK _ -> False;
           MPair m1 m2 -> buildable m1 ms && buildable m2 ms;
           MAEnc ma k -> buildable ma ms && buildable k ms;
           MSig ma k -> buildable ma ms && buildable k ms;
           MSEnc ma k -> buildable ma ms && buildable k ms;
           MExpg _ -> False;
           MModExp ma k -> buildable ma ms && buildable k ms;
           MBitm _ -> False;
           MWat ma k -> buildable ma ms && buildable k ms;
           MJam ma k -> buildable ma ms && buildable k ms;
         }));

un_leak_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Chan a b c d e f -> Dmsg a b c d e f;
un_leak_C (Leak_C x6) = x6;

is_leak_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Bool;
is_leak_C (Env_C x1) = False;
is_leak_C (Send_C x2) = False;
is_leak_C (Cjam_C x3) = False;
is_leak_C (Cdejam_C x4) = False;
is_leak_C (Recv_C x5) = False;
is_leak_C (Leak_C x6) = True;
is_leak_C (Sig_C x7) = False;
is_leak_C (Terminate_C x8) = False;

leak ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Prisms.Prism_ext (Dmsg a b c d e f)
                              (Chan a b c d e f) ();
leak = Channel_Type.ctor_prism Leak_C is_leak_C un_leak_C;

un_recv_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Chan a b c d e f ->
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f)));
un_recv_C (Recv_C x5) = x5;

is_recv_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Bool;
is_recv_C (Env_C x1) = False;
is_recv_C (Send_C x2) = False;
is_recv_C (Cjam_C x3) = False;
is_recv_C (Cdejam_C x4) = False;
is_recv_C (Recv_C x5) = True;
is_recv_C (Leak_C x6) = False;
is_recv_C (Sig_C x7) = False;
is_recv_C (Terminate_C x8) = False;

recv ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Prisms.Prism_ext
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f)))
                              (Chan a b c d e f) ();
recv = Channel_Type.ctor_prism Recv_C is_recv_C un_recv_C;

un_send_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Chan a b c d e f ->
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f)));
un_send_C (Send_C x2) = x2;

is_send_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Bool;
is_send_C (Env_C x1) = False;
is_send_C (Send_C x2) = True;
is_send_C (Cjam_C x3) = False;
is_send_C (Cdejam_C x4) = False;
is_send_C (Recv_C x5) = False;
is_send_C (Leak_C x6) = False;
is_send_C (Sig_C x7) = False;
is_send_C (Terminate_C x8) = False;

send ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Prisms.Prism_ext
                              (Dagent a,
                                (Dagent a, (Dagent a, Dmsg a b c d e f)))
                              (Chan a b c d e f) ();
send = Channel_Type.ctor_prism Send_C is_send_C un_send_C;

un_terminate_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> ();
un_terminate_C (Terminate_C x8) = x8;

is_terminate_C ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f, Typerep.Typerep f) => Chan a b c d e f -> Bool;
is_terminate_C (Env_C x1) = False;
is_terminate_C (Send_C x2) = False;
is_terminate_C (Cjam_C x3) = False;
is_terminate_C (Cdejam_C x4) = False;
is_terminate_C (Recv_C x5) = False;
is_terminate_C (Leak_C x6) = False;
is_terminate_C (Sig_C x7) = False;
is_terminate_C (Terminate_C x8) = True;

terminate ::
  forall a b c d e f.
    (Type_Length.Len a, Typerep.Typerep a, Type_Length.Len b, Typerep.Typerep b,
      Type_Length.Len c, Typerep.Typerep c, Type_Length.Len d,
      Typerep.Typerep d, Type_Length.Len e, Typerep.Typerep e,
      Type_Length.Len f,
      Typerep.Typerep f) => Prisms.Prism_ext () (Chan a b c d e f) ();
terminate = Channel_Type.ctor_prism Terminate_C is_terminate_C un_terminate_C;

filter_buildable ::
  forall a b c d e f.
    (Type_Length.Len a, Type_Length.Len b, Type_Length.Len c, Type_Length.Len d,
      Type_Length.Len e,
      Type_Length.Len f) => [Dmsg a b c d e f] ->
                              Set.Set (Dmsg a b c d e f) -> [Dmsg a b c d e f];
filter_buildable xs ms =
  concatMap (\ x -> (if buildable x ms then [x] else [])) xs;

}

{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  FSNat(Fsnat(..), fsnatlist, nat_of_fsnat, enum_fsnat, equal_fsnat,
         less_eq_fsnat)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified List;
import qualified HOL;
import qualified Type_Length;
import qualified Arith;

newtype Fsnat a = Nmk Arith.Nat deriving (Prelude.Read, Prelude.Show);

fsnatlist :: forall a. (Type_Length.Len a) => [Fsnat a];
fsnatlist =
  map Nmk
    (List.upt Arith.zero_nat
      ((Type_Length.len_of :: HOL.Itself a -> Arith.Nat) HOL.Type));

nat_of_fsnat :: forall a. (Type_Length.Len a) => Fsnat a -> Arith.Nat;
nat_of_fsnat (Nmk x) =
  Arith.modulo_nat x
    ((Type_Length.len_of :: HOL.Itself a -> Arith.Nat) HOL.Type);

enum_fsnat :: forall a. (Type_Length.Len a) => [Fsnat a];
enum_fsnat = fsnatlist;

equal_fsnat :: forall a. (Type_Length.Len a) => Fsnat a -> Fsnat a -> Bool;
equal_fsnat = (\ k l -> Arith.equal_nat (nat_of_fsnat k) (nat_of_fsnat l));

less_eq_fsnat :: forall a. (Type_Length.Len a) => Fsnat a -> Fsnat a -> Bool;
less_eq_fsnat x y = Arith.less_eq_nat (nat_of_fsnat x) (nat_of_fsnat y);

}

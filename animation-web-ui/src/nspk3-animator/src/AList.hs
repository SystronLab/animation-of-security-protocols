{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AList(delete, update, compose, restrict, clearjunk) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Rational;
import qualified Set;
import qualified Option;
import qualified Map;
import qualified Product_Type;

delete :: forall a b. (Eq a) => a -> [(a, b)] -> [(a, b)];
delete k = filter (\ (ka, _) -> not (k == ka));

update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> [(a, b)];
update k v [] = [(k, v)];
update k v (p : ps) = (if fst p == k then (k, v) : ps else p : update k v ps);

compose :: forall a b c. (Eq a, Eq b) => [(a, b)] -> [(b, c)] -> [(a, c)];
compose [] ys = [];
compose (x : xs) ys = (case Map.map_of ys (snd x) of {
                        Nothing -> compose (delete (fst x) xs) ys;
                        Just v -> (fst x, v) : compose xs ys;
                      });

restrict :: forall a b. (Eq a) => Set.Set a -> [(a, b)] -> [(a, b)];
restrict a = filter (\ (k, _) -> Set.member k a);

clearjunk :: forall a b. (Eq a) => [(a, b)] -> [(a, b)];
clearjunk [] = [];
clearjunk (p : ps) = p : clearjunk (delete (fst p) ps);

}

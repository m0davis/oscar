{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RoleAnnotations #-}

module Match where

import qualified Data.Map.Lazy as Map
import Control.Monad
import Control.Monad.Free
import Data.List
import Data.List.Unicode
import Data.Monoid.Unicode

type Map = Map.Map

match ∷ (Ord a) ⇒ Free [] a → Free [] a → [a] → Maybe (Map a (Free [] a))
match = match' Map.empty

match'expectation ∷ (Ord a) ⇒ Free [] a → Free [] a → Maybe (Map a (Free [] a))
match'expectation pat exp = if pat == exp then return Map.empty
                                          else mzero

{-
   match' binds pattern expression patternVariables
      => Nothing, if there is a failure to match
      => Just binds', if sublis (binds ∪ binds') pattern == expression
                         and binds `intersect` binds' == empty
-}
match' ∷ (Ord a) ⇒ Map a (Free [] a) → Free [] a → Free [] a → [a] → Maybe (Map a (Free [] a))
match' binds (Pure pat) exp vars =
    if pat ∈ vars
      then
          case pat `Map.lookup` binds of
              Just bpat → match'expectation bpat exp
              Nothing → return $ Map.singleton pat exp
      else
          match'expectation (Pure pat) exp
match' binds (Free (pat:pats)) (Free (exp:exps)) vars =
    case match' binds pat exp vars of
        Just mbinds →
            case match' (mbinds `Map.union` binds) (Free pats) (Free exps) vars of
                Just mbinds' → Just $ mbinds `Map.union` mbinds'
                Nothing → Nothing
        Nothing → Nothing
match' _ (Free []) (Free []) _ = Just Map.empty
match' _ (Free _) (Free _) _ = Nothing
match' _ (Free _) (Pure _) _ = Nothing

{-
    case oneOneMatch p q pvs qvs of
        Just m →
            q == sublis (map Pure m) p
              &&
            p == sublis (map Pure (reverseMap m)) q
              &&
            keys m `isSubsetOf` pvs
              &&
            elems m `isSubsetOf` qvs
        Nothing →

-}
oneOneMatch ∷ (Ord a) ⇒ Free [] a → Free [] a → [a] → [a] → Maybe (Map a a)
oneOneMatch pat exp patv expv =
    case match pat exp patv of
        Nothing → Nothing
        Just m →
            if m == Map.empty then
                Just Map.empty
            else
                case Map.elems m `isSubsequenceOf` (Pure <$> expv) of
                    False → Nothing
                    True →
                        case pureMap m of
                            Nothing → Nothing
                            Just m' →
                                if pat == sublis (Pure <$> reverseMap m') exp then
                                    Just m'
                                else
                                    Nothing
  where
    pureMap ∷ Map a (Free [] a) → Maybe (Map a a)
    pureMap m =
        let (f, p) = (`Map.mapEither` m) (\v →
                case v of
                    Pure x → Right x
                    Free _ → Left ()
              ) in
                if null f then
                    Just p
                else
                    Nothing

reverseMap ∷ (Ord a) ⇒ Map a a → Map a a
reverseMap = Map.fromList . map (\(x, y) -> (y, x)) . Map.toList

sublis ∷ (Ord a) ⇒ Map a (Free [] a) → Free [] a → Free [] a
sublis m (Pure x) =
    case x `Map.lookup` m of
        Nothing → Pure x
        Just y → y
sublis m (Free []) = Free []
sublis m (Free (x:xs)) = Free $ sublis m x : (sublis m <$> xs)

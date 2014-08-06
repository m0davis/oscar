{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Oscar.Parenthesis where

import ClassyPrelude

import Control.Monad.Free               (Free(Free))
import Control.Monad.Free               (Free(Pure))
import Numeric.Natural                  (Natural)

-- | Parentheses are like this y(). See 'freeFromParentheses'
data Parenthesis = OpenParenthesis | CloseParenthesis
    deriving (Bounded, Eq, Read, Show)

freeFromParentheses ::
    forall as a b.
    (IsSequence as, Element as ~ a) =>
    (a -> Either Parenthesis b) ->
    as ->
    Free [] b
freeFromParentheses f = fst . ffp 0 []
  where

    ffp :: Natural -> [Free [] b] -> as -> (Free [] b, as)
    ffp d prev ass
        | onull ass =
            (Free prev, mempty)
        | Left OpenParenthesis <- f a =
            let (paren, rest) = ffp (succ d) [] as
            in  ffp d (prev ++ [paren]) rest
        | Left CloseParenthesis <- f a
        , d == 0 =
            error "unexpected CloseParenthesis at depth 0"
        | Left CloseParenthesis <- f a =
            (Free prev, as)
        | Right b <- f a =
            ffp d (prev ++ [Pure b]) as
        | otherwise = error ""
          -- suppresses invalid ghc warning about non-exhaustive pattern match
        where
            Just (a, as) = uncons ass


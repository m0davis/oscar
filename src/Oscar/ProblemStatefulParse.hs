{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemStatefulParse where

import ClassyPrelude

import Control.Applicative              (many)
import Text.Parsec                      (anyChar)
import Text.Parsec.Text                 (Parser)

import Oscar.Utilities                  (simpleParse)
import Oscar.Utilities                  (type (⁞))
import Oscar.Utilities                  (unƭ)
import Oscar.Utilities                  (ƭ)

-- | Allows for parsing with type-level state transitions.
--
-- For example:
--
-- @
-- data AtTheBeginning
-- data SomewhereInTheMiddle
-- data AtTheEnd
-- 
--     instance StatefulParse Text Beginning Middle where
--         statefulParse = ƭ $ string "Hello, " *> 
--     
--     instance StatefulParse Text Middle End where
--         statefulParse = ƭ $ pack <$> many anyChar
-- 
--     fullText ∷ Text ⁞ AtTheBeginning
--     fullText = pack $ "Hello, World!"
-- 
--     parseHelloSomeone ∷ (Text ⁞ SomewhereInTheMiddle, Text ⁞ AtTheEnd)
--     parseHelloSomeone = do
--         (beginningToMiddleValue, middleToEndText) ← runStatefulParse fullText
--         (middleToEndValue, _) ← runStatefulParse fullText
-- @
--
-- Don't you love type safety?
class StatefulParse value state1 state2 | value state1 → state2 where
    statefulParse ∷ Parser value ⁞ state1

    -- | The default implementation uses 'simpleParse'.
    runStatefulParse ∷ Text ⁞ state1 → (value, Text ⁞ state2)
    runStatefulParse = simpleParse p' . unƭ
      where
        p' ∷ Parser (value, Text ⁞ state2)
        p' = do
            v ← unƭ (statefulParse ∷ Parser value ⁞ state1)
            r ← pack <$> many anyChar
            return (v, ƭ r)

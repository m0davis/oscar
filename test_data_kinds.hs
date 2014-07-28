{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

import ClassyPrelude
import Control.Monad.Free

newtype L0Text = L0Text Text

data Parenthesis = OpenParenthesis | CloseParenthesis

data LexemeParentheses c
    =   LPCParenthesis Parenthesis
    |   LPCChar c

data LexemeParenthesesTexts a
    =   LPTParenthesis Parenthesis
    |   LPTText a

foo :: [Free [] (LPTText Text)] -> [LexemeParenthesesTexts Text]
foo = undefined

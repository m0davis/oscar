{-# LANGUAGE NoImplicitPrelude #-}

module Oscar.FormulaParser (
    formulaFromText,
  ) where

import ClassyPrelude

import Oscar.FormulaParser.Internal     (freeFromParentheses)
import Oscar.FormulaParser.Internal     (makeFormula)
import Oscar.FormulaParser.Internal     (makePQTokens)
import Oscar.FormulaParser.Internal     (makeQSTokenTree)
import Oscar.FormulaParser.Internal     (reformQSTokenTree)
import Oscar.Formula                    (Formula)

formulaFromText :: Text -> Formula
formulaFromText = id
    . makeFormula
    . reformQSTokenTree
    . makeQSTokenTree
    . freeFromParentheses id
    . makePQTokens

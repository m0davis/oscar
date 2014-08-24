{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.FormulaParser (
    formulaFromText,
  ) where

import Oscar.Main.Prelude

import Oscar.FormulaParser.Internal     (freeFromParentheses)
import Oscar.FormulaParser.Internal     (makeFormula)
import Oscar.FormulaParser.Internal     (makePQTokens)
import Oscar.FormulaParser.Internal     (makeQSTokenTree)
import Oscar.FormulaParser.Internal     (reformQSTokenTree)
import Oscar.Formula                    (Formula)

-- | See "Oscar.Documentation" for examples of how to write a Formula.
formulaFromText ∷ Text → Formula
formulaFromText = id
    . makeFormula
    . reformQSTokenTree
    . makeQSTokenTree
    . freeFromParentheses id
    . makePQTokens

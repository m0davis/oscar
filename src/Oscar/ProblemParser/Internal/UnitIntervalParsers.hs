{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.UnitIntervalParsers (
    LispPositiveDouble(..),
    parserLispPositiveDouble,
    parserProblemJustificationDegree,
    parserProblemInterestDegree,
    parserProblemStrengthDegree,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem                    (ProblemJustificationDegree(ProblemJustificationDegree))
import Oscar.Problem                    (ProblemInterestDegree(ProblemInterestDegree))
import Oscar.Problem                    (ProblemStrengthDegree(ProblemStrengthDegree))
import Oscar.Problem                    (LispPositiveDouble(LispPositiveDouble))

-- | TODO rename LispPositiveDouble to ...? require the number to lie in (0,1]
parserLispPositiveDouble ∷ Parser LispPositiveDouble
parserLispPositiveDouble = do
    d ← many space *> manyTill anyChar ((space *> pure ()) <|> eof)
    if null d then
        mzero
    else
        if headEx d == '.' then
            return . LispPositiveDouble . read $ "0" ++ d
        else if headEx d == '-' then
            error "LispPositiveDouble negative number?"
        else
            return . LispPositiveDouble . read $ d

parserProblemJustificationDegree ∷ Parser ProblemJustificationDegree
parserProblemJustificationDegree = ProblemJustificationDegree <$>
    (many space *>
     string "justification" *>
     many space *>
     char '=' *>
     parserLispPositiveDouble
     )

parserProblemInterestDegree ∷ Parser ProblemInterestDegree
parserProblemInterestDegree = ProblemInterestDegree <$>
    (many space *>
     string "interest" *>
     many space *>
     char '=' *>
     parserLispPositiveDouble
     )

parserProblemStrengthDegree ∷ Parser ProblemStrengthDegree
parserProblemStrengthDegree = ProblemStrengthDegree <$>
    (many space *>
     string "strength" *>
     many space *>
     char '=' *>
     parserLispPositiveDouble
     )

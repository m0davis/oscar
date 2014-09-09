{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.DegreeParsers (
    Degree(..),
    parserDegree,
    parserProblemJustificationDegree,
    parserProblemInterestDegree,
    parserProblemStrengthDegree,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem                    (ProblemJustificationDegree(ProblemJustificationDegree))
import Oscar.Problem                    (ProblemInterestDegree(ProblemInterestDegree))
import Oscar.Problem                    (ProblemStrengthDegree(ProblemStrengthDegree))
import Oscar.Problem                    (Degree(Degree))

{- | Reads a Degree, ensuring that it lies in the interval (0,1]. 

     Consumes nothing upon failure.
-}
parserDegree ∷ Parser Degree
parserDegree = try $ do
    d ← many space *> manyTill anyChar ((space *> pure ()) <|> eof)
    if null d then
        mzero
    else
        if headEx d == '.' then
            return . Degree . read $ "0" ++ d
        else if headEx d == '-' then
            error "Degree given as a negative number?"
        else do
            let d' = read d
            if d' > 0 && d' <= 1 then
                return $ Degree d'
            else
                error "Degree must be > 0 and <= 1"

{- | Consumes @justification = <Degree>@, ignoring whitespace.

     Consumes nothing upon failure.
-}
parserProblemJustificationDegree ∷ Parser ProblemJustificationDegree
parserProblemJustificationDegree = try $ ProblemJustificationDegree <$>
    (many space *>
     string "justification" *>
     many space *>
     char '=' *>
     parserDegree
     )

{- | Consumes @interest = <Degree>@, ignoring whitespace.

     Consumes nothing upon failure.
-}
parserProblemInterestDegree ∷ Parser ProblemInterestDegree
parserProblemInterestDegree = try $ ProblemInterestDegree <$>
    (many space *>
     string "interest" *>
     many space *>
     char '=' *>
     parserDegree
     )

{- | Consumes @strength = <Degree>@, ignoring whitespace.

     Consumes nothing upon failure.
-}
parserProblemStrengthDegree ∷ Parser ProblemStrengthDegree
parserProblemStrengthDegree = try $ ProblemStrengthDegree <$>
    (many space *>
     string "strength" *>
     many space *>
     char '=' *>
     parserDegree
     )

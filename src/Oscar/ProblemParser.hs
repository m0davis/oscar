{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}

module Oscar.ProblemParser (
    readFileProblems,
    readProblemsTextFile,
    ) where

import Oscar.Main.Prelude

import Oscar.ProblemParser.Internal     (partitionProblemsText)
import Oscar.ProblemParser.Internal     (problemFromText)
import Oscar.Problem                    (Problem)

-- | This is the highest-level problem decoder available in this module. Uses "readProblemsTextFile".
readFileProblems ∷ FilePath ⁞ [Problem] → IO [Problem]
readFileProblems = return . map problemFromText . partitionProblemsText <=< readProblemsTextFile

-- | Wrapper around "readFile".
readProblemsTextFile ∷ (FilePath ⁞ [Problem])  -- ^ The input file is presumed to represent one or more problems...
                     → IO (Text ⁞ [Problem])   -- ^ as 'Text'. 'IO' obtained via 'readFile'.
readProblemsTextFile = map ƭ . readFile . unƭ

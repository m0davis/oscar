{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}

{- See 'Oscar.Documentation' for an example of how to write a 'Problem' -}

module Oscar.ProblemParser (
    readFileProblems,
    readProblemsTextFile,
    stripLineComments,
    ) where

import Oscar.Main.Prelude

import Data.List.Split                      (splitOn)

import Oscar.Problem                        (Problem)
import Oscar.ProblemParser.Internal         (partitionProblemsText)
import Oscar.ProblemParser.Internal         (problemFromText)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemsWithLineComments)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemsWithoutLineComments)

{- | This is the highest-level problem decoder available in this module.
     Uses 'readProblemsTextFile'.
-}
readFileProblems ∷ FilePath ⁞ ƮProblemsWithLineComments → IO [Problem]
readFileProblems =
        return . map problemFromText . partitionProblemsText
    <=<
        readProblemsTextFile

-- | Wrapper around 'readFile' and 'stripLineComments'.
readProblemsTextFile ∷ (FilePath ⁞ ƮProblemsWithLineComments)    -- ^ The input file is presumed to represent one or more problems...
                     → IO (Text ⁞ ƮProblemsWithoutLineComments)  -- ^ as 'Text'. 'IO' obtained via 'readFile'.
readProblemsTextFile = (map $ reƭ . stripLineComments . ƭ) . readFile . unƭ

{- | Strips line comments. That is, any characters on or after \";" on each
     given line.
-}
stripLineComments ∷ Text ⁞ ƮProblemsWithLineComments
                  → Text ⁞ ƮProblemsWithoutLineComments
stripLineComments = reƭ . map (unlines . map stripLineComment . lines)
  where
    stripLineComment ∷ Text → Text
    stripLineComment = pack . headEx . splitOn ";" . unpack

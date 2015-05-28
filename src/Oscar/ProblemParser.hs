{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Oscar.ProblemParser (
    -- * Quick start
    -- $QuickStart
    readFileProblems,
    -- * Helpers
    readProblemsTextFile,
    stripLineComments,
    ) where

import Oscar.Main.Prelude

import Data.List.Split                              (splitOn)

import Oscar.Problem                                (Problem)
import Oscar.ProblemParser.Internal                 (problemFromText)
import Oscar.ProblemParser.Internal                 (evalStatefulParser)
import Oscar.ProblemParser.Internal.Tags            (ƮWithLineComments)
import Oscar.ProblemParser.Internal.Tags            (ƮWithoutLineComments)

{- $QuickStart

See 'Oscar.Documentation' for an example of how to write a 'Problem'.
-}

{- | Read problems formatted as decribed in 'Oscar.Documentation'. from the 
     filesystem. Uses 'readProblemsTextFile'.
-}
readFileProblems ∷ FilePath ⁞ ƮWithLineComments → IO [Problem]
readFileProblems =
        return . map problemFromText . evalStatefulParser
    <=<
        readProblemsTextFile

-- | Wrapper around 'readFile' and 'stripLineComments'.
readProblemsTextFile ∷ (FilePath ⁞ ƮWithLineComments)    
                       -- ^ The input file is presumed to represent one or 
                       --   more problems...
                     → IO (Text ⁞ ƮWithoutLineComments)  
                       -- ^ as 'Text'. 'IO' obtained via 'readFile'.
readProblemsTextFile = (map $ reƭ . stripLineComments . ƭ) . readFile . unƭ

{- | Strips line comments. That is, any characters on or after \";" on each
     given line.
-}
stripLineComments ∷ Text ⁞ ƮWithLineComments
                  → Text ⁞ ƮWithoutLineComments
stripLineComments = reƭ . map (unlines . map stripLineComment . lines)
  where
    stripLineComment ∷ Text → Text
    stripLineComment = pack . headEx . splitOn ";" . unpack

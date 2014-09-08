{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}

module Oscar.Main (
    combinedProblemsPath,
    ) where

import Oscar.Main.Prelude

import Oscar.ProblemParser.Internal.Tags    (ƮWithLineComments)

-- | The "combined-problems" file in the current working directory.
combinedProblemsPath ∷ FilePath ⁞ ƮWithLineComments
combinedProblemsPath = ƭ $ fpFromString "combined-problems"

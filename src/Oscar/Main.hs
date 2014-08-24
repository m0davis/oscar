{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}

module Oscar.Main (
    combinedProblemsPath,
    ) where

import Oscar.Main.Prelude

import Oscar.ProblemParser.Internal.Tags    (ƮProblemsWithLineComments)

-- | The "combined-problems" file in the current working directory.
combinedProblemsPath ∷ FilePath ⁞ ƮProblemsWithLineComments
combinedProblemsPath = ƭ $ fpFromString "combined-problems"

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemBase where

import ClassyPrelude

import Oscar.Problem                    (BackwardsReason)
import Oscar.Problem                    (ForwardsReason)
import Oscar.Problem                    (Problem(Problem))
import Oscar.Problem                    (ProblemReasonName)
import Oscar.Problem                    (ProblemStrengthDegree)

stripMeta ∷ (ProblemReasonName, ForwardsReason, ProblemStrengthDegree) → (ForwardsReason, ProblemStrengthDegree)
stripMeta (_, r, d) = (r, d)

stripMeta' ∷ (ProblemReasonName, BackwardsReason, ProblemStrengthDegree) → (BackwardsReason, ProblemStrengthDegree)
stripMeta' (_, r, d) = (r, d)

pattern BaseProblem p i fpfr fcr bpfr bcr ← Problem _ _ p i (map stripMeta → fpfr) (map stripMeta → fcr) (map stripMeta' → bpfr) (map stripMeta' → bcr)

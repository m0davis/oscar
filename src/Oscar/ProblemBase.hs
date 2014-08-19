{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemBase where

import ClassyPrelude

import Oscar.Problem.Internal.Internal  (BackwardsReason)
import Oscar.Problem.Internal.Internal  (ForwardsReason)
import Oscar.Problem.Internal.Internal  (Problem(Problem))
import Oscar.Problem.Internal.Internal  (ProblemReasonName)
import Oscar.Problem.Internal.Internal  (ProblemStrengthDegree)

stripMeta ∷ (ProblemReasonName, ForwardsReason, ProblemStrengthDegree) → (ForwardsReason, ProblemStrengthDegree)
stripMeta (_, r, d) = (r, d)

stripMeta1 ∷ (ProblemReasonName, ForwardsReason) → ForwardsReason
stripMeta1 (_, r) = r

stripMeta' ∷ (ProblemReasonName, BackwardsReason, ProblemStrengthDegree) → (BackwardsReason, ProblemStrengthDegree)
stripMeta' (_, r, d) = (r, d)

stripMeta1' ∷ (ProblemReasonName, BackwardsReason) → BackwardsReason
stripMeta1' (_, r) = r

pattern BaseProblem p i fpfr fcr bpfr bcr ← Problem _ _ p i (map stripMeta → fpfr) (map stripMeta1 → fcr) (map stripMeta' → bpfr) (map stripMeta1' → bcr) 

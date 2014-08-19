{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.Problem (
    -- * readers
    problemsM,
    -- * data
    Problem(..),
    ProblemNumber(..),
    ProblemDescription(..),
    ProblemPremise,
    ProblemInterest,
    ProblemForwardsPrimaFacieReason,
    ProblemForwardsConclusiveReason,
    ProblemBackwardsPrimaFacieReason,
    ProblemBackwardsConclusiveReason,
    ProblemReasonName(..),
    ForwardsReason(..),
    BackwardsReason(..),
    ProblemJustificationDegree(..),
    ProblemInterestDegree(..),
    ProblemStrengthDegree(..),
    Formula(..),
    BinaryOp(..),
    Quantifier(..),
    Symbol(..),
    UnaryOp(..),
    Predication(..),
    DomainFunction(..),
    LispPositiveDouble(..),
    ) where

import ClassyPrelude

import Control.Monad                    ((<=<))

import Oscar.Utilities                  (type (⁞))

import Oscar.DomainFunction             (DomainFunction(..))
import Oscar.Formula                    (Formula(..))
import Oscar.Formula                    (Predication(..))
import Oscar.Problem.Internal.Internal  (BackwardsReason(..))
import Oscar.Problem.Internal.Internal  (ForwardsReason(..))
import Oscar.Problem.Internal.Internal  (Problem(..))
import Oscar.Problem.Internal.Internal  (ProblemBackwardsConclusiveReason)
import Oscar.Problem.Internal.Internal  (ProblemBackwardsPrimaFacieReason)
import Oscar.Problem.Internal.Internal  (ProblemDescription(..))
import Oscar.Problem.Internal.Internal  (ProblemForwardsConclusiveReason)
import Oscar.Problem.Internal.Internal  (ProblemForwardsPrimaFacieReason)
import Oscar.Problem.Internal.Internal  (ProblemInterest)
import Oscar.Problem.Internal.Internal  (ProblemInterestDegree(..))
import Oscar.Problem.Internal.Internal  (ProblemJustificationDegree(..))
import Oscar.Problem.Internal.Internal  (ProblemNumber(..))
import Oscar.Problem.Internal.Internal  (ProblemPremise)
import Oscar.Problem.Internal.Internal  (ProblemReasonName(..))
import Oscar.Problem.Internal.Internal  (ProblemStrengthDegree(..))
import Oscar.Problem.Parser             
import Oscar.ProblemDoubleParser        (LispPositiveDouble(LispPositiveDouble))
import Oscar.QUBS                       (BinaryOp(..))
import Oscar.QUBS                       (Quantifier(..))
import Oscar.QUBS                       (Symbol(..))
import Oscar.QUBS                       (UnaryOp(..))

-- | This is the highest-level problem decoder available in this module.
problemsM ∷ FilePath ⁞ [Problem] → IO [Problem]
problemsM = return . map problemFromText . partitionProblemsText <=< readProblemsTextFile

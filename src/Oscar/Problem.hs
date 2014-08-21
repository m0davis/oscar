{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Problem (
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

import Oscar.Main.Prelude

import Oscar.Formula                    (DomainFunction(..))
import Oscar.Formula                    (Formula(..))
import Oscar.Formula                    (Predication(..))
import Oscar.Formula                    (BinaryOp(..))
import Oscar.Formula                    (Quantifier(..))
import Oscar.Formula                    (Symbol(..))
import Oscar.Formula                    (UnaryOp(..))

-- | A Problem reflects exactly as much information as is parsed from a Text of an OSCAR problem
data Problem = Problem
    { _problemNumber                     ∷ !ProblemNumber
    , _problemDescription                ∷ !ProblemDescription
    , _problemPremises                   ∷ ![ProblemPremise]
    , _problemInterests                  ∷ ![ProblemInterest]
    , _problemForwardsPrimaFacieReasons  ∷ ![ProblemForwardsPrimaFacieReason]
    , _problemForwardsConclusiveReasons  ∷ ![ProblemForwardsConclusiveReason]
    , _problemBackwardsPrimaFacieReasons ∷ ![ProblemBackwardsPrimaFacieReason]
    , _problemBackwardsConclusiveReasons ∷ ![ProblemBackwardsConclusiveReason]
    }
  deriving (Show)

-- | A (hopefully) unique identifier of a 'Problem'.
newtype ProblemNumber = ProblemNumber Int
  deriving (Show)

-- | A (possibly empty) description of the problem.
newtype ProblemDescription = ProblemDescription Text
  deriving (Show)

-- | A formula for a premise with its justification
type ProblemPremise                   = (Formula, ProblemJustificationDegree)

-- | The degree of justification (of a premise)
newtype ProblemJustificationDegree = ProblemJustificationDegree LispPositiveDouble
  deriving (Show)


-- | A formula for an interest with its degree of interest
type ProblemInterest                  = (Formula, ProblemInterestDegree)

-- | The degree of interest (of an interest)
newtype ProblemInterestDegree = ProblemInterestDegree LispPositiveDouble
  deriving (Show)



-- | A forwards p.f. reason with its name and strength
type ProblemForwardsPrimaFacieReason  = (ProblemReasonName, ForwardsReason, ProblemStrengthDegree)

-- | A forwards conclusive reason with its name (the strength is unity, implicitly)
type ProblemForwardsConclusiveReason  = (ProblemReasonName, ForwardsReason)

-- | A backwards p.f. reason with its name and strength
type ProblemBackwardsPrimaFacieReason = (ProblemReasonName, BackwardsReason, ProblemStrengthDegree)

-- | A backwards conclusive reason with its name (the strength is unity, implicitly)
type ProblemBackwardsConclusiveReason = (ProblemReasonName, BackwardsReason)

-- | A name for a reason
newtype ProblemReasonName = ProblemReasonName Text
  deriving (Show)

-- | A forwards reason
data ForwardsReason = ForwardsReason
    { _frForwardsPremises ∷ ![Formula]  -- ^ TODO [] -> Set
    , _frConclusion       ∷ !Formula    -- ^ conclusion
    }
  deriving (Show)

-- | A backwards reason
data BackwardsReason = BackwardsReason
    { _brForwardsPremises  ∷ ![Formula]
    , _brBackwardsPremises ∷ ![Formula]
    , _brConclusion        ∷ !Formula
    }
  deriving (Show)

-- | The strength (of a reason)
newtype ProblemStrengthDegree = ProblemStrengthDegree LispPositiveDouble
  deriving (Show)

newtype LispPositiveDouble = LispPositiveDouble Double
  deriving (Show)

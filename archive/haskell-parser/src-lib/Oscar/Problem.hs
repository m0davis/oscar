{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Problem (
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
    QuantifierOp(..),
    Symbol(..),
    UnaryOp(..),
    Predication(..),
    DomainFunction(..),
    Degree(..),
    -- * "Control.Lens"
    problemNumber,
    problemDescription,
    problemPremises,
    problemInterests,
    problemForwardsPrimaFacieReasons,
    problemForwardsConclusiveReasons,
    problemBackwardsPrimaFacieReasons,
    problemBackwardsConclusiveReasons,
    frForwardsPremises,
    frConclusion,
    brForwardsPremises,
    brBackwardsPremises,
    brConclusion,
    ) where

import Oscar.Main.Prelude

import Control.Lens

import Oscar.Formula                    (BinaryOp(..))
import Oscar.Formula                    (DomainFunction(..))
import Oscar.Formula                    (Formula(..))
import Oscar.Formula                    (Predication(..))
import Oscar.Formula                    (QuantifierOp(..))
import Oscar.Formula                    (Symbol(..))
import Oscar.Formula                    (UnaryOp(..))

type SFormula = Formula Symbol Symbol Symbol Symbol

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
  deriving (Eq, Read, Show)

-- | A (hopefully) unique identifier of a 'Problem'.
newtype ProblemNumber = ProblemNumber Int
  deriving (Eq, Ord, Read, Show)

-- | A (possibly empty) description of the problem.
newtype ProblemDescription = ProblemDescription Text
  deriving (Eq, Read, Show)

-- | A formula of a premise with its justification
type ProblemPremise                   = (SFormula, ProblemJustificationDegree)

-- | The degree of justification (of a premise)
newtype ProblemJustificationDegree = ProblemJustificationDegree Degree
  deriving (Eq, Ord, Read, Show)

-- | A formula of an interest with its degree of interest
type ProblemInterest                  = (SFormula, ProblemInterestDegree)

-- | The degree of interest (of an interest)
newtype ProblemInterestDegree = ProblemInterestDegree Degree
  deriving (Eq, Ord, Read, Show)


{- | A forwards prima facie reason with its name and strength -}
type ProblemForwardsPrimaFacieReason  = (ProblemReasonName
                                        ,ForwardsReason
                                        ,ProblemStrengthDegree
                                        )

{- | A forwards conclusive reason with its name (the strength is unity,
     implicitly)
-}
type ProblemForwardsConclusiveReason  = (ProblemReasonName
                                        ,ForwardsReason)

{- | A backwards prima facie reason with its name and strength -}
type ProblemBackwardsPrimaFacieReason = (ProblemReasonName
                                        ,BackwardsReason
                                        ,ProblemStrengthDegree
                                        )

{- | A backwards conclusive reason with its name (the strength is unity,
     implicitly)
-}
type ProblemBackwardsConclusiveReason = (ProblemReasonName
                                        ,BackwardsReason)

-- | A name of a reason
newtype ProblemReasonName = ProblemReasonName Text
  deriving (Eq, Read, Show)

-- | A forwards reason
data ForwardsReason = ForwardsReason
    { _frForwardsPremises ∷ ![SFormula]
      -- TODO change [] to Set where appropriate
    , _frConclusion       ∷ !SFormula
    }
  deriving (Eq, Read, Show)

-- | A backwards reason
data BackwardsReason = BackwardsReason
    { _brForwardsPremises  ∷ ![SFormula]
    , _brBackwardsPremises ∷ ![SFormula]
    , _brConclusion        ∷ !SFormula
    }
  deriving (Eq, Read, Show)

-- | The strength (of a reason)
newtype ProblemStrengthDegree = ProblemStrengthDegree Degree
  deriving (Eq, Read, Show)

-- | This should only hold values in the interval (0,1].
newtype Degree = Degree Double
  deriving (Eq, Ord, Read, Show)

makeLenses ''Problem
makeLenses ''ForwardsReason
makeLenses ''BackwardsReason

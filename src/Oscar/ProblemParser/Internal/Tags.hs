{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.Tags (
    ƮProblemsWithLineComments,
    ƮProblemsWithoutLineComments,
    ƮProblemAfterNumberLabel,
    ƮProblemAfterNumber,
    ƮProblemAfterDescription,
    ƮGivenPremise,
    ƮUltimateEpistemicInterest,
    ƮProblemVariables,
    ƮReason,
    Direction(..),
    Defeasibility(..),
    ƮSection,
    ) where

import Oscar.Main.Prelude

-- | Prior to stripping those ;...\'s
data ƮProblemsWithLineComments

-- | After stripping those ;...\'s
data ƮProblemsWithoutLineComments

-- | Stuff after the \"Problem #\"
data ƮProblemAfterNumberLabel

-- | Stuff after the \"Problem #\<number>\"
data ƮProblemAfterNumber

-- | Stuff after the \"Problem #\<number>\\n\<description>\" (and starting at the first section)
data ƮProblemAfterDescription

-- | Variables for a reason
data ƮProblemVariables

-- | The premise section
data ƮGivenPremise

-- | The interest section
data ƮUltimateEpistemicInterest

-- | A reason section
data ƮReason (direction ∷ Direction) (defeasibility ∷ Defeasibility)

-- | The only types that make sense here are one of the three Ʈ...\'s above
data ƮSection section

-- | The orientation of a reason.
data Direction
    = Forwards   -- ^ For reasons that require matching premises to draw new conclusions
    | Backwards  -- ^ For reasons that require matching conclusions to draw new interests
  deriving (Show)

-- | The defeasibility of a reason
data Defeasibility
    = PrimaFacie  -- ^ For reasons whose conclusions can be undercut or rebutted
    | Conclusive  -- ^ For reasons whose conclusions are logical consequences of their premises
  deriving (Show)

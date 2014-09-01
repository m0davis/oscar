{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.Tags (
    ƮWithLineComments,
    ƮWithoutLineComments,
    ƮAfterNumberLabel,
    ƮAfterNumber,
    ƮBeginningOfSections,
    ƮGivenPremise,
    ƮUltimateEpistemicInterest,
    ƮVariables,
    ƮReason,
    Direction(..),
    Defeasibility(..),
    ƮSection,
    ) where

import Oscar.Main.Prelude

{- | a Text ⁞ ƮWithLineComments is a representation of a set of Oscar 
     'Problem's. The formatting of such a Problem is described in 
     "Oscar.Documentation".
-}
data ƮWithLineComments

{- | The same as above, but with all line comments removed. See 
     'Oscar.ProblemParser.stripLineComments'.
-}
data ƮWithoutLineComments

-- | Everything after the \"Problem #\".
data ƮAfterNumberLabel

-- | Everything after the \"Problem #\<number>\".
data ƮAfterNumber

{- | Everything after the \"Problem #\<number><whitespace>\\n\<description>\" 
     (and starting at the first section).
-}
data ƮBeginningOfSections

{- | The variables optionally defined for a reason, written as

@
variables = {var1,var2,...,varN}
@
-}
data ƮVariables

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
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | The defeasibility of a reason
data Defeasibility
    = PrimaFacie  -- ^ For reasons whose conclusions can be undercut or rebutted
    | Conclusive  -- ^ For reasons whose conclusions are logical consequences of their premises
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

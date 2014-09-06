{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.Tags (
    ƮWithLineComments,
    ƮWithoutLineComments,
    ƮAfterNumberLabel,
    ƮAfterNumber,
    ƮEndOfDescription,
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

Uses: 

* Text ⁞ ƮWithLineComments
-}
data ƮWithLineComments

{- | The same as above, but with all line comments removed. See
     'Oscar.ProblemParser.stripLineComments'.

Uses: 

* Text ⁞ ƮWithoutLineComments
-}
data ƮWithoutLineComments

{- | Everything after the \"Problem #\".

Uses: 

* Text ⁞ ƮAfterNumberLabel
-}
data ƮAfterNumberLabel

{- | Everything after the \"Problem #\<number>\".

Uses: 

* Text ⁞ ƮAfterNumber
-}
data ƮAfterNumber

{- | Everything after the end of the description. There are two cases. If
     there is some (non-whitespace) description, this marks the first
     position after it (and, necessarily, prior to any sections). If the
     description is empty, this marks the same location as ƮAfterNumber.

Uses: 

* Text ⁞ ƮEndOfDescription
-}
data ƮEndOfDescription

{- | The variables optionally defined for a reason, written as

@
variables = {var1,var2,...,varN}
@

Uses: 

* Text ⁞ ƮVariables
-}
data ƮVariables

{- | The premise section

Uses: 

* Text ⁞ ƮSection ƮGivenPremise
-}
data ƮGivenPremise

{- | The interest section

Uses: 

* Text ⁞ ƮSection ƮUltimateEpistemicInterest
-}
data ƮUltimateEpistemicInterest

{- | A reason section

Uses: 

* Text ⁞ ƮSection (ƮReason Forwards PrimaFacie)
* Text ⁞ ƮSection (ƮReason Forwards Conclusive)
* Text ⁞ ƮSection (ƮReason Backwards PrimaFacie)
* Text ⁞ ƮSection (ƮReason Backwards Conclusive)
* Text ⁞ ƮReason Forwards PrimaFacie
* Text ⁞ ƮReason Forwards Conclusive
* Text ⁞ ƮReason Backwards PrimaFacie
* Text ⁞ ƮReason Backwards Conclusive
-}
data ƮReason (direction ∷ Direction) (defeasibility ∷ Defeasibility)

{- | The only types that make sense here are one of the three Ʈ...\'s above.
     
     A (Text ⁞ ƮSection section) starts at the end of the section label
     and continues to the end of that section, discarding trailing whitespace. 

     __Example__     
     
     Snippet of a 'Problem'

@
∘Given premises:∘∘↵
∘∘some premise text↵
∘∘↵
↵
∘∘Ultimate epistemic interests:↵
@

    Text ⁞ ƮSection ƮGivenPremise is

     @
∘∘↵
∘∘some premise text
@

Uses: (see above, e.g. ƮGivenPremise)
-}
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

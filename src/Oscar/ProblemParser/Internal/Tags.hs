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

{- | Used as: 

* Text ⁞ ƮWithLineComments

    A representation of a set of Oscar 'Oscar.Problem.Problem's. The 
    formatting of such a Problem is described in "Oscar.Documentation".

* FilePath ⁞ ƮWithLineComments

    A file containing a Text ⁞ ƮWithLineComments.
-}
data ƮWithLineComments

{- | Used as: 

* Text ⁞ ƮWithoutLineComments

    The same as ƮWithLineComments, but with all line comments removed. See
    'Oscar.ProblemParser.stripLineComments'.
-}
data ƮWithoutLineComments

{- | Used as: 

* Text ⁞ ƮAfterNumberLabel

    Everything after the \"Problem #\".
-}
data ƮAfterNumberLabel

{- | Used as: 

* Text ⁞ ƮAfterNumber

    Everything after the \"Problem #\<number>\".
-}
data ƮAfterNumber

{- | Used as: 

* Text ⁞ ƮEndOfDescription

    Everything after the end of the description. There are two cases. If
    there is some (non-whitespace) description, this marks the first
    position after it (and, necessarily, prior to any sections). If the
    description is empty, this marks the same location as ƮAfterNumber.
-}
data ƮEndOfDescription

{- | Used as: 

* Text ⁞ ƮVariables

    The variables optionally defined for a reason, written as

    @
    variables = {var1,var2,...,varN}
    @
-}
data ƮVariables

{- | Used as: 

* Text ⁞ ƮSection ƮGivenPremise

    The premise section
-}
data ƮGivenPremise

{- | Used as: 

* Text ⁞ ƮSection ƮUltimateEpistemicInterest

    The interest section
-}
data ƮUltimateEpistemicInterest

{- | Used as: 

* Text ⁞ ƮSection (ƮReason direction defeasibility)

    A reason section, containing a number of reasons. For example,

    @
    FORWARDS PRIMA FACIE REASONS

        {A} ||=> B    justification = 1.0
        {B} ||=> C    justification = 1.0
    @

* Text ⁞ ƮReason direction defeasibility

    An element of a reason section. For example,

    @
    {A} ||=> B    justification = 1.0
    @
-}
data ƮReason (direction ∷ Direction) (defeasibility ∷ Defeasibility)

{- | The only types that make sense here are one of the three Ʈ...\'s above.
     
A (Text ⁞ ƮSection section) starts at the end of the section label
and continues to the end of that section, discarding trailing whitespace. 

__Example__     

* Snippet of a 'Problem'

    @
    ∘Given premises:∘∘↵
    ∘∘some premise text↵
    ∘∘↵
    ↵
    ∘∘Ultimate epistemic interests:↵
    @

* Text ⁞ ƮSection ƮGivenPremise is

    @
    ∘∘↵
    ∘∘some premise text
    @

Used as: (see above, e.g. ƮGivenPremise)
-}
data ƮSection section

-- | The orientation of a reason.
data Direction
    = Forwards   
      -- ^ For reasons that create new inferences
    | Backwards  
      -- ^ For reasons that create new interests
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | The defeasibility of a reason
data Defeasibility
    = PrimaFacie  
      -- ^ For reasons whose conclusions can be undercut or rebutted
    | Conclusive  
      -- ^ For reasons whose conclusions are logical consequences of their 
      ---  premises
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

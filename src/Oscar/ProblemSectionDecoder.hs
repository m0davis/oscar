{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemSectionDecoder where

import ClassyPrelude

import Oscar.ProblemSection             (Section)
import Oscar.Utilities                  (type (⁞))
import Oscar.ProblemLocation            (ƮSection)

-- | 
class (DecodedSection kind ~ decode) ⇒ InjectiveSection kind decode | decode → kind where
    -- | We would write @type DecodedSection kind = decode@, but GHC complains.
    type DecodedSection kind

    -- | decode (or parse) the text block in a section
    decodeSection ∷ Text ⁞ ƮSection kind → decode

-- | 
class HasSection s where
    -- | 
    section ∷ s → Section

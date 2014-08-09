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

class (DecodedSection kind ~ decode) ⇒ InjectiveSection kind decode | decode → kind where
    type DecodedSection kind :: *
    decodeSection ∷ Text ⁞ ƮSection kind → decode

data IsAKind kind ⇒ ƮSection kind

class HasSection s where
    section ∷ s → Section

class IsAKind k where

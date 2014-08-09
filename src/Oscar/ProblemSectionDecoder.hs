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

class InjectiveSection kind decode | decode → kind where
    decodeSection ∷ Text ⁞ ƮSection kind → decode

type family DecodedSection kind

data IsAKind kind ⇒ ƮSection kind

class HasSection s where
    section ∷ s → Section

class IsAKind k where

{-# OPTIONS --allow-unsolved-metas #-}

open import Oscar.Prelude

-- meta-class
open import Oscar.Class

-- classes
open import Oscar.Class.Smap

-- individual instances
open import Oscar.Class.Hmap.Transleftidentity
open import Oscar.Class.Reflexivity.Function
open import Oscar.Class.Transitivity.Function

-- instance bundles
open import Oscar.Property.Functor.SubstitunctionExtensionTerm

module Test.ProblemWithDerivation-2 where

postulate
  A : Set
  B : Set
  _~A~_ : A → A → Set
  _~B~_ : B → B → Set
  s1 : A → B
  f1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y

instance

  𝓢urjectivity1 : Smap.class _~A~_ _~B~_ s1 s1
  𝓢urjectivity1 .⋆ _ _ = f1

test : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test {x} {y} = smap -- FIXME confused by Oscar.Class.Hmap.Transleftidentity.Relprop'idFromTransleftidentity

{-# OPTIONS --allow-unsolved-metas #-}

open import Everything

module Test.ProblemWithSym where

module _ {a} {A : ¶ → Set a} where

  private AList = Descender⟨ A ⟩

  instance

    test-works : Transassociativity.class (flip AList) Proposequality transitivity
    test-works .⋆ f g h = symmetry (transassociativity h g f)

    test-fails : Transassociativity.class (flip AList) Proposequality transitivity
    test-fails .⋆ f g h = symmetry (transassociativity h g f) -- FIXME this was problematic when using a version of symmetry which did not include a negative argument in .⋆ It deserves explanation.

    test-hole : Transassociativity.class (flip AList) Proposequality transitivity
    test-hole .⋆ f g h = symmetry {!!}

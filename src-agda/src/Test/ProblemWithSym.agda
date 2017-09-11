{-# OPTIONS --allow-unsolved-metas #-}

open import Everything

module Test.ProblemWithSym where

module _ {a} {A : ¶ → Set a} where

  private AList = Descender⟨ A ⟩

  instance

    test-works : Transassociativity.class (flip AList) Proposequality transitivity
    test-works .⋆ f g h = symmetry (transassociativity h g f)

    test-fails : Transassociativity.class (flip AList) Proposequality transitivity
    test-fails .⋆ f g h = Sym.[] (transassociativity h g f)

    test-hole : Transassociativity.class (flip AList) Proposequality transitivity
    test-hole .⋆ f g h = Sym.[] {!!}

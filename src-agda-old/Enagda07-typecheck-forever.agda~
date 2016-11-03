module _ where

record Wrappable (F : Set → Set) : Set₁ where
  field
    wrap : ∀ {X} → X → F X
open Wrappable {{...}} public

instance
  wrappableComp : ∀ {F G} → Wrappable F → Wrappable G → Wrappable (λ X → F (G X))
  wrappableComp _ _ = record { wrap = λ x → wrap (wrap x) }

{-
record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _<*>_
  field
    pure : ∀ {X} → X → F X
    _<*>_ : ∀ {S T} → F (S → T) → F S → F T
open Applicative {{...}} public

instance
  applicativeComp : ∀ {F G} → Applicative F → Applicative G → Applicative (λ X → F (G X))
  applicativeComp _ _ = record { pure = λ x → pure (pure x) ; _<*>_ = {!!} }
-}

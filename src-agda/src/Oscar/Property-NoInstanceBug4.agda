
module Oscar.Property-NoInstanceBug4 where

Extension : ∀ {A : Set} (P : A → Set) → A → A → Set
Extension P m n = P m → P n

ExtensionProperty : ∀ {A : Set} (P : A → Set) → A → Set₁
ExtensionProperty P x = ∀ {v} → Extension P x v → Set

record Surjectivity
    {A : Set}
    (P : A → Set)
    (Q : A → Set₁)
  : Set₁ where
  field
    surjectivity : ∀ {x y} → Extension P x y → Q x → Q y

open Surjectivity ⦃ … ⦄ public

open import Oscar.Prelude using (_$_)

module TestPropertyFunctions
  {A : Set}
  {P : A → Set}
  ⦃ theInstance : Surjectivity P (ExtensionProperty P) ⦄
  where

  works1 : ∀ {x y} → Extension P x y → ExtensionProperty P x → ExtensionProperty P y
  works1 f = surjectivity f

  works2 : ∀ {x y} → Extension P x y → ExtensionProperty P x → ExtensionProperty P y
  works2 f P = works1 f P

  works3 : ∀ {x y} → Extension P x y → ExtensionProperty P x → ExtensionProperty P y
  works3 f P = surjectivity ⦃ theInstance ⦄ f P

  --fails : ∀ {x y} → Extension P x y → ExtensionProperty P x → ExtensionProperty P y
  --fails f P = surjectivity f P

module TestPropertyFunctions2
  {A : Set}
  {P : A → Set}
  ⦃ theInstance : Surjectivity P (λ x → ∀ {v} → Extension P x v → Set) ⦄
  where

  works1 : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  works1 f = surjectivity f

  works2 : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  works2 f P = works1 f P

  works3 : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  works3 f P = surjectivity ⦃ theInstance ⦄ f P

  --fails : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  --fails f P = surjectivity f P

module TestPropertyFunctions3
  {A : Set}
  {P : A → Set}
  ⦃ theInstance : Surjectivity P (λ x → ∀ {v} → Extension P x v → Set) ⦄
  ⦃ theInstance' : Surjectivity P (λ x → ∀ v → Extension P x v → Set) ⦄
  where

  works1 : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  works1 f = surjectivity f

  works2 : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  works2 f P = works1 f P

  works3 : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  works3 f P = surjectivity ⦃ theInstance ⦄ f P

  fails : ∀ {x y} → Extension P x y → (∀ {v} → Extension P x v → Set) → ∀ {v} → Extension P y v → Set
  fails f P {v} = (λ {w} → surjectivity ⦃ theInstance ⦄ f P {w}) {v} -- λ {w} → surjectivity f P w

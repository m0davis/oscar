
open import Oscar.Prelude

module Oscar.Class.Fmap where

module _ where
  open import Oscar.Data.Proposequality
  open import Oscar.Class.IsFunctor
  open import Oscar.Class.Reflexivity
  import Oscar.Class.Reflexivity.Function
  open import Oscar.Class.Surjidentity

  record Fmap {𝔬₁ 𝔬₂} (𝓕 : Ø 𝔬₁ → Ø 𝔬₂) : Ø (↑̂ (↑̂ 𝔬₁ ∙̂ 𝔬₂)) where
    constructor ∁
    field
      fmap : ∀ {𝔄 𝔅} → (𝔄 → 𝔅) → 𝓕 𝔄 → 𝓕 𝔅 -- level-polymorphic functors cannot be represented by `Functor` or any other type in universe < ω.
      ⦃ isFunctor ⦄ : IsFunctor
                         Function⟦ 𝔬₁ ⟧
                           Proposextensequality ε (flip _∘′_)
                         (MFunction 𝓕)
                           Proposextensequality ε (flip _∘′_)
                         fmap
    fmap-id-law : ∀ {𝔄} → fmap ¡[ 𝔄 ] ≡̇ ¡
    fmap-id-law = surjidentity

  open Fmap ⦃ … ⦄ public using (fmap)

-- level-polymorphic functor
module _
  (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
  𝔬₁ 𝔬₂
  where
  𝓯map = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} (f : 𝔒₁ → 𝔒₂) → 𝔉 𝔒₁ → 𝔉 𝔒₂
  record 𝓕map : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where field fmap′ : 𝓯map
open 𝓕map ⦃ … ⦄ public

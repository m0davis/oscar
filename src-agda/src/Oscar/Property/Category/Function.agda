
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.IsPrecategory
open import Oscar.Class.IsCategory
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transassociativity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.Transitivity
open import Oscar.Class.Precategory
open import Oscar.Class.Category
open import Oscar.Property.Setoid.Proposequality
open import Oscar.Property.Setoid.Proposextensequality
open import Oscar.Data.Proposequality
import Oscar.Class.Reflexivity.Function
import Oscar.Class.Transextensionality.Proposequality

module Oscar.Property.Category.Function where

module _ where

module _ {𝔬 : Ł} where

  instance

    TransitivityFunction : Transitivity.class Function⟦ 𝔬 ⟧
    TransitivityFunction .⋆ f g = g ∘ f

module _ {𝔬 : Ł} where

  instance

    HasEquivalenceFunction : ∀ {A B : Ø 𝔬} → HasEquivalence (Function⟦ 𝔬 ⟧ A B) 𝔬
    HasEquivalenceFunction .⋆ = _≡̇_
    HasEquivalenceFunction .Rℭlass.⋆⋆ = !

  instance

    TransassociativityFunction : Transassociativity.class Function⟦ 𝔬 ⟧ _≡̇_ transitivity
    TransassociativityFunction .⋆ _ _ _ _ = ∅

  instance

    𝓣ransextensionalityFunctionProposextensequality : Transextensionality.class Function⟦ 𝔬 ⟧ Proposextensequality transitivity
    𝓣ransextensionalityFunctionProposextensequality .⋆ {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

  instance

    IsPrecategoryFunction : IsPrecategory Function⟦ 𝔬 ⟧ _≡̇_ transitivity
    IsPrecategoryFunction = ∁

  instance

    TransleftidentityFunction : Transleftidentity.class Function⟦ 𝔬 ⟧ _≡̇_ ε transitivity
    TransleftidentityFunction .⋆ _ = ∅

    TransrightidentityFunction : Transrightidentity.class Function⟦ 𝔬 ⟧ _≡̇_ ε transitivity
    TransrightidentityFunction .⋆ _ = ∅

  instance

    IsCategoryFunction : IsCategory Function⟦ 𝔬 ⟧ _≡̇_ ε transitivity
    IsCategoryFunction = ∁

  PrecategoryFunction : Precategory _ _ _
  PrecategoryFunction = ∁ Function⟦ 𝔬 ⟧ Proposextensequality transitivity

  CategoryFunction : Category _ _ _
  CategoryFunction = ∁ Function⟦ 𝔬 ⟧ Proposextensequality ε transitivity

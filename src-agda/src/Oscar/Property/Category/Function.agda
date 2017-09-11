
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
open import Oscar.Property.Setoid.Proposequality
open import Oscar.Property.Setoid.Proposextensequality
open import Oscar.Data.Proposequality
import Oscar.Class.Reflexivity.Function
import Oscar.Class.Transextensionality.Proposequality
import Oscar.Property.Category.ExtensionProposextensequality

module Oscar.Property.Category.Function where

module _ where

module _ {𝔬 : Ł} where

  instance

    HasEquivalenceFunction : ∀ {A B : Ø 𝔬} → HasEquivalence (Function⟦ 𝔬 ⟧ A B) 𝔬
    HasEquivalenceFunction .⋆ = _≡̇_
    HasEquivalenceFunction .Rℭlass.⋆⋆ = !

  instance

    TransassociativityFunction : Transassociativity.class Function⟦ 𝔬 ⟧ _≡̇_ transitivity
    TransassociativityFunction .⋆ _ _ _ _ = ∅

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

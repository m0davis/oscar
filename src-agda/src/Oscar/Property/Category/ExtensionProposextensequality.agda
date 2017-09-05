
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity
open import Oscar.Class.IsEquivalence
open import Oscar.Class.Setoid
open import Oscar.Class.Transassociativity
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.[IsExtensionB]
open import Oscar.Class.HasEquivalence
open import Oscar.Class.IsPrecategory
open import Oscar.Class.IsCategory
open import Oscar.Class.Precategory
open import Oscar.Class.Category
open import Oscar.Data.Proposequality
import Oscar.Property.Setoid.Proposextensequality
import Oscar.Data.Constraint

module Oscar.Property.Category.ExtensionProposextensequality where

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    𝓡eflexivityExtension : Refl.⟦ Extension B ⟧
    𝓡eflexivityExtension .⋆ = ¡

    𝓣ransitivityExtension : Transitivity.class (Extension B)
    𝓣ransitivityExtension {x∼y = f} {g} .⋆ = g ∘ f

    [𝓣ransassociativity]ExtensionProposextensequality : [𝓣ransassociativity] (Extension B) Proposextensequality
    [𝓣ransassociativity]ExtensionProposextensequality = ∁

    𝓣ransassociativityExtensionProposextensequality : 𝓣ransassociativity (Extension B) Proposextensequality
    𝓣ransassociativityExtensionProposextensequality .𝓣ransassociativity.transassociativity _ _ _ _ = !

    𝓣ransextensionalityExtensionProposextensequality : Transextensionality.class (Extension B) Proposextensequality
    𝓣ransextensionalityExtensionProposextensequality .⋆ {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

    [𝓣ransleftidentity]ExtensionProposextensequality : [𝓣ransleftidentity] (Extension B) Proposextensequality
    [𝓣ransleftidentity]ExtensionProposextensequality = ∁

    𝓣ransleftidentityExtensionProposextensequality : 𝓣ransleftidentity (Extension B) Proposextensequality
    𝓣ransleftidentityExtensionProposextensequality .𝓣ransleftidentity.transleftidentity _ = !

    [𝓣ransrightidentity]ExtensionProposextensequality : [𝓣ransrightidentity] (Extension B) Proposextensequality
    [𝓣ransrightidentity]ExtensionProposextensequality = ∁

    𝓣ransrightidentityExtensionProposextensequality : 𝓣ransrightidentity (Extension B) Proposextensequality
    𝓣ransrightidentityExtensionProposextensequality .𝓣ransrightidentity.transrightidentity _ = !

    HasEquivalenceExtension : ∀ {x y : A} ⦃ _ : [IsExtensionB] B ⦄ → HasEquivalence (Extension B x y) _
    HasEquivalenceExtension = ∁ Proposextensequality

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    IsPrecategoryExtension : IsPrecategory (Extension B) Proposextensequality
    IsPrecategoryExtension = ∁

    IsCategoryExtension : IsCategory (Extension B) Proposextensequality
    IsCategoryExtension = ∁

module _
  {a} {A : Ø a} {b} (B : A → Ø b)
  where

  PrecategoryExtension : Precategory _ _ _
  PrecategoryExtension = ∁ (Extension B) Proposextensequality

  CategoryExtension : Category _ _ _
  CategoryExtension = ∁ (Extension B) Proposextensequality

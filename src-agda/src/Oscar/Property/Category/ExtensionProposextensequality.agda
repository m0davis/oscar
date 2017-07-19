
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Property.Setoid.Proposextensequality

module Oscar.Property.Category.ExtensionProposextensequality where

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    𝓡eflexivityExtension : 𝓡eflexivity (Extension B)
    𝓡eflexivity.reflexivity 𝓡eflexivityExtension = ¡

    𝓣ransitivityExtension : 𝓣ransitivity (Extension B)
    𝓣ransitivity.transitivity 𝓣ransitivityExtension f g = g ∘ f

    [𝓣ransassociativity]ExtensionProposextensequality : [𝓣ransassociativity] (Extension B) Proposextensequality
    [𝓣ransassociativity]ExtensionProposextensequality = ∁

    𝓣ransassociativityExtensionProposextensequality : 𝓣ransassociativity (Extension B) Proposextensequality
    𝓣ransassociativityExtensionProposextensequality .𝓣ransassociativity.transassociativity _ _ _ _ = !

    [𝓣ransextensionality]ExtensionProposextensequality : [𝓣ransextensionality] (Extension B) Proposextensequality
    [𝓣ransextensionality]ExtensionProposextensequality = ∁

    𝓣ransextensionalityExtensionProposextensequality : 𝓣ransextensionality (Extension B) Proposextensequality
    𝓣ransextensionalityExtensionProposextensequality .𝓣ransextensionality.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

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

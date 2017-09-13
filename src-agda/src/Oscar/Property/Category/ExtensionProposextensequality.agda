
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
import Oscar.Class.Reflexivity.Function

module Oscar.Property.Category.ExtensionProposextensequality where

open import Oscar.Property.Category.Function public

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    𝓣ransassociativityExtensionProposextensequality : Transassociativity.class (Extension B) Proposextensequality transitivity
    𝓣ransassociativityExtensionProposextensequality .⋆ _ _ _ _ = !

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    𝓣ransextensionalityExtensionProposextensequality : Transextensionality.class (Extension B) Proposextensequality transitivity
    𝓣ransextensionalityExtensionProposextensequality .⋆ {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    𝓣ransleftidentityExtensionProposextensequality : Transleftidentity.class (Extension B) Proposextensequality ε transitivity
    𝓣ransleftidentityExtensionProposextensequality .⋆ _ = !

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    𝓣ransrightidentityExtensionProposextensequality : Transrightidentity.class (Extension B) Proposextensequality ε transitivity
    𝓣ransrightidentityExtensionProposextensequality .⋆ _ = !

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    HasEquivalenceExtension : ∀ {x y : A} ⦃ _ : [IsExtensionB] B ⦄ → HasEquivalence (Extension B x y) _
    HasEquivalenceExtension = ∁ Proposextensequality

module _
  {a} {A : Ø a} {b} {B : A → Ø b}
  where

  instance

    IsPrecategoryExtension : IsPrecategory (Extension B) Proposextensequality transitivity
    IsPrecategoryExtension = ∁

    IsCategoryExtension : IsCategory (Extension B) Proposextensequality ε transitivity
    IsCategoryExtension = ∁

module _
  {a} {A : Ø a} {b} (B : A → Ø b)
  where

  PrecategoryExtension : Precategory _ _ _
  PrecategoryExtension = ∁ (Extension B) Proposextensequality transitivity

  CategoryExtension : Category _ _ _
  CategoryExtension = ∁ (Extension B) Proposextensequality ε transitivity

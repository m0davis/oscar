
module Oscar.Data.Fin.AlphaConversion.instances.ExtensionalEquality where

open import Oscar.Data.Fin.Core
open import Oscar.Data.Fin.AlphaConversion
open import Oscar.Data.Equality
open import Oscar.Class.ExtensionalEquality

instance ExtensionalEquality↬ : ∀ {m n} → ExtensionalEquality (Fin m) (λ _ → Fin n)
ExtensionalEquality._≐_ ExtensionalEquality↬ f g = ∀ x → f x ≡ g x

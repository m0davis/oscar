
module Oscar.Data.Term.ThickAndThin.internal {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Class.AlphaConversion
import Oscar.Class.ThickAndThin as ⋆
open import Oscar.Data.Term FunctionName
open import Oscar.Data.Term.Injectivity FunctionName
open import Oscar.Data.Term.AlphaConversion FunctionName
open import Oscar.Data.Equality
open import Oscar.Data.Equality.properties
open import Oscar.Data.Fin
open import Oscar.Data.Fin.ThickAndThin
open import Oscar.Data.Nat
open import Oscar.Data.Vec
open import Oscar.Data.Vec.Injectivity
open import Oscar.Function

private

  Fin⋆thin = ⋆.ThickAndThin.thin ThickAndThinFin
  Fin⋆thick = ⋆.ThickAndThin.thick ThickAndThinFin

thin : ∀ {m} → Fin (suc m) → Term m → Term (suc m)
thin = _◂_ ∘ Fin⋆thin

thins : ∀ {m} → Fin (suc m) → ∀ {N} → Vec (Term m) N → Vec (Term (suc m)) N
thins y = Fin⋆thin y ◂_ -- TODO: make point-free

mutual

  thin-injective : ∀ {m} (y : Fin (suc m)) {τ₁ τ₂ : Term m} → thin y τ₁ ≡ thin y τ₂ → τ₁ ≡ τ₂
  thin-injective y {i _} {i _} eq
    rewrite ⋆.thin-injective y (Term-i-inj eq)
    = refl
  thin-injective y {_ fork _} {_ fork _} eq
    rewrite thin-injective y (Term-forkLeft-inj eq)
          | thin-injective y (Term-forkRight-inj eq)
    = refl
  thin-injective _ {leaf} {leaf} _ = refl
  thin-injective y {function _ _} {function _ _} eq rewrite Term-functionName-inj eq with Term-functionArity-inj eq
  … | refl with Term-functionTerms-inj eq
  … | eq' rewrite (thins-injective y eq') = refl
  thin-injective _ {i _} {leaf} ()
  thin-injective _ {i _} {_ fork _} ()
  thin-injective _ {i _} {function _ _} ()
  thin-injective _ {leaf} {i _} ()
  thin-injective _ {leaf} {_ fork _} ()
  thin-injective _ {leaf} {function _ _} ()
  thin-injective _ {_ fork _} {i _} ()
  thin-injective _ {_ fork _} {leaf} ()
  thin-injective _ {_ fork _} {function _ _} ()
  thin-injective _ {function _ _} {i _} ()
  thin-injective _ {function _ _} {leaf} ()
  thin-injective _ {function _ _} {_ fork _} ()

  thins-injective : ∀ {m} (f : Fin (suc m)) → ∀ {N} {τs₁ τs₂ : Vec (Term m) N} → thins f τs₁ ≡ thins f τs₂ → τs₁ ≡ τs₂
  thins-injective y {_} {[]} {[]} x₁ = refl
  thins-injective y {_} {_ ∷ _} {_ ∷ _} eq
    rewrite thin-injective y (Vec-head-inj eq)
          | thins-injective y (Vec-tail-inj eq)
    = refl

thick : ∀ {m} → Term (suc m) → Fin m → Term m
thick τ = flip _◂_ τ ∘ flip Fin⋆thick

thicks : ∀ {m N} → Terms N (suc m) → Fin m → Terms N m
thicks τ = flip _◂_ τ ∘ flip Fin⋆thick

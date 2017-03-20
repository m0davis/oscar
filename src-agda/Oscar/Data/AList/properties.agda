
module Oscar.Data.AList.properties {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Category.Category
open import Oscar.Category.Functor
open import Oscar.Category.Morphism
open import Oscar.Category.Semigroupoid
open import Oscar.Category.Semifunctor
open import Oscar.Category.Setoid
open import Oscar.Class.ThickAndThin
open import Oscar.Data.AList FunctionName
open import Oscar.Data.Equality
open import Oscar.Data.Equality.properties
open import Oscar.Data.Fin
open import Oscar.Data.Fin.ThickAndThin
open import Oscar.Data.Maybe
open import Oscar.Data.Nat
open import Oscar.Data.Product
open import Oscar.Data.Term FunctionName
import      Oscar.Data.Term.internal.SubstituteAndSubstitution FunctionName as S
open import Oscar.Data.Term.ThickAndThin FunctionName
open import Oscar.Function

module 𝔊₂ = Category S.𝔾₁
module 𝔉◃ = Functor S.𝔽◂

𝕞₁ = ⇧ AList

module 𝔐₁ = Morphism 𝕞₁

private

  _∙_ : ∀ {m n} → m 𝔐₁.↦ n → ∀ {l} → l 𝔐₁.↦ m → l 𝔐₁.↦ n
  ρ ∙ anil = ρ
  ρ ∙ (σ asnoc t' / x) = (ρ ∙ σ) asnoc t' / x

  ∙-associativity : ∀ {l m} (ρ : l 𝔐₁.↦ m) {n} (σ : n 𝔐₁.↦ _) {o} (τ : o 𝔐₁.↦ _) → (ρ ∙ σ) ∙ τ ≡ ρ ∙ (σ ∙ τ)
  ∙-associativity ρ σ anil = refl
  ∙-associativity ρ σ (τ asnoc t / x) = cong (λ s → s asnoc t / x) (∙-associativity ρ σ τ)

instance

  IsSemigroupoid𝕞₁∙ : IsSemigroupoid 𝕞₁ _∙_
  IsSemigroupoid.extensionality IsSemigroupoid𝕞₁∙ f₁≡f₂ g₁≡g₂ = cong₂ (λ ‵ → _∙_ ‵) g₁≡g₂ f₁≡f₂
  IsSemigroupoid.associativity IsSemigroupoid𝕞₁∙ f g h = ∙-associativity h g f

𝕘₁ : Semigroupoid _ _ _
𝕘₁ = 𝕞₁ , _∙_

private

  ε : ∀ {n} → n 𝔐₁.↦ n
  ε = anil

  ∙-left-identity : ∀ {m n} (σ : AList m n) → ε ∙ σ ≡ σ
  ∙-left-identity anil = refl
  ∙-left-identity (σ asnoc t' / x) = cong (λ σ → σ asnoc t' / x) (∙-left-identity σ)

instance

  IsCategory𝕘₁ε : IsCategory 𝕘₁ ε
  IsCategory.left-identity IsCategory𝕘₁ε = ∙-left-identity
  IsCategory.right-identity IsCategory𝕘₁ε _ = refl

𝔾₁ : Category _ _ _
𝔾₁ = 𝕘₁ , ε

𝕞₂ = 𝔊₂.𝔐
module 𝔐₂ = Morphism 𝕞₂

private

  sub : ∀ {m n} → m 𝔐₁.↦ n → m 𝔊₂.↦ n
  sub anil = i
  sub (σ asnoc t' / x) =  sub σ 𝔊₂.∙ (t' for x)

  fact1 : ∀ {l m n} (ρ : AList m n) (σ : AList l m) → sub (ρ ∙ σ) ≡̇ (sub ρ 𝔊₂.∙ sub σ)
  fact1 ρ anil v = refl
  fact1 {suc l} {m} {n} r (s asnoc t' / x) v = trans hyp-on-terms ◃-assoc
    where
      t = (t' for x) v
      hyp-on-terms = 𝔉◃.extensionality (fact1 r s) t
      ◃-assoc = 𝔉◃.distributivity (sub s) (sub r) t

𝕘₁,₂ : Semigroupoids _ _ _ _ _ _
𝕘₁,₂ = 𝕘₁ , 𝔊₂.semigroupoid

instance

  IsSemifunctorSub∙◇ : IsSemifunctor 𝕘₁,₂ sub
  IsSemifunctor.extensionality IsSemifunctorSub∙◇ refl _ = refl
  IsSemifunctor.distributivity IsSemifunctorSub∙◇ f g x = fact1 g f x

semifunctorSub∙◇ : Semifunctor _ _ _ _ _ _
semifunctorSub∙◇ = 𝕘₁,₂ , sub

instance

  IsFunctor𝔽 : IsFunctor (𝔾₁ , S.𝔾₁) sub
  IsFunctor.identity IsFunctor𝔽 _ _ = refl

𝔽 : Functor _ _ _ _ _ _
𝔽 = (𝔾₁ , S.𝔾₁) , sub

--   fact1 : ∀ {l m n} (ρ : AList m n) (σ : AList l m) → sub (ρ ∙ σ) ≡̇ (sub ρ ◇ sub σ)
--   fact1 ρ anil v = refl
--   fact1 {suc l} {m} {n} r (s asnoc t' / x) v = trans hyp-on-terms ◃-assoc
--     where
--       t = (t' for x) v
--       hyp-on-terms = ◃-extensionality (fact1 r s) t
--       ◃-assoc = ◃-associativity (sub s) (sub r) t

-- _∃asnoc_/_ : ∀ {m} (a : ∃ (AList m)) (t' : Term m) (x : Fin (suc m))
--   → ∃ (AList (suc m))
-- (n , σ) ∃asnoc t' / x = n , σ asnoc t' / x

-- flexFlex : ∀ {m} (x y : Fin m) → ∃ (AList m)
-- flexFlex {suc m} x y with check x y
-- ...              | just y' = m , anil asnoc i y' / x
-- ...              | nothing = suc m , anil
-- flexFlex {zero} () _

-- flexRigid : ∀ {m} (x : Fin m) (t : Term m) → Maybe (∃(AList m))
-- flexRigid {suc m} x t with check x t
-- ...                   | just t' = just (m , anil asnoc t' / x)
-- ...                   | nothing = nothing
-- flexRigid {zero} () _

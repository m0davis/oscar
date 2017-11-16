open import Relation.Binary using (IsDecEquivalence)
open import Agda.Builtin.Equality

module UnifyMguCorrectG (FunctionName : Set) ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName}) ⦄ (PredicateName VariableName : Set) where


open import UnifyTermF FunctionName
open import UnifyMguF FunctionName
open import UnifyMguCorrectF FunctionName

open import Data.Nat
open import Data.Vec
open import Function
open import Data.Fin renaming (thin to thinF; thick to thickF)

data Formula (n : ℕ) : Set
 where
  atomic : PredicateName → ∀ {t} → Vec (Term n) t → Formula n
  logical : Formula n →
            Formula n →
            Formula n
  quantified : Formula (suc n) → Formula n

open import Relation.Binary.PropositionalEquality

instance ThinFormula : Thin Formula
Thin.thin ThinFormula x (atomic x₁ x₂) = atomic x₁ (thin x x₂)
Thin.thin ThinFormula x (logical x₁ x₂) = logical (thin x x₁) (thin x x₂)
Thin.thin ThinFormula x (quantified x₁) = quantified (thin zero x₁)
Thin.thinfact1 ThinFormula f {atomic pn1 ts1} {atomic pn2 ts2} r = {!!}
Thin.thinfact1 ThinFormula f {atomic x x₁} {logical y y₁} ()
Thin.thinfact1 ThinFormula f {atomic x x₁} {quantified y} ()
Thin.thinfact1 ThinFormula f {logical x x₁} {atomic x₂ x₃} ()
Thin.thinfact1 ThinFormula f {logical x x₁} {logical y y₁} x₂ = {!!}
Thin.thinfact1 ThinFormula f {logical x x₁} {quantified y} ()
Thin.thinfact1 ThinFormula f {quantified x} {atomic x₁ x₂} ()
Thin.thinfact1 ThinFormula f {quantified x} {logical y y₁} ()
Thin.thinfact1 ThinFormula f {quantified x} {quantified y} x₁ = {!!}

foo~ : ∀ {m₁ n₁} →
       (Fin m₁ → Term n₁) →
       Fin (suc m₁) → Term (suc n₁)
foo~ f = (λ { zero → i zero ; (suc x) → thin zero (f x)})

foo~i≐i : ∀ {m} → foo~ {m} i ≐ i
foo~i≐i zero = refl
foo~i≐i (suc x) = refl

instance SubstitutionFormula : Substitution Formula
Substitution._◃_ SubstitutionFormula = _◃′_ where
  _◃′_ : ∀ {m n} -> (f : m ~> n) -> Formula m -> Formula n
  f ◃′ atomic 𝑃 τs = atomic 𝑃 (f ◃ τs)
  f ◃′ logical φ₁ φ₂ = logical (f ◃ φ₁) (f ◃ φ₂)
  f ◃′ quantified φ = quantified (foo~ f ◃ φ)

instance SubstitutionExtensionalityFormula : SubstitutionExtensionality Formula
SubstitutionExtensionality.◃ext SubstitutionExtensionalityFormula x (atomic x₁ x₂) = cong (atomic x₁) (◃ext x x₂)
SubstitutionExtensionality.◃ext SubstitutionExtensionalityFormula x (logical t t₁) = cong₂ logical (◃ext x t) (◃ext x t₁)
SubstitutionExtensionality.◃ext SubstitutionExtensionalityFormula x (quantified t) = cong quantified ((◃ext (λ { zero → refl ; (suc x₁) → cong (mapTerm suc) (x x₁)}) t)) --

instance SubFact1Formula : Sub.Fact1 Formula
Sub.Fact1.fact1 SubFact1Formula (atomic x x₁) = cong (atomic x) (Sub.fact1 x₁)
Sub.Fact1.fact1 SubFact1Formula (logical t t₁) = cong₂ logical (Sub.fact1 t) (Sub.fact1 t₁)
Sub.Fact1.fact1 SubFact1Formula {n} (quantified φ) = cong quantified (trans (◃ext {Formula} {_} {_} {foo~ {_} i} {i} (foo~i≐i {_}) φ) (Sub.fact1 φ))

Unifies⋆F : ∀ {m} (s t : Formula m) -> Property⋆ m
Unifies⋆F s t f = f ◃ s ≡ f ◃ t

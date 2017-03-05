
module Oscar.Data.Term.instances.ThickAndThin {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Term.Injectivity FunctionName
open import Oscar.Data.Term.AlphaConversion FunctionName
open import Oscar.Data.Fin
--open import Oscar.Data.Fin.Core
--open import Oscar.Data.Fin.instances.ThickAndThin
open import Oscar.Data.Nat.Core
open import Oscar.Data.Vec.Core
open import Oscar.Data.Equality
open import Oscar.Class.ThickAndThin
open import Oscar.Function

private

  thin-Term : ∀ {n} → Fin (suc n) → Term n → Term (suc n)
  thin-Term = _◂_ ∘ thin

  thin-Terms : ∀ {n N} → Fin (suc n) → Vec (Term n) N → Vec (Term (suc n)) N
  thin-Terms = _◂s_ ∘ thin

  mutual

    thin-injective-Term : ∀ {n} (z : Fin (suc n)) {x y : Term n} → thin-Term z x ≡ thin-Term z y → x ≡ y
    thin-injective-Term x₁ {i x} {i x₃} x₂ = {!!} -- cong i (thinfact1 x₁ (term-i-inj x₂))
    thin-injective-Term x₁ {i x} {leaf} ()
    thin-injective-Term x₁ {i x} {y fork y₁} ()
    thin-injective-Term x₁ {i x} {function x₂ x₃} ()
    thin-injective-Term x₁ {leaf} {i x} ()
    thin-injective-Term x₁ {leaf} {leaf} x₂ = refl
    thin-injective-Term x₁ {leaf} {y fork y₁} ()
    thin-injective-Term x₁ {leaf} {function x x₂} ()
    thin-injective-Term x₁ {x fork x₂} {i x₃} ()
    thin-injective-Term x₁ {x fork x₂} {leaf} ()
    thin-injective-Term x₁ {x fork x₂} {y fork y₁} x₃ = {!!} -- cong₂ _fork_ (thin-injective-Term x₁ (term-fork-l-inj x₃)) ((thin-injective-Term x₁ (term-fork-r-inj x₃)))
    thin-injective-Term x₁ {x fork x₂} {function x₃ x₄} ()
    thin-injective-Term x₁ {function x x₂} {i x₃} ()
    thin-injective-Term x₁ {function x x₂} {leaf} ()
    thin-injective-Term x₁ {function x x₂} {y fork y₁} ()
    thin-injective-Term x₁ {function f1 {n} ts1} {function f2 ts2} r rewrite Term-function-inj-FunctionName r with Term-function-inj-VecSize r
    thin-injective-Term x₁ {function f1 {n} ts1} {function f2 ts2} r | refl with Term-function-inj-Vector r
    thin-injective-Term {m} x₁ {function f1 {n} ts1} {function f2 {.n} ts2} r | refl | w = cong (function f2) (((thin-injective-Terms x₁ w)))

    thin-injective-Terms : ∀ {N} {n} (f : Fin (suc n)) → {x y : Vec (Term n) N} → thin-Terms f x ≡ thin-Terms f y → x ≡ y
    thin-injective-Terms {.0} f {[]} {[]} x₁ = refl
    thin-injective-Terms {.(suc _)} f {x ∷ x₁} {x₂ ∷ y} x₃ = {!!} -- cong₂ _∷_ (thin-injective-Term f (cong Data.Vec.head x₃)) (thin-injective-Terms f (cong Data.Vec.tail x₃))

instance ThickAndThinTerm : ThickAndThin Term
ThickAndThin.thin ThickAndThinTerm = thin-Term
ThickAndThin.thick ThickAndThinTerm x = {!!} -- flip mapTerm x ∘ flip thick
ThickAndThin.thin-injective ThickAndThinTerm = {!!}
ThickAndThin.thick∘thin=id ThickAndThinTerm = {!!}
ThickAndThin.check ThickAndThinTerm = {!!}
ThickAndThin.thin-check-id ThickAndThinTerm = {!!}

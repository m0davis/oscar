
module Oscar.Data.Term.instances.TermSubstitution {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Term.Substitution FunctionName
open import Oscar.Data.Term.Substitution.Core.bootstrap FunctionName using (_◃Term_; _◃VecTerm_)
open import Oscar.Class.TermSubstitution FunctionName

open import Oscar.Data.Equality
open import Oscar.Data.Vec.Core
open import Oscar.Function

private

  mutual

    ◃Term-identity : ∀ {n} → (t : Term n) → i ◃Term t ≡ t
    ◃Term-identity (i x) = refl
    ◃Term-identity leaf = refl
    ◃Term-identity (s fork t) = cong₂ _fork_ (◃Term-identity s) (◃Term-identity t)
    ◃Term-identity (function fn ts) = cong (function fn) (◃VecTerm-identity ts)

    ◃VecTerm-identity : ∀ {N n} → (t : Vec (Term n) N) → i ◃VecTerm t ≡ t
    ◃VecTerm-identity [] = refl
    ◃VecTerm-identity (t ∷ ts) = cong₂ _∷_ (◃Term-identity t) (◃VecTerm-identity ts)

  mutual

    ◃Term-extentionality : ∀ {m n} {f g : m ⊸ n} → f ≐ g → ∀ t → f ◃Term t ≡ g ◃Term t
    ◃Term-extentionality p (i x) = p x
    ◃Term-extentionality p leaf = refl
    ◃Term-extentionality p (s fork t) = cong₂ _fork_ (◃Term-extentionality p s) (◃Term-extentionality p t)
    ◃Term-extentionality p (function fn ts) = cong (function fn) (◃VecTerm-extentionality p ts)

    ◃VecTerm-extentionality : ∀ {m n} {f g : m ⊸ n} {N} → f ≐ g → (t : Vec (Term m) N) → f ◃VecTerm t ≡ g ◃VecTerm t
    ◃VecTerm-extentionality p [] = refl
    ◃VecTerm-extentionality p (t ∷ ts) = cong₂ _∷_ (◃Term-extentionality p t) (◃VecTerm-extentionality p ts)

  mutual

    ◃Term-associativity : ∀ {l m n} → {f : m ⊸ n} {g : _} (t : Term l) → (f ◇ g) ◃Term t ≡ f ◃Term (g ◃Term t)
    ◃Term-associativity (i x) = refl
    ◃Term-associativity leaf = refl
    ◃Term-associativity (s fork t) = cong₂ _fork_ (◃Term-associativity s) (◃Term-associativity t)
    ◃Term-associativity {f = f} {g = g} (function fn ts) = cong (function fn) (◃VecTerm-associativity {f = f} {g = g} ts)

    ◃VecTerm-associativity : ∀ {l m n} → {f : m ⊸ n} {g : _} → ∀ {N} (t : Vec (Term l) N) → (f ◇ g) ◃VecTerm t ≡ f ◃VecTerm (g ◃VecTerm t)
    ◃VecTerm-associativity [] = refl
    ◃VecTerm-associativity (t ∷ ts) = cong₂ _∷_ (◃Term-associativity t) (◃VecTerm-associativity ts)

mutual

  instance SubstitutionTerm : Substitution Term
  Substitution._◃_ SubstitutionTerm = _◃Term_
  Substitution.◃-extentionality SubstitutionTerm = ◃Term-extentionality
  Substitution.◃-identity SubstitutionTerm = ◃Term-identity
  Substitution.◃-associativity SubstitutionTerm = ◃Term-associativity

  instance SubstitutionVecTerm : ∀ {N} → Substitution (flip Vec N ∘ Term )
  Substitution._◃_ SubstitutionVecTerm = _◃VecTerm_
  Substitution.◃-extentionality SubstitutionVecTerm = ◃VecTerm-extentionality
  Substitution.◃-identity SubstitutionVecTerm = ◃VecTerm-identity
  Substitution.◃-associativity SubstitutionVecTerm = ◃VecTerm-associativity


data HasUniqueValues (A : Set) : List A → Set
 where
  [] : HasUniqueValues A []
  _∷_ : {x : A} → {xs : List A} → x ∉ xs → (uxs : HasUniqueValues A xs) → HasUniqueValues A (x ∷ xs)

record AList (A : Set) (B : Set) : Set
 where
  field
    domain : List A
    uniquedomain : HasUniqueValues A domain
    range : ∀ {x : A} → x ∈ domain → B

open AList

record Unifiable (F : Set) (T : Set) (U₁ U₂ : Set) (σ : (T → F) → F → F) : Set₁ where
  field
    _≈u≈_ : (φ₁ φ₂ : F) → Set
    unifier : (φ₁ φ₂ : F) → φ₁ ≈u≈ φ₂ → (F → F) × (F → F)
    unifier-law : (φ₁ φ₂ : F) → (=u= : φ₁ ≈u≈ φ₂) → (let u = unifier φ₁ φ₂ =u=) → (fst u) φ₁ ≡ (snd u) φ₂

mutual
  data FTerm : 𝕃 VariableName → Set
   where
    variable : (𝑥 : VariableName) → FTerm (𝕃⟦ 𝑥 ⟧)
    function : (𝑓 : FunctionName) → ..{𝑥s : 𝕃 VariableName} {arity : Nat} → (τs : FTerms 𝑥s arity) → FTerm 𝑥s

  data FTerms : 𝕃 VariableName → Nat → Set
   where
    [] : FTerms ∅ zero
    _∷_ : ∀ ..{𝑥s' 𝑥s : 𝕃 VariableName} → FTerm 𝑥s' → {n : Nat} → FTerms 𝑥s n → FTerms (union {m = VariableName} 𝑥s' 𝑥s) (⊹ n)

instance MembershipVariableNameFTerm : ∀ {𝑥s} → Membership VariableName (FTerm 𝑥s)
MembershipVariableNameFTerm = {!!}

record TotalIntersection {ℓ} (m : Set ℓ) (M : Set ℓ) ⦃ _ : Membership m M ⦄ : Set ℓ
 where
  field
    intersection : M → M → M
    intersectionLaw1 : ∀ {x : m} {X₁ X₂ : M} → x ∈ intersection X₁ X₂ → x ∈ X₁
    intersectionLaw2 : ∀ {x : m} {X₁ X₂ : M} → x ∈ intersection X₁ X₂ → x ∈ X₂
    intersectionLaw3 : ∀ {x : m} {X₁ X₂ : M} → x ∈ X₁ × x ∈ X₂ → x ∈ intersection X₁ X₂

open TotalIntersection ⦃ … ⦄

{-# DISPLAY TotalIntersection.intersection _ = intersection #-}

instance Intersection𝕃 : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → TotalIntersection A (𝕃 A)
Intersection𝕃 = {!!}

mutual
  subst : AList VariableName (∃ FTerm) → ∃ FTerm → ∃ FTerm
  subst x t@(.(✓ ∅) , variable 𝑥) with 𝑥 ∈? domain x
  … | yes x∈D = range x x∈D
  … | no x∉D = t
  subst x (fst₁ , function 𝑓 {𝑥s = 𝑥s} {arity = a} τs) with substs x a (𝑥s , τs)
  subst x (fst₁ , function 𝑓 {.fst₁} {arity₁} τs) | fst₂ , snd₁ = fst₂ , (function 𝑓 snd₁)

  substs : AList VariableName (∃ FTerm) → (a : Nat) → ∃ (flip FTerms a) → ∃ (flip FTerms a)
  substs x .0 (.∅ , []) = ∅ , []
  substs x .(suc _) (._ , (x₁ ∷ snd₁)) with {!subst x (_ , x₁)!}
  substs x .(suc _) (._ , (x₁ ∷ snd₁)) | sb = {!!}

-- indexed by the number of function symbols contained
data DTerm : Nat → Set
 where
  variable : (𝑥 : VariableName) → DTerm zero
  function : (𝑓 : FunctionName) → {arity : Nat} → (τs : Vec (∃ DTerm) arity) → DTerm (suc (sum (fst <$> vecToList τs)))

mutual
  substD : VariableName → ∃ DTerm → {n : Nat} → DTerm n → ∃ DTerm
  substD x x₁ (variable 𝑥) = ifYes 𝑥 ≟ x then x₁ else _ , variable 𝑥
  substD x x₁ (function 𝑓 τs) with substsD x x₁ τs
  substD x x₁ (function 𝑓 τs) | ss = suc (sum (fst <$> vecToList ss)) , function 𝑓 {_} ss

  substsD : VariableName → ∃ DTerm → {n : Nat} → Vec (Σ Nat DTerm) n → Vec (Σ Nat DTerm) n
  substsD x x₁ [] = []
  substsD x x₁ (x₂ ∷ x₃) with substD x x₁ (snd x₂) | substsD x x₁ x₃
  substsD x x₁ (x₂ ∷ x₃) | fst₁ , snd₁ | sss = (fst₁ , snd₁) ∷ sss

data HDTerm : Set where
  ⟨_⟩ : {n : Nat} → DTerm n → HDTerm

substituteD : (AList VariableName HDTerm) → HDTerm → HDTerm
substituteD = {!!}

amgu : HDTerm → HDTerm → (AList VariableName HDTerm) → Maybe (AList VariableName HDTerm)
amgu ⟨ variable 𝑥 ⟩ ⟨ variable 𝑥₁ ⟩ f = {!!}
amgu ⟨ variable 𝑥 ⟩ ⟨ function 𝑓 τs ⟩ f = {!!}
amgu ⟨ function 𝑓 τs ⟩ ⟨ variable 𝑥 ⟩ f = {!!}
amgu ⟨ function 𝑓 τs₁ ⟩ ⟨ function 𝑓₁ τs ⟩ f = {!!}

{-
data AList : 𝕃 VariableName → Set
 where
  [] : AList ∅
  _∷_ :
-}
record JohnUnification {𝑥s₁} (τ₁ : FTerm 𝑥s₁) {𝑥s₂} (τ₂ : FTerm 𝑥s₂) (_ : intersection {m = VariableName} 𝑥s₁ 𝑥s₂ ≡ ∅) : Set where
  field
    u₁ u₂ : AList VariableName (∃ FTerm)
    unification-law₁ : fst (subst u₁ (𝑥s₁ , τ₁)) ≡ fst (subst u₂ (𝑥s₂ , τ₂))
    unification-law₂ : snd (subst u₁ (𝑥s₁ , τ₁)) ≡ transport FTerm (sym unification-law₁) (snd (subst u₂ (𝑥s₂ , τ₂)))

record UnificationEquation (𝑥s : 𝕃 VariableName) : Set
 where
  field
    {lhs-terms} : 𝕃 VariableName
    lhs : FTerm lhs-terms
    {rhs-terms} : 𝕃 VariableName
    rhs : FTerm rhs-terms
    lhs∪rhs-terms : 𝑥s ≡ union {m = VariableName} lhs-terms rhs-terms

open UnificationEquation

number-of-variables-that-occur-more-than-once : ∀ {n-eqn} → Vec (∃ λ 𝑥s → UnificationEquation 𝑥s) n-eqn → Nat
number-of-variables-that-occur-more-than-once {zero} [] = 0
number-of-variables-that-occur-more-than-once {suc n-eqn} x = {!!}

number-of-function-symbols : ∀ {𝑥s} → FTerm 𝑥s → Nat
number-of-function-symbols = {!!}

record UnificationProblem (n-var n-lhs n-eqn : Nat) : Set
 where
  field
    equations : Vec (∃ λ 𝑥s → UnificationEquation 𝑥s) n-eqn
    n-var-law : number-of-variables-that-occur-more-than-once equations ≤ n-var
    n-lhs-law : (sum ∘ vecToList $ number-of-function-symbols ∘ lhs ∘ snd <$> equations) ≤ n-lhs

instance MembershipUnificationEquationUnificationProblem : ∀ {n-var n-lhs n-eqn 𝑥s} → Membership (UnificationEquation 𝑥s) (UnificationProblem n-var n-lhs n-eqn)
MembershipUnificationEquationUnificationProblem = {!!}

instance MembershipVariableNameUnificationProblem : ∀ {n-var n-lhs n-eqn} → Membership VariableName (UnificationProblem n-var n-lhs n-eqn)
MembershipVariableNameUnificationProblem = {!!}

deletable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
deletable = {!!}

deletable? : ∀ {𝑥s} → (eq : UnificationEquation 𝑥s) → Dec (deletable eq)
deletable? = {!!}

u-deletable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → deletable εq × εq ∈ up)
u-deletable? {n-var} {n-lhs} {zero} up = no {!!}
u-deletable? {n-var} {n-lhs} {suc n-eqn} up = {!!}

deleteRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var n-lhs (suc n-eqn)} {𝑥s} {εq : UnificationEquation 𝑥s} → deletable εq → εq ∈ up → UnificationProblem n-var n-lhs n-eqn
deleteRule = {!!}

decomposable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
decomposable = {!!}

decomposable? : ∀ {𝑥s} → (eq : UnificationEquation 𝑥s) → Dec (decomposable eq)
decomposable? = {!!}

u-decomposable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var (suc n-lhs) n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → decomposable εq × εq ∈ up)
u-decomposable? = {!!}

decomposeRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var (suc n-lhs) n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → decomposable εq → εq ∈ up → UnificationProblem n-var n-lhs n-eqn
decomposeRule = {!!}

swapable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
swapable = {!!}

swapable? : ∀ {𝑥s} → (eq : UnificationEquation 𝑥s) → Dec (swapable eq)
swapable? = {!!}

u-swapable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var (suc n-lhs) n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → swapable εq × εq ∈ up)
u-swapable? = {!!}

swapRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var (suc n-lhs) n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → swapable εq → εq ∈ up → UnificationProblem n-var n-lhs n-eqn
swapRule = {!!}

eliminatable : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var n-lhs n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → (εq∈up : εq ∈ up) → Set
eliminatable = {!!}

u-eliminatable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem (suc n-var) n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → ∃ λ (εq∈up : εq ∈ up) → eliminatable {up = up} {εq = εq} εq∈up)
u-eliminatable? = {!!}

eliminateRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem (suc n-var) n-lhs n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → {εq∈up : εq ∈ up} → eliminatable {up = up} {εq = εq} εq∈up → UnificationProblem n-var n-lhs n-eqn
eliminateRule = {!!}

conflictable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
conflictable = {!!}

conflictable? : ∀ {𝑥s} → (εq : UnificationEquation 𝑥s) → Dec (conflictable εq)
conflictable? = {!!}

u-conflictable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → conflictable εq × εq ∈ up)
u-conflictable? = {!!}

checkable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
checkable = {!!}

checkable? : ∀ {𝑥s} → (εq : UnificationEquation 𝑥s) → Dec (checkable εq)
checkable? = {!!}

u-checkable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → checkable εq × εq ∈ up)
u-checkable? = {!!}


postulate
  substituteFormula : (VariableName → Term) → Formula → Formula

record Unifier' : Set
 where
  field
    unifier-left unifier-right : VariableName → Term

open Unifier'

record _Unifies_and_ (υ : Unifier') (φ₁ φ₂ : Formula) : Set
 where
  field
    unification-law : substituteFormula (unifier-left υ) φ₁ ≡ substituteFormula (unifier-right υ) φ₂

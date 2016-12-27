
module Term where

open import OscarPrelude
open import VariableName
open import FunctionName
open import Arity
open import Vector
open import TermByFunctionNames
open import Membership

mutual

  data Term : Set
   where
    variable : VariableName → Term
    function : FunctionName → Terms → Term

  record Terms : Set
   where
    constructor ⟨_⟩
    inductive
    field
      {arity} : Arity
      terms : Vector Term arity

open Terms public

termVariable-inj : ∀ {𝑥₁ 𝑥₂} → Term.variable 𝑥₁ ≡ variable 𝑥₂ → 𝑥₁ ≡ 𝑥₂
termVariable-inj refl = refl

termFunction-inj₁ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → 𝑓₁ ≡ 𝑓₂
termFunction-inj₁ refl = refl

termFunction-inj₂ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → τ₁s ≡ τ₂s
termFunction-inj₂ refl = refl

terms-inj : ∀ {𝑎} → {τs₁ τs₂ : Vector Term 𝑎} → (τs₁≡τs₂ : (Terms.⟨_⟩ {𝑎} τs₁) ≡ ⟨ τs₂ ⟩) → τs₁ ≡ τs₂
terms-inj refl = refl

mutual
  termToTermByFunctionNames : Term → Σ Nat TermByFunctionNames
  termToTermByFunctionNames (variable x) = _ , (variable x)
  termToTermByFunctionNames (function x x₁) = {!!}

  termsToVec : Terms → Σ Nat (λ arity → Σ (Vec (Σ Nat TermByFunctionNames) arity) λ τs → Σ Nat λ n → n ≡ sum (vecToList $ (fst <$> τs)))
  termsToVec (⟨_⟩ {arity = arity₁} ⟨ vector₁ ⟩) = {!!}

iTermToTerm : Σ Nat TermByFunctionNames → Term
iTermToTerm = {!!}

eq-term-round : ∀ τ → iTermToTerm (termToTermByFunctionNames τ) ≡ τ
eq-term-round = {!!}

eq-iterm-round : ∀ τ → termToTermByFunctionNames (iTermToTerm τ) ≡ τ
eq-iterm-round = {!!}

instance EqTerm : Eq Term
Eq._==_ EqTerm x y with termToTermByFunctionNames x | graphAt termToTermByFunctionNames x | termToTermByFunctionNames y | graphAt termToTermByFunctionNames y
Eq._==_ EqTerm x y | ix | ingraph eqx | iy | ingraph eqy with ix ≟ iy
Eq._==_ EqTerm x y | ix | ingraph eqx | .ix | ingraph eqy | yes refl = yes $ ((cong iTermToTerm eqy ⟨≡⟩ʳ cong iTermToTerm eqx) ⟨≡⟩ eq-term-round x) ʳ⟨≡⟩ eq-term-round y
Eq._==_ EqTerm x y | ix | ingraph eqx | iy | ingraph eqy | no neq = {!!}

instance EqTerms : Eq Terms
EqTerms = {!!}

{-
module _ {i : Size}
 where

  mutual

    EqTerm⇑ : (x y : Term) → Delay i ∘ Dec $ x ≡ y
    EqTerm⇑ (variable _) (variable _) = now (decEq₁ termVariable-inj $ _≟_ _ _)
    EqTerm⇑ (function 𝑓₁ τ₁s) (function 𝑓₂ τ₂s) =
      {-
      τ₁s≟τ₂s ← EqTerms⇑ τ₁s τ₂s -|
      (now $ decEq₂ termFunction-inj₁ termFunction-inj₂ (𝑓₁ ≟ 𝑓₂) τ₁s≟τ₂s)
      -}

      EqTerms⇑ τ₁s τ₂s >>= λ
      τ₁s≟τ₂s → now $ decEq₂ termFunction-inj₁ termFunction-inj₂ (𝑓₁ ≟ 𝑓₂) τ₁s≟τ₂s

    EqTerm⇑ (variable _)   (function _ _) = now $ no λ ()
    EqTerm⇑ (function _ _) (variable _)   = now $ no λ ()

    EqTerms⇑ : (x y : Terms) → Delay i ∘ Dec $ x ≡ y
    EqTerms⇑ (⟨_⟩ {𝑎₁} τ₁s) (⟨_⟩ {𝑎₂} τ₂s)
     with 𝑎₁ ≟ 𝑎₂
    … | no 𝑎₁≢𝑎₂ = now $ no λ {τ₁≡τ₂ → 𝑎₁≢𝑎₂ (cong arity τ₁≡τ₂)}
    … | yes refl =
      EqVectorTerm⇑ τ₁s τ₂s >>= λ
      { (yes refl) → now $ yes refl
      ; (no τ₁s≢τ₂s) → now $ no (λ ⟨τ₁s⟩≡⟨τ₂s⟩ → τ₁s≢τ₂s (terms-inj ⟨τ₁s⟩≡⟨τ₂s⟩)) }

    EqVectorTerm⇑ : ∀ {n} → (x y : Vector Term n) → Delay i ∘ Dec $ x ≡ y
    EqVectorTerm⇑ ⟨ [] ⟩ ⟨ [] ⟩ = now (yes refl)
    EqVectorTerm⇑ ⟨ τ₁ ∷ τ₁s ⟩ ⟨ τ₂ ∷ τ₂s ⟩ =
      EqTerm⇑ τ₁ τ₂ >>= λ
      { (yes refl) → EqVectorTerm⇑ ⟨ τ₁s ⟩ ⟨ τ₂s ⟩ >>= λ
                     { (yes refl) → now $ yes refl
                     ; (no τ₁s≢τ₂s) → now $ no λ τ₁₁s≡τ₁₂s → τ₁s≢τ₂s $ cong ⟨_⟩ ((vcons-inj-tail (cong vector τ₁₁s≡τ₁₂s))) }
      ; (no τ₁≢τ₂) → now $ no λ τ₁₁s≡τ₂₂s → τ₁≢τ₂ $ vcons-inj-head (cong vector τ₁₁s≡τ₂₂s) }

EqVectorTerm⇓ : ∀ {n} → (x y : Vector Term n) → EqVectorTerm⇑ x y ⇓
EqVectorTerm⇓ ⟨ [] ⟩ ⟨ [] ⟩ = _ , now⇓
EqVectorTerm⇓ ⟨ variable 𝑥₁ ∷ τ₁s ⟩ ⟨ variable 𝑥₂ ∷ τ₂s ⟩
 with 𝑥₁ ≟ 𝑥₂
… | yes refl with EqVectorTerm⇓ ⟨ τ₁s ⟩ ⟨ τ₂s ⟩
EqVectorTerm⇓ ⟨ variable 𝑥₁ ∷ τ₁s ⟩ ⟨ variable .𝑥₁ ∷ .τ₁s ⟩ | yes refl | (yes refl , snd₁) = _ , snd₁ >>=⇓ now⇓
EqVectorTerm⇓ ⟨ variable 𝑥₁ ∷ τ₁s ⟩ ⟨ variable .𝑥₁ ∷ τ₂s ⟩ | yes refl | (no x , snd₁) = _ , snd₁ >>=⇓ now⇓
EqVectorTerm⇓ ⟨ variable 𝑥₁ ∷ τ₁s ⟩ ⟨ variable 𝑥₂ ∷ τ₂s ⟩ | no 𝑥₁≢𝑥₂ = _ , now⇓
EqVectorTerm⇓ ⟨ variable x ∷ τ₁s ⟩ ⟨ function x₁ x₂ ∷ τ₂s ⟩ = _ , now⇓
EqVectorTerm⇓ ⟨ function x x₁ ∷ τ₁s ⟩ ⟨ variable x₂ ∷ τ₂s ⟩ = _ , now⇓
EqVectorTerm⇓ ⟨ function 𝑓₁ (⟨_⟩ {𝑎₁} τ₁s) ∷ τ₁₂s ⟩ ⟨ function 𝑓₂ (⟨_⟩ {𝑎₂} τ₂s) ∷ τ₂₂s ⟩
 with 𝑎₁ ≟ 𝑎₂ | 𝑓₁ ≟ 𝑓₂
… | no 𝑎₁≢𝑎₂ | no 𝑓₁≢𝑓₂  = _ , now⇓
… | no 𝑎₁≢𝑎₂ | yes refl  = _ , now⇓
… | yes refl | no 𝑓₁≢𝑓₂
 with EqVectorTerm⇓ τ₁s τ₂s
… | (no τ₁s≢τ₂s , τ⇓)  = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
… | (yes refl , τ⇓)    = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
EqVectorTerm⇓ ⟨ function 𝑓₁ (⟨_⟩ {𝑎₁} τ₁s) ∷ τ₁₂s ⟩ ⟨ function 𝑓₂ (⟨_⟩ {𝑎₂} τ₂s) ∷ τ₂₂s ⟩ | yes refl | yes refl
 with EqVectorTerm⇓ τ₁s τ₂s | EqVectorTerm⇓ ⟨ τ₁₂s ⟩ ⟨ τ₂₂s ⟩
… | (no τ₁s≢τ₂s , τ⇓) | (no τ₁₂s≢τ₂₂s , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
… | (yes refl , τ⇓)   | (no τ₁₂s≢τ₂₂s , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ (τs⇓ >>=⇓ now⇓)
… | (no τ₁s≢τ₂s , τ⇓) | (yes refl , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
… | (yes refl , τ⇓)   | (yes refl , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ (τs⇓ >>=⇓ now⇓)

EqTerms⇓ : (x y : Terms) → EqTerms⇑ x y ⇓
EqTerms⇓ (⟨_⟩ {𝑎₁} τ₁s) (⟨_⟩ {𝑎₂} τ₂s)
 with 𝑎₁ ≟ 𝑎₂
… | no 𝑎₁≢𝑎₂ = _ , now⇓
… | yes refl
 with EqVectorTerm⇓ τ₁s τ₂s
… | (yes refl , τ⇓) = _ , τ⇓ >>=⇓ now⇓
… | (no _ , τ⇓) = _ , τ⇓ >>=⇓ now⇓

EqTerm⇓ : (x y : Term) → EqTerm⇑ x y ⇓
EqTerm⇓ (variable x) (variable x₁) = _ , now⇓
EqTerm⇓ (function _ τ₁s) (function _ τ₂s)
 with EqTerms⇓ τ₁s τ₂s
… | (_ , τ⇓) = _ , τ⇓ >>=⇓ now⇓
EqTerm⇓ (variable x) (function x₁ x₂) = _ , now⇓
EqTerm⇓ (function x x₁) (variable x₂) = _ , now⇓

instance EqTerm : Eq Term
EqTerm = record { _==_ = λ x y → fst (EqTerm⇓ x y) }

instance EqTerms : Eq Terms
Eq._==_ EqTerms x y = fst (EqTerms⇓ x y)
-}

instance MembershipTermTerms : Membership Term Terms
Membership._∈_ MembershipTermTerms = _ᵗ∈ᵗˢ_ where
  data _ᵗ∈ᵗˢ_ (τ : Term) : Terms → Set
   where
    zero : τ ᵗ∈ᵗˢ ⟨ ⟨ τ ∷ [] ⟩ ⟩
    suc : ∀ {τs} → τ ᵗ∈ᵗˢ τs → τ ᵗ∈ᵗˢ ⟨ ⟨ τ ∷ vector (terms τs) ⟩ ⟩
Membership._∉_ MembershipTermTerms x X = ¬ x ∈ X
fst (Membership.xor-membership MembershipTermTerms) x₁ x₂ = x₂ x₁
snd (Membership.xor-membership MembershipTermTerms) x₁ x₂ = x₁ x₂

instance MembershipVariableNameTerm : Membership VariableName Term
Membership._∈_ MembershipVariableNameTerm = _ᵛ∈ᵗ_ where
  data _ᵛ∈ᵗ_ (𝑥 : VariableName) : Term → Set
   where
    variable : 𝑥 ᵛ∈ᵗ variable 𝑥
    function : ∀ 𝑓 {τ : Term} {τs} → {_ : 𝑥 ∈ τ} → τ ∈ τs → 𝑥 ᵛ∈ᵗ function 𝑓 τs
Membership._∉_ MembershipVariableNameTerm x X = ¬ x ∈ X
fst (Membership.xor-membership MembershipVariableNameTerm) x₁ x₂ = x₂ x₁
snd (Membership.xor-membership MembershipVariableNameTerm) x₁ x₂ = x₁ x₂

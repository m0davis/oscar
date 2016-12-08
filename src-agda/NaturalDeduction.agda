module NaturalDeduction
 where

-- custom prelude
module _ where

  open import Prelude public
    renaming (_==_ to _≟_) -- TODO ask Agda to rename Eq._==_ to Eq._≟_

  {-# DISPLAY Eq._==_ _ = _≟_ #-}

  open import Container.List renaming (_∈_ to _∈C_; lookup∈ to lookup∈C) public

  _∈C?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ (a : A) → (xs : List A) → Dec (a ∈C xs)
  a ∈C? [] = no λ ()
  a ∈C? (x ∷ xs) with a ≟ x
  … | yes a≡x rewrite a≡x = yes (zero refl)
  … | no a≢x with a ∈C? xs
  … | yes a∈xs = yes (suc a∈xs)
  … | no a∉xs = no (λ {(zero a≡x) → a≢x a≡x ; (suc a∈xs) → a∉xs a∈xs})

  data _∈_ {ℓ} {A : Set ℓ} (a : A) : List A → Set ℓ
   where
    here : (as : List A) → a ∈ (a ∷ as)
    there : (x : A) {as : List A} → a ∈ as → a ∈ (x ∷ as)

  _∉_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ (a : A) → (xs : List A) → Set ℓ
  a ∉ xs = ¬ (a ∈ xs)

  _∈?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ (a : A) → (xs : List A) → Dec (a ∈ xs)
  a ∈? [] = no λ ()
  a ∈? (x ∷ xs) with a ≟ x
  … | yes a≡x rewrite a≡x = yes (here xs)
  … | no a≢x with a ∈? xs
  … | yes a∈xs = yes (there x a∈xs)
  … | no a∉xs = no (λ {(here _) → a≢x refl ; (there _ a∈xs) → a∉xs a∈xs})

  _⊆_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
  R ⊆ S = ∀ {x} → x ∈ R → x ∈ S

  _≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  x ≢ y = ¬ (x ≡ y)

  infix 0 _↔_
  _↔_ : {ℓ¹ : Level} → Set ℓ¹ → {ℓ² : Level} → Set ℓ² → Set (ℓ¹ ⊔ ℓ²)
  P ↔ Q = (P → Q) × (Q → P)

  ∃ : ∀ {ℓᴬ ℓᴮ} {A : Set ℓᴬ} (B : A → Set ℓᴮ) → Set (ℓᴬ ⊔ ℓᴮ)
  ∃ = Σ _

  ∄ : ∀ {ℓᴬ ℓᴮ} {A : Set ℓᴬ} (B : A → Set ℓᴮ) → Set (ℓᴬ ⊔ ℓᴮ)
  ∄ = ¬_ ∘ ∃

  infixl 4 _⊎_
  _⊎_ = Either

  {-# DISPLAY Either = _⊎_ #-}

  open import Agda.Builtin.Size public

  open import Control.Monad.State public
  open import Control.Monad.Identity public

  {-
  open import Tactic.Nat
  open import Tactic.Deriving.Eq
  -}

TruthValue = Bool

-- reification of elements of the domain
Element = Nat

record VariableName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat
open VariableName

record FunctionName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat
open FunctionName

record PredicateName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat
open PredicateName

record Arity : Set
 where
  constructor ⟨_⟩
  field
    arity : Nat
open Arity

Vector : Set → Arity → Set
Vector A a = Vec A (arity a)

record Elements : Set
 where
  constructor ⟨_⟩
  field
    {arity} : Arity
    elements : Vector Element arity
open Elements

record Interpretation : Set
 where
  field
    μ⟦_⟧ : VariableName → Element
    𝑓⟦_⟧ : FunctionName → Elements → Element
    𝑃⟦_⟧ : PredicateName → Elements → TruthValue
open Interpretation

mutual
  data Term {i : Size} : Set
   where
    variable : VariableName → Term
    function : FunctionName → {j : Size< i} → Terms {j} → Term
  record Terms {i : Size} : Set
   where
    constructor ⟨_⟩
    inductive
    field
      {arity} : Arity
      terms : Vector (Term {i}) arity
open Terms

data Formula : Set
 where
  atomic : PredicateName → Terms → Formula
  logical : Formula →
            Formula →
            Formula
  quantified : VariableName → Formula → Formula

record HasNegation (A : Set) : Set
 where
  field
    ~ : A → A
open HasNegation ⦃ … ⦄
{-# DISPLAY HasNegation.~ _ = ~ #-}

record BeFormula (A : Set) : Set where
  constructor ⟨_⟩
  field
    formula : A → Formula
open BeFormula ⦃ … ⦄

record HasSatisfaction (A : Set) : Set₁
 where
  field
    _⊨_ : Interpretation → A → Set
  _⊭_ : Interpretation → A → Set
  _⊭_ I = ¬_ ∘ I ⊨_
open HasSatisfaction ⦃ … ⦄
{-# DISPLAY HasSatisfaction._⊨_ _ = _⊨_ #-}
{-# DISPLAY HasSatisfaction._⊭_ _ = _⊭_ #-}

record HasDecidableSatisfaction (A : Set) ⦃ _ : HasSatisfaction A ⦄ : Set₁
 where
  field
    _⊨?_ : (I : Interpretation) → (x : A) → Dec (I ⊨ x)
open HasDecidableSatisfaction ⦃ … ⦄
{-# DISPLAY HasDecidableSatisfaction._⊨?_ _ = _⊨?_ #-}

infix 15 _╱_
record Sequent (A : Set) ⦃ _ : BeFormula A ⦄ : Set
 where
  constructor _╱_
  field
    statement : A
    suppositions : List A
open Sequent

record HasValidation (A : Set) : Set₁
 where
  field
    ⊨_ : A → Set
  ⊭_ : A → Set
  ⊭_ = ¬_ ∘ ⊨_
open HasValidation ⦃ … ⦄
{-# DISPLAY HasValidation.⊨_ _ = ⊨_ #-}
{-# DISPLAY HasValidation.⊭_ _ = ⊭_ #-}

𝑃[_♭_] : PredicateName → Terms → Formula
𝑃[_♭_] = atomic
{-# DISPLAY atomic = 𝑃[_♭_] #-}

_⊗_ : Formula → Formula → Formula
_⊗_ = logical
{-# DISPLAY logical = _⊗_ #-}

instance

  HasNegationFormula : HasNegation Formula
  HasNegation.~ HasNegationFormula φ = φ ⊗ φ

data IsLiteral : Formula → Set
 where
  atomic : (𝑃 : PredicateName) → (τs : Terms) → IsLiteral $ 𝑃[ 𝑃 ♭ τs ]
  logical : (𝑃 : PredicateName) → (τs : Terms) → IsLiteral ∘ ~ $ 𝑃[ 𝑃 ♭ τs ]

record LiteralFormula : Set
 where
  constructor ⟨_⟩
  field
    {formula} : Formula
    isLiteral : IsLiteral formula
open LiteralFormula

infix 13 _¶_
record Problem (A : Set) ⦃ _ : BeFormula A ⦄ : Set
 where
  constructor _¶_
  field
    inferences : List (Sequent A)
    interest : Sequent A
open Problem

record HasSubstantiveDischarge (+ : Set) (- : Set) : Set₁
 where
  field
    _≽_ : + → - → Set
open HasSubstantiveDischarge ⦃ … ⦄
{-# DISPLAY HasSubstantiveDischarge._≽_ _ = _≽_ #-}

record HasVacuousDischarge (+ : Set) : Set₁
 where
  field
    ◁_ : + → Set
open HasVacuousDischarge ⦃ … ⦄
{-# DISPLAY HasVacuousDischarge.◁_ _ = ◁_ #-}

record HasSalvation (A : Set) : Set₁
 where
  field
    ▷_ : A → Set
open HasSalvation ⦃ … ⦄
{-# DISPLAY HasSalvation.▷_ _ = ▷_ #-}

record HasDecidableSalvation (A : Set) ⦃ _ : HasSalvation A ⦄ : Set
 where
  field
    ▷?_ : (x : A) → Dec $ ▷_ x
open HasDecidableSalvation ⦃ … ⦄
{-# DISPLAY HasDecidableSalvation.▷?_ _ = ▷?_ #-}

τ⟦_⟧ : Interpretation → {i : Size} → Term {i} → Element
τ⟦ I ⟧ (variable 𝑥) = μ⟦ I ⟧ 𝑥
τ⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ⟨ τ⟦ I ⟧ <$> terms τs ⟩

∀[_♭_] : VariableName → Formula → Formula
∀[_♭_] = quantified
{-# DISPLAY quantified = ∀[_♭_] #-}

_∧_ : Formula → Formula → Formula
φ₁ ∧ φ₂ = ~ φ₁ ⊗ ~ φ₂

_∨_ : Formula → Formula → Formula
φ₁ ∨ φ₂ = ~ (φ₁ ⊗ φ₂)

_⊃_ : Formula → Formula → Formula
φ₁ ⊃ φ₂ = ~ φ₁ ∨ φ₂

_⟷_ : Formula → Formula → Formula
φ₁ ⟷ φ₂ = (φ₁ ⊗ (φ₂ ⊗ φ₂)) ⊗ ((φ₁ ⊗ φ₁) ⊗ φ₂) -- TODO check that this is logically equivalent to the more verbose, (φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)

record _≞_/_ (𝓘 : Interpretation) (I : Interpretation) (𝑥 : VariableName) : Set
 where
  field
    μEquality : {𝑥′ : VariableName} → 𝑥′ ≢ 𝑥 → μ⟦ 𝓘 ⟧ 𝑥 ≡ μ⟦ I ⟧ 𝑥′
    𝑓Equality : (𝑓 : FunctionName) (μs : Elements) → 𝑓⟦ 𝓘 ⟧ 𝑓 μs ≡ 𝑓⟦ I ⟧ 𝑓 μs
    𝑃Equality : (𝑃 : PredicateName) → (μs : Elements) → 𝑃⟦ 𝓘 ⟧ 𝑃 μs ≡ 𝑃⟦ I ⟧ 𝑃 μs

instance

  EqVariableName : Eq VariableName
  Eq._==_ EqVariableName ⟨ x ⟩ ⟨ y ⟩ with x ≟ y
  … | yes x≡y rewrite x≡y = yes refl
  … | no x≢y = no λ { refl → x≢y refl }

  EqFunctionName : Eq FunctionName
  Eq._==_ EqFunctionName ⟨ x ⟩ ⟨ y ⟩ with x ≟ y
  … | yes x≡y rewrite x≡y = yes refl
  … | no x≢y = no λ { refl → x≢y refl }

  EqPredicateName : Eq PredicateName
  Eq._==_ EqPredicateName ⟨ x ⟩ ⟨ y ⟩ with x ≟ y
  … | yes x≡y rewrite x≡y = yes refl
  … | no x≢y = no λ { refl → x≢y refl }

  EqArity : Eq Arity
  Eq._==_ EqArity ⟨ x ⟩ ⟨ y ⟩ with x ≟ y
  … | yes x≡y rewrite x≡y = yes refl
  … | no x≢y = no λ { refl → x≢y refl }

  EqFormula : Eq Formula
  EqFormula = {!!}

  EqLiteralFormula : Eq LiteralFormula
  Eq._==_ EqLiteralFormula φ₁ φ₂ = {!!}

instance

  BeFormulaFormula : BeFormula Formula
  BeFormula.formula BeFormulaFormula = id

  BeFormulaLiteralFormula : BeFormula LiteralFormula
  BeFormula.formula BeFormulaLiteralFormula = formula

instance

  HasNegationLiteralFormula : HasNegation LiteralFormula
  HasNegation.~ HasNegationLiteralFormula ⟨ atomic 𝑃 τs ⟩ = ⟨ logical 𝑃 τs ⟩
  HasNegation.~ HasNegationLiteralFormula ⟨ logical 𝑃 τs ⟩ = ⟨ atomic 𝑃 τs ⟩

  HasNegationSequent : {A : Set} ⦃ _ : HasNegation A ⦄ ⦃ _ : BeFormula A ⦄ → HasNegation $ Sequent A
  HasNegation.~ HasNegationSequent ( φᵗ ╱ φˢs ) = ~ φᵗ ╱ φˢs

instance

  HasSatisfactionList : {A : Set} ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction $ List A
  HasSatisfaction._⊨_ HasSatisfactionList I [] = ⊤
  HasSatisfaction._⊨_ HasSatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs

  HasSatisfactionBeFormula : {A : Set} → ⦃ _ : BeFormula A ⦄ → HasSatisfaction A
  HasSatisfaction._⊨_ (HasSatisfactionBeFormula ⦃ beFormula ⦄) = λ I φ → I ⊨φ formula beFormula φ
   where
    _⊨φ_ : Interpretation → Formula → Set
    I ⊨φ (atomic 𝑃 τs) = 𝑃⟦ I ⟧ 𝑃 ⟨ τ⟦ I ⟧ <$> terms τs ⟩ ≡ true
    I ⊨φ (logical φ₁ φ₂) = ¬ I ⊨φ φ₁ × ¬ I ⊨φ φ₂
    I ⊨φ (quantified 𝑥 φ) = (𝓘 : Interpretation) → 𝓘 ≞ I / 𝑥 → 𝓘 ⊨φ φ
    {-# DISPLAY _⊨φ_ = _⊨_ #-}

  HasSatisfactionSequent : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSatisfaction $ Sequent A
  HasSatisfaction._⊨_ HasSatisfactionSequent I (φᵗ ╱ φˢs) = I ⊨ φˢs → I ⊨ φᵗ

instance

  HasValidationBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation A
  HasValidation.⊨_ HasValidationBeFormula φ = (I : Interpretation) → I ⊨ φ

  HasValidationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation $ Sequent A
  HasValidation.⊨_ HasValidationSequent Φ = (I : Interpretation) → I ⊨ Φ

  HasValidationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation $ Problem A
  HasValidation.⊨_ HasValidationProblem (χs ¶ ι) = (I : Interpretation) → I ⊨ χs → I ⊨ ι

instance

  HasSubstantiveDischargeBeFormulaBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge A A
  HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeBeFormulaBeFormula ⦃ ⟨ beFormula ⟩ ⦄) = _≡_ on beFormula -- _≡_ on (formula beFormula) -- _≡_

  HasSubstantiveDischargeListBeFormulaBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List A) A
  HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListBeFormulaBeFormula ⦃ ⟨ beFormula ⟩ ⦄) +s - = beFormula - ∈ (beFormula <$> +s) -- flip _∈_

  HasSubstantiveDischargeListFormulaListFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List A) (List A)
  HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListFormulaListFormula ⦃ ⟨ beFormula ⟩ ⦄) = flip $ _⊆_ on fmap beFormula -- flip _⊆_

  HasSubstantiveDischargeSequentSequent : ∀ {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (Sequent A) (Sequent A)
  HasSubstantiveDischarge._≽_ HasSubstantiveDischargeSequentSequent (+ᵗ ╱ +ᵖs) (-ᵗ ╱ -ᵖs) = +ᵗ ≽ -ᵗ × +ᵖs ≽ -ᵖs

  HasSubstantiveDischargeListSequentSequent : ∀ {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List $ Sequent A) (Sequent A)
  HasSubstantiveDischarge._≽_ HasSubstantiveDischargeListSequentSequent χs ι = ∃ λ c → (c ∈ χs) × c ≽ ι

instance

  HasVacuousDischargeList : {A : Set} ⦃ _ : HasSubstantiveDischarge (List A) A ⦄ ⦃ _ : HasNegation A ⦄ → HasVacuousDischarge (List A)
  HasVacuousDischarge.◁_ (HasVacuousDischargeList {A}) xs = ∃ λ (x : A) → xs ≽ x × xs ≽ ~ x

  HasVacuousDischargeSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasNegation A ⦄ → HasVacuousDischarge (Sequent A)
  HasVacuousDischarge.◁_ HasVacuousDischargeSequent (_ ╱ φˢs) = ∃ λ s → (s ∈ φˢs) × (φˢs ≽ s) × (φˢs ≽ ~ s)

instance

  HasSalvationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasVacuousDischarge $ List A ⦄ → HasSalvation $ Sequent A
  HasSalvation.▷_ HasSalvationSequent (φᵗ ╱ φᵖs) = ◁ φᵖs ⊎ φᵖs ≽ φᵗ

  HasSalvationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasVacuousDischarge ∘ List $ Sequent A ⦄ → HasSalvation $ Problem A
  HasSalvation.▷_ HasSalvationProblem (χs ¶ ι) = ◁ χs ⊎ χs ≽ ι

instance

  HasDecidableSalvationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasSalvation $ Sequent A ⦄ → HasDecidableSalvation $ Sequent A
  HasDecidableSalvationSequent = {!!}

  HasDecidableSalvationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasVacuousDischarge ∘ List $ Sequent A ⦄ → HasDecidableSalvation $ Problem A
  HasDecidableSalvationProblem = {!!}

Theorem1 : {Φ : Problem LiteralFormula} → ⊨ Φ ↔ ▷ Φ
Theorem1 {Φ@(χs ¶ ι)} = Theorem1a , Theorem1b
 where
  Theorem1a : ⊨ Φ → ▷ Φ
  Theorem1a with ▷? Φ
  … | yes ⊫Φ = const ⊫Φ
  … | no ⊯Φ =
    let I , I⊨χs , I⊭ι = Lemma1a in
    λ I→I⊨cs→I⊨i → ⊥-elim $ I⊭ι $ I→I⊨cs→I⊨i I I⊨χs
   where
    Lemma1a : ∃ λ I → I ⊨ χs × I ⊭ ι
    -- To construct the interpretation, consider a unique list, τ₀, τ₁, …, τₙ, of terms in ι ∷ χs. For each term, τ, we find <TODO> interpretations, 𝓘, such that for any I ∈ 𝓘, and any i ∈ 0, …, n, τ⟦ I ⟧ τᵢ = i. For each formula φ ∈ ι ∷ χs, we find <TODO> an interpretation I ∈ 𝓘 such that 𝑃⟦ I ⟧ φ = true when φ ∈ χs and 𝑃⟦ I ⟧ φ = false when φ = ι.
    -- For all terms in ι ∷ χs, find a coding into Nat that uniquely determines each term. To do this, compute the maximum functional depth of terms, D, the maximal arity of terms, A, the maximal function name, F, and the maximal variable name, V. Each term can then be coded into Fin V + (D₀ = F + F * V + F * V ^ 2 + ... + F * V ^ A) + (D₀ ...
    -- Encode each term in a discrimination network. Each new term stored is assigned a unique id
    Lemma1a = {!!}
     where

      data TermCode : Set
       where
        variable : VariableName → TermCode
        function : FunctionName → Arity → TermCode

      termCode-function-inj₁ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → 𝑓₁ ≡ 𝑓₂
      termCode-function-inj₁ refl = refl

      termCode-function-inj₂ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → arity₁ ≡ arity₂
      termCode-function-inj₂ refl = refl

      instance
        EqTermCode : Eq TermCode
        Eq._==_ EqTermCode (variable 𝑥₁) (variable 𝑥₂) with 𝑥₁ ≟ 𝑥₂
        … | yes 𝑥₁≡𝑥₂ rewrite 𝑥₁≡𝑥₂ = yes refl
        … | no 𝑥₁≢𝑥₂ = no (λ { refl → 𝑥₁≢𝑥₂ refl})
        Eq._==_ EqTermCode (variable x) (function x₁ x₂) = no (λ ())
        Eq._==_ EqTermCode (function x x₁) (variable x₂) = no (λ ())
        Eq._==_ EqTermCode (function 𝑓₁ 𝑎₁) (function 𝑓₂ 𝑎₂) = decEq₂ termCode-function-inj₁ termCode-function-inj₂ (𝑓₁ ≟ 𝑓₂) (𝑎₁ ≟ 𝑎₂)

      mutual
        encodeTerm : Term → List TermCode
        encodeTerm (variable 𝑥) = variable 𝑥 ∷ []
        encodeTerm (function 𝑓 (⟨_⟩ {arity} τs)) = function 𝑓 arity ∷ encodeTerms τs

        encodeTerms : {arity : Arity} → Vector Term arity → List TermCode
        encodeTerms [] = []
        encodeTerms (τ ∷ τs) = encodeTerm τ ++ encodeTerms τs

      mutual

        decodeTerm : Nat → StateT (List TermCode) Maybe Term
        decodeTerm zero = lift nothing
        decodeTerm (suc n) = do
          caseM get of λ
          { [] → lift nothing
          ; (variable 𝑥 ∷ _) →
            modify (drop 1) ~|
            return (variable 𝑥)
          ; (function 𝑓 arity ∷ _) →
            modify (drop 1) ~|
            decodeFunction n 𝑓 arity }

        decodeFunction : Nat → FunctionName → Arity → StateT (List TermCode) Maybe Term
        decodeFunction n 𝑓 arity = do
          τs ← decodeTerms n arity -|
          return (function 𝑓 ⟨ τs ⟩)

        decodeTerms : Nat → (arity : Arity) → StateT (List TermCode) Maybe (Vector Term arity)
        decodeTerms n ⟨ zero ⟩ = return []
        decodeTerms n ⟨ suc arity ⟩ = do
          τ ← decodeTerm n -|
          τs ← decodeTerms n ⟨ arity ⟩ -|
          return (τ ∷ τs)

      .decode-is-inverse-of-encode : ∀ τ → runStateT (decodeTerm ∘ length $ encodeTerm τ) (encodeTerm τ) ≡ (just $ τ , [])
      decode-is-inverse-of-encode (variable 𝑥) = refl
      decode-is-inverse-of-encode (function 𝑓 ⟨ [] ⟩) = {!!}
      decode-is-inverse-of-encode (function 𝑓 ⟨ variable 𝑥 ∷ τs ⟩) = {!!}
      decode-is-inverse-of-encode (function 𝑓 ⟨ function 𝑓' τs' ∷ τs ⟩) = {!!}

      module ExampleEncodeDecode where
        example-Term : Term
        example-Term =
          (function ⟨ 2 ⟩
                    ⟨ variable ⟨ 0 ⟩
                    ∷ function ⟨ 3 ⟩
                               ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩
                    ∷ variable ⟨ 5 ⟩
                    ∷ []
                    ⟩
          )

        -- function ⟨ 2 ⟩ ⟨ 3 ⟩ ∷ variable ⟨ 0 ⟩ ∷ function ⟨ 3 ⟩ ⟨ 1 ⟩ ∷ variable ⟨ 2 ⟩ ∷ variable ⟨ 5 ⟩ ∷ []
        example-TermCodes : List TermCode
        example-TermCodes = encodeTerm example-Term

        example-TermDecode : Maybe (Term × List TermCode)
        example-TermDecode = runStateT (decodeTerm (length example-TermCodes)) example-TermCodes

        example-verified : example-TermDecode ≡ (just $ example-Term , [])
        example-verified = refl

        example-bad : runStateT (decodeTerm 2) (function ⟨ 2 ⟩ ⟨ 2 ⟩ ∷ variable ⟨ 0 ⟩ ∷ []) ≡ nothing
        example-bad = refl

      record TermNode : Set
       where
        inductive
        field
          children : List (TermCode × TermNode)
          number : Nat

      open TermNode

      _child∈_ : TermCode → TermNode → Set
      _child∈_ 𝔠 𝔫 = 𝔠 ∈ (fst <$> children 𝔫)

      _child∉_ : TermCode → TermNode → Set
      𝔠 child∉ 𝔫 = ¬ (𝔠 child∈ 𝔫)

      _child∈?_ : (𝔠 : TermCode) → (𝔫 : TermNode) → Dec $ 𝔠 child∈ 𝔫
      c child∈? record { children = cs } = c ∈? (fst <$> cs)

      getChild : {𝔠 : TermCode} → (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode
      getChild {𝔠} (record { children = [] ; number = number₁ }) ()
      getChild {._} (record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }) (here .(map fst children₁)) = snd₁
      getChild {𝔠} (𝔫@record { children = x ∷ children₁ ; number = number₁ }) (there .(fst x) x₁) = getChild record 𝔫 { children = children₁ } x₁

      addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∉ 𝔫 → TermNode → TermNode
      addChild {𝔠} 𝔫 𝔠∉𝔫 𝔫' =
        record 𝔫 { children = (𝔠 , 𝔫') ∷ children 𝔫 }

      setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode → TermNode
      setChild {𝔠} record { children = [] ; number = number₁ } () 𝔫'
      setChild 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (here .(map fst children₁)) 𝔫' =
        record 𝔫 { children = ((fst₁ , 𝔫') ∷ children₁) }
      setChild {𝔠} 𝔫@record { children = (x ∷ children₁) ; number = number₁ } (there .(fst x) 𝔠∈𝔫) 𝔫' =
        record 𝔫 { children = (x ∷ children (setChild (record 𝔫 { children = children₁ }) 𝔠∈𝔫 𝔫')) }

      storeTermCodes : List TermCode → Nat → StateT TermNode Identity Nat
      storeTermCodes [] 𝔑 = return 𝔑
      storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
        𝔫 ← get -|
        case 𝔠 child∈? 𝔫 of λ
        { (no 𝔠∉tests) →
          let 𝔑' , 𝔫' = runIdentity $
                        runStateT
                          (storeTermCodes 𝔠s $ suc 𝔑)
                          (record
                            { children = []
                            ; number = suc 𝔑 }) in
          put ((addChild 𝔫 𝔠∉tests 𝔫')) ~|
          return 𝔑'
        ; (yes 𝔠∈tests) →
          let 𝔑' , 𝔫' = runIdentity $
                        runStateT
                          (storeTermCodes 𝔠s $ suc 𝔑)
                          ((getChild 𝔫 𝔠∈tests)) in
          put ((setChild 𝔫 𝔠∈tests 𝔫')) ~|
          return 𝔑' }

      storeTermCodes' : List TermCode → StateT Nat (StateT TermNode Identity) ⊤
      storeTermCodes' 𝔠s =
        𝔑 ← get -|
        tn ← lift get -|
        (let 𝔑' , tn' = runIdentity $ runStateT (storeTermCodes 𝔠s 𝔑) tn in
         put 𝔑' ~| lift (put tn') ~| return tt)

      mutual

        storeTerm : Term → StateT Nat (StateT TermNode Identity) ⊤
        storeTerm τ@(variable _) = storeTermCodes' (encodeTerm τ)
        storeTerm τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTerms τs

        storeTerms : Terms → StateT Nat (StateT TermNode Identity) ⊤
        storeTerms ⟨ [] ⟩ = return tt
        storeTerms ⟨ τ ∷ τs ⟩ = storeTerm τ ~| storeTerms ⟨ τs ⟩ ~| return tt

      module ExampleStoreTerm where
        example-Term₁ : Term
        example-Term₁ =
          (function ⟨ 2 ⟩
                    ⟨ variable ⟨ 0 ⟩
                    ∷ function ⟨ 3 ⟩
                               ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩
                    ∷ variable ⟨ 5 ⟩
                    ∷ []
                    ⟩
          )

        example-Term₂ : Term
        example-Term₂ =
          (function ⟨ 2 ⟩
                    ⟨ variable ⟨ 0 ⟩
                    ∷ variable ⟨ 2 ⟩
                    ∷ function ⟨ 3 ⟩
                               ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩
                    ∷ variable ⟨ 5 ⟩
                    ∷ []
                    ⟩
          )

        topNode : TermNode
        topNode = record { children = [] ; number = 0 }

        example-storeTerm : (⊤ × Nat) × TermNode
        example-storeTerm = {!runIdentity $ runStateT (runStateT (storeTerm example-Term₁ >> storeTerm example-Term₂) 0) topNode!}

      NodeStateT = StateT TermNode
      TopNodeState = StateT Nat (NodeStateT Identity)

      storeLiteralFormulaTerms : LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤
      storeLiteralFormulaTerms ⟨ atomic 𝑃 τs ⟩ = storeTerms τs
      storeLiteralFormulaTerms ⟨ logical 𝑃 τs ⟩ = storeTerms τs

      sequence : ∀ {a b} {A : Set a} {F : Set a → Set b} ⦃ _ : Applicative F ⦄ → List (F A) → F ⊤′
      sequence [] = pure tt
      sequence (x ∷ xs) = x *> sequence xs

      storeSequentLiteralFormulaTerms : Sequent LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤′
      storeSequentLiteralFormulaTerms (φᵗ ╱ φˢs) = sequence $ storeLiteralFormulaTerms <$> (φᵗ ∷ φˢs)

      record FindTermNode (A : Set) : Set
       where
        field
          findTermNode : A → TermNode → Maybe TermNode

      open FindTermNode ⦃ … ⦄

      instance
        FindTermNodeTermCode : FindTermNode TermCode
        FindTermNode.findTermNode FindTermNodeTermCode termCode record { children = [] ; number = number₁ } = nothing
        FindTermNode.findTermNode FindTermNodeTermCode termCode 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } = ifYes fst₁ ≟ termCode then just snd₁ else findTermNode termCode record 𝔫 { children = children₁ }

        FindTermNodeTermCodes : FindTermNode (List TermCode)
        FindTermNode.findTermNode FindTermNodeTermCodes [] node = just node
        FindTermNode.findTermNode FindTermNodeTermCodes (x ∷ termCodes) node = join $ findTermNode termCodes <$> findTermNode x node

        FindTermNodeTerm : FindTermNode Term
        FindTermNode.findTermNode FindTermNodeTerm term node = findTermNode (encodeTerm term) node

      -- This is starting to get difficult. We need Agda to know that the Term is encoded in the TermNode. Then we can drop the Maybe
      getInterpretationOfTerm : Term → TermNode → Maybe Element
      getInterpretationOfTerm τ node = number <$> findTermNode (encodeTerm τ) node

      mutual

        storeTermVerifiably' : (τ : Term) → StateT Nat (StateT (Σ TermNode λ n → IsJust (findTermNode τ n)) Identity) ⊤
        storeTermVerifiably' (variable x) = {!!}
        storeTermVerifiably' (function x x₁) = {!!}

        storeTermVerifiably : Term → StateT Nat (StateT TermNode Identity) ⊤
        storeTermVerifiably τ@(variable _) = storeTermCodes' (encodeTerm τ)
        storeTermVerifiably τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTermsVerifiably τs

        storeTermsVerifiably : Terms → StateT Nat (StateT TermNode Identity) ⊤
        storeTermsVerifiably ⟨ [] ⟩ = return tt
        storeTermsVerifiably ⟨ τ ∷ τs ⟩ = storeTermVerifiably τ ~| storeTermsVerifiably ⟨ τs ⟩ ~| return tt



      foo : {!!}
      foo = {!sequence (storeSequentLiteralFormulaTerms <$> (ι ∷ χs)) !}

  Theorem1b : ▷ Φ → ⊨ Φ
  Theorem1b = {!!}

-- -- -- -- negationEliminationRule : (I : Interpretation) (φ : Formula) → I ⊨ ~ (~ φ) → I ⊨ φ
-- -- -- -- negationEliminationRule I φ (¬[I⊭φ×I⊭φ] , _) with I ⊨? φ
-- -- -- -- … | yes I⊨φ = I⊨φ
-- -- -- -- … | no I⊭φ = ⊥-elim $ ¬[I⊭φ×I⊭φ] $ I⊭φ , I⊭φ

-- -- -- -- -- -- justifieds simplification and
-- -- -- -- -- simplificationRule₁ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ logical φ₁ φ₂ → I ⊨ logical φ₁ φ₁
-- -- -- -- -- simplificationRule₁ I φ₁ φ₂ x = (fst x) , (fst x)

-- -- -- -- -- simplificationRule₂ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ logical φ₁ φ₂ → I ⊨ logical φ₂ φ₂
-- -- -- -- -- simplificationRule₂ I φ₁ φ₂ x = snd x , snd x

-- -- -- -- -- -- logical (logical (logical p p) q) (logical (logical p p) q)
-- -- -- -- -- conditionalization : (I : Interpretation) (p q : Formula) → I ⊨ q → I ⊨ ((p ∷ []) ⊢ p ⊃ q)
-- -- -- -- -- conditionalization I p q ⊨q -⊨p = let ⊨p = -⊨p p (here []) in (λ { (x , ~q) → ~q ⊨q}) , (λ { (x , y) → y ⊨q})

-- -- -- -- -- modusPonens : (I : Interpretation) (p q : Formula) → I ⊨ p → I ⊨ ((p ⊗ p) ⊗ q) ⊗ ((p ⊗ p) ⊗ q) → I ⊨ q
-- -- -- -- -- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) with I ⊨? q
-- -- -- -- -- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | yes x = x
-- -- -- -- -- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | no x = ⊥-elim (~[~p&~p&~q] ((λ { (x₁ , y) → y P}) , (λ x₁ → x x₁)))

-- -- -- -- -- data SkolemFormula {ι : Size} (α : Alphabet) : Set where
-- -- -- -- --   atomic : Predication α → SkolemFormula α
-- -- -- -- --   logical : {ι¹ : Size< ι} → SkolemFormula {ι¹} α → {ι² : Size< ι} → SkolemFormula {ι²} α → SkolemFormula {ι} α

-- -- -- -- -- record Alphabet₊ᵥ (α : Alphabet) : Set where
-- -- -- -- --   constructor α₊ᵥ⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     alphabet : Alphabet
-- -- -- -- --     .one-variable-is-added : (number ∘ variables $ alphabet) ≡ suc (number ∘ variables $ α)
-- -- -- -- --     .there-are-no-functions-of-maximal-arity : number (functions alphabet) zero ≡ zero
-- -- -- -- --     .shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → number (functions alphabet) (suc ytira₁) ≡ number (functions α) ytira₀
-- -- -- -- -- open Alphabet₊ᵥ

-- -- -- -- -- record Alphabet₊ₛ (α : Alphabet) : Set where
-- -- -- -- --   constructor α₊ₛ⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- open Alphabet₊ₛ

-- -- -- -- -- {-
-- -- -- -- --   toSkolemFormula
-- -- -- -- --   ∀x(F x v₀ v₁) ⟿ F v₀ v₁ v₂
-- -- -- -- --   ∃x(F x v₀ v₁) ⟿ F (s₀͍₂ v₀ v₁) v₀ v₁
-- -- -- -- --   ∀x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F v₀ (s₀͍₂ v₁ v₂) v₂
-- -- -- -- --   ∃x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F (s₀͍₂ v₀ v₁) (s₁͍₂ v₁ v₂) v₂
-- -- -- -- --   F v₀ ⊗ G v₀ ⟿ F v₀ ⊗ G v₀
-- -- -- -- --   ∀x(F x v₀ v₁) ⊗ ∀x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₂ v₃ ⊗ G v₁ (s₀͍₂ v₀ v₃) v₃

-- -- -- -- --   ∀x(F x v₀ v₁) ⊗ ∃x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₁ v₂ ⊗ G (s₀͍₁ v₂) (s₁͍₂ (s₀͍₂ v₂) v₂) v₂

-- -- -- -- --   Φ₀ = ∃x(G x (s₀͍₂ x v₁) v₁) has alphabet of 2 variables, skolem functions: 0, 0, 1
-- -- -- -- --   this is existential {α₊ₛ} Φ₁, where
-- -- -- -- --     Φ₁ = G (s₀͍₂ v₀ v₁) (s₁͍₂ (s₀͍₂ v₀ v₁)) v₁
-- -- -- -- --     α₊ₛ = ⟨ 2 , 0 ∷ 0 ∷ 2 ∷ [] ⟩

-- -- -- -- --   maybe Φ₋₁ = ∀y∃x(G x (s₀͍₂ x v₀) v₀)
-- -- -- -- --    and  Φ₋₂ = ∀z∀y∃x(G x (s₀͍₂ x z) z), finally having no free variables, but nevertheless having skolem functions! these are user-defined functions, so this notion of Alphabet is somehow wrong. we have also left out constants (i.e. user-defined skolem-functions of arity 0)

-- -- -- -- --   Instead, take the alphabet as defining
-- -- -- -- --     a stack of free variables
-- -- -- -- --     a matrix (triangle?) of skolem functions

-- -- -- -- --   Let's try to reverse Φ₁ from a Skolem to a 1st-order formula. Is there a unique way to do it?
-- -- -- -- --   Φ₀' = ∀x(G (s₀͍₂ x v₀) (s₁͍₂ (s₀͍₂ x v₀)) v₀

-- -- -- -- --   Nope!


-- -- -- -- --   toSkolemFormula of



-- -- -- -- -- -}

-- -- -- -- -- -- toSkolemFormula (logical Φ₁ Φ₂) ⟿
-- -- -- -- -- --   let α' , φ₁ = toSkolemFormula Φ₁
-- -- -- -- -- --       Φ₂' = transcodeToAugmentedAlphabet Φ₂ α'
-- -- -- -- -- --       α'' , φ₂' = toSkolemFormula Φ₂'
-- -- -- -- -- --       φ₁' = transcodeToAugmentedAlphabet φ₁ α''

-- -- -- -- -- {-
-- -- -- -- -- given Δv = #varibles α' - #variables α
-- -- -- -- -- for every variable v in α, v in Φ, v stays the same in Φ'
-- -- -- -- -- for the added variable v⁺ in α₊ - α, v⁺ in Φ, v⁺ ⟿ v⁺ + Δv in transcode (universal {α₊} Φ)
-- -- -- -- -- α'₊ = α' + 1 variable
-- -- -- -- -- -}

-- -- -- -- -- -- record AddVariable (A : Alphabet → Set) : Set where
-- -- -- -- -- --   field
-- -- -- -- -- --     addVariableToAlphabet : {α : Alphabet} → A α → {α₊ : Alphabet} → Alphabet₊ᵥ α₊ → A α₊

-- -- -- -- -- -- instance
-- -- -- -- -- --   AddVariableFirstOrderFormula : AddVariable FirstOrderFormula
-- -- -- -- -- --   AddVariableFirstOrderFormula = {!!}

-- -- -- -- -- -- #variables = number ∘ variables

-- -- -- -- -- -- #functions_ofArity_ : Alphabet → Nat → Nat
-- -- -- -- -- -- #functions α⟨ V⟨ #variables ⟩ , S⟨ #functions ⟩ ⟩ ofArity arity = if′ lessNat arity (suc #variables) then #functions (natToFin arity) else 0

-- -- -- -- -- -- record _⊇_ (α' α : Alphabet) : Set where
-- -- -- -- -- --   field
-- -- -- -- -- --     at-least-as-many-variables : #variables α' ≥ #variables α
-- -- -- -- -- --     at-least-as-many-functions : ∀ {arity} → arity < #variables α → #functions α' ofArity arity ≥ #functions α ofArity arity

-- -- -- -- -- -- record AddAlphabet (α-top α-bottom : Alphabet) : Set where
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet

-- -- -- -- -- -- record Transcodeable (A : Alphabet → Set) : Set where
-- -- -- -- -- --   field
-- -- -- -- -- --     transcode : {α' α : Alphabet} → ⦃ _ : α' ⊇ α ⦄ → A α → A α'

-- -- -- -- -- -- open Transcodeable ⦃ … ⦄

-- -- -- -- -- -- record TransferAlphabet {α' α : Alphabet} (α'⊇α : α' ⊇ α) (α₊ : Alphabet₊ᵥ α) (Φ : FirstOrderFormula (alphabet α₊)) : Set where
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- --     firstOrderFormula : FirstOrderFormula alphabet


-- -- -- -- -- -- instance
-- -- -- -- -- --   TranscodeablePredication : Transcodeable Predication
-- -- -- -- -- --   TranscodeablePredication = {!!}

-- -- -- -- -- --   TranscodeableAlphabet+Variable : Transcodeable Alphabet₊ᵥ
-- -- -- -- -- --   TranscodeableAlphabet+Variable = {!!}

-- -- -- -- -- --   TranscodeableSkolemFormula : Transcodeable SkolemFormula
-- -- -- -- -- --   TranscodeableSkolemFormula = {!!}

-- -- -- -- -- --   TranscodeableFirstOrderFormula : Transcodeable FirstOrderFormula
-- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (atomic p) = atomic (transcode p)
-- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (logical Φ₁ Φ₂) = logical (transcode Φ₁) (transcode Φ₂)
-- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula {α'} {α} ⦃ α'⊇α ⦄ (universal {α₊} Φ) = {!!} -- universal {_} {_} {transcode α₊} (transcode Φ)

-- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (existential Φ) = {!!}

-- -- -- -- -- -- --(α' α : Alphabet) (α'⊇α : α' ⊇ α) (α₊ : Alphabet+Variable α) (Φ : FirstOrderFormula (alphabet α₊)) → Σ _ λ (α''' : Alphabet) → FirstOrderFormula α'''

-- -- -- -- -- -- --FirstOrderFormula (alphabet α₊)
-- -- -- -- -- -- {-
-- -- -- -- -- -- -}

-- -- -- -- -- -- -- --transcodeIntoAugmentedAlphabet :



-- -- -- -- -- -- -- --toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)

-- -- -- -- -- -- -- --record IsEquivalentFormulas {α₀ : Alphabet} (φ₀ : SkolemFormula α₀) {α₁ : Alphabet} (Φ₁ : FirstOrderFormula α₁) : Set where
-- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- --    .atomicCase : {p : Predication α₀} → φ₀ ≡ atomic p → Φ₁ ≡ atomic p




-- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- record Alphabet+Alphabet (α₀ α₁ α₂ : Alphabet) : Set where
-- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- --     alphabet :

-- -- -- -- -- -- -- -- -- ∀xφ₁(x) ⊗ φ₂ ⟿ ∀x(φ₁ ⊗ φ₂)

-- -- -- -- -- -- -- -- -- hasQuantifiers : FirstOrderFormula α → Bool

-- -- -- -- -- -- -- -- --record Skolemization {α : Alphabet} (φ : FirstOrderFormula α) : Set where
-- -- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- -- --    alphabet : Alphabet
-- -- -- -- -- -- -- -- --    skolemization : SkolemFormula alphabet

-- -- -- -- -- -- -- -- record _IsAugmentationOf_ (α₁ α₀ : Alphabet) : Set where

-- -- -- -- -- -- -- -- record AugmentedAlphabet (α : Alphabet) : Set where
-- -- -- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- -- --     ..laws : alphabet ≡ α
-- -- -- -- -- -- -- -- open AugmentedAlphabet

-- -- -- -- -- -- -- -- trivialAugmentation : (α : Alphabet) → AugmentedAlphabet α
-- -- -- -- -- -- -- -- trivialAugmentation = {!!}

-- -- -- -- -- -- -- -- record DisjointRelativeUnion {α : Alphabet} (α¹ α² : AugmentedAlphabet α) : Set where
-- -- -- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     augmentation : AugmentedAlphabet α
-- -- -- -- -- -- -- --     .laws : {!!}
-- -- -- -- -- -- -- -- open DisjointRelativeUnion

-- -- -- -- -- -- -- -- disjointRelativeUnion : {α : Alphabet} → (α¹ α² : AugmentedAlphabet α) → DisjointRelativeUnion α¹ α²
-- -- -- -- -- -- -- -- disjointRelativeUnion = {!!}

-- -- -- -- -- -- -- -- -- inAugmentedAlphabet : {α : Alphabet} → (α¹ : AugmentedAlphabet α) → SkolemFormula α → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- -- -- inAugmentedAlphabet = {!!}

-- -- -- -- -- -- -- -- -- toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (atomic 𝑃) = trivialAugmentation α₀ , atomic 𝑃
-- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) with toSkolemFormula φ₁ | toSkolemFormula φ₂
-- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) | α¹ , Φ₁ | α² , Φ₂ = augmentation (disjointRelativeUnion α¹ α²) , logical {!inAugmentedAlphabet (augmentation (disjointRelativeUnion α¹ α²)) Φ₁!} {!Φ₂!}
-- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (universal x) = {!!}
-- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (existential x) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- --FunctionArity = Fin ∘ suc ∘ size
-- -- -- -- -- -- -- -- -- -- -- -- --FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     |v| : Nat -- number of variables
-- -- -- -- -- -- -- -- -- -- -- -- --     |f| : Fin (suc |v|) → Nat -- number of functions of each arity, |v| through 0

-- -- -- -- -- -- -- -- -- -- -- -- -- open Alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- FunctionArity = Fin ∘ suc ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   variable : VariableName alphabet → Term alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {arity : FunctionArity alphabet} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              FunctionName alphabet (natToFin (|v| alphabet) - arity) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∀ {j : Size< i} → Vec (Term {j} alphabet) (finToNat arity) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Term {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PredicateArity = Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PredicateName = Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a zeroth-order formula? (i.e. no quantifiers)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data NQFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → NQFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → NQFormula {j} alphabet → {k : Size< i} → NQFormula {k} alphabet → NQFormula {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedByVariable (alphabet₀ alphabet₁ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     one-variable-is-added : |v| alphabet₁ ≡ suc (|v| alphabet₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     function-domain-is-zero-at-new-variable : |f| alphabet₁ zero ≡ 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → |f| alphabet₁ (suc ytira₁) ≡ |f| alphabet₀ ytira₀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentVariables (alphabet₀ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     alphabet₁ : Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     augmentation : AugmentedByVariable alphabet₀ alphabet₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open AugmentVariables

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : (alphabet : Alphabet) → AugmentVariables alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables ⟨ |v| , |f| ⟩ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   { alphabet₁ = ⟨ suc |v| , (λ { zero → zero ; (suc ytira) → |f| ytira}) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ; augmentation =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     { one-variable-is-added = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; function-domain-is-zero-at-new-variable = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; shifted-function-matches = cong |f| ∘ finToNat-inj } }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- |f|₀ = |f|₀ + 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions ⟨ |v| , |f| ⟩ = ⟨ |v| , (λ { zero → suc (|f| zero) ; (suc ytira) → |f| (suc ytira) }) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data QFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → QFormula {j} alphabet → {k : Size< i} → QFormula {k} alphabet → QFormula {i} alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   universal : QFormula (alphabet₁ (augmentVariables alphabet)) → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   existential : QFormula (augmentFunctions alphabet) → QFormula alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Assignment (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     μ : VariableName alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑓 : ∀ {arity} → FunctionName alphabet arity → Vec Domain (finToNat arity) → Domain

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm : ∀ {i alphabet} → Assignment alphabet → Term {i} alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm ⟨ μ , _ ⟩ (variable x) = μ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm 𝑎@(⟨ μ , 𝑓 ⟩) (function f x) = 𝑓 f (evaluateTerm 𝑎 <$> x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Interpretation (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Assignment
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑎 : Assignment alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑃 : PredicateName → ∀ {arity} → Vec Domain arity → Bool

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula : ∀ {i alphabet} → Interpretation alphabet → NQFormula {i} alphabet → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula ⟨ 𝑎 , 𝑃 ⟩ (atomic name terms) = 𝑃 name $ evaluateTerm 𝑎 <$> terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula I (logical formula₁ formula₂) = not (evaluateNQFormula I formula₁) && not (evaluateNQFormula I formula₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record IsADisjointUnionOfNQFormulas
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {alphabet₁ alphabet₂ alphabet₁₊₂ : Alphabet}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁ : NQFormula alphabet₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₂ : NQFormula alphabet₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁₊₂ : NQFormula alphabet₁₊₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     alphabet-size : |v| alphabet₁₊₂ ≡ |v| alphabet₁ + |v| alphabet₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --|f| alphabet₁₊₂ ytira


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ----record AlphabetSummed  (alphabet₀ alphabet₁ : Alphabet)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets : Alphabet → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets ⟨ |v|₁ , |f|₁ ⟩ ⟨ |v|₂ , |f|₂ ⟩ = ⟨ (|v|₁ + |v|₂) , (λ x → if′ finToNat x ≤? |v|₁ && finToNat x ≤? |v|₂ then {!!} else {!!}) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sup : ∀ {alphabet₁} → Formula alphabet₁ → ∀ {alphabet₂} → Formula alphabet₂ → Σ _ λ alphabet₁₊₂ → Formula alphabet₁₊₂ × Formula alphabet₁₊₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sup {⟨ |v|₁ , |a|₁ , |f|₁ ⟩} φ₁ {⟨ |v|₂ , |a|₂ , |f|₂ ⟩} φ₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf : ∀ {alphabet} → Formula alphabet → Σ _ λ alphabet+ → Formula₀ alphabet+
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --universal (P 0) = ∀ x → P x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (∀ x ∃ y (P x y)) ∨ (∀ x ∃ y (P x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- P x₀ (s₀͍₁ x₀) ∨ P x₁ (s₁͍₁ x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| : (arity : Arity) → Vec ℕ (suc |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a variable to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN : ∀ {n} → Fin n → (Fin n → Nat) → Fin n → Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedFunctions {|a| : Arity} (arity : Arity) (|f| : Vec ℕ (++arity |a|)) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA : ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA-law : max arity |a| ≡ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ++|f| : Vec ℕ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f-law : increaseTabulationAt arity (indexVec |f|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ⊗ b ≡ False a and False b

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- now, we can define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ¬a = a ⊗ a ≡ False a and False a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∨ b = ¬(a ⊗ b) ≡ False (False a and False b) and False (False a and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∧ b = ¬(¬a ∨ ¬b) = ¬(¬(¬a ⊗ ¬b)) = ¬a ⊗ ¬b = False (False a and False a) and False (False b and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a → b = ¬a ∨ b = (a ⊗ a) ∨ b = ¬((a ⊗ a) ⊗ b) = ((a ⊗ a) ⊗ b) ⊗ ((a ⊗ a) ⊗ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- conversion to prenex
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∀xF ⊗ G ⟿ ∃x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∃xF ⊗ G ⟿ ∀x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∀xG ⟿ ∃x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∃xG ⟿ ∀x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ========================
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (a ⊗ ∀xB) ⊗ c ⟿ ∃x(wk(a) ⊗ B) ⊗ c ⟿ ∀x((wk(a) ⊗ B) ⊗ wk(c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF : (arity : Arity) → ∀ {|a| : Arity} → Vec ℕ (++arity |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  with decBool (lessNat |a| arity)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x with compare arity |a|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.(suc (k + arity))} |f| | yes x | less (diff k refl) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl with lessNat arity arity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl | false = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF zero {.zero} |f| | yes true | equal refl | true = {!!} ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF (suc arity) {.(suc arity)} |f| | yes true | equal refl | true = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x | greater gt = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x with decBool (lessNat arity |a|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | yes x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | no x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- = case arity <? |a| of λ { false → {!!} ; true → {!!} }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a function of a given arity to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Arity → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions arity ⟨ |v| , |a| , |f| ⟩ = ⟨ |v| , max arity |a| , augmentF arity |f| ⟩


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data DomainSignifier : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   free : Nat → DomainSignifier

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartiallyAppliedFunction : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constant : PartiallyAppliedFunction 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {n} → PartiallyAppliedFunction 0 → PartiallyAppliedFunction (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Term = PartiallyAppliedFunction 0

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartialyAppliedPredicate : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   statement : PartialyAppliedPredicate 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   partial : ∀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Language : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Name = String

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Function : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     name : Name
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     number-of-arguments : Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Vec

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Function : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : Function →

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Sentence : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   predication : Name →

-- -- -- -- -- {-

-- -- -- -- -- record Variables : Set where
-- -- -- -- --   constructor V⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     number : Nat
-- -- -- -- -- open Variables

-- -- -- -- -- record Functions (υ : Variables) : Set where
-- -- -- -- --   constructor S⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     number : Fin (suc (number υ)) → Nat
-- -- -- -- -- open Functions

-- -- -- -- -- record Alphabet : Set where
-- -- -- -- --   constructor α⟨_,_⟩
-- -- -- -- --   field
-- -- -- -- --     variables : Variables
-- -- -- -- --     functions : Functions variables
-- -- -- -- -- open Alphabet

-- -- -- -- -- record Variable (α : Alphabet) : Set where
-- -- -- -- --   constructor v⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     name : Fin (number (variables α))
-- -- -- -- -- open Variable

-- -- -- -- -- record Function (α : Alphabet) : Set where
-- -- -- -- --   constructor s⟨_,_⟩
-- -- -- -- --   field
-- -- -- -- --     arity : Fin ∘ suc ∘ number ∘ variables $ α
-- -- -- -- --     name : Fin $ number (functions α) arity
-- -- -- -- -- open Function

-- -- -- -- -- data Term (𝑽 : Nat) : Set where
-- -- -- -- --   variable : Fin 𝑽 → Term 𝑽
-- -- -- -- --   function : (𝑓 : Function α) → {ι₋₁ : Size< ι₀} → Vec (Term {ι₋₁} α) (finToNat (arity 𝑓)) →
-- -- -- -- --              Term {ι₀} α

-- -- -- -- -- record Predication (alphabet : Alphabet) : Set where
-- -- -- -- --   constructor P⟨_,_,_⟩
-- -- -- -- --   field
-- -- -- -- --     name : Nat
-- -- -- -- --     arity : Nat
-- -- -- -- --     terms : Vec (Term alphabet) arity
-- -- -- -- -- open Predication
-- -- -- -- -- -}


-- module NotUsed where

--   -- thought it might be easier to use this
--   module UsingContainerList where

--     record TermNode : Set
--      where
--       inductive
--       field
--         children : List (TermCode × TermNode)
--         number : Nat

--     open TermNode

--     _child∈_ : TermCode → TermNode → Set
--     _child∈_ 𝔠 𝔫 = Any ((𝔠 ≡_) ∘ fst) (children 𝔫)

--   -- this still has a lambda problem, albeit weirder
--   module RememberChildren where

--     record TermNode : Set
--      where
--       inductive
--       field
--         tests : List TermCode
--         children : ∀ {𝔠} → 𝔠 ∈ tests → TermNode
--         number : Nat
--     open TermNode

--     addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 ∉ tests 𝔫 → TermNode → TermNode
--     addChild {𝔠} 𝔫 𝔠∉tests𝔫 𝔫' =
--       record 𝔫
--       { tests = 𝔠 ∷ tests 𝔫
--       ; children = λ
--         { (here _) → 𝔫'
--         ; (there _ 𝔠'∈tests) → children 𝔫 𝔠'∈tests }}

--     setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 ∈ tests 𝔫 → TermNode → TermNode
--     setChild {𝔠} 𝔫 𝔠∈tests𝔫 𝔫' =
--       record 𝔫
--       { children = λ {𝔠'} 𝔠'∈tests𝔫' → ifYes 𝔠' ≟ 𝔠 then 𝔫' else children 𝔫 𝔠'∈tests𝔫' }

--     storeTermCodes : List TermCode → Nat → StateT TermNode Identity Nat
--     storeTermCodes [] 𝔑 = return 𝔑
--     storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
--       𝔫 ← get -|
--       case 𝔠 ∈? tests 𝔫 of λ
--       { (no 𝔠∉tests) →
--         let 𝔑' , 𝔫' = runIdentity $
--                       runStateT
--                         (storeTermCodes 𝔠s $ suc 𝔑)
--                         (record
--                           { tests = []
--                           ; children = λ ()
--                           ; number = suc 𝔑 }) in
--         put (addChild 𝔫 𝔠∉tests 𝔫') ~|
--         return 𝔑'
--       ; (yes 𝔠∈tests) →
--         let 𝔑' , 𝔫' = runIdentity $
--                       runStateT
--                         (storeTermCodes 𝔠s $ suc 𝔑)
--                         (children 𝔫 𝔠∈tests) in
--         put (setChild 𝔫 𝔠∈tests 𝔫') ~|
--         return 𝔑' }

--     topNode : TermNode
--     topNode = record { tests = [] ; children = λ () ; number = 0 }

--     example-store : TermNode
--     example-store = snd ∘ runIdentity $ runStateT (storeTermCodes example-TermCodes 0) topNode

--     foo : TermNode × TermNode
--     foo =
--       {!example-store!} ,
--       {!snd ∘ runIdentity $ runStateT (storeTermCodes example-TermCodes 10) example-store!}

--   -- using a lambda for the children results in extra unnecessary structure when adding to an existing node; perhaps using an explicit mapping? or use another field to state what codes are present in the mapping?
--   module NoParents where

--     mutual

--       record TermNode : Set
--        where
--         inductive
--         field
--           children : TermCode → Maybe TermNode -- Map TermCode TermNode
--           self : TermCode
--           number : Nat

--       record TopTermNode : Set
--        where
--         inductive
--         field
--           children : TermCode → Maybe TermNode

--     open TermNode
--     open TopTermNode

--     storeTermCodes : List TermCode → Nat → StateT TermNode Identity ⊤
--     storeTermCodes [] _ = return tt
--     storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
--       𝔫 ← get -|
--       case children 𝔫 𝔠 of λ
--       { nothing →
--         put
--           (record 𝔫
--             { children =
--               λ 𝔠' →
--               ifYes 𝔠' ≟ 𝔠 then
--                 just ∘ snd ∘ runIdentity $
--                 (runStateT
--                   (storeTermCodes 𝔠s (suc 𝔑))
--                     (record
--                       { self = 𝔠
--                       ; children = const nothing
--                       ; number = suc 𝔑 }))
--               else
--                 children 𝔫 𝔠' } ) ~|
--         return tt
--       ; (just 𝔫') →
--         put (record 𝔫
--               { children =
--                 λ 𝔠' →
--                 ifYes 𝔠' ≟ 𝔠 then
--                   just ∘ snd ∘ runIdentity $
--                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
--                 else
--                   children 𝔫 𝔠' }) ~|
--         return tt }

--     storeTermCodesAtTop : List TermCode → Nat → StateT TopTermNode Identity ⊤
--     storeTermCodesAtTop [] _ = return tt
--     storeTermCodesAtTop (𝔠 ∷ 𝔠s) 𝔑 =
--       𝔫 ← get -|
--       case children 𝔫 𝔠 of λ
--       { nothing →
--         put
--           (record 𝔫
--             { children =
--               λ 𝔠' →
--               ifYes 𝔠' ≟ 𝔠 then
--                 just ∘ snd ∘ runIdentity $
--                 (runStateT
--                   (storeTermCodes 𝔠s (suc 𝔑))
--                     (record
--                       { self = 𝔠
--                       ; children = const nothing
--                       ; number = suc 𝔑 }))
--               else
--                 children 𝔫 𝔠' } ) ~|
--         return tt
--       ; (just 𝔫') →
--         put (record 𝔫
--               { children =
--                 λ 𝔠' →
--                 ifYes 𝔠' ≟ 𝔠 then
--                   just ∘ snd ∘ runIdentity $
--                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
--                 else
--                   children 𝔫 𝔠' }) ~|
--         return tt }

--     initialTopNode : TopTermNode
--     initialTopNode = record { children = const nothing }

--     example-store : TopTermNode
--     example-store = snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 0) initialTopNode

--     foo : TopTermNode × TopTermNode
--     foo =
--       {!example-store!} ,
--       {!snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 10) example-store!}

--   -- it's tricky to keep the parents up to date when the children change (viz adolescence)
--   module FirstTryWithParent where
--     mutual

--       record TermNode : Set
--        where
--         inductive
--         field
--           parent : TopTermNode ⊎ TermNode
--           self : TermCode
--           children : TermCode → Maybe TermNode -- Map TermCode TermNode
--           number : Nat

--       record TopTermNode : Set
--        where
--         inductive
--         field
--           children : TermCode → Maybe TermNode

--     open TermNode
--     open TopTermNode

--     storeTermCodes : List TermCode → Nat → StateT TermNode Identity ⊤
--     storeTermCodes [] _ = return tt
--     storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
--       𝔫 ← get -|
--       case children 𝔫 𝔠 of λ
--       { nothing →
--         put
--           (record 𝔫
--             { children =
--               λ 𝔠' →
--               ifYes 𝔠' ≟ 𝔠 then
--                 just ∘ snd ∘ runIdentity $
--                 (runStateT
--                   (storeTermCodes 𝔠s (suc 𝔑))
--                     (record
--                       { parent = right 𝔫
--                       ; self = 𝔠
--                       ; children = const nothing
--                       ; number = suc 𝔑 }))
--               else
--                 children 𝔫 𝔠' } ) ~|
--         return tt
--       ; (just 𝔫') →
--         put (record 𝔫
--               { children =
--                 λ 𝔠' →
--                 ifYes 𝔠' ≟ 𝔠 then
--                   just ∘ snd ∘ runIdentity $
--                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
--                 else
--                   children 𝔫 𝔠' }) ~|
--         return tt }

--     storeTermCodesAtTop : List TermCode → Nat → StateT TopTermNode Identity ⊤
--     storeTermCodesAtTop [] _ = return tt
--     storeTermCodesAtTop (𝔠 ∷ 𝔠s) 𝔑 =
--       𝔫 ← get -|
--       case children 𝔫 𝔠 of λ
--       { nothing →
--         put
--           (record 𝔫
--             { children =
--               λ 𝔠' →
--               ifYes 𝔠' ≟ 𝔠 then
--                 just ∘ snd ∘ runIdentity $
--                 (runStateT
--                   (storeTermCodes 𝔠s (suc 𝔑))
--                     (record
--                       { parent = left 𝔫
--                       ; self = 𝔠
--                       ; children = const nothing
--                       ; number = suc 𝔑 }))
--               else
--                 children 𝔫 𝔠' } ) ~|
--         return tt
--       ; (just 𝔫') →
--         put (record 𝔫
--               { children =
--                 λ 𝔠' →
--                 ifYes 𝔠' ≟ 𝔠 then
--                   just ∘ snd ∘ runIdentity $
--                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
--                 else
--                   children 𝔫 𝔠' }) ~|
--         return tt }

--     initialTopNode : TopTermNode
--     initialTopNode = record { children = const nothing }

--     example-store : TopTermNode
--     example-store = snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 0) initialTopNode

--     foo : TopTermNode
--     foo = {!example-store!}

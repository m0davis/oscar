module NaturalDeduction
 where

module _ where

  open import Prelude public
    renaming (_==_ to _≟_) -- TODO ask Agda to rename Eq._==_ to Eq._≟_

  data _∈_ {ℓ} {A : Set ℓ} (a : A) : List A → Set ℓ
   where
    here : (as : List A) → a ∈ (a ∷ as)
    there : (x : A) {as : List A} → a ∈ as → a ∈ (x ∷ as)

  _⊆_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
  R ⊆ S = ∀ {x} → x ∈ R → x ∈ S

  _≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  x ≢ y = ¬ (x ≡ y)

  infix 0 _↔_
  _↔_ : {ℓ¹ : Level} → Set ℓ¹ → {ℓ² : Level} → Set ℓ² → Set (ℓ¹ ⊔ ℓ²)
  P ↔ Q = (P → Q) × (Q → P)

  ∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃ = Σ _

  ∄ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∄ = ¬_ ∘ ∃

  infixl 4 _⊎_
  _⊎_ = Either

  {-# DISPLAY Either = _⊎_ #-}

open import Agda.Builtin.Size

open import Tactic.Nat

open import Tactic.Deriving.Eq

Element = Nat

record VariableName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

instance
  EqVariableName : Eq VariableName
  Eq._==_ EqVariableName ⟨ x ⟩ ⟨ y ⟩ with x ≟ y
  … | yes x≡y rewrite x≡y = yes refl
  … | no x≢y = no λ { refl → x≢y refl }

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

TruthValue = Bool

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


τ⟦_⟧ : Interpretation → {i : Size} → Term {i} → Element
τ⟦_⟧ I (variable 𝑥) = μ⟦ I ⟧ 𝑥
τ⟦_⟧ I (function 𝑓 {j} τs) = 𝑓⟦ I ⟧ 𝑓 ⟨ τ⟦ I ⟧ <$> terms τs ⟩

data Formula : Set
 where
  atomic : PredicateName → Terms → Formula
  logical : Formula →
            Formula →
            Formula
  quantified : VariableName → Formula → Formula

𝑃[_♭_] : PredicateName → Terms → Formula
𝑃[ 𝑃 ♭ τs ] = atomic 𝑃 τs

{-# DISPLAY atomic 𝑃 τs = 𝑃[ 𝑃 ♭ τs ] #-}

_⊗_ : Formula → Formula → Formula
φ₁ ⊗ φ₂ = logical φ₁ φ₂

{-# DISPLAY logical φ₁ φ₂ = φ₁ ⊗ φ₂ #-}

∀[_♭_] : VariableName → Formula → Formula
∀[ 𝑥 ♭ φ ] = quantified 𝑥 φ

{-# DISPLAY quantified 𝑥 φ = ∀[ 𝑥 ♭ φ ] #-}

record Negation (A : Set) : Set
 where
  field
    ~ : A → A

open Negation ⦃ … ⦄

{-# DISPLAY Negation.~ _ = ~ #-}

instance
  NegationFormula : Negation Formula
  Negation.~ NegationFormula φ = φ ⊗ φ

_∧_ : Formula → Formula → Formula
φ₁ ∧ φ₂ = ~ φ₁ ⊗ ~ φ₂

_∨_ : Formula → Formula → Formula
φ₁ ∨ φ₂ = ~ (φ₁ ⊗ φ₂)

_⊃_ : Formula → Formula → Formula
φ₁ ⊃ φ₂ = ~ φ₁ ∨ φ₂

_⟷_ : Formula → Formula → Formula
φ₁ ⟷ φ₂ = (φ₁ ⊗ (φ₂ ⊗ φ₂)) ⊗ ((φ₁ ⊗ φ₁) ⊗ φ₂) -- TODO check that this is logically equivalent to the more verbose, (φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)

record _≞_/_ (I : Interpretation) (I₀ : Interpretation) (𝑥₀ : VariableName) : Set
 where
  field
    μEquality : {𝑥 : VariableName} → 𝑥 ≢ 𝑥₀ → μ⟦ I ⟧ 𝑥 ≡ μ⟦ I₀ ⟧ 𝑥
    𝑓Equality : (𝑓 : FunctionName) (μs : Elements) → 𝑓⟦ I ⟧ 𝑓 μs ≡ 𝑓⟦ I₀ ⟧ 𝑓 μs
    𝑃Equality : (𝑃 : PredicateName) → (μs : Elements) → 𝑃⟦ I ⟧ 𝑃 μs ≡ 𝑃⟦ I₀ ⟧ 𝑃 μs

record Satisfaction (A : Set) : Set₁
 where
  field
    _⊨_ : Interpretation → A → Set

  postulate _⊨?_ : (I : Interpretation) → (x : A) → Dec (I ⊨ x)

  _⊭_ : Interpretation → A → Set
  _⊭_ I = ¬_ ∘ I ⊨_

open Satisfaction ⦃ … ⦄

{-# DISPLAY Satisfaction._⊨_ _ = _⊨_ #-}
{-# DISPLAY Satisfaction._⊭_ _ = _⊭_ #-}
{-# DISPLAY Satisfaction._⊨?_ _ = _⊨?_ #-}

instance
  SatisfactionList : {A : Set} ⦃ _ : Satisfaction A ⦄ → Satisfaction (List A)
  Satisfaction._⊨_ SatisfactionList I [] = ⊤
  Satisfaction._⊨_ SatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs

instance
  SatisfactionFormula : Satisfaction Formula
  Satisfaction._⊨_ SatisfactionFormula = _⊨φ_
   where
    _⊨φ_ : Interpretation → Formula → Set
    _⊨φ_ I₀ (atomic 𝑃 τs) = 𝑃⟦ I₀ ⟧ 𝑃 ⟨ τ⟦ I₀ ⟧ <$> terms τs ⟩ ≡ true
    _⊨φ_ I₀ (logical φ₁ φ₂) = ¬ I₀ ⊨φ φ₁ × ¬ I₀ ⊨φ φ₂
    _⊨φ_ I₀ (quantified 𝑥₀ φ) = (I : Interpretation) → I ≞ I₀ / 𝑥₀ → I ⊨φ φ
    {-# DISPLAY _⊨φ_ = _⊨_ #-}

infix 15 _╱_
record Sequent (A : Set) : Set
 where
  constructor _╱_
  field
    statement : A
    suppositions : List A

open Sequent

instance
  SatisfactionSequent : {A : Set} → ⦃ _ : Satisfaction A ⦄ → Satisfaction (Sequent A)
  Satisfaction._⊨_ SatisfactionSequent I (φᶠ ╱ φˢs) = I ⊨ φˢs → I ⊨ φᶠ

  NegationSequent : {A : Set} → ⦃ _ : Negation A ⦄ → Negation (Sequent A)
  Negation.~ NegationSequent ( φᶠ ╱ φˢs ) = ~ φᶠ ╱ φˢs

record Validity (A : Set) : Set₁
 where
  field
    ⊨_ : A → Set

  ⊭_ : A → Set
  ⊭_ = ¬_ ∘ ⊨_

open Validity ⦃ … ⦄

instance
  ValidityFormula : Validity Formula
  Validity.⊨_ ValidityFormula φ = (I : Interpretation) → I ⊨ φ

  ValiditySequent : {A : Set} → ⦃ _ : Satisfaction (Sequent A) ⦄ → Validity (Sequent A)
  Validity.⊨_ ValiditySequent Φ = (I : Interpretation) → I ⊨ Φ

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

instance
  EqLiteralFormula : Eq LiteralFormula
  EqLiteralFormula = {!!}

instance
  SatisfactionLiteralFormula : Satisfaction LiteralFormula
  Satisfaction._⊨_ SatisfactionLiteralFormula I φ = I ⊨ formula φ

  ValidityLiteralFormula : Validity LiteralFormula
  Validity.⊨_ ValidityLiteralFormula φ = (I : Interpretation) → I ⊨ formula φ

  NegationLiteralFormula : Negation LiteralFormula
  Negation.~ NegationLiteralFormula ⟨ atomic 𝑃 τs ⟩ = ⟨ logical 𝑃 τs ⟩
  Negation.~ NegationLiteralFormula ⟨ logical 𝑃 τs ⟩ = ⟨ atomic 𝑃 τs ⟩

infix 13 _¶_
record Problem (A : Set) : Set
 where
  constructor _¶_
  field
    inferences : List (Sequent A)
    interest : Sequent A

instance
  ValidityProblem : ∀ {A} → ⦃ _ : Satisfaction A ⦄ → Validity (Problem A)
  Validity.⊨_ ValidityProblem (χs ¶ ι) = (I : Interpretation) → I ⊨ χs → I ⊨ ι

discharges : ∀ {A} → Sequent A → Sequent A → Set
discharges (χᶠ ╱ χˢs) (ιᶠ ╱ ιˢs) = χᶠ ≡ ιᶠ × χˢs ⊆ ιˢs

sequent-fortuitous-reductio : ∀ {A} → Sequent A → Set
sequent-fortuitous-reductio (_ ╱ χˢs) = ? -- ∃ λ s → s ∈ χˢs → ~ s ∈ χˢs

discharged : ∀ {A} → Problem A → Set
discharged (χs ¶ ι) = ∃ λ χ → χ ∈ χs × discharges χ ι

problem-fortuitous-reductio : ∀ {A} → ⦃ _ : Negation A ⦄ → Problem A → Set
problem-fortuitous-reductio (χs ¶ (_ ╱ ιˢs)) = ∃ λ c → (let _ ╱ cˢs = c) → c ∈ χs × ~ c ∈ χs × cˢs ⊆ ιˢs

open Problem

⊫_ : ∀ {A} → ⦃ _ : Negation A ⦄ → Problem A → Set
⊫ 𝔓 = discharged 𝔓 ⊎ problem-fortuitous-reductio 𝔓 ⊎ sequent-fortuitous-reductio (interest 𝔓)

⊯_ : ∀ {A} → ⦃ _ : Negation A ⦄ → Problem A → Set
⊯_ = ¬_ ∘ ⊫_

infix 10 ⊫?_
⊫?_ : ∀ {A} ⦃ _ : Eq A ⦄ ⦃ _ : Negation A ⦄ (𝔓 : Problem A) → Dec $ ⊫ 𝔓
⊫?_ = ?
{-
--⊫? ([] ¶ ι) = no (λ {x → {!!}})
⊫? ([] ¶ ι) = no ? -- λ {(left (_ , () , _)) ; (right (_ , () , _))}
⊫? ((χ ∷ χs) ¶ ι) with ⊫? χs ¶ ι
… | yes (left (c , c∈χs , cᶠ≡ιᶠ , cˢs⊆ιˢs)) = yes $ left $ c , there χ c∈χs , cᶠ≡ιᶠ , λ {_} → cˢs⊆ιˢs
… | yes (right (cᶠ ╱ cˢs , c∈χs , ~c∈χs , cˢs⊆ιˢs)) = yes $ right $ {!!}
… | no inq = {!!}
-}
Theorem1 : {Φ : Problem LiteralFormula} → ⊨ Φ ↔ ⊫ Φ
Theorem1 {Φ@(χs ¶ ι)} = Theorem1a , Theorem1b
 where
  Theorem1a : ⊨ Φ → ⊫ Φ
  Theorem1a with ⊫? Φ
  … | yes ⊫Φ = const ⊫Φ
  … | no ⊯Φ =
    let I , I⊨χs , I⊭ι = Lemma1a in
    λ I→I⊨cs→I⊨i → ⊥-elim $ I⊭ι $ I→I⊨cs→I⊨i I I⊨χs
   where
    Lemma1a : ∃ λ I → I ⊨ χs × I ⊭ ι
    -- -- To construct the interpretation, consider a unique list, τ₀, τ₁, …, τₙ, of terms in ι ∷ χs. For each term, τ, we find <TODO> interpretations, 𝓘, such that for any I ∈ 𝓘, and any i ∈ 0, …, n, τ⟦ I ⟧ τᵢ = i. For each formula φ ∈ ι ∷ χs, we find <TODO> an interpretation I ∈ 𝓘 such that 𝑃⟦ I ⟧ φ = true when φ ∈ χs and 𝑃⟦ I ⟧ φ = false when φ = ι.
    Lemma1a = {!!}

-- Lemma1a : {sndp : SimpleNaturalDeductionProblem} → (let χs ⊢ ι = sndp) → ⊯ sndp → ∃ λ I → I ⊨ χs × I ⊭ ι

-- Lemma1a {χs ⊢ ι} ⊯sndp = {!!} where

  Theorem1b : ⊫ Φ → ⊨ Φ
  Theorem1b = {!!}



{-
Lemma1a : {Φ : Sequent LiteralFormula} → (let φᶠ ╱ φˢs = Φ) → ⊯ Φ → ∃ λ I → I ⊨ φˢs × I ⊭ φᶠ
-- To construct the interpretation, consider a unique list, τ₀, τ₁, …, τₙ, of terms in ι ∷ χs. For each term, τ, we find <TODO> interpretations, 𝓘, such that for any I ∈ 𝓘, and any i ∈ 0, …, n, τ⟦ I ⟧ τᵢ = i. For each formula φ ∈ ι ∷ χs, we find <TODO> an interpretation I ∈ 𝓘 such that 𝑃⟦ I ⟧ φ = true when φ ∈ χs and 𝑃⟦ I ⟧ φ = false when φ = ι.
Lemma1a {φᶠ ╱ φˢs} ⊯Φ = {!!}
-}

{-
⊫? ([] ¶ interest) = no λ { (left ()) ; (right (_ , () , _)) } -- TODO Agda is buggy when using C-c C-c to solve this
⊫? ((χ ∷ χs) ¶ ι) with ⊫? ι ╱ χs
… | yes (left ι∈χs) = yes $ left $ there χ ι∈χs
… | yes (right (q , q∈χs , ~q∈χs)) = yes $ right $ q , there χ q∈χs , there χ ~q∈χs
… | no inq = {!inq!}
-}

-- negationEliminationRule : (I : Interpretation) (φ : Formula) → I ⊨ ~ (~ φ) → I ⊨ φ
-- negationEliminationRule I φ (¬[I⊭φ×I⊭φ] , _) with I ⊨? φ
-- … | yes I⊨φ = I⊨φ
-- … | no I⊭φ = ⊥-elim $ ¬[I⊭φ×I⊭φ] $ I⊭φ , I⊭φ

-- -- -- justifieds simplification and
-- -- simplificationRule₁ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ logical φ₁ φ₂ → I ⊨ logical φ₁ φ₁
-- -- simplificationRule₁ I φ₁ φ₂ x = (fst x) , (fst x)

-- -- simplificationRule₂ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ logical φ₁ φ₂ → I ⊨ logical φ₂ φ₂
-- -- simplificationRule₂ I φ₁ φ₂ x = snd x , snd x

-- -- -- logical (logical (logical p p) q) (logical (logical p p) q)
-- -- conditionalization : (I : Interpretation) (p q : Formula) → I ⊨ q → I ⊨ ((p ∷ []) ⊢ p ⊃ q)
-- -- conditionalization I p q ⊨q -⊨p = let ⊨p = -⊨p p (here []) in (λ { (x , ~q) → ~q ⊨q}) , (λ { (x , y) → y ⊨q})

-- -- modusPonens : (I : Interpretation) (p q : Formula) → I ⊨ p → I ⊨ ((p ⊗ p) ⊗ q) ⊗ ((p ⊗ p) ⊗ q) → I ⊨ q
-- -- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) with I ⊨? q
-- -- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | yes x = x
-- -- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | no x = ⊥-elim (~[~p&~p&~q] ((λ { (x₁ , y) → y P}) , (λ x₁ → x x₁)))

-- -- data SkolemFormula {ι : Size} (α : Alphabet) : Set where
-- --   atomic : Predication α → SkolemFormula α
-- --   logical : {ι¹ : Size< ι} → SkolemFormula {ι¹} α → {ι² : Size< ι} → SkolemFormula {ι²} α → SkolemFormula {ι} α

-- -- record Alphabet₊ᵥ (α : Alphabet) : Set where
-- --   constructor α₊ᵥ⟨_⟩
-- --   field
-- --     alphabet : Alphabet
-- --     .one-variable-is-added : (number ∘ variables $ alphabet) ≡ suc (number ∘ variables $ α)
-- --     .there-are-no-functions-of-maximal-arity : number (functions alphabet) zero ≡ zero
-- --     .shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → number (functions alphabet) (suc ytira₁) ≡ number (functions α) ytira₀
-- -- open Alphabet₊ᵥ

-- -- record Alphabet₊ₛ (α : Alphabet) : Set where
-- --   constructor α₊ₛ⟨_⟩
-- --   field
-- --     alphabet : Alphabet
-- -- open Alphabet₊ₛ

-- -- {-
-- --   toSkolemFormula
-- --   ∀x(F x v₀ v₁) ⟿ F v₀ v₁ v₂
-- --   ∃x(F x v₀ v₁) ⟿ F (s₀͍₂ v₀ v₁) v₀ v₁
-- --   ∀x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F v₀ (s₀͍₂ v₁ v₂) v₂
-- --   ∃x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F (s₀͍₂ v₀ v₁) (s₁͍₂ v₁ v₂) v₂
-- --   F v₀ ⊗ G v₀ ⟿ F v₀ ⊗ G v₀
-- --   ∀x(F x v₀ v₁) ⊗ ∀x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₂ v₃ ⊗ G v₁ (s₀͍₂ v₀ v₃) v₃

-- --   ∀x(F x v₀ v₁) ⊗ ∃x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₁ v₂ ⊗ G (s₀͍₁ v₂) (s₁͍₂ (s₀͍₂ v₂) v₂) v₂

-- --   Φ₀ = ∃x(G x (s₀͍₂ x v₁) v₁) has alphabet of 2 variables, skolem functions: 0, 0, 1
-- --   this is existential {α₊ₛ} Φ₁, where
-- --     Φ₁ = G (s₀͍₂ v₀ v₁) (s₁͍₂ (s₀͍₂ v₀ v₁)) v₁
-- --     α₊ₛ = ⟨ 2 , 0 ∷ 0 ∷ 2 ∷ [] ⟩

-- --   maybe Φ₋₁ = ∀y∃x(G x (s₀͍₂ x v₀) v₀)
-- --    and  Φ₋₂ = ∀z∀y∃x(G x (s₀͍₂ x z) z), finally having no free variables, but nevertheless having skolem functions! these are user-defined functions, so this notion of Alphabet is somehow wrong. we have also left out constants (i.e. user-defined skolem-functions of arity 0)

-- --   Instead, take the alphabet as defining
-- --     a stack of free variables
-- --     a matrix (triangle?) of skolem functions

-- --   Let's try to reverse Φ₁ from a Skolem to a 1st-order formula. Is there a unique way to do it?
-- --   Φ₀' = ∀x(G (s₀͍₂ x v₀) (s₁͍₂ (s₀͍₂ x v₀)) v₀

-- --   Nope!


-- --   toSkolemFormula of



-- -- -}

-- -- -- toSkolemFormula (logical Φ₁ Φ₂) ⟿
-- -- --   let α' , φ₁ = toSkolemFormula Φ₁
-- -- --       Φ₂' = transcodeToAugmentedAlphabet Φ₂ α'
-- -- --       α'' , φ₂' = toSkolemFormula Φ₂'
-- -- --       φ₁' = transcodeToAugmentedAlphabet φ₁ α''

-- -- {-
-- -- given Δv = #varibles α' - #variables α
-- -- for every variable v in α, v in Φ, v stays the same in Φ'
-- -- for the added variable v⁺ in α₊ - α, v⁺ in Φ, v⁺ ⟿ v⁺ + Δv in transcode (universal {α₊} Φ)
-- -- α'₊ = α' + 1 variable
-- -- -}

-- -- -- record AddVariable (A : Alphabet → Set) : Set where
-- -- --   field
-- -- --     addVariableToAlphabet : {α : Alphabet} → A α → {α₊ : Alphabet} → Alphabet₊ᵥ α₊ → A α₊

-- -- -- instance
-- -- --   AddVariableFirstOrderFormula : AddVariable FirstOrderFormula
-- -- --   AddVariableFirstOrderFormula = {!!}

-- -- -- #variables = number ∘ variables

-- -- -- #functions_ofArity_ : Alphabet → Nat → Nat
-- -- -- #functions α⟨ V⟨ #variables ⟩ , S⟨ #functions ⟩ ⟩ ofArity arity = if′ lessNat arity (suc #variables) then #functions (natToFin arity) else 0

-- -- -- record _⊇_ (α' α : Alphabet) : Set where
-- -- --   field
-- -- --     at-least-as-many-variables : #variables α' ≥ #variables α
-- -- --     at-least-as-many-functions : ∀ {arity} → arity < #variables α → #functions α' ofArity arity ≥ #functions α ofArity arity

-- -- -- record AddAlphabet (α-top α-bottom : Alphabet) : Set where
-- -- --   field
-- -- --     alphabet : Alphabet

-- -- -- record Transcodeable (A : Alphabet → Set) : Set where
-- -- --   field
-- -- --     transcode : {α' α : Alphabet} → ⦃ _ : α' ⊇ α ⦄ → A α → A α'

-- -- -- open Transcodeable ⦃ … ⦄

-- -- -- record TransferAlphabet {α' α : Alphabet} (α'⊇α : α' ⊇ α) (α₊ : Alphabet₊ᵥ α) (Φ : FirstOrderFormula (alphabet α₊)) : Set where
-- -- --   field
-- -- --     alphabet : Alphabet
-- -- --     firstOrderFormula : FirstOrderFormula alphabet


-- -- -- instance
-- -- --   TranscodeablePredication : Transcodeable Predication
-- -- --   TranscodeablePredication = {!!}

-- -- --   TranscodeableAlphabet+Variable : Transcodeable Alphabet₊ᵥ
-- -- --   TranscodeableAlphabet+Variable = {!!}

-- -- --   TranscodeableSkolemFormula : Transcodeable SkolemFormula
-- -- --   TranscodeableSkolemFormula = {!!}

-- -- --   TranscodeableFirstOrderFormula : Transcodeable FirstOrderFormula
-- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (atomic p) = atomic (transcode p)
-- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (logical Φ₁ Φ₂) = logical (transcode Φ₁) (transcode Φ₂)
-- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula {α'} {α} ⦃ α'⊇α ⦄ (universal {α₊} Φ) = {!!} -- universal {_} {_} {transcode α₊} (transcode Φ)

-- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (existential Φ) = {!!}

-- -- -- --(α' α : Alphabet) (α'⊇α : α' ⊇ α) (α₊ : Alphabet+Variable α) (Φ : FirstOrderFormula (alphabet α₊)) → Σ _ λ (α''' : Alphabet) → FirstOrderFormula α'''

-- -- -- --FirstOrderFormula (alphabet α₊)
-- -- -- {-
-- -- -- -}

-- -- -- -- --transcodeIntoAugmentedAlphabet :



-- -- -- -- --toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)

-- -- -- -- --record IsEquivalentFormulas {α₀ : Alphabet} (φ₀ : SkolemFormula α₀) {α₁ : Alphabet} (Φ₁ : FirstOrderFormula α₁) : Set where
-- -- -- -- --  field
-- -- -- -- --    .atomicCase : {p : Predication α₀} → φ₀ ≡ atomic p → Φ₁ ≡ atomic p




-- -- -- -- -- --
-- -- -- -- -- -- record Alphabet+Alphabet (α₀ α₁ α₂ : Alphabet) : Set where
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet :

-- -- -- -- -- -- ∀xφ₁(x) ⊗ φ₂ ⟿ ∀x(φ₁ ⊗ φ₂)

-- -- -- -- -- -- hasQuantifiers : FirstOrderFormula α → Bool

-- -- -- -- -- --record Skolemization {α : Alphabet} (φ : FirstOrderFormula α) : Set where
-- -- -- -- -- --  field
-- -- -- -- -- --    alphabet : Alphabet
-- -- -- -- -- --    skolemization : SkolemFormula alphabet

-- -- -- -- -- record _IsAugmentationOf_ (α₁ α₀ : Alphabet) : Set where

-- -- -- -- -- record AugmentedAlphabet (α : Alphabet) : Set where
-- -- -- -- --   constructor ⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     alphabet : Alphabet
-- -- -- -- --     ..laws : alphabet ≡ α
-- -- -- -- -- open AugmentedAlphabet

-- -- -- -- -- trivialAugmentation : (α : Alphabet) → AugmentedAlphabet α
-- -- -- -- -- trivialAugmentation = {!!}

-- -- -- -- -- record DisjointRelativeUnion {α : Alphabet} (α¹ α² : AugmentedAlphabet α) : Set where
-- -- -- -- --   constructor ⟨_⟩
-- -- -- -- --   field
-- -- -- -- --     augmentation : AugmentedAlphabet α
-- -- -- -- --     .laws : {!!}
-- -- -- -- -- open DisjointRelativeUnion

-- -- -- -- -- disjointRelativeUnion : {α : Alphabet} → (α¹ α² : AugmentedAlphabet α) → DisjointRelativeUnion α¹ α²
-- -- -- -- -- disjointRelativeUnion = {!!}

-- -- -- -- -- -- inAugmentedAlphabet : {α : Alphabet} → (α¹ : AugmentedAlphabet α) → SkolemFormula α → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- inAugmentedAlphabet = {!!}

-- -- -- -- -- -- toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- toSkolemFormula {α₀} (atomic 𝑃) = trivialAugmentation α₀ , atomic 𝑃
-- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) with toSkolemFormula φ₁ | toSkolemFormula φ₂
-- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) | α¹ , Φ₁ | α² , Φ₂ = augmentation (disjointRelativeUnion α¹ α²) , logical {!inAugmentedAlphabet (augmentation (disjointRelativeUnion α¹ α²)) Φ₁!} {!Φ₂!}
-- -- -- -- -- -- toSkolemFormula {α₀} (universal x) = {!!}
-- -- -- -- -- -- toSkolemFormula {α₀} (existential x) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- --VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- --FunctionArity = Fin ∘ suc ∘ size
-- -- -- -- -- -- -- -- -- --FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     |v| : Nat -- number of variables
-- -- -- -- -- -- -- -- -- --     |f| : Fin (suc |v|) → Nat -- number of functions of each arity, |v| through 0

-- -- -- -- -- -- -- -- -- -- open Alphabet

-- -- -- -- -- -- -- -- -- -- -- VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- FunctionArity = Fin ∘ suc ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- -- data Term {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   variable : VariableName alphabet → Term alphabet
-- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {arity : FunctionArity alphabet} →
-- -- -- -- -- -- -- -- -- -- -- --              FunctionName alphabet (natToFin (|v| alphabet) - arity) →
-- -- -- -- -- -- -- -- -- -- -- --              ∀ {j : Size< i} → Vec (Term {j} alphabet) (finToNat arity) →
-- -- -- -- -- -- -- -- -- -- -- --              Term {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- PredicateArity = Nat
-- -- -- -- -- -- -- -- -- -- -- -- PredicateName = Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- a zeroth-order formula? (i.e. no quantifiers)
-- -- -- -- -- -- -- -- -- -- -- -- data NQFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → NQFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → NQFormula {j} alphabet → {k : Size< i} → NQFormula {k} alphabet → NQFormula {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- record AugmentedByVariable (alphabet₀ alphabet₁ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- --     one-variable-is-added : |v| alphabet₁ ≡ suc (|v| alphabet₀)
-- -- -- -- -- -- -- -- -- -- -- --     function-domain-is-zero-at-new-variable : |f| alphabet₁ zero ≡ 0
-- -- -- -- -- -- -- -- -- -- -- --     shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → |f| alphabet₁ (suc ytira₁) ≡ |f| alphabet₀ ytira₀

-- -- -- -- -- -- -- -- -- -- -- -- record AugmentVariables (alphabet₀ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- --     alphabet₁ : Alphabet
-- -- -- -- -- -- -- -- -- -- -- --     augmentation : AugmentedByVariable alphabet₀ alphabet₁

-- -- -- -- -- -- -- -- -- -- -- -- open AugmentVariables

-- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : (alphabet : Alphabet) → AugmentVariables alphabet
-- -- -- -- -- -- -- -- -- -- -- -- augmentVariables ⟨ |v| , |f| ⟩ =
-- -- -- -- -- -- -- -- -- -- -- --   record
-- -- -- -- -- -- -- -- -- -- -- --   { alphabet₁ = ⟨ suc |v| , (λ { zero → zero ; (suc ytira) → |f| ytira}) ⟩
-- -- -- -- -- -- -- -- -- -- -- --   ; augmentation =
-- -- -- -- -- -- -- -- -- -- -- --     record
-- -- -- -- -- -- -- -- -- -- -- --     { one-variable-is-added = refl
-- -- -- -- -- -- -- -- -- -- -- --     ; function-domain-is-zero-at-new-variable = refl
-- -- -- -- -- -- -- -- -- -- -- --     ; shifted-function-matches = cong |f| ∘ finToNat-inj } }

-- -- -- -- -- -- -- -- -- -- -- -- -- |f|₀ = |f|₀ + 1
-- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions ⟨ |v| , |f| ⟩ = ⟨ |v| , (λ { zero → suc (|f| zero) ; (suc ytira) → |f| (suc ytira) }) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- data QFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → QFormula {j} alphabet → {k : Size< i} → QFormula {k} alphabet → QFormula {i} alphabet
-- -- -- -- -- -- -- -- -- -- -- --   universal : QFormula (alphabet₁ (augmentVariables alphabet)) → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- --   existential : QFormula (augmentFunctions alphabet) → QFormula alphabet

-- -- -- -- -- -- -- -- -- -- -- -- record Assignment (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- --     μ : VariableName alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- --     𝑓 : ∀ {arity} → FunctionName alphabet arity → Vec Domain (finToNat arity) → Domain

-- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm : ∀ {i alphabet} → Assignment alphabet → Term {i} alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm ⟨ μ , _ ⟩ (variable x) = μ x
-- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm 𝑎@(⟨ μ , 𝑓 ⟩) (function f x) = 𝑓 f (evaluateTerm 𝑎 <$> x)

-- -- -- -- -- -- -- -- -- -- -- -- record Interpretation (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- --   open Assignment
-- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- --     𝑎 : Assignment alphabet
-- -- -- -- -- -- -- -- -- -- -- --     𝑃 : PredicateName → ∀ {arity} → Vec Domain arity → Bool

-- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula : ∀ {i alphabet} → Interpretation alphabet → NQFormula {i} alphabet → Bool
-- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula ⟨ 𝑎 , 𝑃 ⟩ (atomic name terms) = 𝑃 name $ evaluateTerm 𝑎 <$> terms
-- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula I (logical formula₁ formula₂) = not (evaluateNQFormula I formula₁) && not (evaluateNQFormula I formula₂)

-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- record IsADisjointUnionOfNQFormulas
-- -- -- -- -- -- -- -- -- -- -- --        {alphabet₁ alphabet₂ alphabet₁₊₂ : Alphabet}
-- -- -- -- -- -- -- -- -- -- -- --        (formula₁ : NQFormula alphabet₁)
-- -- -- -- -- -- -- -- -- -- -- --        (formula₂ : NQFormula alphabet₂)
-- -- -- -- -- -- -- -- -- -- -- --        (formula₁₊₂ : NQFormula alphabet₁₊₂)
-- -- -- -- -- -- -- -- -- -- -- --        : Set where
-- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- --     alphabet-size : |v| alphabet₁₊₂ ≡ |v| alphabet₁ + |v| alphabet₂
-- -- -- -- -- -- -- -- -- -- -- --     --|f| alphabet₁₊₂ ytira


-- -- -- -- -- -- -- -- -- -- -- -- ----record AlphabetSummed  (alphabet₀ alphabet₁ : Alphabet)
-- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets : Alphabet → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets ⟨ |v|₁ , |f|₁ ⟩ ⟨ |v|₂ , |f|₂ ⟩ = ⟨ (|v|₁ + |v|₂) , (λ x → if′ finToNat x ≤? |v|₁ && finToNat x ≤? |v|₂ then {!!} else {!!}) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- sup : ∀ {alphabet₁} → Formula alphabet₁ → ∀ {alphabet₂} → Formula alphabet₂ → Σ _ λ alphabet₁₊₂ → Formula alphabet₁₊₂ × Formula alphabet₁₊₂
-- -- -- -- -- -- -- -- -- -- -- -- -- sup {⟨ |v|₁ , |a|₁ , |f|₁ ⟩} φ₁ {⟨ |v|₂ , |a|₂ , |f|₂ ⟩} φ₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- pnf : ∀ {alphabet} → Formula alphabet → Σ _ λ alphabet+ → Formula₀ alphabet+
-- -- -- -- -- -- -- -- -- -- -- -- -- pnf = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- --universal (P 0) = ∀ x → P x
-- -- -- -- -- -- -- -- -- -- -- -- -- (∀ x ∃ y (P x y)) ∨ (∀ x ∃ y (P x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- P x₀ (s₀͍₁ x₀) ∨ P x₁ (s₁͍₁ x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -}






-- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| : (arity : Arity) → Vec ℕ (suc |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a variable to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN : ∀ {n} → Fin n → (Fin n → Nat) → Fin n → Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedFunctions {|a| : Arity} (arity : Arity) (|f| : Vec ℕ (++arity |a|)) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA : ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA-law : max arity |a| ≡ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ++|f| : Vec ℕ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- --     f-law : increaseTabulationAt arity (indexVec |f|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- -- define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- a ⊗ b ≡ False a and False b

-- -- -- -- -- -- -- -- -- -- -- -- -- -- now, we can define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ¬a = a ⊗ a ≡ False a and False a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∨ b = ¬(a ⊗ b) ≡ False (False a and False b) and False (False a and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∧ b = ¬(¬a ∨ ¬b) = ¬(¬(¬a ⊗ ¬b)) = ¬a ⊗ ¬b = False (False a and False a) and False (False b and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- a → b = ¬a ∨ b = (a ⊗ a) ∨ b = ¬((a ⊗ a) ⊗ b) = ((a ⊗ a) ⊗ b) ⊗ ((a ⊗ a) ⊗ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- conversion to prenex
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∀xF ⊗ G ⟿ ∃x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∃xF ⊗ G ⟿ ∀x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∀xG ⟿ ∃x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∃xG ⟿ ∀x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ========================
-- -- -- -- -- -- -- -- -- -- -- -- -- -- (a ⊗ ∀xB) ⊗ c ⟿ ∃x(wk(a) ⊗ B) ⊗ c ⟿ ∀x((wk(a) ⊗ B) ⊗ wk(c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF : (arity : Arity) → ∀ {|a| : Arity} → Vec ℕ (++arity |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f|
-- -- -- -- -- -- -- -- -- -- -- -- -- --  with decBool (lessNat |a| arity)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x with compare arity |a|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.(suc (k + arity))} |f| | yes x | less (diff k refl) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl with lessNat arity arity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl | false = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF zero {.zero} |f| | yes true | equal refl | true = {!!} ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF (suc arity) {.(suc arity)} |f| | yes true | equal refl | true = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x | greater gt = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x with decBool (lessNat arity |a|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | yes x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | no x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- = case arity <? |a| of λ { false → {!!} ; true → {!!} }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a function of a given arity to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Arity → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions arity ⟨ |v| , |a| , |f| ⟩ = ⟨ |v| , max arity |a| , augmentF arity |f| ⟩


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data DomainSignifier : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   free : Nat → DomainSignifier

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartiallyAppliedFunction : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constant : PartiallyAppliedFunction 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {n} → PartiallyAppliedFunction 0 → PartiallyAppliedFunction (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Term = PartiallyAppliedFunction 0

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartialyAppliedPredicate : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   statement : PartialyAppliedPredicate 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   partial : ∀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Language : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Name = String

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Function : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     name : Name
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     number-of-arguments : Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Vec

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Function : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : Function →

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Sentence : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   predication : Name →

-- -- {-

-- -- record Variables : Set where
-- --   constructor V⟨_⟩
-- --   field
-- --     number : Nat
-- -- open Variables

-- -- record Functions (υ : Variables) : Set where
-- --   constructor S⟨_⟩
-- --   field
-- --     number : Fin (suc (number υ)) → Nat
-- -- open Functions

-- -- record Alphabet : Set where
-- --   constructor α⟨_,_⟩
-- --   field
-- --     variables : Variables
-- --     functions : Functions variables
-- -- open Alphabet

-- -- record Variable (α : Alphabet) : Set where
-- --   constructor v⟨_⟩
-- --   field
-- --     name : Fin (number (variables α))
-- -- open Variable

-- -- record Function (α : Alphabet) : Set where
-- --   constructor s⟨_,_⟩
-- --   field
-- --     arity : Fin ∘ suc ∘ number ∘ variables $ α
-- --     name : Fin $ number (functions α) arity
-- -- open Function

-- -- data Term (𝑽 : Nat) : Set where
-- --   variable : Fin 𝑽 → Term 𝑽
-- --   function : (𝑓 : Function α) → {ι₋₁ : Size< ι₀} → Vec (Term {ι₋₁} α) (finToNat (arity 𝑓)) →
-- --              Term {ι₀} α

-- -- record Predication (alphabet : Alphabet) : Set where
-- --   constructor P⟨_,_,_⟩
-- --   field
-- --     name : Nat
-- --     arity : Nat
-- --     terms : Vec (Term alphabet) arity
-- -- open Predication
-- -- -}

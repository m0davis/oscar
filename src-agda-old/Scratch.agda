module Scratch where

open import Prelude

open import Agda.Builtin.Size

open import Tactic.Nat

postulate
  Domain : Set

record Interpretation : Set where
  field
    V : Nat → Domain
    F : (arity name : Nat) → Vec Domain arity → Domain
    P : (arity name : Nat) → Vec Domain arity → Bool

data Term {i : Size} : Set where
  variable : Nat → Term
  function : (arity name : Nat) → {j : Size< i} → Vec (Term {j}) arity → Term {i}

interpretTerm : Interpretation → {i : Size} → Term {i} → Domain
interpretTerm I (variable v) = Interpretation.V I v
interpretTerm I (function arity name {j} domA) = Interpretation.F I arity name (interpretTerm I <$> domA)

data Formula : Set where
  atomic : (arity name : Nat) → Vec Term arity → Formula
  logical : Formula →
            Formula →
            Formula
  quantified : Nat → Formula → Formula

infix 40 _⊗_
_⊗_ : Formula → Formula → Formula
_⊗_ a b = logical a b

~ : Formula → Formula
~ a = logical a a

infix 50 _⊃_
_⊃_ : Formula → Formula → Formula
_⊃_ p q = ~ (~ p ⊗ q)

data Literal : Formula → Set where
  Latomic : (arity name : Nat) → (terms : Vec Term arity) → Literal (atomic arity name terms)
  logical : (arity name : Nat) → (terms : Vec Term arity) → Literal (logical (atomic arity name terms) (atomic arity name terms))

record Sequent : Set where
  constructor _⊢_
  field
    premises : List Formula
    conclusion : Formula

data _∈_ {A : Set} (a : A) : List A → Set where
  here : (as : List A) → a ∈ (a ∷ as)
  there : (x : A) (as : List A) → a ∈ (x ∷ as)

record SimpleNDProblem (s : Sequent) : Set where
  field
    simpleConclusion : Literal (Sequent.conclusion s)
    simplePremises : ∀ p → p ∈ Sequent.premises s → Literal p

record _≞_/_ (I : Interpretation) (I₀ : Interpretation) (v₀ : Nat) : Set where
  field
    lawV : (v : Nat) → (v ≡ v₀ → ⊥) → Interpretation.V I v ≡ Interpretation.V I₀ v
    lawF : (arity name : Nat) → (domA : Vec Domain arity) → Interpretation.F I arity name domA ≡ Interpretation.F I₀ arity name domA
    lawP : (arity name : Nat) → (domA : Vec Domain arity) → Interpretation.P I arity name domA ≡ Interpretation.P I₀ arity name domA

record Satisfaction (A : Set) : Set₁ where
  field
    _⊨_ : Interpretation → A → Set

  postulate _⊨?_ : (I : Interpretation) → (φ : A) → Dec (I ⊨ φ)

  _⊭_ : Interpretation → A → Set
  I ⊭ x = I ⊨ x → ⊥

open Satisfaction ⦃ … ⦄

instance
  SatisfactionFormula : Satisfaction Formula
  Satisfaction._⊨_ SatisfactionFormula = _⊨ᴹ_ where
    _⊨ᴹ_ : Interpretation → Formula → Set
    _⊨ᴹ_ I₀ (quantified v₀ φ) = (I : Interpretation) → I ≞ I₀ / v₀ → I ⊨ᴹ φ
    _⊨ᴹ_ I₀ (atomic arity name domA) = Interpretation.P I₀ arity name (interpretTerm I₀ <$> domA) ≡ true
    _⊨ᴹ_ I₀ (logical φ₁ φ₂) = (I₀ ⊨ᴹ φ₁ → ⊥) × (I₀ ⊨ᴹ φ₂ → ⊥)
    {-# DISPLAY _⊨ᴹ_ I f = I ⊨ f #-}

record Validity (A : Set) : Set₁ where
  field
    ⊨_ : A → Set

  ⊭_ : A → Set
  ⊭ x = ⊨ x → ⊥

open Validity ⦃ … ⦄

instance
  ValidityFormula : Validity Formula
  Validity.⊨_ ValidityFormula φ = (I : Interpretation) → I ⊨ φ


instance
  SatisfactionSequent : Satisfaction Sequent
  Satisfaction._⊨_ SatisfactionSequent I (premises ⊢ conclusion) = (_ : (premise : Formula) → premise ∈ premises → I ⊨ premise) →  I ⊨ conclusion

  ValiditySequent : Validity Sequent
  Validity.⊨_ ValiditySequent sequent = (I : Interpretation) → I ⊨ sequent

negationElimination : (I : Interpretation) (φ : Formula) → I ⊨ (φ ⊗ φ) ⊗ (φ ⊗ φ) → I ⊨ φ
negationElimination I φ (x , y) with I ⊨? φ
negationElimination I φ (x₁ , y) | yes x = x
negationElimination I φ (x₁ , y) | no x = ⊥-elim (x₁ (x , x))

-- logical (logical (logical p p) q) (logical (logical p p) q)
conditionalization : (I : Interpretation) (p q : Formula) → I ⊨ q → I ⊨ ((p ∷ []) ⊢ p ⊃ q)
conditionalization I p q ⊨q -⊨p = let ⊨p = -⊨p p (here []) in (λ { (x , ~q) → ~q ⊨q}) , (λ { (x , y) → y ⊨q})

modusPonens : (I : Interpretation) (p q : Formula) → I ⊨ p → I ⊨ ((p ⊗ p) ⊗ q) ⊗ ((p ⊗ p) ⊗ q) → I ⊨ q
modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) with I ⊨? q
modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | yes x = x
modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | no x = ⊥-elim (~[~p&~p&~q] ((λ { (x₁ , y) → y P}) , (λ x₁ → x x₁)))

theorem1a : (s : Sequent) → SimpleNDProblem s → ⊨ s → Either (Sequent.conclusion s ∈ Sequent.premises s) (Σ _ λ q → q ∈ Sequent.premises s × ~ q ∈ Sequent.premises s)
theorem1a ([] ⊢ atomic arity name x) record { simpleConclusion = (Latomic .arity .name .x) ; simplePremises = simplePremises } x₂ = {!!}
theorem1a ((x₁ ∷ premises) ⊢ atomic arity name x) record { simpleConclusion = (Latomic .arity .name .x) ; simplePremises = simplePremises } x₂ = {!!}
theorem1a (premises ⊢ logical .(atomic arity name terms) .(atomic arity name terms)) record { simpleConclusion = (logical arity name terms) ; simplePremises = simplePremises } x₁ = {!!}
theorem1a (premises ⊢ quantified x conclusion) record { simpleConclusion = () ; simplePremises = simplePremises } x₂

theorem1b : (s : Sequent) → SimpleNDProblem s → Either (Sequent.conclusion s ∈ Sequent.premises s) (Σ _ λ q → q ∈ Sequent.premises s × ~ q ∈ Sequent.premises s) → ⊨ s
theorem1b s x (left x₁) I x₂ = x₂ (Sequent.conclusion s) x₁
theorem1b s x (right (x₁ , x₂ , y)) I x₃ = let ~q = x₃ (~ x₁) y in let q = x₃ x₁ x₂ in ⊥-elim (fst ~q q)

{-
p ≡ q
p -> q & q -> p
(~p v q) & (~q v p)
~(p & ~q) & ~(q & ~p)
~(~~p & ~q) & ~(~~q & ~p)

bicondit elim is just simplification

modus ponens
p , (p ⊗ (q ⊗ q)) ⊗ (p ⊗ (q ⊗ q)) --> q

~(~p & q)
p or ~q


p -> q
~p v q
~(p & ~q)
~(p & ~q) & ~(p & ~q)
~(~~p & ~q) & ~(~~p & ~q)
(~~p & ~q) ⊗ (~~p & ~q)
(~p ⊗ q) ⊗ (~p ⊗ q)
((p ⊗ p) ⊗ q) ⊗ ((p ⊗ p) ⊗ q)
-}


{-
conditionalization p -> q from q, with discharge p
(p ∷ [] ⊢ q) ⊨ (∅ ⊢ q)
-}



--data ReasonerState : List Sequent → List Sequent → Set

{-
p <-> q
p -> q and q -> p
~p v q  and  ~q or p
~(p and ~q) and ~(q and ~p)
(p and ~q) ⊗ (q and ~p)
((p ⊗ p) ⊗ q) ⊗ ((q ⊗ q) ⊗ p)

p -> q
~p v q
~(p and ~q)
~(p and ~q) and ~(p and ~q)
((p ⊗ p) ⊗ q) ⊗ ((p ⊗ p) ⊗ q)
but this is just simplification


p , p -> q ⊢ q
p , ((p ⊗ p) ⊗ q) ⊗ ((p ⊗ p) ⊗ q) ⊢ q

p , q <-- p & q


p <-- ~~p
p <-- (p ⊗ p) ⊗ (p ⊗ p)
-}

-- PorNotP : (I : Interpretation) (P : Formula) → I ⊨ (logical (logical P (logical P P)) (logical P (logical P P)))
-- PorNotP I P = (λ { (x , y) → y (x , x)}) , (λ { (x , y) → y (x , x)})

-- IFTHEN : Formula → Formula → Formula
-- IFTHEN P Q = logical (logical (logical P P) Q) (logical (logical P P) Q)

-- EXISTS : Nat → Formula → Formula
-- EXISTS n φ = (logical (quantified n (logical φ φ)) (quantified n (logical φ φ)))

-- F : Nat → Formula
-- F n = atomic 1 0 (variable n ∷ [])

-- Fa : Formula
-- Fa = F 0

-- ∃xFx : Formula
-- ∃xFx = EXISTS 1 (F 1)

-- IfFaThenExistsFa : (I : Interpretation) → I ⊨ (IFTHEN Fa ∃xFx)
-- IfFaThenExistsFa I = (λ { (I⊭~Fa , I⊭∃xFx) → I⊭~Fa ((λ x → I⊭∃xFx ((λ x₁ → fst (x₁ {!!} {!!}) {!!}) , (λ x₁ → {!!}))) , {!!})}) , (λ { (x , y) → {!!}})

-- NotPAndNotNotP : (I : Interpretation) (P : Formula) → I ⊨ (logical P (logical P P))
-- NotPAndNotNotP = {!!}

-- -- Valid : Formula → Set₁
-- -- Valid φ = (I : Interpretation) → I Satisfies φ

-- -- -- data SkolemFormula {ι : Size} (α : Alphabet) : Set where
-- -- --   atomic : Predication α → SkolemFormula α
-- -- --   logical : {ι¹ : Size< ι} → SkolemFormula {ι¹} α → {ι² : Size< ι} → SkolemFormula {ι²} α → SkolemFormula {ι} α

-- -- -- record Alphabet₊ᵥ (α : Alphabet) : Set where
-- -- --   constructor α₊ᵥ⟨_⟩
-- -- --   field
-- -- --     alphabet : Alphabet
-- -- --     .one-variable-is-added : (number ∘ variables $ alphabet) ≡ suc (number ∘ variables $ α)
-- -- --     .there-are-no-functions-of-maximal-arity : number (functions alphabet) zero ≡ zero
-- -- --     .shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → number (functions alphabet) (suc ytira₁) ≡ number (functions α) ytira₀
-- -- -- open Alphabet₊ᵥ

-- -- -- record Alphabet₊ₛ (α : Alphabet) : Set where
-- -- --   constructor α₊ₛ⟨_⟩
-- -- --   field
-- -- --     alphabet : Alphabet
-- -- -- open Alphabet₊ₛ

-- -- -- {-
-- -- --   toSkolemFormula
-- -- --   ∀x(F x v₀ v₁) ⟿ F v₀ v₁ v₂
-- -- --   ∃x(F x v₀ v₁) ⟿ F (s₀͍₂ v₀ v₁) v₀ v₁
-- -- --   ∀x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F v₀ (s₀͍₂ v₁ v₂) v₂
-- -- --   ∃x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F (s₀͍₂ v₀ v₁) (s₁͍₂ v₁ v₂) v₂
-- -- --   F v₀ ⊗ G v₀ ⟿ F v₀ ⊗ G v₀
-- -- --   ∀x(F x v₀ v₁) ⊗ ∀x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₂ v₃ ⊗ G v₁ (s₀͍₂ v₀ v₃) v₃

-- -- --   ∀x(F x v₀ v₁) ⊗ ∃x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₁ v₂ ⊗ G (s₀͍₁ v₂) (s₁͍₂ (s₀͍₂ v₂) v₂) v₂

-- -- --   Φ₀ = ∃x(G x (s₀͍₂ x v₁) v₁) has alphabet of 2 variables, skolem functions: 0, 0, 1
-- -- --   this is existential {α₊ₛ} Φ₁, where
-- -- --     Φ₁ = G (s₀͍₂ v₀ v₁) (s₁͍₂ (s₀͍₂ v₀ v₁)) v₁
-- -- --     α₊ₛ = ⟨ 2 , 0 ∷ 0 ∷ 2 ∷ [] ⟩

-- -- --   maybe Φ₋₁ = ∀y∃x(G x (s₀͍₂ x v₀) v₀)
-- -- --    and  Φ₋₂ = ∀z∀y∃x(G x (s₀͍₂ x z) z), finally having no free variables, but nevertheless having skolem functions! these are user-defined functions, so this notion of Alphabet is somehow wrong. we have also left out constants (i.e. user-defined skolem-functions of arity 0)

-- -- --   Instead, take the alphabet as defining
-- -- --     a stack of free variables
-- -- --     a matrix (triangle?) of skolem functions

-- -- --   Let's try to reverse Φ₁ from a Skolem to a 1st-order formula. Is there a unique way to do it?
-- -- --   Φ₀' = ∀x(G (s₀͍₂ x v₀) (s₁͍₂ (s₀͍₂ x v₀)) v₀

-- -- --   Nope!


-- -- --   toSkolemFormula of



-- -- -- -}

-- -- -- -- toSkolemFormula (logical Φ₁ Φ₂) ⟿
-- -- -- --   let α' , φ₁ = toSkolemFormula Φ₁
-- -- -- --       Φ₂' = transcodeToAugmentedAlphabet Φ₂ α'
-- -- -- --       α'' , φ₂' = toSkolemFormula Φ₂'
-- -- -- --       φ₁' = transcodeToAugmentedAlphabet φ₁ α''

-- -- -- {-
-- -- -- given Δv = #varibles α' - #variables α
-- -- -- for every variable v in α, v in Φ, v stays the same in Φ'
-- -- -- for the added variable v⁺ in α₊ - α, v⁺ in Φ, v⁺ ⟿ v⁺ + Δv in transcode (universal {α₊} Φ)
-- -- -- α'₊ = α' + 1 variable
-- -- -- -}

-- -- -- -- record AddVariable (A : Alphabet → Set) : Set where
-- -- -- --   field
-- -- -- --     addVariableToAlphabet : {α : Alphabet} → A α → {α₊ : Alphabet} → Alphabet₊ᵥ α₊ → A α₊

-- -- -- -- instance
-- -- -- --   AddVariableFirstOrderFormula : AddVariable FirstOrderFormula
-- -- -- --   AddVariableFirstOrderFormula = {!!}

-- -- -- -- #variables = number ∘ variables

-- -- -- -- #functions_ofArity_ : Alphabet → Nat → Nat
-- -- -- -- #functions α⟨ V⟨ #variables ⟩ , S⟨ #functions ⟩ ⟩ ofArity arity = if′ lessNat arity (suc #variables) then #functions (natToFin arity) else 0

-- -- -- -- record _⊇_ (α' α : Alphabet) : Set where
-- -- -- --   field
-- -- -- --     at-least-as-many-variables : #variables α' ≥ #variables α
-- -- -- --     at-least-as-many-functions : ∀ {arity} → arity < #variables α → #functions α' ofArity arity ≥ #functions α ofArity arity

-- -- -- -- record AddAlphabet (α-top α-bottom : Alphabet) : Set where
-- -- -- --   field
-- -- -- --     alphabet : Alphabet

-- -- -- -- record Transcodeable (A : Alphabet → Set) : Set where
-- -- -- --   field
-- -- -- --     transcode : {α' α : Alphabet} → ⦃ _ : α' ⊇ α ⦄ → A α → A α'

-- -- -- -- open Transcodeable ⦃ … ⦄

-- -- -- -- record TransferAlphabet {α' α : Alphabet} (α'⊇α : α' ⊇ α) (α₊ : Alphabet₊ᵥ α) (Φ : FirstOrderFormula (alphabet α₊)) : Set where
-- -- -- --   field
-- -- -- --     alphabet : Alphabet
-- -- -- --     firstOrderFormula : FirstOrderFormula alphabet


-- -- -- -- instance
-- -- -- --   TranscodeablePredication : Transcodeable Predication
-- -- -- --   TranscodeablePredication = {!!}

-- -- -- --   TranscodeableAlphabet+Variable : Transcodeable Alphabet₊ᵥ
-- -- -- --   TranscodeableAlphabet+Variable = {!!}

-- -- -- --   TranscodeableSkolemFormula : Transcodeable SkolemFormula
-- -- -- --   TranscodeableSkolemFormula = {!!}

-- -- -- --   TranscodeableFirstOrderFormula : Transcodeable FirstOrderFormula
-- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (atomic p) = atomic (transcode p)
-- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (logical Φ₁ Φ₂) = logical (transcode Φ₁) (transcode Φ₂)
-- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula {α'} {α} ⦃ α'⊇α ⦄ (universal {α₊} Φ) = {!!} -- universal {_} {_} {transcode α₊} (transcode Φ)

-- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (existential Φ) = {!!}

-- -- -- -- --(α' α : Alphabet) (α'⊇α : α' ⊇ α) (α₊ : Alphabet+Variable α) (Φ : FirstOrderFormula (alphabet α₊)) → Σ _ λ (α''' : Alphabet) → FirstOrderFormula α'''

-- -- -- -- --FirstOrderFormula (alphabet α₊)
-- -- -- -- {-
-- -- -- -- -}

-- -- -- -- -- --transcodeIntoAugmentedAlphabet :



-- -- -- -- -- --toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)

-- -- -- -- -- --record IsEquivalentFormulas {α₀ : Alphabet} (φ₀ : SkolemFormula α₀) {α₁ : Alphabet} (Φ₁ : FirstOrderFormula α₁) : Set where
-- -- -- -- -- --  field
-- -- -- -- -- --    .atomicCase : {p : Predication α₀} → φ₀ ≡ atomic p → Φ₁ ≡ atomic p




-- -- -- -- -- -- --
-- -- -- -- -- -- -- record Alphabet+Alphabet (α₀ α₁ α₂ : Alphabet) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     alphabet :

-- -- -- -- -- -- -- ∀xφ₁(x) ⊗ φ₂ ⟿ ∀x(φ₁ ⊗ φ₂)

-- -- -- -- -- -- -- hasQuantifiers : FirstOrderFormula α → Bool

-- -- -- -- -- -- --record Skolemization {α : Alphabet} (φ : FirstOrderFormula α) : Set where
-- -- -- -- -- -- --  field
-- -- -- -- -- -- --    alphabet : Alphabet
-- -- -- -- -- -- --    skolemization : SkolemFormula alphabet

-- -- -- -- -- -- record _IsAugmentationOf_ (α₁ α₀ : Alphabet) : Set where

-- -- -- -- -- -- record AugmentedAlphabet (α : Alphabet) : Set where
-- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- --     ..laws : alphabet ≡ α
-- -- -- -- -- -- open AugmentedAlphabet

-- -- -- -- -- -- trivialAugmentation : (α : Alphabet) → AugmentedAlphabet α
-- -- -- -- -- -- trivialAugmentation = {!!}

-- -- -- -- -- -- record DisjointRelativeUnion {α : Alphabet} (α¹ α² : AugmentedAlphabet α) : Set where
-- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     augmentation : AugmentedAlphabet α
-- -- -- -- -- --     .laws : {!!}
-- -- -- -- -- -- open DisjointRelativeUnion

-- -- -- -- -- -- disjointRelativeUnion : {α : Alphabet} → (α¹ α² : AugmentedAlphabet α) → DisjointRelativeUnion α¹ α²
-- -- -- -- -- -- disjointRelativeUnion = {!!}

-- -- -- -- -- -- -- inAugmentedAlphabet : {α : Alphabet} → (α¹ : AugmentedAlphabet α) → SkolemFormula α → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- inAugmentedAlphabet = {!!}

-- -- -- -- -- -- -- toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- toSkolemFormula {α₀} (atomic 𝑃) = trivialAugmentation α₀ , atomic 𝑃
-- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) with toSkolemFormula φ₁ | toSkolemFormula φ₂
-- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) | α¹ , Φ₁ | α² , Φ₂ = augmentation (disjointRelativeUnion α¹ α²) , logical {!inAugmentedAlphabet (augmentation (disjointRelativeUnion α¹ α²)) Φ₁!} {!Φ₂!}
-- -- -- -- -- -- -- toSkolemFormula {α₀} (universal x) = {!!}
-- -- -- -- -- -- -- toSkolemFormula {α₀} (existential x) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- ... | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- --VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- --FunctionArity = Fin ∘ suc ∘ size
-- -- -- -- -- -- -- -- -- -- --FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- --     |v| : Nat -- number of variables
-- -- -- -- -- -- -- -- -- -- --     |f| : Fin (suc |v|) → Nat -- number of functions of each arity, |v| through 0

-- -- -- -- -- -- -- -- -- -- -- open Alphabet

-- -- -- -- -- -- -- -- -- -- -- -- VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- FunctionArity = Fin ∘ suc ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- -- -- data Term {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   variable : VariableName alphabet → Term alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {arity : FunctionArity alphabet} →
-- -- -- -- -- -- -- -- -- -- -- -- --              FunctionName alphabet (natToFin (|v| alphabet) - arity) →
-- -- -- -- -- -- -- -- -- -- -- -- --              ∀ {j : Size< i} → Vec (Term {j} alphabet) (finToNat arity) →
-- -- -- -- -- -- -- -- -- -- -- -- --              Term {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- PredicateArity = Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- PredicateName = Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- a zeroth-order formula? (i.e. no quantifiers)
-- -- -- -- -- -- -- -- -- -- -- -- -- data NQFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → NQFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → NQFormula {j} alphabet → {k : Size< i} → NQFormula {k} alphabet → NQFormula {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedByVariable (alphabet₀ alphabet₁ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     one-variable-is-added : |v| alphabet₁ ≡ suc (|v| alphabet₀)
-- -- -- -- -- -- -- -- -- -- -- -- --     function-domain-is-zero-at-new-variable : |f| alphabet₁ zero ≡ 0
-- -- -- -- -- -- -- -- -- -- -- -- --     shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → |f| alphabet₁ (suc ytira₁) ≡ |f| alphabet₀ ytira₀

-- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentVariables (alphabet₀ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     alphabet₁ : Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --     augmentation : AugmentedByVariable alphabet₀ alphabet₁

-- -- -- -- -- -- -- -- -- -- -- -- -- open AugmentVariables

-- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : (alphabet : Alphabet) → AugmentVariables alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables ⟨ |v| , |f| ⟩ =
-- -- -- -- -- -- -- -- -- -- -- -- --   record
-- -- -- -- -- -- -- -- -- -- -- -- --   { alphabet₁ = ⟨ suc |v| , (λ { zero → zero ; (suc ytira) → |f| ytira}) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --   ; augmentation =
-- -- -- -- -- -- -- -- -- -- -- -- --     record
-- -- -- -- -- -- -- -- -- -- -- -- --     { one-variable-is-added = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     ; function-domain-is-zero-at-new-variable = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     ; shifted-function-matches = cong |f| ∘ finToNat-inj } }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- |f|₀ = |f|₀ + 1
-- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions ⟨ |v| , |f| ⟩ = ⟨ |v| , (λ { zero → suc (|f| zero) ; (suc ytira) → |f| (suc ytira) }) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- data QFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → QFormula {j} alphabet → {k : Size< i} → QFormula {k} alphabet → QFormula {i} alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --   universal : QFormula (alphabet₁ (augmentVariables alphabet)) → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --   existential : QFormula (augmentFunctions alphabet) → QFormula alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- record Assignment (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     μ : VariableName alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- --     𝑓 : ∀ {arity} → FunctionName alphabet arity → Vec Domain (finToNat arity) → Domain

-- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm : ∀ {i alphabet} → Assignment alphabet → Term {i} alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm ⟨ μ , _ ⟩ (variable x) = μ x
-- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm 𝑎@(⟨ μ , 𝑓 ⟩) (function f x) = 𝑓 f (evaluateTerm 𝑎 <$> x)

-- -- -- -- -- -- -- -- -- -- -- -- -- record Interpretation (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- --   open Assignment
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     𝑎 : Assignment alphabet
-- -- -- -- -- -- -- -- -- -- -- -- --     𝑃 : PredicateName → ∀ {arity} → Vec Domain arity → Bool

-- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula : ∀ {i alphabet} → Interpretation alphabet → NQFormula {i} alphabet → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula ⟨ 𝑎 , 𝑃 ⟩ (atomic name terms) = 𝑃 name $ evaluateTerm 𝑎 <$> terms
-- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula I (logical formula₁ formula₂) = not (evaluateNQFormula I formula₁) && not (evaluateNQFormula I formula₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- ... | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- record IsADisjointUnionOfNQFormulas
-- -- -- -- -- -- -- -- -- -- -- -- --        {alphabet₁ alphabet₂ alphabet₁₊₂ : Alphabet}
-- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁ : NQFormula alphabet₁)
-- -- -- -- -- -- -- -- -- -- -- -- --        (formula₂ : NQFormula alphabet₂)
-- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁₊₂ : NQFormula alphabet₁₊₂)
-- -- -- -- -- -- -- -- -- -- -- -- --        : Set where
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     alphabet-size : |v| alphabet₁₊₂ ≡ |v| alphabet₁ + |v| alphabet₂
-- -- -- -- -- -- -- -- -- -- -- -- --     --|f| alphabet₁₊₂ ytira


-- -- -- -- -- -- -- -- -- -- -- -- -- ----record AlphabetSummed  (alphabet₀ alphabet₁ : Alphabet)
-- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets : Alphabet → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets ⟨ |v|₁ , |f|₁ ⟩ ⟨ |v|₂ , |f|₂ ⟩ = ⟨ (|v|₁ + |v|₂) , (λ x → if′ finToNat x ≤? |v|₁ && finToNat x ≤? |v|₂ then {!!} else {!!}) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- sup : ∀ {alphabet₁} → Formula alphabet₁ → ∀ {alphabet₂} → Formula alphabet₂ → Σ _ λ alphabet₁₊₂ → Formula alphabet₁₊₂ × Formula alphabet₁₊₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- sup {⟨ |v|₁ , |a|₁ , |f|₁ ⟩} φ₁ {⟨ |v|₂ , |a|₂ , |f|₂ ⟩} φ₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf : ∀ {alphabet} → Formula alphabet → Σ _ λ alphabet+ → Formula₀ alphabet+
-- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --universal (P 0) = ∀ x → P x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- (∀ x ∃ y (P x y)) ∨ (∀ x ∃ y (P x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- P x₀ (s₀͍₁ x₀) ∨ P x₁ (s₁͍₁ x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}






-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| : (arity : Arity) → Vec ℕ (suc |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a variable to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN : ∀ {n} → Fin n → (Fin n → Nat) → Fin n → Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedFunctions {|a| : Arity} (arity : Arity) (|f| : Vec ℕ (++arity |a|)) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA : ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA-law : max arity |a| ≡ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ++|f| : Vec ℕ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f-law : increaseTabulationAt arity (indexVec |f|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ⊗ b ≡ False a and False b

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- now, we can define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ¬a = a ⊗ a ≡ False a and False a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∨ b = ¬(a ⊗ b) ≡ False (False a and False b) and False (False a and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∧ b = ¬(¬a ∨ ¬b) = ¬(¬(¬a ⊗ ¬b)) = ¬a ⊗ ¬b = False (False a and False a) and False (False b and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a → b = ¬a ∨ b = (a ⊗ a) ∨ b = ¬((a ⊗ a) ⊗ b) = ((a ⊗ a) ⊗ b) ⊗ ((a ⊗ a) ⊗ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- conversion to prenex
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∀xF ⊗ G ⟿ ∃x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∃xF ⊗ G ⟿ ∀x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∀xG ⟿ ∃x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∃xG ⟿ ∀x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ========================
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (a ⊗ ∀xB) ⊗ c ⟿ ∃x(wk(a) ⊗ B) ⊗ c ⟿ ∀x((wk(a) ⊗ B) ⊗ wk(c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF : (arity : Arity) → ∀ {|a| : Arity} → Vec ℕ (++arity |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  with decBool (lessNat |a| arity)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x with compare arity |a|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.(suc (k + arity))} |f| | yes x | less (diff k refl) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl with lessNat arity arity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl | false = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF zero {.zero} |f| | yes true | equal refl | true = {!!} ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF (suc arity) {.(suc arity)} |f| | yes true | equal refl | true = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x | greater gt = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x with decBool (lessNat arity |a|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | yes x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | no x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- = case arity <? |a| of λ { false → {!!} ; true → {!!} }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a function of a given arity to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Arity → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions arity ⟨ |v| , |a| , |f| ⟩ = ⟨ |v| , max arity |a| , augmentF arity |f| ⟩


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data DomainSignifier : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   free : Nat → DomainSignifier

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartiallyAppliedFunction : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constant : PartiallyAppliedFunction 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {n} → PartiallyAppliedFunction 0 → PartiallyAppliedFunction (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Term = PartiallyAppliedFunction 0

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartialyAppliedPredicate : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   statement : PartialyAppliedPredicate 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   partial : ∀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Language : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Name = String

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Function : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     name : Name
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     number-of-arguments : Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Vec

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Function : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : Function →

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Sentence : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   predication : Name →

-- -- -- {-

-- -- -- record Variables : Set where
-- -- --   constructor V⟨_⟩
-- -- --   field
-- -- --     number : Nat
-- -- -- open Variables

-- -- -- record Functions (υ : Variables) : Set where
-- -- --   constructor S⟨_⟩
-- -- --   field
-- -- --     number : Fin (suc (number υ)) → Nat
-- -- -- open Functions

-- -- -- record Alphabet : Set where
-- -- --   constructor α⟨_,_⟩
-- -- --   field
-- -- --     variables : Variables
-- -- --     functions : Functions variables
-- -- -- open Alphabet

-- -- -- record Variable (α : Alphabet) : Set where
-- -- --   constructor v⟨_⟩
-- -- --   field
-- -- --     name : Fin (number (variables α))
-- -- -- open Variable

-- -- -- record Function (α : Alphabet) : Set where
-- -- --   constructor s⟨_,_⟩
-- -- --   field
-- -- --     arity : Fin ∘ suc ∘ number ∘ variables $ α
-- -- --     name : Fin $ number (functions α) arity
-- -- -- open Function

-- -- -- data Term (𝑽 : Nat) : Set where
-- -- --   variable : Fin 𝑽 → Term 𝑽
-- -- --   function : (𝑓 : Function α) → {ι₋₁ : Size< ι₀} → Vec (Term {ι₋₁} α) (finToNat (arity 𝑓)) →
-- -- --              Term {ι₀} α

-- -- -- record Predication (alphabet : Alphabet) : Set where
-- -- --   constructor P⟨_,_,_⟩
-- -- --   field
-- -- --     name : Nat
-- -- --     arity : Nat
-- -- --     terms : Vec (Term alphabet) arity
-- -- -- open Predication
-- -- -- -}

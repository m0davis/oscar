--{-# OPTIONS --rewriting #-}
--{-# OPTIONS --exact-split #-}
--{-# OPTIONS --show-implicit #-}
--{-# OPTIONS --allow-unsolved-metas #-}

module NaturalDeduction where

open import OscarPrelude
open import Delay
open import Successor
open import Membership
open import DecidableMembership renaming (DecidableMembership to RDecidableMembership)
open import VariableName
open import FunctionName
open import PredicateName
open import Arity
open import Vector
open import 𝕃ist
open import TermByFunctionNames
open import Term
--open import TermUnification
open import MGU-revised
open import HasNegation
open import Formula
open import IsFormula
open import 𝓕ormula
open import HasNeitherNor
open import IsLiteralFormula
open import LiteralFormula
open import IsPropositionalFormula
open import 𝓐ssertion
open import 𝓢equent
open import Sequent
open import 𝑱udgement
open import IsLiteralSequent
open import LiteralSequent
open import Problem
open import IsLiteralProblem
open import LiteralProblem
open import Element
open import Elements
open import TruthValue
open import Interpretation
open import HasSatisfaction
open import InterpretationEqualityExceptAtVariableName
open import HasDecidableSatisfaction
open import Validation
open import HasDecidableValidation
open import HasSubstantiveDischarge
open import HasDecidableSubstantiveDischarge
open import HasVacuousDischarge
open import HasSalvation
open import SubstantiveDischargeIsConsistent
open import SubstantiveDischargeIsReflexive
open import HasDecidableVacuousDischarge
open import HasDecidableSalvation
open import TermCode
open import TermNode
open import FindTermNode
open import Theorem1

-- infixr 1 ,_
-- pattern  ,_ p = _ , p

-- pattern ◁pattern c₁∈xs c₁≽s c₂∈xs c₂≽~s = , (((, (c₁∈xs , c₁≽s)) , (, (c₂∈xs , c₂≽~s))))

-- negationEliminationRule : (I : Interpretation) (φ : Formula) → I ⊨ ~ (~ φ) → I ⊨ φ
-- negationEliminationRule I φ (¬[I⊭φ×I⊭φ] , _) with I ⊨? φ
-- … | yes I⊨φ = I⊨φ
-- … | no I⊭φ = ⊥-elim $ ¬[I⊭φ×I⊭φ] $ I⊭φ , I⊭φ

-- -- justifieds simplification and ... more?
-- simplificationRule₁ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ Formula.logical φ₁ φ₂ → I ⊨ Formula.logical φ₁ φ₁
-- simplificationRule₁ I φ₁ φ₂ x = (fst x) , (fst x)

-- simplificationRule₂ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ Formula.logical φ₁ φ₂ → I ⊨ Formula.logical φ₂ φ₂
-- simplificationRule₂ I φ₁ φ₂ x = snd x , snd x

-- -- logical (logical (logical p p) q) (logical (logical p p) q)
-- {-
-- conditionalizationRule : (I : Interpretation) (p q : Formula) → I ⊨ q → I ⊨ (p ⊃ q ╱ (p ∷ []) )
-- conditionalizationRule I p q ⊨q (_ , _) = let prf = λ { (_ , ⊭q) → ⊭q ⊨q} in prf , prf
-- --let ⊨p = {!-⊨p p (here [])!} in (λ { (x , ~q) → ~q ⊨q}) , (λ { (x , y) → y ⊨q})
-- -}

-- modusPonens : (I : Interpretation) (p q : Formula) → I ⊨ p → I ⊨ (p ⊃ q) → I ⊨ q
-- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) with I ⊨? q
-- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | yes x = x
-- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | no x = ⊥-elim (~[~p&~p&~q] ((λ { (x₁ , y) → y P}) , (λ x₁ → x x₁)))

-- -- -- -- -- -- data SkolemFormula {ι : Size} (α : Alphabet) : Set where
-- -- -- -- -- --   atomic : Predication α → SkolemFormula α
-- -- -- -- -- --   logical : {ι¹ : Size< ι} → SkolemFormula {ι¹} α → {ι² : Size< ι} → SkolemFormula {ι²} α → SkolemFormula {ι} α

-- -- -- -- -- -- record Alphabet₊ᵥ (α : Alphabet) : Set where
-- -- -- -- -- --   constructor α₊ᵥ⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- --     .one-variable-is-added : (number ∘ variables $ alphabet) ≡ suc (number ∘ variables $ α)
-- -- -- -- -- --     .there-are-no-functions-of-maximal-arity : number (functions alphabet) zero ≡ zero
-- -- -- -- -- --     .shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → number (functions alphabet) (suc ytira₁) ≡ number (functions α) ytira₀
-- -- -- -- -- -- open Alphabet₊ᵥ

-- -- -- -- -- -- record Alphabet₊ₛ (α : Alphabet) : Set where
-- -- -- -- -- --   constructor α₊ₛ⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- open Alphabet₊ₛ

-- -- -- -- -- -- {-
-- -- -- -- -- --   toSkolemFormula
-- -- -- -- -- --   ∀x(F x v₀ v₁) ⟿ F v₀ v₁ v₂
-- -- -- -- -- --   ∃x(F x v₀ v₁) ⟿ F (s₀͍₂ v₀ v₁) v₀ v₁
-- -- -- -- -- --   ∀x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F v₀ (s₀͍₂ v₁ v₂) v₂
-- -- -- -- -- --   ∃x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F (s₀͍₂ v₀ v₁) (s₁͍₂ v₁ v₂) v₂
-- -- -- -- -- --   F v₀ ⊗ G v₀ ⟿ F v₀ ⊗ G v₀
-- -- -- -- -- --   ∀x(F x v₀ v₁) ⊗ ∀x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₂ v₃ ⊗ G v₁ (s₀͍₂ v₀ v₃) v₃

-- -- -- -- -- --   ∀x(F x v₀ v₁) ⊗ ∃x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₁ v₂ ⊗ G (s₀͍₁ v₂) (s₁͍₂ (s₀͍₂ v₂) v₂) v₂

-- -- -- -- -- --   Φ₀ = ∃x(G x (s₀͍₂ x v₁) v₁) has alphabet of 2 variables, skolem functions: 0, 0, 1
-- -- -- -- -- --   this is existential {α₊ₛ} Φ₁, where
-- -- -- -- -- --     Φ₁ = G (s₀͍₂ v₀ v₁) (s₁͍₂ (s₀͍₂ v₀ v₁)) v₁
-- -- -- -- -- --     α₊ₛ = ⟨ 2 , 0 ∷ 0 ∷ 2 ∷ [] ⟩

-- -- -- -- -- --   maybe Φ₋₁ = ∀y∃x(G x (s₀͍₂ x v₀) v₀)
-- -- -- -- -- --    and  Φ₋₂ = ∀z∀y∃x(G x (s₀͍₂ x z) z), finally having no free variables, but nevertheless having skolem functions! these are user-defined functions, so this notion of Alphabet is somehow wrong. we have also left out constants (i.e. user-defined skolem-functions of arity 0)

-- -- -- -- -- --   Instead, take the alphabet as defining
-- -- -- -- -- --     a stack of free variables
-- -- -- -- -- --     a matrix (triangle?) of skolem functions

-- -- -- -- -- --   Let's try to reverse Φ₁ from a Skolem to a 1st-order formula. Is there a unique way to do it?
-- -- -- -- -- --   Φ₀' = ∀x(G (s₀͍₂ x v₀) (s₁͍₂ (s₀͍₂ x v₀)) v₀

-- -- -- -- -- --   Nope!


-- -- -- -- -- --   toSkolemFormula of



-- -- -- -- -- -- -}

-- -- -- -- -- -- -- toSkolemFormula (logical Φ₁ Φ₂) ⟿
-- -- -- -- -- -- --   let α' , φ₁ = toSkolemFormula Φ₁
-- -- -- -- -- -- --       Φ₂' = transcodeToAugmentedAlphabet Φ₂ α'
-- -- -- -- -- -- --       α'' , φ₂' = toSkolemFormula Φ₂'
-- -- -- -- -- -- --       φ₁' = transcodeToAugmentedAlphabet φ₁ α''

-- -- -- -- -- -- {-
-- -- -- -- -- -- given Δv = #varibles α' - #variables α
-- -- -- -- -- -- for every variable v in α, v in Φ, v stays the same in Φ'
-- -- -- -- -- -- for the added variable v⁺ in α₊ - α, v⁺ in Φ, v⁺ ⟿ v⁺ + Δv in transcode (universal {α₊} Φ)
-- -- -- -- -- -- α'₊ = α' + 1 variable
-- -- -- -- -- -- -}

-- -- -- -- -- -- -- record AddVariable (A : Alphabet → Set) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     addVariableToAlphabet : {α : Alphabet} → A α → {α₊ : Alphabet} → Alphabet₊ᵥ α₊ → A α₊

-- -- -- -- -- -- -- instance
-- -- -- -- -- -- --   AddVariableFirstOrderFormula : AddVariable FirstOrderFormula
-- -- -- -- -- -- --   AddVariableFirstOrderFormula = {!!}

-- -- -- -- -- -- -- #variables = number ∘ variables

-- -- -- -- -- -- -- #functions_ofArity_ : Alphabet → Nat → Nat
-- -- -- -- -- -- -- #functions α⟨ V⟨ #variables ⟩ , S⟨ #functions ⟩ ⟩ ofArity arity = if′ lessNat arity (suc #variables) then #functions (natToFin arity) else 0

-- -- -- -- -- -- -- record _⊇_ (α' α : Alphabet) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     at-least-as-many-variables : #variables α' ≥ #variables α
-- -- -- -- -- -- --     at-least-as-many-functions : ∀ {arity} → arity < #variables α → #functions α' ofArity arity ≥ #functions α ofArity arity

-- -- -- -- -- -- -- record AddAlphabet (α-top α-bottom : Alphabet) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     alphabet : Alphabet

-- -- -- -- -- -- -- record Transcodeable (A : Alphabet → Set) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     transcode : {α' α : Alphabet} → ⦃ _ : α' ⊇ α ⦄ → A α → A α'

-- -- -- -- -- -- -- open Transcodeable ⦃ … ⦄

-- -- -- -- -- -- -- record TransferAlphabet {α' α : Alphabet} (α'⊇α : α' ⊇ α) (α₊ : Alphabet₊ᵥ α) (Φ : FirstOrderFormula (alphabet α₊)) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- --     firstOrderFormula : FirstOrderFormula alphabet


-- -- -- -- -- -- -- instance
-- -- -- -- -- -- --   TranscodeablePredication : Transcodeable Predication
-- -- -- -- -- -- --   TranscodeablePredication = {!!}

-- -- -- -- -- -- --   TranscodeableAlphabet+Variable : Transcodeable Alphabet₊ᵥ
-- -- -- -- -- -- --   TranscodeableAlphabet+Variable = {!!}

-- -- -- -- -- -- --   TranscodeableSkolemFormula : Transcodeable SkolemFormula
-- -- -- -- -- -- --   TranscodeableSkolemFormula = {!!}

-- -- -- -- -- -- --   TranscodeableFirstOrderFormula : Transcodeable FirstOrderFormula
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (atomic p) = atomic (transcode p)
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (logical Φ₁ Φ₂) = logical (transcode Φ₁) (transcode Φ₂)
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula {α'} {α} ⦃ α'⊇α ⦄ (universal {α₊} Φ) = {!!} -- universal {_} {_} {transcode α₊} (transcode Φ)

-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (existential Φ) = {!!}

-- -- -- -- -- -- -- --(α' α : Alphabet) (α'⊇α : α' ⊇ α) (α₊ : Alphabet+Variable α) (Φ : FirstOrderFormula (alphabet α₊)) → Σ _ λ (α''' : Alphabet) → FirstOrderFormula α'''

-- -- -- -- -- -- -- --FirstOrderFormula (alphabet α₊)
-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- --transcodeIntoAugmentedAlphabet :



-- -- -- -- -- -- -- -- --toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)

-- -- -- -- -- -- -- -- --record IsEquivalentFormulas {α₀ : Alphabet} (φ₀ : SkolemFormula α₀) {α₁ : Alphabet} (Φ₁ : FirstOrderFormula α₁) : Set where
-- -- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- -- --    .atomicCase : {p : Predication α₀} → φ₀ ≡ atomic p → Φ₁ ≡ atomic p




-- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- record Alphabet+Alphabet (α₀ α₁ α₂ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     alphabet :

-- -- -- -- -- -- -- -- -- -- ∀xφ₁(x) ⊗ φ₂ ⟿ ∀x(φ₁ ⊗ φ₂)

-- -- -- -- -- -- -- -- -- -- hasQuantifiers : FirstOrderFormula α → Bool

-- -- -- -- -- -- -- -- -- --record Skolemization {α : Alphabet} (φ : FirstOrderFormula α) : Set where
-- -- -- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- -- -- --    alphabet : Alphabet
-- -- -- -- -- -- -- -- -- --    skolemization : SkolemFormula alphabet

-- -- -- -- -- -- -- -- -- record _IsAugmentationOf_ (α₁ α₀ : Alphabet) : Set where

-- -- -- -- -- -- -- -- -- record AugmentedAlphabet (α : Alphabet) : Set where
-- -- -- -- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- -- -- --     ..laws : alphabet ≡ α
-- -- -- -- -- -- -- -- -- open AugmentedAlphabet

-- -- -- -- -- -- -- -- -- trivialAugmentation : (α : Alphabet) → AugmentedAlphabet α
-- -- -- -- -- -- -- -- -- trivialAugmentation = {!!}

-- -- -- -- -- -- -- -- -- record DisjointRelativeUnion {α : Alphabet} (α¹ α² : AugmentedAlphabet α) : Set where
-- -- -- -- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- --     augmentation : AugmentedAlphabet α
-- -- -- -- -- -- -- -- --     .laws : {!!}
-- -- -- -- -- -- -- -- -- open DisjointRelativeUnion

-- -- -- -- -- -- -- -- -- disjointRelativeUnion : {α : Alphabet} → (α¹ α² : AugmentedAlphabet α) → DisjointRelativeUnion α¹ α²
-- -- -- -- -- -- -- -- -- disjointRelativeUnion = {!!}

-- -- -- -- -- -- -- -- -- -- inAugmentedAlphabet : {α : Alphabet} → (α¹ : AugmentedAlphabet α) → SkolemFormula α → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- -- -- -- inAugmentedAlphabet = {!!}

-- -- -- -- -- -- -- -- -- -- toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (atomic 𝑃) = trivialAugmentation α₀ , atomic 𝑃
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) with toSkolemFormula φ₁ | toSkolemFormula φ₂
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) | α¹ , Φ₁ | α² , Φ₂ = augmentation (disjointRelativeUnion α¹ α²) , logical {!inAugmentedAlphabet (augmentation (disjointRelativeUnion α¹ α²)) Φ₁!} {!Φ₂!}
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (universal x) = {!!}
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (existential x) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- --FunctionArity = Fin ∘ suc ∘ size
-- -- -- -- -- -- -- -- -- -- -- -- -- --FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- --     |v| : Nat -- number of variables
-- -- -- -- -- -- -- -- -- -- -- -- -- --     |f| : Fin (suc |v|) → Nat -- number of functions of each arity, |v| through 0

-- -- -- -- -- -- -- -- -- -- -- -- -- -- open Alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FunctionArity = Fin ∘ suc ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   variable : VariableName alphabet → Term alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {arity : FunctionArity alphabet} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              FunctionName alphabet (natToFin (|v| alphabet) - arity) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∀ {j : Size< i} → Vec (Term {j} alphabet) (finToNat arity) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Term {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PredicateArity = Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PredicateName = Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a zeroth-order formula? (i.e. no quantifiers)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data NQFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → NQFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → NQFormula {j} alphabet → {k : Size< i} → NQFormula {k} alphabet → NQFormula {i} alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedByVariable (alphabet₀ alphabet₁ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     one-variable-is-added : |v| alphabet₁ ≡ suc (|v| alphabet₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     function-domain-is-zero-at-new-variable : |f| alphabet₁ zero ≡ 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → |f| alphabet₁ (suc ytira₁) ≡ |f| alphabet₀ ytira₀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentVariables (alphabet₀ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     alphabet₁ : Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     augmentation : AugmentedByVariable alphabet₀ alphabet₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open AugmentVariables

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : (alphabet : Alphabet) → AugmentVariables alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables ⟨ |v| , |f| ⟩ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   { alphabet₁ = ⟨ suc |v| , (λ { zero → zero ; (suc ytira) → |f| ytira}) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ; augmentation =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     { one-variable-is-added = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; function-domain-is-zero-at-new-variable = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; shifted-function-matches = cong |f| ∘ finToNat-inj } }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- |f|₀ = |f|₀ + 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions ⟨ |v| , |f| ⟩ = ⟨ |v| , (λ { zero → suc (|f| zero) ; (suc ytira) → |f| (suc ytira) }) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data QFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → QFormula {j} alphabet → {k : Size< i} → QFormula {k} alphabet → QFormula {i} alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   universal : QFormula (alphabet₁ (augmentVariables alphabet)) → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   existential : QFormula (augmentFunctions alphabet) → QFormula alphabet

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Assignment (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     μ : VariableName alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑓 : ∀ {arity} → FunctionName alphabet arity → Vec Domain (finToNat arity) → Domain

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm : ∀ {i alphabet} → Assignment alphabet → Term {i} alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm ⟨ μ , _ ⟩ (variable x) = μ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm 𝑎@(⟨ μ , 𝑓 ⟩) (function f x) = 𝑓 f (evaluateTerm 𝑎 <$> x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Interpretation (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Assignment
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑎 : Assignment alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑃 : PredicateName → ∀ {arity} → Vec Domain arity → Bool

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula : ∀ {i alphabet} → Interpretation alphabet → NQFormula {i} alphabet → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula ⟨ 𝑎 , 𝑃 ⟩ (atomic name terms) = 𝑃 name $ evaluateTerm 𝑎 <$> terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula I (logical formula₁ formula₂) = not (evaluateNQFormula I formula₁) && not (evaluateNQFormula I formula₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record IsADisjointUnionOfNQFormulas
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {alphabet₁ alphabet₂ alphabet₁₊₂ : Alphabet}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁ : NQFormula alphabet₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₂ : NQFormula alphabet₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁₊₂ : NQFormula alphabet₁₊₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     alphabet-size : |v| alphabet₁₊₂ ≡ |v| alphabet₁ + |v| alphabet₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --|f| alphabet₁₊₂ ytira


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ----record AlphabetSummed  (alphabet₀ alphabet₁ : Alphabet)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets : Alphabet → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets ⟨ |v|₁ , |f|₁ ⟩ ⟨ |v|₂ , |f|₂ ⟩ = ⟨ (|v|₁ + |v|₂) , (λ x → if′ finToNat x ≤? |v|₁ && finToNat x ≤? |v|₂ then {!!} else {!!}) ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sup : ∀ {alphabet₁} → Formula alphabet₁ → ∀ {alphabet₂} → Formula alphabet₂ → Σ _ λ alphabet₁₊₂ → Formula alphabet₁₊₂ × Formula alphabet₁₊₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sup {⟨ |v|₁ , |a|₁ , |f|₁ ⟩} φ₁ {⟨ |v|₂ , |a|₂ , |f|₂ ⟩} φ₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf : ∀ {alphabet} → Formula alphabet → Σ _ λ alphabet+ → Formula₀ alphabet+
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --universal (P 0) = ∀ x → P x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (∀ x ∃ y (P x y)) ∨ (∀ x ∃ y (P x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- P x₀ (s₀͍₁ x₀) ∨ P x₁ (s₁͍₁ x₁)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}






-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| : (arity : Arity) → Vec ℕ (suc |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a variable to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN : ∀ {n} → Fin n → (Fin n → Nat) → Fin n → Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- increaseTabulationAtN = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedFunctions {|a| : Arity} (arity : Arity) (|f| : Vec ℕ (++arity |a|)) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA : ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     maxA-law : max arity |a| ≡ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ++|f| : Vec ℕ maxA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f-law : increaseTabulationAt arity (indexVec |f|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ⊗ b ≡ False a and False b

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- now, we can define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ¬a = a ⊗ a ≡ False a and False a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∨ b = ¬(a ⊗ b) ≡ False (False a and False b) and False (False a and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∧ b = ¬(¬a ∨ ¬b) = ¬(¬(¬a ⊗ ¬b)) = ¬a ⊗ ¬b = False (False a and False a) and False (False b and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a → b = ¬a ∨ b = (a ⊗ a) ∨ b = ¬((a ⊗ a) ⊗ b) = ((a ⊗ a) ⊗ b) ⊗ ((a ⊗ a) ⊗ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- conversion to prenex
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∀xF ⊗ G ⟿ ∃x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∃xF ⊗ G ⟿ ∀x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∀xG ⟿ ∃x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∃xG ⟿ ∀x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ========================
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (a ⊗ ∀xB) ⊗ c ⟿ ∃x(wk(a) ⊗ B) ⊗ c ⟿ ∀x((wk(a) ⊗ B) ⊗ wk(c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF : (arity : Arity) → ∀ {|a| : Arity} → Vec ℕ (++arity |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  with decBool (lessNat |a| arity)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x with compare arity |a|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.(suc (k + arity))} |f| | yes x | less (diff k refl) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl with lessNat arity arity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {.arity} |f| | yes x | equal refl | false = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF zero {.zero} |f| | yes true | equal refl | true = {!!} ∷ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF (suc arity) {.(suc arity)} |f| | yes true | equal refl | true = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | yes x | greater gt = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x with decBool (lessNat arity |a|)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | yes x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentF arity {|a|} |f| | no x₁ | no x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- = case arity <? |a| of λ { false → {!!} ; true → {!!} }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a function of a given arity to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Arity → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions arity ⟨ |v| , |a| , |f| ⟩ = ⟨ |v| , max arity |a| , augmentF arity |f| ⟩


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data DomainSignifier : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   free : Nat → DomainSignifier

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartiallyAppliedFunction : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constant : PartiallyAppliedFunction 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {n} → PartiallyAppliedFunction 0 → PartiallyAppliedFunction (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Term = PartiallyAppliedFunction 0

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartialyAppliedPredicate : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   statement : PartialyAppliedPredicate 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   partial : ∀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Language : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Name = String

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Function : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     name : Name
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     number-of-arguments : Nat

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Vec

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Function : Set where


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : Function →

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Sentence : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   predication : Name →

-- -- -- -- -- -- {-

-- -- -- -- -- -- record Variables : Set where
-- -- -- -- -- --   constructor V⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     number : Nat
-- -- -- -- -- -- open Variables

-- -- -- -- -- -- record Functions (υ : Variables) : Set where
-- -- -- -- -- --   constructor S⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     number : Fin (suc (number υ)) → Nat
-- -- -- -- -- -- open Functions

-- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- --   constructor α⟨_,_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     variables : Variables
-- -- -- -- -- --     functions : Functions variables
-- -- -- -- -- -- open Alphabet

-- -- -- -- -- -- record Variable (α : Alphabet) : Set where
-- -- -- -- -- --   constructor v⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     name : Fin (number (variables α))
-- -- -- -- -- -- open Variable

-- -- -- -- -- -- record Function (α : Alphabet) : Set where
-- -- -- -- -- --   constructor s⟨_,_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     arity : Fin ∘ suc ∘ number ∘ variables $ α
-- -- -- -- -- --     name : Fin $ number (functions α) arity
-- -- -- -- -- -- open Function

-- -- -- -- -- -- data Term (𝑽 : Nat) : Set where
-- -- -- -- -- --   variable : Fin 𝑽 → Term 𝑽
-- -- -- -- -- --   function : (𝑓 : Function α) → {ι₋₁ : Size< ι₀} → Vec (Term {ι₋₁} α) (finToNat (arity 𝑓)) →
-- -- -- -- -- --              Term {ι₀} α

-- -- -- -- -- -- record Predication (alphabet : Alphabet) : Set where
-- -- -- -- -- --   constructor P⟨_,_,_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     name : Nat
-- -- -- -- -- --     arity : Nat
-- -- -- -- -- --     terms : Vec (Term alphabet) arity
-- -- -- -- -- -- open Predication
-- -- -- -- -- -- -}


-- -- module NotUsed where

-- --   -- thought it might be easier to use this
-- --   module UsingContainerList where

-- --     record TermNode : Set
-- --      where
-- --       inductive
-- --       field
-- --         children : List (TermCode × TermNode)
-- --         number : Nat

-- --     open TermNode

-- --     _child∈_ : TermCode → TermNode → Set
-- --     _child∈_ 𝔠 𝔫 = Any ((𝔠 ≡_) ∘ fst) (children 𝔫)

-- --   -- this still has a lambda problem, albeit weirder
-- --   module RememberChildren where

-- --     record TermNode : Set
-- --      where
-- --       inductive
-- --       field
-- --         tests : List TermCode
-- --         children : ∀ {𝔠} → 𝔠 ∈ tests → TermNode
-- --         number : Nat
-- --     open TermNode

-- --     addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 ∉ tests 𝔫 → TermNode → TermNode
-- --     addChild {𝔠} 𝔫 𝔠∉tests𝔫 𝔫' =
-- --       record 𝔫
-- --       { tests = 𝔠 ∷ tests 𝔫
-- --       ; children = λ
-- --         { (here _) → 𝔫'
-- --         ; (there _ 𝔠'∈tests) → children 𝔫 𝔠'∈tests }}

-- --     setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 ∈ tests 𝔫 → TermNode → TermNode
-- --     setChild {𝔠} 𝔫 𝔠∈tests𝔫 𝔫' =
-- --       record 𝔫
-- --       { children = λ {𝔠'} 𝔠'∈tests𝔫' → ifYes 𝔠' ≟ 𝔠 then 𝔫' else children 𝔫 𝔠'∈tests𝔫' }

-- --     storeTermCodes : List TermCode → Nat → StateT TermNode Identity Nat
-- --     storeTermCodes [] 𝔑 = return 𝔑
-- --     storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
-- --       𝔫 ← get -|
-- --       case 𝔠 ∈? tests 𝔫 of λ
-- --       { (no 𝔠∉tests) →
-- --         let 𝔑' , 𝔫' = runIdentity $
-- --                       runStateT
-- --                         (storeTermCodes 𝔠s $ suc 𝔑)
-- --                         (record
-- --                           { tests = []
-- --                           ; children = λ ()
-- --                           ; number = suc 𝔑 }) in
-- --         put (addChild 𝔫 𝔠∉tests 𝔫') ~|
-- --         return 𝔑'
-- --       ; (yes 𝔠∈tests) →
-- --         let 𝔑' , 𝔫' = runIdentity $
-- --                       runStateT
-- --                         (storeTermCodes 𝔠s $ suc 𝔑)
-- --                         (children 𝔫 𝔠∈tests) in
-- --         put (setChild 𝔫 𝔠∈tests 𝔫') ~|
-- --         return 𝔑' }

-- --     topNode : TermNode
-- --     topNode = record { tests = [] ; children = λ () ; number = 0 }

-- --     example-store : TermNode
-- --     example-store = snd ∘ runIdentity $ runStateT (storeTermCodes example-TermCodes 0) topNode

-- --     foo : TermNode × TermNode
-- --     foo =
-- --       {!example-store!} ,
-- --       {!snd ∘ runIdentity $ runStateT (storeTermCodes example-TermCodes 10) example-store!}

-- --   -- using a lambda for the children results in extra unnecessary structure when adding to an existing node; perhaps using an explicit mapping? or use another field to state what codes are present in the mapping?
-- --   module NoParents where

-- --     mutual

-- --       record TermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           children : TermCode → Maybe TermNode -- Map TermCode TermNode
-- --           self : TermCode
-- --           number : Nat

-- --       record TopTermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           children : TermCode → Maybe TermNode

-- --     open TermNode
-- --     open TopTermNode

-- --     storeTermCodes : List TermCode → Nat → StateT TermNode Identity ⊤
-- --     storeTermCodes [] _ = return tt
-- --     storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
-- --       𝔫 ← get -|
-- --       case children 𝔫 𝔠 of λ
-- --       { nothing →
-- --         put
-- --           (record 𝔫
-- --             { children =
-- --               λ 𝔠' →
-- --               ifYes 𝔠' ≟ 𝔠 then
-- --                 just ∘ snd ∘ runIdentity $
-- --                 (runStateT
-- --                   (storeTermCodes 𝔠s (suc 𝔑))
-- --                     (record
-- --                       { self = 𝔠
-- --                       ; children = const nothing
-- --                       ; number = suc 𝔑 }))
-- --               else
-- --                 children 𝔫 𝔠' } ) ~|
-- --         return tt
-- --       ; (just 𝔫') →
-- --         put (record 𝔫
-- --               { children =
-- --                 λ 𝔠' →
-- --                 ifYes 𝔠' ≟ 𝔠 then
-- --                   just ∘ snd ∘ runIdentity $
-- --                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
-- --                 else
-- --                   children 𝔫 𝔠' }) ~|
-- --         return tt }

-- --     storeTermCodesAtTop : List TermCode → Nat → StateT TopTermNode Identity ⊤
-- --     storeTermCodesAtTop [] _ = return tt
-- --     storeTermCodesAtTop (𝔠 ∷ 𝔠s) 𝔑 =
-- --       𝔫 ← get -|
-- --       case children 𝔫 𝔠 of λ
-- --       { nothing →
-- --         put
-- --           (record 𝔫
-- --             { children =
-- --               λ 𝔠' →
-- --               ifYes 𝔠' ≟ 𝔠 then
-- --                 just ∘ snd ∘ runIdentity $
-- --                 (runStateT
-- --                   (storeTermCodes 𝔠s (suc 𝔑))
-- --                     (record
-- --                       { self = 𝔠
-- --                       ; children = const nothing
-- --                       ; number = suc 𝔑 }))
-- --               else
-- --                 children 𝔫 𝔠' } ) ~|
-- --         return tt
-- --       ; (just 𝔫') →
-- --         put (record 𝔫
-- --               { children =
-- --                 λ 𝔠' →
-- --                 ifYes 𝔠' ≟ 𝔠 then
-- --                   just ∘ snd ∘ runIdentity $
-- --                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
-- --                 else
-- --                   children 𝔫 𝔠' }) ~|
-- --         return tt }

-- --     initialTopNode : TopTermNode
-- --     initialTopNode = record { children = const nothing }

-- --     example-store : TopTermNode
-- --     example-store = snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 0) initialTopNode

-- --     foo : TopTermNode × TopTermNode
-- --     foo =
-- --       {!example-store!} ,
-- --       {!snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 10) example-store!}

-- --   -- it's tricky to keep the parents up to date when the children change (viz adolescence)
-- --   module FirstTryWithParent where
-- --     mutual

-- --       record TermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           parent : TopTermNode ⊎ TermNode
-- --           self : TermCode
-- --           children : TermCode → Maybe TermNode -- Map TermCode TermNode
-- --           number : Nat

-- --       record TopTermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           children : TermCode → Maybe TermNode

-- --     open TermNode
-- --     open TopTermNode

-- --     storeTermCodes : List TermCode → Nat → StateT TermNode Identity ⊤
-- --     storeTermCodes [] _ = return tt
-- --     storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
-- --       𝔫 ← get -|
-- --       case children 𝔫 𝔠 of λ
-- --       { nothing →
-- --         put
-- --           (record 𝔫
-- --             { children =
-- --               λ 𝔠' →
-- --               ifYes 𝔠' ≟ 𝔠 then
-- --                 just ∘ snd ∘ runIdentity $
-- --                 (runStateT
-- --                   (storeTermCodes 𝔠s (suc 𝔑))
-- --                     (record
-- --                       { parent = right 𝔫
-- --                       ; self = 𝔠
-- --                       ; children = const nothing
-- --                       ; number = suc 𝔑 }))
-- --               else
-- --                 children 𝔫 𝔠' } ) ~|
-- --         return tt
-- --       ; (just 𝔫') →
-- --         put (record 𝔫
-- --               { children =
-- --                 λ 𝔠' →
-- --                 ifYes 𝔠' ≟ 𝔠 then
-- --                   just ∘ snd ∘ runIdentity $
-- --                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
-- --                 else
-- --                   children 𝔫 𝔠' }) ~|
-- --         return tt }

-- --     storeTermCodesAtTop : List TermCode → Nat → StateT TopTermNode Identity ⊤
-- --     storeTermCodesAtTop [] _ = return tt
-- --     storeTermCodesAtTop (𝔠 ∷ 𝔠s) 𝔑 =
-- --       𝔫 ← get -|
-- --       case children 𝔫 𝔠 of λ
-- --       { nothing →
-- --         put
-- --           (record 𝔫
-- --             { children =
-- --               λ 𝔠' →
-- --               ifYes 𝔠' ≟ 𝔠 then
-- --                 just ∘ snd ∘ runIdentity $
-- --                 (runStateT
-- --                   (storeTermCodes 𝔠s (suc 𝔑))
-- --                     (record
-- --                       { parent = left 𝔫
-- --                       ; self = 𝔠
-- --                       ; children = const nothing
-- --                       ; number = suc 𝔑 }))
-- --               else
-- --                 children 𝔫 𝔠' } ) ~|
-- --         return tt
-- --       ; (just 𝔫') →
-- --         put (record 𝔫
-- --               { children =
-- --                 λ 𝔠' →
-- --                 ifYes 𝔠' ≟ 𝔠 then
-- --                   just ∘ snd ∘ runIdentity $
-- --                   runStateT (storeTermCodes 𝔠s 𝔑) 𝔫'
-- --                 else
-- --                   children 𝔫 𝔠' }) ~|
-- --         return tt }

-- --     initialTopNode : TopTermNode
-- --     initialTopNode = record { children = const nothing }

-- --     example-store : TopTermNode
-- --     example-store = snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 0) initialTopNode

-- --     foo : TopTermNode
-- --     foo = {!example-store!}
-- --
-- --
-- -- _⟪_⟫_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
-- --         A → (A → B → C) → B → C
-- -- x ⟪ f ⟫ y = f x y
-- --
-- -- {-
-- -- infixr 9 _∘₂′_
-- -- _∘₂′_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
-- --          (C → D) → (A → B → C) → (A → B → D)
-- -- _∘₂′_ = _∘′_ ∘ _∘′_
-- -- {-# INLINE _∘₂′_ #-}
-- --
-- -- infixr 9 _∘₂′_
-- -- _∘₂′_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
-- --          (C → D) → (A → B → C) → (A → B → D)
-- -- _∘₂′_ = _∘′_ ∘ _∘′_
-- -- {-# INLINE _∘₂′_ #-}
-- -- -}
-- -- {-
-- -- infixr 9 _∘₂_
-- -- _∘₂_ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → B x → C x
-- --          (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
-- --          ∀ x → C x (g x)
-- -- _∘₂_ = _∘′_ ∘ _∘′_
-- -- {-# INLINE _∘₂′_ #-}
-- -- -}


module Oscar.Object {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Category.Category
open import Oscar.Category.Functor
open import Oscar.Category.Morphism
open import Oscar.Category.Semifunctor
open import Oscar.Category.Semigroupoid
open import Oscar.Category.Setoid
open import Oscar.Data.AList FunctionName
open import Oscar.Data.Equality
open import Oscar.Data.Equality.properties
open import Oscar.Data.Fin
open import Oscar.Data.List
open import Oscar.Data.Nat
open import Oscar.Data.Product
open import Oscar.Data.Step FunctionName
open import Oscar.Data.Term FunctionName
open import Oscar.Data.Term.internal.SubstituteAndSubstitution FunctionName
open import Oscar.Data.Unit
open import Oscar.Function
open import Oscar.Level

{-
List : Set
ListNatAction : Nat → Set
ListNatMorphism : Nat → Nat → Set

Nat : Set
NatNatAction : Nat → Set
NatNatMorphism : Nat → Nat → Set
-}

{-
data ⋆ : Set where
  ∅ : ⋆
  ↧ : ⋆ → ⋆

data ⟱ {a} {A : Set a} : Set a where



data Nat[_↦_] (m : Nat) : Nat → Set where
  zero : Nat[ m ↦ m ]
  suc : ∀ {n} → Nat[ m ↦ n ] → Nat[ m ↦ suc n ]

_+²_ : ∀ {i₂ i₃} → Nat[ i₂ ↦ i₃ ] → ∀ {i₁} → Nat[ i₁ ↦ i₂ ] → Nat[ i₁ ↦ i₃ ]
zero +² y = y
suc x +² y = suc (x +² y)

data

Nat↥ = Fin

bar = Nat[ 0 ↦ 3 ]
br = Nat
br2 = Nat↥ 3
-}

data Object : Set where
  alist : Object
  finterm : Object
  termterm : Object
  termsterms : Nat → Object
  stepstep : Object
  listStepN : Nat → Object
  termtermN : Nat → Object
  list∘ : Object → Object

{-
object⋆ : Object → Set _
object⋆ alist = Nat
object⋆ finterm = Nat
object⋆ termterm = Nat
object⋆ (termsterms N) = Nat
object⋆ stepstep = Nat
object⋆ (listStepN _) = ⊤
object⋆ (termtermN _) = ⊤

objectMorphism : (o : Object) → Morphism (object⋆ o) 𝔣 𝔣
objectMorphism alist = ⇧ AList
objectMorphism finterm = Fin ⇨ Term
objectMorphism termterm = Term ⇨ Term
objectMorphism (termsterms N) = Terms N ⇨ Terms N
objectMorphism stepstep = Step ⇨ Step
Setoid.⋆ ((objectMorphism (listStepN n) Morphism.⇒ _) _) = List (Step n)
IsSetoid._≋_ (Setoid.isSetoid ((objectMorphism (listStepN N) Morphism.⇒ _) _)) = _≡_
Setoid.⋆ ((objectMorphism (termtermN n) Morphism.⇒ _) _) = Term n → Term n
IsSetoid._≋_ (Setoid.isSetoid ((objectMorphism (termtermN N) Morphism.⇒ _) _)) = _≡̇_
IsSetoid._≋_ (Morphism.isSetoid (objectMorphism (termtermN N))) = _≡̇_
-}

objectCategory : Object → Category lzero 𝔣 𝔣
objectCategory alist = {!!}
objectCategory finterm = 𝔾₁
objectCategory termterm = 𝔾₂
objectCategory (termsterms N) = 𝔾₂ₛ N
objectCategory stepstep = {!!}
objectCategory (listStepN x) = {!!}
objectCategory (termtermN x) = {!!}
Semigroupoid.⋆ (Category.semigroupoid (objectCategory (list∘ G))) = List (Category.⋆ (objectCategory G))
Morphism._⇒_ (Semigroupoid.𝔐 (Category.semigroupoid (objectCategory (list∘ G)))) = {!!}
Morphism.isSetoid (Semigroupoid.𝔐 (Category.semigroupoid (objectCategory (list∘ G)))) = {!!}
Semigroupoid._∙_ (Category.semigroupoid (objectCategory (list∘ G))) = {!!}
Semigroupoid.isSemigroupoid (Category.semigroupoid (objectCategory (list∘ G))) = {!!}
Category.ε (objectCategory (list∘ G)) = {!!}
Category.isCategory (objectCategory (list∘ G)) = {!!}

data Arrow : Object → Object → Set where
  unpack : Arrow alist finterm
  substitute : Arrow finterm termterm
  substitutes : (N : Nat) → Arrow finterm (termsterms N)
  stepify : Arrow termterm stepstep
  collapse : (n : Nat) → Arrow (listStepN n) (termtermN n)
  reduce : (n : Nat) → Arrow (termtermN n) termterm
  COMPOSE : ∀ {o₂ o₃} → Arrow o₂ o₃ → ∀ {o₁} → Arrow o₁ o₂ → Arrow o₁ o₃

data SimpleArrow : ∀ {o1 o2} → Arrow o1 o2 → Set where
  unpack : SimpleArrow unpack
  substitute : SimpleArrow substitute
  substitutes : (N : Nat) → SimpleArrow (substitutes N)
  stepify : SimpleArrow stepify
  collapse : (n : Nat) → SimpleArrow (collapse n)
  reduce : (n : Nat) → SimpleArrow (reduce n)

import Data.List as LIST
open import Algebra using (Monoid)

serialiseArrow : ∀ {o1 o2} → Arrow o1 o2 → List (∃ λ o1 → ∃ λ o2 → ∃ λ (a : Arrow o1 o2) → SimpleArrow a)
serialiseArrow unpack = (_ , _ , _ , unpack) ∷ []
serialiseArrow substitute = {!!}
serialiseArrow (substitutes N) = {!!}
serialiseArrow stepify = {!!}
serialiseArrow (collapse n) = {!!}
serialiseArrow (reduce n) = {!!}
serialiseArrow (COMPOSE g f) =
  let g' = serialiseArrow g
      f' = serialiseArrow f
  in Monoid._∙_ (LIST.monoid (∃ (λ o1 → ∃ (λ o2 → ∃ SimpleArrow)))) g' f'

open import Data.Empty

eqArrow : ∀ {o1 o2} → Arrow o1 o2 → Arrow o1 o2 → Set
eqArrow x y = serialiseArrow x ≡ serialiseArrow y

open IsSemifunctor ⦃ … ⦄ using () renaming (extensionality to ext; distributivity to dist)

module _
  {𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ 𝔬₃ 𝔪₃ 𝔮₃}
  (c₁ : Semigroupoid 𝔬₁ 𝔪₁ 𝔮₁)
  (c₂ : Semigroupoid 𝔬₂ 𝔪₂ 𝔮₂)
  (c₃ : Semigroupoid 𝔬₃ 𝔪₃ 𝔮₃)
  where
  private
    module 𝔊₁ = Semigroupoid c₁
    module 𝔊₂ = Semigroupoid c₂
    module 𝔊₃ = Semigroupoid c₃
  composeS : ∀
    {μ₁₂ : 𝔊₁.⋆ → 𝔊₂.⋆}
    (𝔣₁₂ : ∀ {x y} → x 𝔊₁.↦ y → μ₁₂ x 𝔊₂.↦ μ₁₂ y)
    {μ₂₃ : 𝔊₂.⋆ → 𝔊₃.⋆}
    (𝔣₂₃ : ∀ {x y} → x 𝔊₂.↦ y → μ₂₃ x 𝔊₃.↦ μ₂₃ y)
    ⦃ _ : IsSemifunctor (c₁ , c₂) 𝔣₁₂ ⦄
    ⦃ _ : IsSemifunctor (c₂ , c₃) 𝔣₂₃ ⦄
    → IsSemifunctor (c₁ , c₃) (𝔣₂₃ ∘ 𝔣₁₂)
  IsSemifunctor.extensionality (composeS 𝔣₁₂ 𝔣₂₃ ⦃ isS₁ ⦄ ⦃ isS₂ ⦄) f₁≋f₂ = ext ⦃ isS₂ ⦄ (ext ⦃ isS₁ ⦄ f₁≋f₂)
  IsSemifunctor.distributivity (composeS {μ₁₂} 𝔣₁₂ {μ₂₃} 𝔣₂₃ ⦃ isS₁ ⦄ ⦃ isS₂ ⦄) {x} {y} f {z} g =
    let eq₁ = ext ⦃ isS₂ ⦄ (dist ⦃ isS₁ ⦄ f g)
        eq₂ = dist ⦃ isS₂ ⦄ (𝔣₁₂ f) (𝔣₁₂ g)
        instance _ = IsSetoid.isEquivalence 𝔊₃.isSetoid
    in transitivity eq₁ eq₂

module _
  {𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ 𝔬₃ 𝔪₃ 𝔮₃}
  (c₁ : Category 𝔬₁ 𝔪₁ 𝔮₁)
  (c₂ : Category 𝔬₂ 𝔪₂ 𝔮₂)
  (c₃ : Category 𝔬₃ 𝔪₃ 𝔮₃)
  where
  private
    module 𝔊₁ = Category c₁
    module 𝔊₂ = Category c₂
    module 𝔊₃ = Category c₃
  composeF : ∀
    {μ₁₂ : 𝔊₁.⋆ → 𝔊₂.⋆}
    (𝔣₁₂ : ∀ {x y} → x 𝔊₁.↦ y → μ₁₂ x 𝔊₂.↦ μ₁₂ y)
    {μ₂₃ : 𝔊₂.⋆ → 𝔊₃.⋆}
    (𝔣₂₃ : ∀ {x y} → x 𝔊₂.↦ y → μ₂₃ x 𝔊₃.↦ μ₂₃ y)
    ⦃ _ : IsFunctor (c₁ , c₂) 𝔣₁₂ ⦄
    ⦃ _ : IsFunctor (c₂ , c₃) 𝔣₂₃ ⦄
    → IsFunctor (c₁ , c₃) (𝔣₂₃ ∘ 𝔣₁₂)
  IsFunctor.isSemifunctor (composeF 𝔣₁₂ 𝔣₂₃ ⦃ isF₁ ⦄ ⦃ isF₂ ⦄) = composeS _ _ _ _ _ ⦃ (IsFunctor.isSemifunctor isF₁) ⦄ ⦃ (IsFunctor.isSemifunctor isF₂) ⦄
  IsFunctor.identity (composeF {μ₁₂} 𝔣₁₂ 𝔣₂₃ ⦃ isF₁ ⦄ ⦃ isF₂ ⦄) x =
    let f₁₂ε≋ε = identity ⦃ isF₁ ⦄ x
        f₂₃f₁₂ε≋f₂₃ε = ext ⦃ IsFunctor.isSemifunctor isF₂ ⦄ f₁₂ε≋ε
        f₂₃ε≋ε = identity ⦃ isF₂ ⦄ (μ₁₂ x)
        instance _ = IsSetoid.isEquivalence 𝔊₃.isSetoid
    in transitivity f₂₃f₁₂ε≋f₂₃ε f₂₃ε≋ε

--𝔬₁ 𝔪₁ 𝔮₁ 𝔬₃ 𝔪₃ 𝔮₃
--composeF 𝔣₁₂ 𝔣₂₃ = (c₁ , c₃) , (𝔣₂₃ ∘ 𝔣₁₂)

arrowIsFunctor : ∀ {o₁ o₂} → Arrow o₁ o₂
  → ∃ λ μ
  → (let c1 = objectCategory o₁)
    (let c2 = objectCategory o₂)
    (let module 𝔊₁ = Category c1)
    (let module 𝔊₂ = Category c2)
  → ∃ λ (f : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y)
  → (IsFunctor (objectCategory o₁ , objectCategory o₂) {μ} f)
arrowIsFunctor unpack = {!!}
arrowIsFunctor substitute = _ , _ , IsFunctor𝔾₁,₂◂
arrowIsFunctor (substitutes N) = _ , _ , IsFunctor𝔾₁,₂ₛ◂ {N}
arrowIsFunctor stepify = {!!}
arrowIsFunctor (collapse n) = {!!}
arrowIsFunctor (reduce n) = {!!}
arrowIsFunctor (COMPOSE a1 a2) =
  let _ , _ , isF1 = arrowIsFunctor a1
      _ , _ , isF2 = arrowIsFunctor a2
  in _ , _ , composeF _ _ _ _ _ ⦃ isF2 ⦄ ⦃ isF1 ⦄

arrowFunctor : ∀ {o₁ o₂} → Arrow o₁ o₂ → Functor _ _ _ _ _ _
arrowFunctor {o₁} {o₂} a =
  let cs , f , IF = arrowIsFunctor a
      instance _ = IF
  in (objectCategory o₁ , objectCategory o₂) , f

category : Category _ _ _
Semigroupoid.⋆ (Category.semigroupoid category) = Object
Setoid.⋆ ((Semigroupoid.𝔐 (Category.semigroupoid category) Morphism.⇒ o1) o2) = Arrow o1 o2
IsSetoid._≋_ (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid category) Morphism.⇒ x) x₁)) = {!!}
IsSetoid.isEquivalence (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid category) Morphism.⇒ x) x₁)) = {!!}
IsSetoid._≋_ (Morphism.isSetoid (Semigroupoid.𝔐 (Category.semigroupoid category))) = eqArrow
IsSetoid.isEquivalence (Morphism.isSetoid (Semigroupoid.𝔐 (Category.semigroupoid category))) = {!!}
Semigroupoid._∙_ (Category.semigroupoid category) g f = COMPOSE g f
IsSemigroupoid.extensionality (Semigroupoid.isSemigroupoid (Category.semigroupoid category)) = {!!}
IsSemigroupoid.associativity (Semigroupoid.isSemigroupoid (Category.semigroupoid category)) = {!!}
Category.ε category = {!!}
IsCategory.left-identity (Category.isCategory category) = {!!}
IsCategory.right-identity (Category.isCategory category) = {!!}

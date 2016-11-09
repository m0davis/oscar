module Match where

module CategoryStuff where
  open import Level
  open import Function

  record EndoFunctor {α β} (F : Set α → Set β) : Set (suc (α ⊔ β)) where
    field
      map : ∀ {S} {T} → (S → T) → F S → F T

  record Applicative {α β} (F : Set α → Set β) : Set (suc (α ⊔ β)) where
    infixl 2 _⊛_
    field
      pure : ∀ {X} → X → F X
      _⊛_ : ∀ {S T} → F (S → T) → F S → F T

    endoFunctor : EndoFunctor F
    endoFunctor = record { map = _⊛_ ∘ pure }

  instance
    applicativeId : ∀ {a} → Applicative (id {suc a})
    applicativeId = record { pure = id ; _⊛_ = _$_ }

  record Monoid {β} (F : Set β) : Set (suc (β)) where
    field
      ∅ : F
      _+_ : F → F → F

  record Monad {α β} (F : Set α → Set β) : Set (suc (α ⊔ β)) where
    field
      return : ∀ {a} → a → F a
      _≫=_ : ∀ {a b} → F a → (a → F b) → F b

  record Traversable {α} (F : Set α → Set α) : Set (suc α) where
    field
      traverse : ∀ {G S T} {{AG : Applicative G}} → (S → G T) → F S → G (F T)
    traversableEndoFunctor : EndoFunctor F
    traversableEndoFunctor = record { map = traverse {{AG = applicativeId}} }

  record MonadFree {α β χ} (f : Set β → Set χ) (m : Set α → Set β) : Set (suc (α ⊔ β ⊔ χ)) where
    field
      wrap : ∀ {a} → f (m a) → m a

module Test where
  open CategoryStuff
  open import Level

  open import Data.Sum
  open import Data.Maybe
  open import Data.Product

  record List {α} (A : Set α) : Set α where
    inductive
    field
      read : Maybe (A × List A)

  efList : ∀ {α} → EndoFunctor {α} λ X → List X
  efList = record { map = mapList } where
    mapList : ∀ {S T} → (S → T) → List S → List T
    mapList f record { read = (just (s , ss)) } = record { read = just (f s , mapList f ss) }
    mapList f record { read = nothing } = record { read = nothing }

  record Map {α} {β} {Key : Set α} (Value : Key → Set β) : Set (α ⊔ β)  where
    inductive
    field
      toList : List (Σ Key Value)
      getKey : (k : Key) → Maybe (Value k)
      putKV : Σ Key Value → Map Value

  record Map' {α} {β} (Key : Set α) (Value : Set β) : Set (α ⊔ β)  where
    inductive
    field
      toList : List (Key × Value)
      getKey : (k : Key) → Maybe Value
      putKV : Key → Value → Map' Key Value

  mapMap : ∀ {α} {β} {Key : Set α} (Value1 Value2 : Key → Set β) → Map Value1 → Map Value2
  mapMap = {!!}

  efMap' : ∀ {α β} {Key : Set α} → EndoFunctor ((λ (X : Set β) → Map' Key X))
  efMap' = {!!}

  open import Category.Functor.Predicate

  rpfMap : ∀ {α} {β} {Key : Set α} → RawPFunctor {J = Key} λ (X : Key → Set β) → λ x → Map X
  rpfMap = {!!}

module Map where
  open import Level
  open import Data.Maybe
  open import Data.Product
  record Map {α} {β} {Key : Set α} (Value : Key → Set β) : Set (α ⊔ β)  where
    inductive
    field
      firstKey : Maybe Key
      removeKey : (k : Key) → Maybe (Value k × Map Value)
      putKey : Σ Key Value → Map Value
open import Data.Sum
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.Core
open import Relation.Binary.HeterogeneousEquality.Core
open import Level

module _ { α φ } ( f : Set α → Set φ ) ( a : Set α ) (let αφ = α ⊔ φ) (let αφ₁ = suc αφ) where
  record FR : Set αφ₁ where
    inductive
    field
      readtop : a ⊎ ∃ λ x → ∃ λ ( fr : x → FR ) → f x

  record FW : Set αφ₁ where
    field
      mkPure : (x : a) → ∃ λ (fr : FR) → FR.readtop fr ≡ inj₁ x
      mkFree : (x : Set α) → (fs : x → FR) → (fx : f x) → ∃ λ (fr : FR) → FR.readtop fr ≡ inj₂ (x , fs , fx)

data Free { α φ } ( f : Set α → Set φ ) ( a : Set α ) : Set ( suc ( α ⊔ φ ) ) where
  Pure : a → Free f a
  free : ∀ { x : Set α } → ( x → Free f a ) → f x → Free f a

data List { α } ( A : Set α ) : Set α where
  ∅ : List A
  _∷_ : A → List A → List A

open CategoryStuff
instance
  efFree : ∀ { α } { A : Set α } → EndoFunctor {α} λ A → Free List A
  efFree = {!!}

Pattern : ∀ {α} (A : Set α) → Set (suc α)
Pattern A = Free List (A ⊎ A)

flatten : ∀ {α} {A : Set α} → Free List (A ⊎ A) → Free List A
flatten = {!!}

Expression : ∀ {α} (A : Set α) → Set (suc α)
Expression A = Free List A

open Map

Binding : ∀ {α} (A : Set α) → Set (suc α)
Binding A = Map λ (_ : A) → Expression A

Binding' : ∀ {α} (A : Set α) → Set α
Binding' A = Map λ (_ : A) → A

Map' : ∀ {α} (Key : Set α) (Value : Set α) → Set α
Map' Key Value = Map λ (_ : Key) → Value

open import Function using (_∘_ ; _$_ )

record S&M {α} (A : Set α) : Set (suc α) where
  field
    sublis : (Binding A ⊎ Binding' A) → Pattern A → Expression A
    match : (exp : Expression A) → (pat : Pattern A) → Dec $ ∃ λ binding → sublis (inj₁ binding) pat ≡ exp
    1-1-match : (pat₁ : Pattern A) → (pat₂ : Pattern A) → Dec $ ∃ λ binding → sublis (inj₂ binding) pat₁ ≡ flatten pat₂ × sublis (inj₂ binding) pat₂ ≡ flatten pat₁

{-
  sublis : (A → Free List B) → Free List (A + B) → Free List B

  sub : (a : A) → (b : Free List A) → ∃ λ (a' : Free List A) → ∀ x → x ∈ b → x ≢ a → x ∈ a'
  sublis : (m : Map A (Free List A)) → (pat : Free List A) → ∃ λ exp →
              (is-empty m → pat ≡ exp) ×
              (∃ λ kv → ∃ λ m' → m ≡ insert kv m' → sublis m'
-}

{-
  oneOneMatch : (s&m : S&M) → ∀ {A : Set α} → (pat : FR List A) → (exp : FR List A) → (patv : List A) → (expv : List A) → Dec (∃ λ (oom : MR (λ (x : A) → ( A ))) → S&M.sublis s&m ({!!} oom) pat ≡ exp)
  oneOneMatch = {!!}
-}
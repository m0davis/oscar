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

{-
The fixed-point definition in section 2.3 of Generic Programming with Indexed Functors [https://www.researchgate.net/publication/228944016_Generic_Programming_with_Indexed_Functors] no longer type-checks in the latest version of Agda, which complains that μ is not strictly positive:

  data μ {I O : Set} (F : (I ⊎ O) ▶ O) (r : Indexed I) (o : O) : Set where
    ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

I haven't had any luck finding a workaround. The code below is ripped from the article and reproduces the problem I'm having. Thanks in advance for any help solving this.
-}

module IndexedFunctor where
  open import Function using (_∘_)
  open import Relation.Binary.Core using (_≡_)

  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤ ; tt)
  
  open import Data.Product using (_×_ ; ∃)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  
  Indexed : Set → Set₁
  Indexed I = I → Set

  _▷_ : Set → Set → Set₁
  I ▷ O = Indexed I → Indexed O

  record _≃_ (A B : Set) : Set where
    field
      from : A → B
      to   : B → A
      iso₁ : ∀ {x} → to (from x) ≡ x
      iso₂ : ∀ {x} → from (to x) ≡ x

  _∣_ : ∀ {A B} → Indexed A → Indexed B → Indexed (A ⊎ B)
  _∣_ ia _ (inj₁ x) = ia x
  _∣_ _ ib (inj₂ x) = ib x

  mutual
    data _▶_ : Set → Set → Set₁ where
      Z      : ∀ {I O} → I ▶ O
      U      : ∀ {I O} → I ▶ O
      I      : ∀ {I O} → I → I ▶ O
      !      : ∀ {I O} → O → I ▶ O
      _⊕_    : ∀ {I O}   → I ▶ O → I ▶ O → I ▶ O
      _⊗_    : ∀ {I O}   → I ▶ O → I ▶ O → I ▶ O
      _⊚_    : ∀ {I M O} → M ▶ O → I ▶ M → I ▶ O
      _↗_↘_  : ∀ {I I' O O'} → I' ▶ O' → (I' → I) → (O → O') → I ▶ O
      Fix    : ∀ {I O} → (I ⊎ O) ▶ O → I ▶ O
      ∑      : ∀ {I O} → {C : ⊥ ▶ ⊤} → (⟦ C ⟧ (λ _ → ⊤) tt → I ▶ O) → I ▶ O
      Iso    : ∀ {I O} → (C : I ▶ O) → (D : I ▷ O) → ((r : Indexed I) → (o : O) → D r o ≃ ⟦ C ⟧ r o) → I ▶ O

    data μ {I O : Set} (F : (I ⊎ O) ▶ O) (r : Indexed I) (o : O) : Set where
      ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o
   
    ⟦_⟧ : ∀ {I O} → I ▶ O → I ▷ O
    ⟦ Z         ⟧ r o = ⊥
    ⟦ U         ⟧ r o = ⊤
    ⟦ I i       ⟧ r o = r i
    ⟦ F ↗ f ↘ g ⟧ r o = ⟦ F ⟧ (r ∘ f) (g o)
    ⟦ F ⊕ G     ⟧ r o = ⟦ F ⟧ r o ⊎ ⟦ G ⟧ r o
    ⟦ F ⊗ G     ⟧ r o = ⟦ F ⟧ r o × ⟦ G ⟧ r o
    ⟦ F ⊚ G     ⟧ r o = ⟦ F ⟧ (⟦ G ⟧ r) o
    ⟦ Fix F     ⟧ r o = μ F r o
    ⟦ ! o'      ⟧ r o = o ≡ o'
    ⟦ ∑ f       ⟧ r o = ∃ (λ i → ⟦ f i ⟧ r o)
    ⟦ Iso C D e ⟧ r o = D r o

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

{-
module _ { α φ } (let αφ = α ⊔ φ) (let αφ₁ = suc αφ)
         {𝑘} {Key : Set 𝑘}
         {𝑣} 
         (let 𝑘𝑣 = 𝑘 ⊔ 𝑣)
         (let 𝑘𝑣₁ = suc 𝑘𝑣)
         where
  record S&M : Set (suc (αφ₁ ⊔ 𝑘𝑣₁)) where
    field
      sublis : ∀ {A : Set α} → (MR λ (a : A) → FR List A) → FR List A → FR List A
      match : ∀ {A : Set α} → (pat : FR List A) → (exp : FR List A) → (var : List A) → Dec ( ∃ λ (ma : MR (λ (x : A) → ( FR List A ))) → sublis ma pat ≡ exp )

--  oneOneMatch : (s&m : S&M) → ∀ {A : Set α} → (pat : FR List A) → (exp : FR List A) → (patv : List A) → (expv : List A) → Dec (∃ λ (oom : MR (λ (x : A) → ( A ))) → S&M.sublis s&m ({!!} oom) pat ≡ exp)
--  oneOneMatch = {!!}
-}

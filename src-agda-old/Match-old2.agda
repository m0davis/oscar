module Match where

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

record Monoid {α β} (F : Set α → Set β) : Set (suc (α ⊔ β)) where
  field
    ∅ : ∀ {x} → F x
    _+_ : ∀ {x} → F x → F x → F x

record Monoid' {β} (F : Set β) : Set (suc (β)) where
  field
    ∅ : F
    _+_ : F → F → F

module MonoidDefinitions where
  open import Data.Nat.Base
  
  sumMonoid : ∀ {α} → Monoid {α} (λ _ → ℕ)
  sumMonoid = record { ∅ = ℕ.zero ; _+_ = λ x₁ x₂ → x₁ + x₂ }
  
  productMonoid : ∀ {α} → Monoid {α} (λ _ → ℕ)
  productMonoid = record { ∅ = ℕ.suc ℕ.zero ; _+_ = λ x₁ x₂ → x₁ * x₂ }

  sumMonoid' : Monoid' (ℕ)
  sumMonoid' = record { ∅ = ℕ.zero ; _+_ = λ x₁ x₂ → x₁ + x₂ }
  
  productMonoid' : Monoid' (ℕ)
  productMonoid' = record { ∅ = ℕ.suc ℕ.zero ; _+_ = λ x₁ x₂ → x₁ * x₂ }

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

module _ where
  open import Data.List
   
  instance
    foo : ∀ {a} → EndoFunctor {a} {a} List
    foo {a} = record { map = map {a = a} }

  instance
    foMonoidList : ∀ {a} → Monoid {a} List
    foMonoidList = {!!}
   
    endofunctorFun : ∀ {α β} {S : Set β} → EndoFunctor λ (X : Set α) → S → X
    endofunctorFun = {!!}
   
    endofunctorId : ∀ {a} → EndoFunctor (id {suc a})
    endofunctorId = {!!}
   
    endofunctorComp : ∀ {α β χ F G} → EndoFunctor {β} {χ} F → EndoFunctor {α} G → EndoFunctor (F ∘ G)
    endofunctorComp aF aG = {!!}
   
    applicativeFun : ∀ {α β} {S : Set β} → Applicative λ (X : Set α) → S → X
    applicativeFun = record
      { pure = λ x s → x
      ; _⊛_ = λ f a s → f s ( a s )
      }

    applicativeComp : ∀ {α β χ F G} → Applicative {β} {χ} F → Applicative {α} G → Applicative (F ∘ G)
    applicativeComp aF aG = record { pure = pure {{aF}} ∘ pure {{aG}} ; _⊛_ = {!!} } where
      open Applicative {{...}}

open import Data.Product 
open import Data.Sum
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.Core
open import Relation.Binary.HeterogeneousEquality.Core
open import Level

module Test where
--  open import Size

  open import Data.Nat.Base

  record List (A : Set) : Set where
    inductive
    field
      read : Maybe (A × List A)

  record List' : Set₁ where
    inductive
    field
      A : Set
      read : Maybe (A × List')

  record ListX (A : Set) (i : ℕ) : Set where
    inductive
    field
      read : Maybe (∃ λ j → ℕ.suc j ≡ i × A × ListX A j)

    data LX : Set where
      ∅ : LX
      _∷_ : A → LX → LX

  record ListX' (A : Set) : Set where
    inductive
    field
      i : ℕ
      read : Maybe (∃ λ j → ℕ.suc j ≡ i × A × ListX' A)

  record ListX'' : Set₁ where
    inductive
    field
      A : Set
      i : ℕ
      read : Maybe (∃ λ j → ℕ.suc j ≡ i × A × ListX'')

  mapList' : ∀ {S T} → (S → T) → (List'S : List') → (List'.A List'S ≡ S) → ∃ λ (lt : List') → List'.A lt ≡ T
  mapList' {T = T} f record { A = A ; read = (just (a , as)) } refl = (record { A = T ; read = just (f a , {!mapList' f as refl!}) }) , {!!}
  mapList' f record { A = A ; read = nothing } refl = {!!}

  mapList : ∀ {S T} → (S → T) → List S → List T
  mapList f record { read = (just (s , ss)) } = record { read = just (f s , mapList f ss) }
  mapList f record { read = nothing } = record { read = nothing }

  efList : EndoFunctor (λ X → List X)
  efList = record { map = mapList }

  mapListX : ∀ {i S T} → (S → T) → ListX S i → ListX T i
  mapListX {i} f ss with ListX.read ss
  mapListX {ℕ.zero} _ record { read = _ } | just (_ , () , _ , _)
  mapListX {ℕ.suc .i} f ss | just (i , refl , s , ls) = record { read = just (i , (refl , ((f s) , (mapListX f ls)))) }
  mapListX f ss | nothing = record { read = nothing }

  efListX : ∀ {i} → EndoFunctor (λ X → ListX X i)
  efListX = record { map = mapListX }

  {-
  mapList' f ss with List'.read ss
  mapList' f ss | asdf = ?
  mapList' {ℕ.zero} _ record { read = _ } | just (_ , () , _ , _)
  mapList' {ℕ.suc .i} f ss | just (i , refl , s , ls) = record { read = just (i , (refl , ((f s) , (mapList f ls)))) }
  mapList' f ss | nothing = record { read = nothing }
  -}


{-

  data Cons (A : Set) : {i : Size} → Set where
    ∅ : {i : Size} → Cons A {↑ i}
    _∷_ : {i : Size} → A → Cons A {i} → Cons A {↑ i}

  data Snoc (A : Set) : Set where
    ∅ : Snoc A
    _∷_ : Snoc A → A → Snoc A

  open import Data.Nat.Base
  
  nList : List ℕ → List ℕ
  nList l = record { read = just (1 , l) }

  0List : List ℕ
  0List = nList (record { read = just (1 , (nList (record { read = nothing }))) })

  open import Data.Unit.Base

  prf : Is-just (List.read 0List)
  prf = just tt

  prf2 : proj₁ (to-witness prf) ≡ 1
  prf2 = refl

  efList : EndoFunctor (λ X → List X)
  efList = record { map = map' } where
    mutual
      map' : ∀ {i S T} → (S → T) → List S {i} → List T {i}
      map' {i} {S = S} {T} f = go where
        go : List S {i} → List T {i}
        go xs with List.read xs {!22!}
        go xs | asdf = {!!}
        
        --go {i} xs | just (y , ys) = record { read = just ((f y) , (go ys)) }
        --go xs | nothing = {!!}

{-
  empty : ∀ {A : Set} → List A
  empty = record { read = nothing }

  write : ∀ {A : Set} → (a : A) → (l : List A) → ∃ λ (l' : List A) → List.read l' ≡ just (a , l)
  write a l = (record { read = just (a , l) }) , refl

  record ListWriter (A : Set) : Set₁ where
    inductive
    field
      w : ∀ {A : Set} → (a : A) → (l : List A) → ∃ λ (l' : List A) → List.read l' ≡ just (a , l)

  consWriter : ∀ {A : Set} → ListWriter A
  consWriter = record { w = λ a l → (record { read = just (a , l) }) , refl }
        
  cons2List : ∀ {A : Set} → Cons A → List A
  cons2List ∅ = record { read = nothing }
  cons2List (x ∷ xs) = record { read = just (x , cons2List xs) }

  cons2List' : ∀ {A : Set} → Cons A → (List A × ListWriter A)
  cons2List' ∅ = record { read = nothing } , consWriter
  cons2List' (x ∷ xs) = record { read = just (x , cons2List xs) } , consWriter
-}

{-
  list2Cons : ∀ {A : Set} → List A → Cons A
  list2Cons record { read = (just (x , xs)) } = x ∷ list2Cons xs
  list2Cons record { read = nothing } = ∅


  infCons : Cons ℕ
  infCons = list2Cons 0List

  foo' : Cons ℕ → ℕ
  foo' = {!!}
-}

{-   
  record List (A : Set) : Set₁ where
    inductive
    field
      read : Maybe (A × List)
      append : (a : A) → List A
      listOK : ListOK A

  record ListOK {A : Set} (List A) : Set₁ where
    field
      listOK : 
   
    read' : ∀ {a} {A' : Set a} → (l : List') → {!!} ≡ A' → Maybe (A' × List' {a})
    read' l = {!!} where
      open List' l
   
  record ListOK' {a} (L : List' {a}) : Set (suc a) where
    field
      append : (aa : List'.A L) → ∃ λ (l : List') → l ≡ record {A = List'.A L ; read = just (aa , L)}
      
  record List'' {a} : Set (suc a) where
    open List' public
    open ListOK' public
-}
-}


record MR' {𝑘 𝑣} : Set (suc (𝑘 ⊔ 𝑣)) where
  private
    𝑘𝑣 : Level
    𝑘𝑣 = 𝑘 ⊔ 𝑣

    𝑘𝑣₁ : Level
    𝑘𝑣₁ = suc 𝑘𝑣
    
  field
    Key : Set 𝑘
    Value : Key → Set 𝑣

  KV : Set 𝑘𝑣
  KV = Σ Key Value

  field
    _∈⋆ : KV → Set 𝑘𝑣
    
  _∈ₖ⋆ : Key → Set 𝑘𝑣
  _∈ₖ⋆ k = ∃ λ v → (k , v) ∈⋆

  _∉⋆ : KV → Set 𝑘𝑣
  _∉⋆ kv = ¬ (kv ∈⋆)

  _∉ₖ⋆ : Key → Set 𝑘𝑣
  _∉ₖ⋆ k = ¬ (k ∈ₖ⋆)

  field
    _∈⋆? : (kv : KV) → Dec (kv ∈⋆)
    _∈ₖ?⋆ : (k : Key) → Dec (k ∈ₖ⋆)
    functional : ∀ {kv} (let (k , v) = kv) → kv ∈⋆ → ∀ {v'} → (k , v') ∈⋆ → v' ≡ v

record PartialFunction {α β} : Set (suc (α ⊔ β)) where
  field
    Domain : Set α
    ∈ : Domain → Set α
    ∈? : (d : Domain) → Dec (∈ d)
    Range : Set β
    f : Domain → Range

PartialFunction' : ∀ {α β} → Set α → Set β → Set (suc β ⊔ suc α)
PartialFunction' A B = ∃ λ (pf : PartialFunction) → PartialFunction.Domain pf ≡ A × PartialFunction.Range pf ≡ B
    
    
    
module _ {𝑘} {Key : Set 𝑘}
         {𝑣} (Value : Key → Set 𝑣)
         (let 𝑘𝑣 = 𝑘 ⊔ 𝑣)
         (let 𝑘𝑣₁ = suc 𝑘𝑣)
         (let KV = Σ Key Value)
       where

  mutual
    record MR : Set 𝑘𝑣₁ where
      field
        _∈⋆ : KV → Set 𝑘𝑣
   
      _∈ₖ⋆ : Key → Set 𝑘𝑣
      _∈ₖ⋆ k = ∃ λ v → (k , v) ∈⋆
   
      _∉⋆ : KV → Set 𝑘𝑣
      _∉⋆ kv = ¬ (kv ∈⋆)
   
      _∉ₖ⋆ : Key → Set 𝑘𝑣
      _∉ₖ⋆ k = ¬ (k ∈ₖ⋆)
   
      field
        _∈⋆? : (kv : KV) → Dec (kv ∈⋆)
   
      field
        _∈ₖ?⋆ : (k : Key) → Dec (k ∈ₖ⋆)
   
      field
        functional : ∀ {kv} (let (k , v) = kv) → kv ∈⋆ → ∀ {v'} → (k , v') ∈⋆ → v' ≡ v

    _∈_ : KV → MR → Set 𝑘𝑣
    kv ∈ m = let open MR m in kv ∈⋆
   
    _∉_ : KV → MR → Set 𝑘𝑣
    kv ∉ m = ¬ (kv ∈ m)
   
    _∈ₖ_ : Key → MR → Set 𝑘𝑣
    k ∈ₖ m = let open MR m in k ∈ₖ⋆
   
    _∉ₖ_ : Key → MR → Set 𝑘𝑣
    k ∉ₖ m = ¬ (k ∈ₖ m)
   
    _∈ₖ?_ : (k : Key) → (m : MR) → Dec (k ∈ₖ m)
    k ∈ₖ? m = let open MR m in k ∈ₖ?⋆
   
    _⊆_ : MR → MR → Set 𝑘𝑣
    m ⊆ M = ∀ {kv} → kv ∈ m → kv ∈ M
      
    _⊆_↰_ : MR → MR → KV → Set 𝑘𝑣
    _⊆_↰_ m M kv = ∀ {kv'} → kv' ∈ m → kv' ∈ M ⊎ kv' ≡ kv
        
    record MW : Set 𝑘𝑣₁ where
      field
        ∅ : ∃ λ r → ∀ {kv} (let open MR r) → kv ∉⋆
        ⋆↰ : (r : MR) (kv : KV) (let (k , v) = kv) {{_ : k ∉ₖ r}} → ∃ λ M → kv ∈ M × r ⊆ M × (M ⊆ r ↰ kv)
{-
mapEndoFunctor : ∀ {a x} {A : Set a} → EndoFunctor (λ (X : Set x) → MR (λ (a : A) → X))
mapEndoFunctor = record { map = map' } where
  map' : ∀ {S T} → (S → T) → MR (λ z → S) → MR (λ z → T)
  map' {S} {T} f m with {!!}
  ... | sdf = {!!}
-}  

module _ { α φ } ( f : Set α → Set φ ) ( a : Set α ) (let αφ = α ⊔ φ) (let αφ₁ = suc αφ) where
  record FR : Set αφ₁ where
    inductive
    field
      readtop : a ⊎ ∃ λ x → ∃ λ ( fr : x → FR ) → f x

  record FW : Set αφ₁ where
    field
      mkPure : (x : a) → ∃ λ (fr : FR) → FR.readtop fr ≡ inj₁ x
      mkFree : (x : Set α) → (fs : x → FR) → (fx : f x) → ∃ λ (fr : FR) → FR.readtop fr ≡ inj₂ (x , fs , fx)

open import Data.List

listMonoid : ∀ {a} → Monoid (List {a})
listMonoid = record { ∅ = [] ; _+_ = _++_ }

record SL {a} (F : Set a → Set a)
     {{M : Monoid F}}
     {{EF : EndoFunctor F}}
     {A : Set a} {B : Set a}
     (fa : F A) (fb : F B) : Set a where
  open Monoid M
  open EndoFunctor EF renaming (map to _<$>_)
  
  field
    s : F (A ⊎ B)
    s* : s ≡ (inj₁ <$> fa) + (inj₂ <$> fb)

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

module Match where

open import Level
open import Function

record EndoFunctor {α β} (F : Set α → Set β) : Set (suc (α ⊔ β)) where
  field
    map : ∀ {S T} → (S → T) → F S → F T

open EndoFunctor {{...}} public

record Applicative {α β} (F : Set α → Set β) : Set (suc (α ⊔ β)) where
  infixl 2 _<*>_
  field
    pure : ∀ {X} → X → F X
    _<*>_ : ∀ {S T} → F (S → T) → F S → F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record {map = _<*>_ ∘ pure}
open Applicative {{...}} public

instance
  applicativeFun : ∀ {α β} {S : Set β} → Applicative λ (X : Set α) → S → X
  applicativeFun = record
    { pure = λ x s → x
    ; _<*>_ = λ f a s → f s ( a s )
    }

  applicativeId : ∀ {a} → Applicative (id {suc a})
  applicativeId = record { pure = id ; _<*>_ = _$_ }

  applicativeComp : ∀ {α β χ F G} → Applicative {β} {χ} F → Applicative {α} G → Applicative (F ∘ G)
  applicativeComp aF aG = record { pure = pure {{aF}} ∘ pure {{aG}} ; _<*>_ = {!!} }

record Traversable {α} (F : Set α → Set α) : Set (suc α) where
  field
    traverse : ∀ {G S T} {{AG : Applicative G}} → (S → G T) → F S → G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse {{AG = applicativeId}} }
open Traversable {{...}} public


open import Data.Product 
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.Core
open import Relation.Binary.HeterogeneousEquality.Core
open import Level

infix 0 _⇔_
_⇔_ : ∀ {p q} → (P : Set p) (Q : Set q) → Set (p ⊔ q)
_⇔_ P Q = (P → Q) × (Q → P)

demorgan⊎ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → ¬ A → B
demorgan⊎ (inj₁ x) x₁ = contradiction x x₁
demorgan⊎ (inj₂ y) x₁ = y

module Map {𝑘 𝑣} {Key : Set 𝑘} (Value : Key → Set 𝑣) where
  𝑘𝑣 : Level
  𝑘𝑣 = 𝑘 ⊔ 𝑣

  𝑘𝑣₁ : Level
  𝑘𝑣₁ = suc 𝑘𝑣

  KV : Set 𝑘𝑣
  KV = Σ Key Value

  mutual
    record Map : Set 𝑘𝑣₁ where
      inductive
      field
        _∈⋆ : KV → Set 𝑘𝑣
        _∈⋆? : (kv : KV) → Dec (kv ∈⋆)

      _∈ₖ⋆ : Key → Set 𝑘𝑣
      _∈ₖ⋆ k = ∃ λ v → (k , v) ∈⋆

      field
        _∈ₖ?⋆ : (k : Key) → Dec (k ∈ₖ⋆)

      ⋆⊆_ : Map → Set 𝑘𝑣
      ⋆⊆_ M = ∀ {kv} → kv ∈⋆ → kv ∈ M

      _⊆⋆ : Map → Set 𝑘𝑣
      _⊆⋆ m = ∀ {kv} → kv ∈ m → kv ∈⋆

      ⋆⊆_↰_ : Map → KV → Set 𝑘𝑣
      ⋆⊆_↰_ M kv = ∀ {kv'} → kv' ∈⋆ → (kv' ∈ M) ⊎ kv' ≡ kv

      _⊆⋆↰_ : Map → KV → Set 𝑘𝑣
      _⊆⋆↰_ m kv = ∀ {kv'} → kv' ∈ m → kv' ∈⋆ ⊎ kv' ≡ kv
      
      _∉⋆ : KV → Set 𝑘𝑣
      _∉⋆ kv = ¬ (kv ∈⋆)

      _∉ₖ⋆ : Key → Set 𝑘𝑣
      _∉ₖ⋆ k = ¬ (k ∈ₖ⋆)

      field
        uniqueK : ∀ {kv} (let (k , v) = kv) → kv ∈⋆ → ∀ {v'} → (k , v') ∈⋆ → v' ≡ v
        ⋆↰ : (kv : KV) (let (k , v) = kv) → (k ∉ₖ⋆) → ∃ λ M → kv ∈ M × ⋆⊆ M × M ⊆⋆↰ kv
        ∅ : ∃ λ M → ∀ kv → kv ∉ M

    _∈_ : KV → Map → Set 𝑘𝑣
    kv ∈ m = let open Map m in kv ∈⋆
      
    _∉_ : KV → Map → Set 𝑘𝑣
    kv ∉ m = ¬ (kv ∈ m)

    _∈ₖ_ : Key → Map → Set 𝑘𝑣
    k ∈ₖ m = let open Map m in k ∈ₖ⋆

    _∉ₖ_ : Key → Map → Set 𝑘𝑣
    k ∉ₖ m = ¬ (k ∈ₖ m)

    _∈ₖ?_ : (k : Key) → (m : Map) → Dec (k ∈ₖ m)
    k ∈ₖ? m = let open Map m in k ∈ₖ?⋆

    _⊆_ : Map → Map → Set 𝑘𝑣
    m ⊆ M = let open Map m in ⋆⊆ M

    _⊆_↰_ : Map → Map → KV → Set 𝑘𝑣
    m ⊆ M ↰ kv = let open Map m in ⋆⊆ M ↰ kv

  open Map public

open import Data.Container
open import Data.Container.FreeMonad
open import Data.List

data Free { α φ } ( f : Set α → Set φ ) ( a : Set α ) : Set ( suc ( α ⊔ φ ) ) where
  Pure : a → Free f a
  free : ∀ { x : Set α } → ( x → Free f a ) → f x → Free f a

open import Data.Unit

module S1 where
  sumList : ∀ { a b } { A : Set a } {B : Set b} → List A → List B → List (A ⊎ B)
  sumList as bs = Data.List.map inj₁ as ++ Data.List.map inj₂ bs 

  module _ {α} {A : Set α} where
    uF : List (Free List A) → Free List A
    uF [] = free (λ x → Pure x) []
    uF (x ∷ xs) with uF xs
    uF (Pure x ∷ _) | Pure x' = free Pure (x ∷ x' ∷ [])
    uF (free x₁ x₂ ∷ _) | Pure x' = free ([_,_] x₁ Pure) (sumList x₂ [ x' ])
    uF (Pure x ∷ _) | free x₁ x₂ = free ([_,_] Pure x₁) (sumList [ x ] x₂)
    uF (free f x ∷ _) | free f' x' = free ([_,_] f f') (sumList x x')

    mutual
      sublis : (Map.Map λ (a : A) → Free List A) → Free List A → Free List A
      sublis m (Pure x₁) with Map._∈ₖ?_ (λ (a : A) → Free List A) x₁ m
      sublis m (Pure x₁) | yes x = proj₁ x -- x
      sublis m (Pure x₁) | no ¬x = Pure x₁
      sublis m (free x₂ []) = free x₂ []
      sublis m (free fx (x ∷ xs)) with sublis m (fx x) | sublis' m fx xs
      sublis m (free fx (x₁ ∷ xs)) | s | s' = uF (s ∷ s')
 
      sublis' : ∀ {x} → (Map.Map (λ (a : A) → ( Free List A ))) → (x → Free List A) → List x → List (Free List A)
      sublis' m fx [] = []
      sublis' m fx (x ∷ xs) with (fx x)
      sublis' m fx (x₁ ∷ xs) | Pure x₂ with Map._∈ₖ?_ (λ (a : A) → Free List A) x₂ m
      sublis' m fx (x₁ ∷ xs) | Pure x₂ | yes y = (proj₁ y) ∷ sublis' m fx xs
      sublis' m fx (x₁ ∷ xs) | Pure x₂ | nothing = Pure x₂ ∷ sublis' m fx xs
      sublis' m f (_ ∷ xs) | free f' [] = free Pure [] ∷ sublis' m f xs
      sublis' m f (x ∷ xs) | free f' xs' = uF (sublis m (f x) ∷ []) ∷ sublis' m f xs

    open import Relation.Binary.PropositionalEquality

    sublis1 : ∀ (f : Free List A) (mv : Map.Map (λ _ → Free List A)) → sublis (proj₁ (Map.Map.∅ mv)) f ≡ f
    sublis1 (Pure x) mv = {!!}
    sublis1 (free x₁ x₂) mv = {!!}

  match : ∀ {a'} {a : Set a'} → (pat : Free List a) → (exp : Free List a) → (var : List a) → Dec ( ∃ λ (ma : Map.Map (λ (x : a) → ( Free List a ))) → sublis ma pat ≡ exp )
  match = {!!}

-- pureMap : 

{-
match' : ∀ {a'} {a : Set a'} → (pat : Free List a) → (exp : Free List a) → (var : List a) → (binds : M a ( Free List a )) → Dec ( ∃! _≡_ λ (ma : M a ( Free List a )) → sublis ma pat ≡ exp )
match' = {!!}

match : ∀ {a'} {a : Set a'} → (pat : Free List a) →
        (exp : Free List a) →
        (var : List a) →
        Dec ( ∃! _≡_ λ (ma : M a ( Free List a )) → (sublis ma pat ≡ exp × {!!}) )
match m₁ m₂ vs = {!!} -- match' m₁ m₂ vs (proj₁ (M.empty {!!}))

-- proj₁ (insert k₁ v₁ (proj₁ empty) (λ kv x x₁ → contradiction x₁ (proj₁ (proj₂ empty)))) , (λ k' v' → (λ x → {!!}) , (λ x → {!!})) , (λ x → {!!}) -- (insert k₁ v₁ (proj₁ empty))

{-

    _<_ : Rel Key k<k
    IsStrictTotalOrder _≡_ _<_


{-
open import Level using ( _⊔_ ; Level )
open import Relation.Binary
open import List
open import Data.List.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Control.Monad.Free
open import Data.Unit.Base
open import Data.Bool.Base
open import Relation.Nullary
open import Data.Product

module Match
  { 𝑼⟨a⟩ 𝑼⟨<ᵃ⟩ 𝑼⟨≡ᶠ⟩ : Level }
  { a : Set 𝑼⟨a⟩ }
  { _<ᵃ_ : Rel a 𝑼⟨<ᵃ⟩ }
  { _≡ᶠ_ : Rel ( Free List a ) 𝑼⟨≡ᶠ⟩ }
  ( isDecEquivalenceᶠ : IsDecEquivalence _≡ᶠ_ )
  ( isStrictTotalOrderᵃ : IsStrictTotalOrder _≡_ _<ᵃ_ )
  where
{-
record ⌜_⌝ { α } ( P : Set α ) : Set α where
  constructor !
  field ⦃ prf ⦄ : P
-}
record ⌜_⌝ ( P : Set ) : Set where
  constructor !
  field ⦃ prf ⦄ : P
{-
_⇛_ : ∀ { α β } → Set α → Set β → Set ( α ⊔ β )
P ⇛ T = ⦃ p : P ⦄ → T
infixr 3 _⇛_
-}
_⇛_ : Set → Set → Set
P ⇛ T = ⦃ p : P ⦄ → T
infixr 3 _⇛_

--_∴_ : ∀ { P T } → ⌜ P ⌝ → ( { p : P } → T )  → T
--! ∴ t = t

open import Map

open import Function

reverseMap : Map a a → Map a a
reverseMap = fromList ∘ Data.List.Base.map swap ∘ toList

open IsStrictTotalOrder ⦃ ... ⦄ using ( _≟_ )
open IsDecEquivalence ⦃ ... ⦄ using () renaming ( _≟_ to _≟ᵈ_ )


_∈ᵃ_ : a → List a → Bool
x ∈ᵃ [] = false
x ∈ᵃ (x₁ ∷ xs) with x ≟ x₁
... | yes _ = true
... | no _ = x ∈ᵃ xs

data _∈ˡ_ {a } {A : Set a} (x : A) : List A → Set a where
  here : (ys : List A) → x ∈ˡ (x ∷ ys)
  tail : (y : A) → (ys : List A) → x ∈ˡ ys  → x ∈ˡ (y ∷ ys)

open import Relation.Nullary.Negation

_∉[] : (x : a) → ¬ (x ∈ˡ [])
_∉[] _ ()

x∉ys∧x≢y→x∉y∷ys : {x : a} {ys : List a} {y : a} → (x∉ys : ¬ (x ∈ˡ ys)) → (x≢y : ¬ (x ≡ y)) → ¬ (x ∈ˡ (y ∷ ys))
x∉ys∧x≢y→x∉y∷ys x∉ys x≢y (here ys) = contradiction refl x≢y
x∉ys∧x≢y→x∉y∷ys x∉ys x≢y (tail x ys x∈ys) = contradiction x∈ys x∉ys

findˡ : (x : a) → (ys : List a) → Dec (x ∈ˡ ys)
findˡ x [] = no λ ()
findˡ x (y ∷ _) with x ≟ y
findˡ x (y ∷ ys) | yes x≡y rewrite x≡y = yes (here ys)
findˡ x (_ ∷ ys) | no _ with findˡ x ys
findˡ x (y ∷ ys) | no _ | yes x∈ys = yes (tail y ys x∈ys)
findˡ x (y ∷ ys) | no x≢y | no x∉ys = no (x∉ys∧x≢y→x∉y∷ys x∉ys x≢y)
  
open import Data.Sum
open import Relation.Nullary
open import Data.Empty

match'expectation! : ( pat : Free List a ) → ( exp : Free List a ) → (∃ λ (mt : Maybe (Map a (Free List a))) → (pat ≡ᶠ exp) × (mt ≡ just empty) ⊎ (((pat ≡ᶠ exp) → ⊥) × mt ≡ nothing))
match'expectation! pat exp with pat ≟ᵈ exp -- IsDecEquivalence._≟_ isDecEquivalenceᶠ pat exp
match'expectation! pat exp | yes p = just empty , inj₁ ( p , refl )
match'expectation! pat exp | no ¬p = nothing , inj₂ (¬p , refl)

match'expectation : ( pat : Free List a ) → ( exp : Free List a ) → Maybe ( Map a ( Free List a ) )
match'expectation pat exp = proj₁ (match'expectation! pat exp)

toIndexed : Map a ( Free List a ) → ∃ λ h → Indexed.Tree Extended-key.⊥⁺ Extended-key.⊤⁺ h
toIndexed (tree t) = _ , t

open import Relation.Nullary.Negation

lookup! : (x : a) → (t : Map a ( Free List a )) → Dec (x Indexed.∈ (proj₂ (toIndexed t)))
lookup! x (tree t) with Indexed.lookup x t
lookup! x (tree t) | just v = {!!}
lookup! x (tree t) | nothing = no (contraposition (Indexed.𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup x t) (λ x₁ → {!_,_ !}))

match' : Free List a → Free List a → List a → Map a ( Free List a ) → Maybe ( Map a ( Free List a ) )
match' (pure x) m₂ vs bs with x ∈ᵃ vs
match' (pure x) m₂ vs bs | true with lookup x bs
match' (pure x₂) m₂ vs bs | true | just x₁ = match'expectation x₁ m₂
match' (pure x) m₂ vs bs | true | nothing = just ( singleton x m₂ )
match' (pure x) m₂ vs bs | false = match'expectation (pure x) m₂
match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs with match' (fpat pat) (fexp exp) vs bs
match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | just mbs with match' (free fpat pats) (free fexp exps) vs (union mbs bs)
match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | just mbs | just mbs' = just (union mbs mbs')
match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | just mbs | nothing = nothing
match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | nothing = nothing
match' (free x₁ []) (free x₅ []) vs bs = just empty
match' (free x₁ _) (free x₄ _) vs bs = nothing
match' (free x₁ _) (pure _) vs bs = nothing

match : Free List a →
        Free List a →
        List a →
        Maybe ( Map a ( Free List a ) )
match m₁ m₂ vs = match' m₁ m₂ vs empty


open import Function

open import Data.Sum

sumList : ∀ { a b } { A : Set a } {B : Set b} → List A → List B → List (A ⊎ B)
sumList as bs = Data.List.Base.map inj₁ as ++ Data.List.Base.map inj₂ bs 

uF : List (Free List a) → Free List a
uF [] = free (λ x → pure x) []
uF (x ∷ xs) with uF xs
uF (pure x ∷ _) | pure x' = free pure (x ∷ x' ∷ [])
uF (free x₁ x₂ ∷ _) | pure x' = free ([_,_] x₁ pure) (sumList x₂ [ x' ])
uF (pure x ∷ _) | free x₁ x₂ = free ([_,_] pure x₁) (sumList [ x ] x₂)
uF (free f x ∷ _) | free f' x' = free ([_,_] f f') (sumList x x')

mutual

  sublis : Map a ( Free List a ) → Free List a → Free List a
  sublis m (pure x₁) with lookup x₁ m
  sublis m (pure x₁) | just x = x
  sublis m (pure x₁) | nothing = pure x₁
  sublis m (free x₂ []) = free x₂ []
  sublis m (free fx (x ∷ xs)) with sublis m (fx x) | sublis' m fx xs
  sublis m (free fx (x₁ ∷ xs)) | s | s' = uF (s ∷ s')
 
  sublis' : ∀ { x } → Map a ( Free List a ) → (x → Free List a) → List x → List (Free List a)
  sublis' m fx [] = []
  sublis' m fx (x ∷ xs) with (fx x)
  sublis' m fx (x₁ ∷ xs) | pure x₂ with lookup x₂ m
  sublis' m fx (x₁ ∷ xs) | pure x₂ | just y = y ∷ sublis' m fx xs
  sublis' m fx (x₁ ∷ xs) | pure x₂ | nothing = pure x₂ ∷ sublis' m fx xs
  sublis' m f (_ ∷ xs) | free f' [] = free pure [] ∷ sublis' m f xs
  sublis' m f (x ∷ xs) | free f' xs' = uF (sublis m (f x) ∷ []) ∷ sublis' m f xs

open import Data.Maybe.Base

pureMap : Map a ( Free List a ) → Maybe ( Map a a )
pureMap m = (if null (toList f) then (just p) else nothing)
  where
    isPure : a × Free List a → Bool
    isPure (_ , pure _) = true
    isPure _ = false

    mapEither : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → Map a ( Free List a ) → Map a A × Map a B
    mapEither {A = A} {B = B} f t = mapEitherA f t , mapEitherB f t
      where
        mel : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → a × Free List a → a × (A ⊎ B)
        mel f (proj₁ , proj₂) = proj₁ , f proj₂
        
        mapEitherList : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → List (a × Free List a) → List (a × (A ⊎ B))
        mapEitherList f l = Data.List.Base.map (map2 f) l
          where
            map2 : ∀ {A'' B C} {a'' : Set A''} {b : Set B} {c : Set C} → (b → c) → a'' × b → a'' × c
            map2 f (proj₁ , proj₂) = proj₁ , (f proj₂)

        mapEitherA : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → Map a ( Free List a ) → Map a A
        mapEitherA {A = A} {B = B} f t = fromList (gfilter (λ { (x , y) → Data.Maybe.map (λ z → x , z) (isInj₁ y) })
                                                               (mapEitherList f (toList t)))

        mapEitherB : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → Map a ( Free List a ) → Map a B
        mapEitherB {A = A} {B = B} f t = fromList (gfilter (λ { (x , y) → Data.Maybe.map (λ z → x , z) (isInj₂ y) })
                                                               (mapEitherList f (toList t)))

    fp = mapEither cv m
      where
        cv : Free List a → ⊤ ⊎ a
        cv (pure x) = inj₂ x
        cv _ = inj₁ tt
    f = proj₁ fp
    p = proj₂ fp



one-one-match : Free List a → Free List a → List a → List a → Maybe (Map a a)
one-one-match pat exp patv expv with match pat exp patv
one-one-match pat exp patv expv | just (tree (Indexed.leaf l<u)) = just empty
one-one-match pat exp patv expv | just m with isSubsequenceOf {ide = isDecEquivalenceᶠ} (elems m) (Data.List.Base.map pure expv)
one-one-match pat exp patv expv | just m | true with pureMap m
one-one-match pat exp patv expv | just m | true | nothing = nothing
one-one-match pat exp patv expv | just _ | true | just m' with pat ≟ᵈ -- IsDecEquivalence._≟_ isDecEquivalenceᶠ pat
              (sublis ( ( fromList (Data.List.Base.map (λ { (a , a1) → a , pure a1 }) (toList (reverseMap m') ) ) ) ) exp )
one-one-match pat exp patv expv | just _ | true | just m' | yes _ = just m'
one-one-match pat exp patv expv | just _ | true | just m' | no _ = nothing
one-one-match pat exp patv expv | just m | false = nothing 
one-one-match pat exp patv expv | nothing = nothing

lemma1 : (pat : Free List a) (exp : Free List a) (patv : List a) (expv : List a) →
         -- ∃ λ m →
         ( m : Map a ( Free List a ) ) →
         match pat exp patv ≡ just m →
         isSubsequenceOf {ide = isDecEquivalenceᶠ} (elems m) (Data.List.Base.map pure expv) ≡ true →
         pureMap m ≡ nothing →
         -- ∃ λ h → ∃ λ m →
         -- one-one-match pat exp patv expv ≡ just ( tree { h = h } m )
         one-one-match pat exp patv expv ≡ nothing
         -- → ⊥
lemma1 (pure x) exp patv expv m x₁ x₂ x₃ = {!!}
lemma1 (free x₁ x₂) exp patv expv m x₃ x₄ x₅ = {!!}

lemma : (pat : Free List a) (exp : Free List a) (patv : List a) (expv : List a) →
        ∃ λ h → ∃ λ m → one-one-match pat exp patv expv ≡ just ( tree { h = h } m ) → Indexed.1-1.1-1 m
lemma pat exp patv expv with match pat exp patv
lemma pat exp patv expv | just (tree (Indexed.leaf l<u)) = 0 , Indexed.empty l<u , (λ x x₁ ())
lemma pat exp patv expv | just m with isSubsequenceOf {ide = isDecEquivalenceᶠ} (elems m) (Data.List.Base.map pure expv)
lemma pat exp patv expv | just m | true with pureMap m
lemma pat exp patv expv | just m | true | nothing = 0 , Indexed.empty _ , (λ x _ _ → {!!})
lemma pat exp patv expv | just m | true | just m' with pat ≟ᵈ -- IsDecEquivalence._≟_ isDecEquivalenceᶠ pat
              (sublis ( ( fromList (Data.List.Base.map (λ { (a , a1) → a , pure a1 }) (toList (reverseMap m') ) ) ) ) exp )
lemma pat exp patv expv | just m | true | just m' | yes _ = {!!}              
lemma pat exp patv expv | just m | true | just m' | no _ = {!!}              
lemma pat exp patv expv | just m | false = {!!}              
lemma pat exp patv expv | nothing = {!!}
-}
-}


-}

{-# OPTIONS --rewriting #-}
--{-# OPTIONS --exact-split #-}
--{-# OPTIONS --show-implicit #-}
module NaturalDeduction
 where

module CustomPrelude where

  open import Prelude public
    renaming (_==_ to _≟_) -- TODO ask Agda to rename Eq._==_ to Eq._≟_
    hiding (force) -- needed by ∞Delay

  {-# BUILTIN REWRITE _≡_ #-}

  {-# DISPLAY Eq._==_ _ = _≟_ #-}

  open import Container.List renaming (_∈_ to _∈C_; lookup∈ to lookup∈C) public

  _∈C?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ (a : A) → (xs : List A) → Dec (a ∈C xs)
  a ∈C? [] = no λ ()
  a ∈C? (x ∷ xs) with a ≟ x
  … | yes a≡x rewrite a≡x = yes (zero refl)
  … | no a≢x with a ∈C? xs
  … | yes a∈xs = yes (suc a∈xs)
  … | no a∉xs = no (λ {(zero a≡x) → a≢x a≡x ; (suc a∈xs) → a∉xs a∈xs})

  _≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  x ≢ y = ¬ (x ≡ y)

  infix 0 _↔_
  _↔_ : {ℓ¹ : Level} → Set ℓ¹ → {ℓ² : Level} → Set ℓ² → Set (ℓ¹ ⊔ ℓ²)
  P ↔ Q = (P → Q) × (Q → P)

  infix 0 _←⊗→_
  _←⊗→_ : {ℓ¹ : Level} → Set ℓ¹ → {ℓ² : Level} → Set ℓ² → Set (ℓ¹ ⊔ ℓ²)
  P ←⊗→ Q = (P → ¬ Q) × (Q → ¬ P)

  ∃ : ∀ {ℓᴬ ℓᴮ} {A : Set ℓᴬ} (B : A → Set ℓᴮ) → Set (ℓᴬ ⊔ ℓᴮ)
  ∃ = Σ _

  ∄ : ∀ {ℓᴬ ℓᴮ} {A : Set ℓᴬ} (B : A → Set ℓᴮ) → Set (ℓᴬ ⊔ ℓᴮ)
  ∄ = ¬_ ∘ ∃

  infixl 4 _⊎_
  _⊎_ = Either

  {-# DISPLAY Either = _⊎_ #-}

  --open import Agda.Builtin.Size public
  open import Size public

  open import Control.Monad.State public
  open import Control.Monad.Identity public
  open import Container.Traversable public

  sequence : ∀ {a b} {A : Set a} {F : Set a → Set b} ⦃ _ : Applicative F ⦄ → List (F A) → F ⊤′
  sequence [] = pure tt
  sequence (x ∷ xs) = x *> sequence xs

  open import Tactic.Nat public

  open import Tactic.Deriving.Eq public

  mutual

    data Delay (i : Size) (A : Set) : Set where
      now    :  A           → Delay i A
      later  :  ∞Delay i A  → Delay i A

    record ∞Delay (i : Size) (A : Set) : Set where
      coinductive
      field
        force : {j : Size< i} → Delay j A

  open ∞Delay public

  module BindDelay
   where

    mutual

      bindDelay          :  ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
      bindDelay (now    a) f   =  f a
      bindDelay (later ∞a) f   =  later (bind∞Delay ∞a f)

      bind∞Delay             :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
      force (bind∞Delay ∞a f)  =  bindDelay (force ∞a) f

  module _
   where

    open BindDelay

    open BindDelay public using () renaming (bind∞Delay to _∞>>=_)

    instance FunctorDelay : {i : Size} → Functor (Delay i)
    Functor.fmap FunctorDelay f x = bindDelay x $ now ∘ f

    instance ApplicativeDelay : {i : Size} → Applicative (Delay i)
    Applicative.pure ApplicativeDelay x = now x
    Applicative._<*>_ ApplicativeDelay (now f) x = f <$> x
    Applicative._<*>_ ApplicativeDelay (later ∞f) x = later ∘ bind∞Delay ∞f $ flip fmap x
    Applicative.super ApplicativeDelay = FunctorDelay

    instance MonadDelay : {i : Size} → Monad (Delay i)
    Monad._>>=_ MonadDelay = bindDelay
    Monad.super MonadDelay = ApplicativeDelay

    {-# DISPLAY BindDelay.bindDelay x f = x >>= f #-}
  mutual

    data _∼_ {i : Size} {A : Set} : (a? b? : Delay ∞ A) → Set where
      ∼now    :  ∀ a                              →  now a     ∼ now a
      ∼later  :  ∀ {a∞ b∞} (eq : a∞ ∞∼⟨ i ⟩∼ b∞)  →  later a∞  ∼ later b∞

    _∼⟨_⟩∼_ = λ {A} a? i b? → _∼_ {i}{A} a? b?

    record _∞∼⟨_⟩∼_ {A} (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
      coinductive
      field
        ∼force : {j : Size< i} → force a∞ ∼⟨ j ⟩∼ force b∞

  open _∞∼⟨_⟩∼_ public

  _∞∼_ = λ {i} {A} a∞ b∞ → _∞∼⟨_⟩∼_ {A} a∞ i b∞

  mutual

    ∼refl    :  ∀{i A} (a?  : Delay ∞ A)   →  a? ∼⟨ i ⟩∼ a?
    ∼refl (now a)    = ∼now a
    ∼refl (later a∞) = ∼later (∞∼refl a∞)

    ∞∼refl   :  ∀{i A} (a∞  : ∞Delay ∞ A)  →  a∞ ∞∼⟨ i ⟩∼ a∞
    ∼force (∞∼refl a∞) = ∼refl (force a∞)

  mutual

    ∼sym     :  ∀{i A}{a?  b?  : Delay ∞ A }  →  a? ∼⟨ i ⟩∼ b?   →  b? ∼⟨ i ⟩∼ a?
    ∼sym (∼now a)    = ∼now a
    ∼sym (∼later eq) = ∼later (∞∼sym eq)

    ∞∼sym    :  ∀{i A}{a∞  b∞  : ∞Delay ∞ A}  →  a∞ ∞∼⟨ i ⟩∼ b∞  →  b∞ ∞∼⟨ i ⟩∼ a∞
    ∼force (∞∼sym eq) = ∼sym (∼force eq)

  mutual

    ∼trans   :  ∀{i A}{a? b? c? : Delay ∞ A} →
                a? ∼⟨ i ⟩∼ b? →  b? ∼⟨ i ⟩∼ c? → a? ∼⟨ i ⟩∼ c?
    ∼trans (∼now a)    (∼now .a)    = ∼now a
    ∼trans (∼later eq) (∼later eq′) = ∼later (∞∼trans eq eq′)

    ∞∼trans  :  ∀{i A}{a∞ b∞ c∞ : ∞Delay ∞ A} →
                a∞ ∞∼⟨ i ⟩∼ b∞ →  b∞ ∞∼⟨ i ⟩∼ c∞ → a∞ ∞∼⟨ i ⟩∼ c∞
    ∼force (∞∼trans eq eq′) = ∼trans (∼force eq) (∼force eq′)

  --∼setoid : (i : Size) (A : Set) → Setoid lzero lzero
  --∞∼setoid : (i : Size) (A : Set) → Setoid lzero lzero

  mutual

    bind-assoc               :  ∀{i A B C} (m : Delay ∞ A)
                                {k : A → Delay ∞ B} {l : B → Delay ∞ C} →
                                ((m >>= k) >>= l) ∼⟨ i ⟩∼ (m >>= λ a → (k a >>= l))
    bind-assoc (now a)       =  ∼refl _
    bind-assoc (later a∞)    =  ∼later (∞bind-assoc a∞)

    ∞bind-assoc              :  ∀{i A B C} (a∞ : ∞Delay ∞ A)
                                {k : A → Delay ∞ B} {l : B → Delay ∞ C} →
                                ((a∞ ∞>>= k) ∞>>= l) ∞∼⟨ i ⟩∼ (a∞ ∞>>= λ a → (k a >>= l))
    ∼force (∞bind-assoc a∞)  =  bind-assoc (force a∞)

  mutual

    bind-cong-l   :  ∀{i A B}{a? b? : Delay ∞ A} →  a? ∼⟨ i ⟩∼ b? →
                     (k : A → Delay ∞ B) → (a? >>= k) ∼⟨ i ⟩∼ (b? >>= k)
    bind-cong-l (∼now a)    k = ∼refl _
    bind-cong-l (∼later eq) k = ∼later (∞bind-cong-l eq k)

    ∞bind-cong-l  :  ∀{i A B}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞∼⟨ i ⟩∼ b∞ →
                     (k : A → Delay ∞ B) → (a∞ ∞>>= k) ∞∼⟨ i ⟩∼ (b∞ ∞>>= k)
    ∼force (∞bind-cong-l eq k) = bind-cong-l (∼force eq) k

  mutual
    bind-cong-r   :  ∀{i A B}(a? : Delay ∞ A){k l : A → Delay ∞ B} →
                     (∀ a → (k a) ∼⟨ i ⟩∼ (l a)) → (a? >>= k) ∼⟨ i ⟩∼ (a? >>= l)
    bind-cong-r (now a)    h = h a
    bind-cong-r (later a∞) h = ∼later (∞bind-cong-r a∞ h)

    ∞bind-cong-r  :  ∀{i A B}(a∞ : ∞Delay ∞ A){k l : A → Delay ∞ B} →
                     (∀ a → (k a) ∼⟨ i ⟩∼ (l a)) → (a∞ ∞>>= k) ∞∼⟨ i ⟩∼ (a∞ ∞>>= l)
    ∼force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h

  map-compose     :  ∀{i A B C} (a? : Delay ∞ A) {f : A → B} {g : B → C} →
                     (g <$> (f <$> a?)) ∼⟨ i ⟩∼ ((g ∘ f) <$> a?)
  map-compose a?  =  bind-assoc a?

  map-cong        :  ∀{i A B}{a? b? : Delay ∞ A} (f : A → B) →
                     a? ∼⟨ i ⟩∼ b? → (f <$> a?) ∼⟨ i ⟩∼ (f <$> b?)
  map-cong f eq   =  bind-cong-l eq (now ∘ f)

  data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
    now⇓    :  ∀{a}                                   → now a ⇓ a
    later⇓  :  ∀{a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a  → later a∞ ⇓ a

  _⇓   :  {A : Set} (x : Delay ∞ A) → Set
  x ⇓  =  ∃ λ a → x ⇓ a

  map⇓     :  ∀{A B}{a : A}{a? : Delay ∞ A}(f : A → B) → a? ⇓ a → (f <$> a?) ⇓ f a
  map⇓ f now⇓        = now⇓
  map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

  bind⇓    :  ∀{A B}(f : A → Delay ∞ B){?a : Delay ∞ A}{a : A}{b : B} →
              ?a ⇓ a → f a ⇓ b → (?a >>= f) ⇓ b
  bind⇓ f now⇓ q = q
  bind⇓ f (later⇓ p) q = later⇓ (bind⇓ f p q)

  infixl 4 _>>=⇓_
  _>>=⇓_    :  ∀{A B}{f : A → Delay ∞ B}{?a : Delay ∞ A}{a : A}{b : B} →
               ?a ⇓ a → f a ⇓ b → (?a >>= f) ⇓ b
  _>>=⇓_ = bind⇓ _

  infixl 4 _⇓>>=⇓_
  _⇓>>=⇓_    :  ∀{A B}{f : A → Delay ∞ B}{?a : Delay ∞ A}{b : B} →
                (?a⇓ : ?a ⇓) → f (fst ?a⇓) ⇓ b → (?a >>= f) ⇓ b
  _⇓>>=⇓_ (_ , a⇓) = bind⇓ _ a⇓

  _⇓Dec>>=⇓_else⇓_ : ∀{A B}{f-yes : A → Delay ∞ B}{f-no : ¬ A → Delay ∞ B}{?a : Delay ∞ (Dec A)}{b : B} →
              (?a⇓ : ?a ⇓) →
              ((a : A) → f-yes a ⇓ b) →
              ((¬a : ¬ A) → f-no ¬a ⇓ b) →
              ((?a >>= (λ { (yes y) → f-yes y ; (no n) → f-no n }))) ⇓ b
  (yes y , y⇓) ⇓Dec>>=⇓ fy⇓ else⇓ fn⇓ = y⇓ >>=⇓ fy⇓ y
  (no n , n⇓) ⇓Dec>>=⇓ fy⇓ else⇓ fn⇓ = n⇓ >>=⇓ fn⇓ n


  _⇓DecEq>>=⇓_else⇓_ : ∀{A : Set} {A₁ A₂ : A} {B}{f-yes : A₁ ≡ A₂ → Delay ∞ B}{f-no : A₁ ≢ A₂ → Delay ∞ B}{?a : Delay ∞ (Dec (A₁ ≡ A₂))}{b : B} →
              (?a⇓ : ?a ⇓) →
              ((eq : A₁ ≡ A₂) → f-yes eq ⇓ b) →
              ((¬eq : A₁ ≢ A₂) → f-no ¬eq ⇓ b) →
              ((?a >>= (λ { (yes refl) → f-yes refl ; (no n) → f-no n }))) ⇓ b
  (yes refl , y⇓) ⇓DecEq>>=⇓ fy⇓ else⇓ fn⇓ = y⇓ >>=⇓ fy⇓ refl
  (no n , n⇓) ⇓DecEq>>=⇓ fy⇓ else⇓ fn⇓ = n⇓ >>=⇓ fn⇓ n

  app⇓ : ∀{A}{B}{f? : Delay ∞ (A → B)}{f : A → B}{x? : Delay ∞ A}{x : A} → f? ⇓ f → x? ⇓ x → (f? <*> x?) ⇓ f x
  app⇓ now⇓ now⇓ = now⇓
  app⇓ now⇓ (later⇓ x?) = later⇓ $ map⇓ _ x?
  app⇓ (later⇓ f?) now⇓ = later⇓ $ bind⇓ _ f? now⇓
  app⇓ (later⇓ ⇓f) (later⇓ ⇓x) = later⇓ $ bind⇓ _ ⇓f $ later⇓ $ bind⇓ _ ⇓x now⇓

  subst∼⇓  :  ∀{A}{a? a?′ : Delay ∞ A}{a : A} → a? ⇓ a → a? ∼ a?′ → a?′ ⇓ a
  subst∼⇓ now⇓ (∼now a) = now⇓
  subst∼⇓ (later⇓ p) (∼later eq) = later⇓ (subst∼⇓ p (∼force eq))
  {-
  traverse⇓' : ∀{A}{B}{f? : A → Delay ∞ B}{T : Set → Set}⦃ _ : Traversable T ⦄{X : T A} → (∀ x → f? x ⇓) → ∀ (x : T A) → traverse f? x ⇓
  traverse⇓' x₁ x₂ = {!!} , {!!}
  -}
  {-
  traverse⇓ : ∀{A}{B}{f : A → B}{T : Set → Set}⦃ _ : Traversable T ⦄{X : T A} → (∀ x → f? x ⇓) → ∀ (x : T A) → traverse f x ⇓
  traverse⇓ x₁ x₂ = {!!} , {!!}
  -}
  traverse-list⇓ : ∀{A}{B} (f? : A → Delay ∞ B) → (∀ x → f? x ⇓) → (xs : List A) → traverse f? xs ⇓
  traverse-list⇓ f? f?⇓ [] = [] , now⇓
  traverse-list⇓ f? f?⇓ (x ∷ xs)
   with f?⇓ x | traverse-list⇓ f? f?⇓ xs
  … | y , y⇓ | ys , ys⇓ = y ∷ ys , app⇓ (map⇓ _ y⇓) ys⇓
  {-
  traverse-vec⇓' : ∀{A}{B}{𝑎} (f? : A → Delay ∞ B) → (∀ x → f? x ⇓) → (xs : Vector A 𝑎) → traverse f? xs ⇓
  traverse-vec⇓' f? f?⇓ [] = [] , now⇓
  traverse-vec⇓' f? f?⇓ (x ∷ xs)
   with f?⇓ x | traverse-vec⇓' f? f?⇓ xs
  … | y , y⇓ | ys , ys⇓ = y ∷ ys , app⇓ (map⇓ _ y⇓) ys⇓

  traverse-vec⇓ : ∀{A}{B}{𝑎} (f : A → B) → (xs : Vector (Delay ∞ A) 𝑎) → traverse {!f!} xs ⇓
  traverse-vec⇓ = {!!}
  -}
{-
  traverse-vec⇓ : ∀{A}{B}{𝑎} (f? : A → Delay ∞ B) → (∀ x → f? x ⇓) → (xs : Vec A 𝑎) → traverse {!f!} xs ⇓
-}
open CustomPrelude

record Successor {ℓᴬ} (A : Set ℓᴬ) {ℓᴮ} (B : Set ℓᴮ) : Set (ℓᴬ ⊔ ℓᴮ)
 where
  field
    ⊹ : A → B

open Successor ⦃ … ⦄

instance SuccessorNat : Successor Nat Nat
Successor.⊹ SuccessorNat = suc

instance SuccessorLevel : Successor Level Level
Successor.⊹ SuccessorLevel = lsuc

record Membership {ℓ} (m : Set ℓ) (M : Set ℓ) : Set (⊹ ℓ)
 where
  field
    _∈_ : m → M → Set ℓ
    _∉_ : m → M → Set ℓ
    xor-membership : ∀ {x : m} {X : M} → x ∈ X ←⊗→ x ∉ X

open Membership ⦃ … ⦄

data _∈L_ {ℓ} {A : Set ℓ} (a : A) : List A → Set ℓ
 where
  zero : {as : List A} → a ∈L (a ∷ as)
  suc : {x : A} {as : List A} → a ∈L as → a ∈L (x ∷ as)

instance Successor∈L : ∀ {ℓ} {A : Set ℓ} {a : A} {x : A} {as : List A} → Successor (a ∈L as) $ a ∈L (x ∷ as)
Successor.⊹ Successor∈L = suc

instance MembershipList : ∀ {ℓ} {A : Set ℓ} → Membership A $ List A
Membership._∈_ MembershipList = _∈L_
Membership._∉_ MembershipList x X = ¬ x ∈ X
Membership.xor-membership MembershipList = (λ x x₁ → x₁ x) , (λ x x₁ → x x₁)

record DecidableMembership {ℓ} (m : Set ℓ) (M : Set ℓ) ⦃ _ : Membership m M ⦄ : Set (⊹ ℓ)
 where
  field _∈?_ : (x : m) → (X : M) → Dec $ x ∈ X
  field _∉?_ : (x : m) → (X : M) → Dec $ x ∉ X

open DecidableMembership ⦃ … ⦄

instance DecidableMembershipList : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → DecidableMembership A $ List A
DecidableMembership._∈?_ (DecidableMembershipList {ℓ} {A}) = _∈L?_
 where
  _∈L?_ : (a : A) → (xs : List A) → Dec (a ∈ xs)
  a ∈L? [] = no λ ()
  a ∈L? (x ∷ xs) with a ≟ x
  … | yes a≡x rewrite a≡x = yes zero
  … | no a≢x with a ∈L? xs
  … | yes a∈xs = yes (⊹ a∈xs)
  … | no a∉xs = no (λ {zero → a≢x refl ; (suc a∈xs) → a∉xs a∈xs})
DecidableMembership._∉?_ (DecidableMembershipList {ℓ} {A}) = {!!}

_⊆_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
_⊆_ {A = A} R S = ∀ {x : A} → x ∈ R → x ∈ S

record VariableName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

open VariableName

instance EqVariableName : Eq VariableName
Eq._==_ EqVariableName _ = decEq₁ (cong name) ∘ (_≟_ on name $ _)

record FunctionName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

open FunctionName

instance EqFunctionName : Eq FunctionName
Eq._==_ EqFunctionName _ = decEq₁ (cong name) ∘ (_≟_ on name $ _)

record PredicateName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

open PredicateName

instance EqPredicateName : Eq PredicateName
Eq._==_ EqPredicateName _ = decEq₁ (cong name) ∘ (_≟_ on name $ _)

record Arity : Set
 where
  constructor ⟨_⟩
  field
    arity : Nat

open Arity

instance EqArity : Eq Arity
Eq._==_ EqArity _ = decEq₁ (cong arity) ∘ (_≟_ on arity $ _)

record Vector (A : Set) (𝑎 : Arity) : Set
 where
  constructor ⟨_⟩
  field
    vector : Vec A (arity 𝑎)

open Vector

instance EqVector : {A : Set} ⦃ _ : Eq A ⦄ {𝑎 : Arity} → Eq (Vector A 𝑎)
Eq._==_ EqVector _ = decEq₁ (cong vector) ∘ (_≟_ on vector $ _)

data ITerm : Nat → Set
 where
  variable : VariableName → ITerm zero
  function : FunctionName → {arity : Nat} → (τs : Vec (Σ Nat ITerm) arity) → {n : Nat} → n ≡ sum (vecToList $ (fst <$> τs)) → ITerm (suc n)

mutual
  eqITerm : ∀ {n} → (x y : ITerm n) → Dec (x ≡ y)
  eqITerm = {!!}
{-
  eqITerm : ∀ {n} → (x y : ITerm n) → Dec (x ≡ y)
  eqITerm {.0} (variable x) (variable x₁) = {!!}
  eqITerm {.(suc n)} (function x {arity = arity₁} τs {n = n} x₁) (function x₂ {arity = arity₂} τs₁ {n = .n} x₃) with x ≟ x₂ | arity₁ ≟ arity₂
  eqITerm {.(suc n)} (function x {arity₁} τs {n} x₄) (function .x {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) with eqITerms τs τs₁
  eqITerm {.(suc n)} (function x₁ {arity₁} τs {n} x₄) (function .x₁ {.arity₁} .τs {.n} x₅) | yes refl | (yes refl) | (yes refl) rewrite x₄ | x₅ = yes refl
  eqITerm {.(suc n)} (function x₁ {arity₁} τs {n} x₄) (function .x₁ {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) | (no x) = {!!}
  eqITerm {.(suc n)} (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | yes x₁ | (no x₃) = {!!}
  eqITerm {.(suc n)} (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (yes x₃) = {!!}
  eqITerm {.(suc n)} (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (no x₃) = {!!}
-}
  eqITerms : ∀ {n} → (x y : Vec (Σ Nat ITerm) n) → Dec (x ≡ y)
  eqITerms {.0} [] [] = {!!}
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) with fst₁ ≟ fst₂
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl with eqITerm snd₁ snd₂
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | yes refl with eqITerms x₁ y
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | yes refl | yes refl = yes refl
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | yes refl | no ref = {!!}
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | no ref = {!!}
  eqITerms (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | no ref = {!!}

instance EqITerm : ∀ {n} → Eq (ITerm n)
Eq._==_ EqITerm = eqITerm

{-
instance EqITerm : ∀ {n} → Eq (ITerm n)
Eq._==_ EqITerm (variable x) (variable x₁) = {!!}
Eq._==_ EqITerm (function x {arity = arity₁} τs {n = n} x₁) (function x₂ {arity = arity₂} τs₁ {n = .n} x₃) with x ≟ x₂ | arity₁ ≟ arity₂
Eq._==_ EqITerm (function x {arity₁} τs {n} x₄) (function .x {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) with τs ≟ τs₁
Eq._==_ EqITerm (function x {arity₁} τs {n} x₄) (function .x {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) | τs≡τs₁ = {!!}
Eq._==_ EqITerm (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | yes x₁ | (no x₃) = {!!}
Eq._==_ EqITerm (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (yes x₃) = {!!}
Eq._==_ EqITerm (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (no x₃) = {!!}
-}



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

open Terms

termVariable-inj : ∀ {𝑥₁ 𝑥₂} → Term.variable 𝑥₁ ≡ variable 𝑥₂ → 𝑥₁ ≡ 𝑥₂
termVariable-inj refl = refl

termFunction-inj₁ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → 𝑓₁ ≡ 𝑓₂
termFunction-inj₁ refl = refl

termFunction-inj₂ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → τ₁s ≡ τ₂s
termFunction-inj₂ refl = refl

terms-inj : ∀ {𝑎} → {τs₁ τs₂ : Vector Term 𝑎} → (τs₁≡τs₂ : (Terms.⟨_⟩ {𝑎} τs₁) ≡ ⟨ τs₂ ⟩) → τs₁ ≡ τs₂
terms-inj refl = refl

mutual
  termToITerm : Term → Σ Nat ITerm
  termToITerm (variable x) = _ , (variable x)
  termToITerm (function x x₁) = {!!}

  termsToVec : Terms → Σ Nat (λ arity → Σ (Vec (Σ Nat ITerm) arity) λ τs → Σ Nat λ n → n ≡ sum (vecToList $ (fst <$> τs)))
  termsToVec (⟨_⟩ {arity = arity₁} ⟨ vector₁ ⟩) = {!!}

iTermToTerm : Σ Nat ITerm → Term
iTermToTerm = {!!}

eq-term-round : ∀ τ → iTermToTerm (termToITerm τ) ≡ τ
eq-term-round = {!!}

eq-iterm-round : ∀ τ → termToITerm (iTermToTerm τ) ≡ τ
eq-iterm-round = {!!}

instance EqTerm : Eq Term
Eq._==_ EqTerm x y with termToITerm x | graphAt termToITerm x | termToITerm y | graphAt termToITerm y
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

record Unifiable (F : Set) (T : Set) (U₁ U₂ : Set) (σ : (T → F) → F → F) : Set₁ where
  field
    _≈u≈_ : (φ₁ φ₂ : F) → Set
    unifier : (φ₁ φ₂ : F) → φ₁ ≈u≈ φ₂ → (F → F) × (F → F)
    unifier-law : (φ₁ φ₂ : F) → (=u= : φ₁ ≈u≈ φ₂) → (let u = unifier φ₁ φ₂ =u=) → (fst u) φ₁ ≡ (snd u) φ₂

{-
{-# TERMINATING #-}
-- substitute 𝑥ₛ τₛ τ = τ, where all occurrences of 𝑥ₛ are replaced by τₛ
substitute : VariableName → Term → Term → Term
substitute 𝑥ₛ τₛ τ@(variable 𝑥)  = ifYes 𝑥ₛ ≟ 𝑥 then τₛ else τ
substitute 𝑥ₛ τₛ (function 𝑓 ⟨ ⟨ τs ⟩ ⟩) = function 𝑓 ⟨ ⟨ substitute 𝑥ₛ τₛ <$> τs ⟩ ⟩
-}
mutual
  substituteTerm⇑ : VariableName → Term → ∀ {i} → Term → Delay i Term
  substituteTerm⇑ 𝑥ₛ τₛ τ@(variable 𝑥)  = now $ ifYes 𝑥ₛ ≟ 𝑥 then τₛ else τ
  substituteTerm⇑ 𝑥ₛ τₛ (function 𝑓 τs) =
    substituteTerms⇑ 𝑥ₛ τₛ τs >>= λ τsₛ →
    now $ function 𝑓 τsₛ

  substituteTerms⇑ : VariableName → Term → ∀ {i} → Terms → Delay i Terms
  substituteTerms⇑ 𝑥ₛ τₛ ⟨ ⟨ [] ⟩ ⟩ = now ⟨ ⟨ [] ⟩ ⟩
  substituteTerms⇑ 𝑥ₛ τₛ ⟨ ⟨ τ ∷ τs ⟩ ⟩ =
    let τs = substituteTerms⇑ 𝑥ₛ τₛ ⟨ ⟨ τs ⟩ ⟩
        τ = substituteTerm⇑ 𝑥ₛ τₛ τ in
    τs >>= λ { ⟨ ⟨ τs ⟩ ⟩ →
    τ >>= λ { τ →
    now $ ⟨ ⟨ τ ∷ τs ⟩ ⟩ } }

substituteTerms⇓ : (𝑥ₛ : VariableName) → (τₛ : Term) → (τs : Terms) → substituteTerms⇑ 𝑥ₛ τₛ τs ⇓
substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ [] ⟩ ⟩ = _ , now⇓
substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ (variable 𝑥) ∷ τs ⟩ ⟩ = _ , substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ τs ⟩ ⟩ ⇓>>=⇓ now⇓
substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ (function 𝑓 τs₁) ∷ τs ⟩ ⟩ = _ , substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ τs ⟩ ⟩ ⇓>>=⇓ ((substituteTerms⇓ 𝑥ₛ τₛ τs₁ ⇓>>=⇓ now⇓) >>=⇓ now⇓)

substituteTerm⇓ : (𝑥ₛ : VariableName) → (τₛ : Term) → (τ : Term) → substituteTerm⇑ 𝑥ₛ τₛ τ ⇓
substituteTerm⇓ 𝑥ₛ τₛ (variable 𝑥) = _ , now⇓
substituteTerm⇓ 𝑥ₛ τₛ (function 𝑓 τs) = _ , substituteTerms⇓ 𝑥ₛ τₛ τs ⇓>>=⇓ now⇓

substitute : VariableName → Term → Term → Term
substitute 𝑥ₛ τₛ τ = fst $ substituteTerm⇓ 𝑥ₛ τₛ τ

{-
record StructureSuitableForSubstitution : Set where
  field
    (∀ x xs → x ∈ xs → )

    VariableConstructor : VariableName → Term
    FunctionConstructor : FunctionName → (a : Nat) → (ts : Vec Term a) → Term

    ∀ v' → VariableConstructor v' ≡ τ → τₛ ≡ substitute 𝑥ₛ τₛ τ
    ∀ f' → FunctionConstructor f' ≡ τ → ∀ τ' → τ' ∈ τ → τₛ ≡ substitute 𝑥ₛ τₛ τ

    constructor-bases : Vec Set #constructors
    eq : ∀ x → x ∈ constructor-bases → Eq x
    substitute :  → constructor-base Structure → Structure
    datatype-constructor₁ : constructor-base₁ → datatype

    MEMBERSHIP : ELEMENT → STRUCTURE → Set
    ELEMENT → MEMBERSHIP e s → Σ STRUCTURE

    VariableConstructor → Term
    FunctionConstructor → Term
    substitute : VariableConstructor → Term → Term → Term

    substitute
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

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉𝕃_ {𝑨} {𝐴 : Set 𝑨} (x : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉𝕃 x₁s → 𝕃 𝐴

instance Successor𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} → {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → Successor (x₀ ∉𝕃 x₁s) (𝕃 𝐴)
Successor.⊹ Successor𝕃 = ✓

data _∉𝕃_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∅ : 𝔞 ∉𝕃 ∅
  ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉𝕃 x₁s → (x₀∉x₁s : x₀ ∉𝕃 x₁s) → 𝔞 ∉𝕃 ✓ x₀∉x₁s

data _∈𝕃_ {𝑨} {𝐴 : Set 𝑨} : (𝔞 : 𝐴) → 𝕃 𝐴 → Set {-𝑨-} where
  here : (𝔞 : 𝐴) {xs : 𝕃 𝐴} (𝔞∉xs : 𝔞 ∉𝕃 xs) → 𝔞 ∈𝕃 (✓ 𝔞∉xs)
  there : {x : 𝐴} {xs : 𝕃 𝐴} (x∉xs : x ∉𝕃 xs) {𝔞 : 𝐴} → 𝔞 ∈𝕃 xs → 𝔞 ∈𝕃 ✓ x∉xs

∈→¬∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → x ∈𝕃 xs → ¬ x ∉𝕃 xs
∈→¬∉ {𝑨} {𝐴} {.𝔞} {.(✓ {_} {_} {𝔞} {xs} 𝔞∉xs)} (here 𝔞 {xs = xs} 𝔞∉xs) (● {x₀ = .𝔞} x {x₁s = .xs} x₂ .𝔞∉xs) = x refl
∈→¬∉ {𝑨} {𝐴} {x₁} {.(✓ {_} {_} {x} {∅} ∅)} (there {x = x} {xs = .∅} ∅ {𝔞 = .x₁} ()) (● {x₀ = .x} x₃ {x₁s = .∅} ∅ .∅)
∈→¬∉ {𝑨} {𝐴} {.𝔞} {.(✓ {_} {_} {x} {✓ {_} {_} {𝔞} {x₁s} x∉xs} (● {_} {_} {_} {𝔞} x₁ {x₁s} x∉xs₁ x∉xs))} (there {x = x} {xs = .(✓ {_} {_} {𝔞} {x₁s} x∉xs)} (● {x₀ = .𝔞} x₁ {x₁s = x₁s} x∉xs₁ x∉xs) {𝔞 = .𝔞} (here 𝔞 {xs = .x₁s} .x∉xs)) (● {x₀ = .x} x₃ {x₁s = .(✓ {_} {_} {𝔞} {x₁s} x∉xs)} (● {x₀ = .𝔞} x₂ {x₁s = .x₁s} x₄ .x∉xs) .(● {_} {_} {_} {𝔞} x₁ {x₁s} x∉xs₁ x∉xs)) = x₂ refl
∈→¬∉ {𝑨} {𝐴} {x} {.(✓ {_} {_} {x₁} {✓ {_} {_} {x₀} {x₁s} x∉xs} (● {_} {_} {_} {x₀} x₂ {x₁s} x∉xs₁ x∉xs))} (there {x = x₁} {xs = .(✓ {_} {_} {x₀} {x₁s} x∉xs)} (● {x₀ = x₀} x₂ {x₁s = x₁s} x∉xs₁ x∉xs) {𝔞 = .x} (there {x = .x₀} {xs = .x₁s} .x∉xs {𝔞 = .x} x₃)) (● {x₀ = .x₁} x₄ {x₁s = .(✓ {_} {_} {x₀} {x₁s} x∉xs)} (● {x₀ = .x₀} x₅ {x₁s = .x₁s} x₆ .x∉xs) .(● {_} {_} {_} {x₀} x₂ {x₁s} x∉xs₁ x∉xs)) = ∈→¬∉ x₃ x₆

∉→¬∈ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → x ∉𝕃 xs → ¬ x ∈𝕃 xs
∉→¬∈ {𝑨} {𝐴} {x} {.∅} ∅ ()
∉→¬∈ {𝑨} {𝐴} {.𝔞} {.(✓ {_} {_} {𝔞} {x₁s} x₁)} (● {x₀ = .𝔞} x {x₁s = x₁s} x₂ x₁) (here 𝔞 {xs = .x₁s} .x₁) = x refl
∉→¬∈ {𝑨} {𝐴} {x} {.(✓ {_} {_} {x₀} {x₁s} x₁)} (● {x₀ = x₀} x₂ {x₁s = x₁s} x₃ x₁) (there {x = .x₀} {xs = .x₁s} .x₁ {𝔞 = .x} x₄) = ∉→¬∈ x₃ x₄

foo : ∀ {𝑨} {𝐴 : Set 𝑨} {x x₀ : 𝐴} (x₁ : _≡_ {𝑨} {𝐴} x x₀) (x₂ : _∈𝕃_ {𝑨} {𝐴} x (✓ {_} {_} {x₀} {∅} ∅) → ⊥) → ⊥
foo {𝑨} {𝐴} {x} {.x} refl x₂ = x₂ (here x ∅)

foo₂ : (𝑨 : Level)
  (𝐴   : Set 𝑨                   )
  (x₀  : 𝐴                       )
  (x₁s : 𝕃 𝐴                     )
  (x₁  : x₀ ∉𝕃 x₁s                )
  (x   : 𝐴                       )
  (x₂  : 𝐴                       )
  (x₃  : x₂ ≡ x₀ → ⊥             )
  (x₄  : x₂ ∉𝕃 x₁s                )
  (x₅  : ¬ (x ∈𝕃 ✓ (● x₃ x₄ x₁)) )
  (x₆  : x ≡ x₂) → ⊥
foo₂ 𝑨 𝐴 x₀ x₁s x₁ x .x x₃ x₄ x₅ refl = x₅ (here x (● x₃ x₄ x₁)) -- x₅ (here x (● x₃ x₄ x₁))

foo₃ : (𝑨   : Level)
     (𝐴   : Set 𝑨                   )
     (x₀  : 𝐴                       )
     (x₁s : 𝕃 𝐴                     )
     (x₁  : x₀ ∉𝕃 x₁s                )
     (x   : 𝐴                       )
     (x₂  : 𝐴                       )
     (x₃  : x₂ ≡ x₀ → ⊥             )
     (x₄  : x₂ ∉𝕃 x₁s                )
     (x₅  : ¬ (x ∈𝕃 ✓ (● x₃ x₄ x₁)) )
     (x₆  : x ≡ x₀)
     → ⊥
foo₃ 𝑨 𝐴 x₀ x₁s x₁ .x₀ x₂ x₃ x₄ x₅ refl = x₅ (there (● x₃ x₄ x₁) (here x₀ x₁))

¬∈→∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → ¬ x ∈𝕃 xs → x ∉𝕃 xs
¬∈→∉ {𝑨} {𝐴} {x} {∅} x₁ = ∅
¬∈→∉ {𝑨} {𝐴} {x} {✓ {x₀ = x₀} {x₁s = .∅} ∅} x₂ = ● (λ {x₁ → foo x₁ x₂}) ∅ ∅
¬∈→∉ {𝑨} {𝐴} {x} {✓ {x₀ = x₂} {x₁s = .(✓ {_} {_} {x₀} {x₁s} x₁)} (● {x₀ = x₀} x₃ {x₁s = x₁s} x₄ x₁)} x₅ = ● (λ {x₆ → foo₂ 𝑨 𝐴 x₀ x₁s x₁ x x₂ x₃ x₄ x₅ x₆}) (● (λ {x₆ → foo₃ 𝑨 𝐴 x₀ x₁s x₁ _ x₂ x₃ x₄ x₅ x₆}) (¬∈→∉ (λ z → x₅ (there (● x₃ x₄ x₁) (there x₁ z)))) x₁) (● x₃ x₄ x₁)

¬∉→∈ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → ¬ x ∉𝕃 xs → x ∈𝕃 xs
¬∉→∈ {𝑨} {𝐴} {x} {∅} x₁ = ⊥-elim (x₁ ∅)
¬∉→∈ {𝑨} {𝐴} {x} {✓ {x₀ = x₀} {x₁s = ∅} ∅} x₂ = {!⊥-elim!}
¬∉→∈ {𝑨} {𝐴} {x₁} {✓ {x₀ = x₂} {x₁s = ✓ {x₀ = x₀} {x₁s = x₁s} x} (● {x₀ = .x₀} x₃ {x₁s = .x₁s} x₄ .x)} x₅ = {!!}

pattern tail= x₁s = ✓ {x₁s = x₁s} _
pattern 𝕃⟦_⟧ x₀ = ✓ {x₀ = x₀} ∅
pattern _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s = ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _)

--{-# DISPLAY ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _) = _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s #-}

pattern _↶_↷_ x₀∉x₂s x₀≢x₁ x₁∉x₂s = ● x₀≢x₁ x₀∉x₂s x₁∉x₂s
pattern _₀∷₁⟦_⟧ x₀ x₁s = ● {x₀} _ {x₁s} _ _

instance Membership𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} → Membership 𝐴 (𝕃 𝐴)
Membership._∉_ Membership𝕃 x xs = x ∉𝕃 xs
Membership._∈_ Membership𝕃 x xs = ¬ x ∉𝕃 xs
fst (Membership.xor-membership Membership𝕃) x₁ x₂ = x₁ x₂
snd (Membership.xor-membership Membership𝕃) x₁ x₂ = x₂ x₁

{-# DISPLAY _∉𝕃_ = _∉_ #-}

add-1-preserves-∈𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (x₀∉x₁s : x₀ ∉ x₁s) {x : 𝐴} → x ∈ x₁s → x ∈ ✓ x₀∉x₁s
add-1-preserves-∈𝕃 x₀∉x₁s x₁ (● x₃ x₄ x₂) = x₁ x₄

--{-# DISPLAY #-}
_∉𝕃?_ : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ → (x : 𝐴) (xs : 𝕃 𝐴) → Dec (x ∉𝕃 xs)
_∉𝕃?_ x ∅ = yes ∅
_∉𝕃?_ x 𝕃⟦ x₀ ⟧ with x ≟ x₀
… | yes refl = no λ {(● x₂ _ .∅) → x₂ refl}
… | no x≢x₀ = yes (● x≢x₀ ∅ ∅)
_∉𝕃?_ x (✓ {x₀ = x₀} (● {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s)) with x ≟ x₀
… | yes refl = no λ { (● x₃ _ _) → x₃ refl}
… | no x≢x₀ with x ≟ x₁
… | yes refl = no λ { ((_ ↶ x≢x ↷ _) ↶ _ ↷ _) → x≢x refl }
… | no x≢x₁ with x ∉𝕃? x₂s
_∉𝕃?_ x₁ (✓ {x₂} (● {x₀} x₃ {.∅} x₄ x₀∉x₁s)) | no x≢x₀ | (no x≢x₁) | (yes ∅) = yes (● x≢x₀ (● x≢x₁ ∅ x₀∉x₁s) (● _ _ x₀∉x₁s))
_∉𝕃?_ x₁ (✓ {x₄} (● {x₃} x₅ {.(✓ asdf)} x₆ x₀∉x₁s)) | no x≢x₀ | (no x≢x₁) | (yes (● x₂ asdf₁ asdf)) = yes (● x≢x₀ (● x≢x₁ (● x₂ asdf₁ asdf) x₀∉x₁s) (● x₅ x₆ x₀∉x₁s))
… | no x∈x₂s = no λ { (● {_} x₃ {.(✓ x₁∉x₂s)} (● x₄ x∉x₀s .x₁∉x₂s) .(● x₀≢x₁ x₀∉x₂s x₁∉x₂s)) → x∈x₂s x∉x₀s}

instance DecidableMembership𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ → DecidableMembership 𝐴 (𝕃 𝐴)
DecidableMembership._∉?_ DecidableMembership𝕃 = _∉𝕃?_
DecidableMembership._∈?_ DecidableMembership𝕃 x X with _∉𝕃?_ x X
… | yes x∉X = no (λ x₁ → x₁ x∉X)
… | no x∈X = yes x∈X

x∈singleton→x=singleton : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} ⦃ _ : Eq 𝐴 ⦄ {x₀∉∅ : _∉_ ⦃ Membership𝕃 ⦄ x₀ 𝕃.∅} {x : 𝐴} → x ∈ ✓ x₀∉∅ → x ≡ x₀
x∈singleton→x=singleton {𝑨} {𝐴} {x₀} {∅} {x} x₁ with x ≟ x₀
x∈singleton→x=singleton {𝑨} {𝐴} {x₀} {∅} {x} x₁ | yes refl = refl
x∈singleton→x=singleton {𝑨} {𝐴} {x₀} {∅} {x} x∈x₀ | no x≢x₀ = ⊥-elim (x∈x₀ (● x≢x₀ ∅ ∅))

foo₄ : (𝑨        : Level                                  )
        (𝐴        : Set 𝑨                                 )
        (x₁       : 𝐴                                     )
        (x₂s      : 𝕃 𝐴                                   )
        (x₁∉x₂s   : x₁ ∉ x₂s                              )
        (x₀       : 𝐴                                     )
        (x₀≢x₁    : x₀ ≡ x₁ → ⊥                           )
        (x₀∉x₂s   : x₀ ∉ x₂s                              )
        (x        : 𝐴                                     )
        (x∈x₀∉x₁s : x ∉ ✓ (● x₀≢x₁ x₀∉x₂s x₁∉x₂s) → ⊥     )
        (x≢x₀     : x ≡ x₀ → ⊥                            )
        (x≢x₁     : x ≡ x₁ → ⊥                            )
        (x∉x₂s    : x ∉ x₂s                               )
        (x₂       : x ≡ x₀                                ) → ⊥
foo₄ 𝑨 𝐴 x₁ x₂s x₁∉x₂s x₀ x₀≢x₁ x₀∉x₂s .x₀ x∈x₀∉x₁s x≢x₀ x≢x₁ x∉x₂s refl = x≢x₀ refl

if-diff-then-somewhere-else-∈𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ {x₀ : 𝐴} (x₁s : 𝕃 𝐴) {x₀∉x₁s : x₀ ∉ x₁s} {x : 𝐴} → x ∈ ✓ x₀∉x₁s → x ≢ x₀ → x ∈ x₁s
if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} ∅ {∅} {x} x∈x₀∉∅ x≢x₀ ∅ = x≢x₀ (x∈singleton→x=singleton x∈x₀∉∅)
if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} (✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s) {● x₀≢x₁ x₀∉x₂s ._} {x} x∈x₀∉x₁s x≢x₀ (● x≢x₁ x∉x₂s _) = x∈x₀∉x₁s (● (λ {x₂ → foo₄ 𝑨 𝐴 x₁ x₂s x₁∉x₂s x₀ x₀≢x₁ x₀∉x₂s _ x∈x₀∉x₁s x≢x₀ x≢x₁ x∉x₂s x₂}) (● x≢x₁ x∉x₂s x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s))

--if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} .∅  {x₀∉x₁s} {x} x∈x₀s x≢x₀ ∅ = {!!}
--if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} ._  {x₀∉x₁s} {x} x∈x₀s x≢x₀ (● {x₀ = x₁} x≢x₁ {x₁s = x₂s} x∉x₂s x₁∉x₂s) = {!!}

record TotalUnion {ℓ} (m : Set ℓ) (M : Set ℓ) ⦃ _ : Membership m M ⦄ : Set ℓ
 where
  field
    union : M → M → M
    unionLaw1 : ∀ {x : m} {X₁ X₂ : M} → x ∈ X₁ → x ∈ union X₁ X₂
    unionLaw2 : ∀ {x : m} {X₁ X₂ : M} → x ∈ X₂ → x ∈ union X₁ X₂
    unionLaw3 : ∀ {x : m} {X₁ X₂ : M} → x ∈ union X₁ X₂ → x ∈ X₁ ⊎ x ∈ X₂

open TotalUnion ⦃ … ⦄

{-# DISPLAY TotalUnion.union _ = union #-}

add1-then-∈𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ {x₀ : 𝐴} (x₁s : 𝕃 𝐴) {x₀∉x₁s : x₀ ∉ x₁s} → x₀ ∈ ✓ {x₀ = x₀} x₀∉x₁s
add1-then-∈𝕃 {𝑨} {𝐴} {{x}} {x₀} x₁s {.x₁} (● {x₀ = .x₀} x₂ {x₁s = .x₁s} x₃ x₁) = x₂ refl

module ModuleTotalUnion𝕃 {ℓ} (A : Set ℓ) ⦃ _ : Eq A ⦄ where
  -- TODO aribtrarily moves from l₀s to r₀s, so a union of 10 and 2 elements takes longer than a union of 2 and 10 elements
  totalUnion : 𝕃 A → 𝕃 A → 𝕃 A
  totalUnion ∅ ∅ = ∅
  totalUnion ∅ r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) = r₀s
  totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) ∅ = l₀s
  totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) with l₀ ∉? r₀s
  totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) | no l₀∈r₀s = totalUnion l₁s r₀s
  totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) | yes l₀∉r₀s = totalUnion l₁s (✓ l₀∉r₀s)

  totalUnionLaw2 : ∀ {x : A} {X₁ X₂ : 𝕃 A} → x ∈ X₂ → x ∈ totalUnion X₁ X₂
  totalUnionLaw2 {x₁} {∅} {∅} x₂ x₃ = x₂ x₃
  totalUnionLaw2 {x₁} {∅} {✓ x₂} x₃ x₄ = x₃ x₄
  totalUnionLaw2 {x₁} {✓ x₂} {∅} x₃ x₄ = x₃ ∅
  totalUnionLaw2 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈r₀s x∉l₀s∪r₀s with l₀ ∉? r₀s
  totalUnionLaw2 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈r₀s x∉l₀s∪r₀s | no l₀∈r₀s = totalUnionLaw2 {X₁ = l₁s} x∈r₀s $ x∉l₀s∪r₀s
  totalUnionLaw2 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈r₀s x∉l₀s∪r₀s | yes l₀∉r₀s = (totalUnionLaw2 {X₁ = l₁s} $ add-1-preserves-∈𝕃 l₀∉r₀s x∈r₀s) $ x∉l₀s∪r₀s

  totalUnionLaw1 : ∀ {x : A} {X₁ X₂ : 𝕃 A} → x ∈ X₁ → x ∈ totalUnion X₁ X₂
  totalUnionLaw1 {x₁} {∅} {∅} x₂ x₃ = x₂ x₃
  totalUnionLaw1 {x₁} {∅} {✓ {x₀ = x₀} {x₁s = X₂} x₂} x₃ x₄ = x₃ ∅
  totalUnionLaw1 {x₁} {✓ {x₀ = x₀} {x₁s = X₁} x₂} {∅} x₃ x₄ = x₃ x₄
  totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s with l₀ ∉? r₀s
  totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | no l₀∈r₀s with x ≟ l₀
  totalUnionLaw1 {.l₀} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | no l₀∈r₀s | yes refl = totalUnionLaw2 {X₁ = l₁s} l₀∈r₀s $ x∉l₀s∪r₀s
  totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | no l₀∈r₀s | no x≢l₀ = let x∈l₁s = if-diff-then-somewhere-else-∈𝕃 l₁s x∈l₀s x≢l₀ in totalUnionLaw1 x∈l₁s $ x∉l₀s∪r₀s
  -- with x ≟ l₀
  -- = {!!}
  totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | yes l₀∉r₀s with x ≟ l₀
--totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} l₀∈l₀s l₀∉l₀s∪r₀s | yes l₀∉r₀s | yes refl = {!l₀∉r₀s!}
  totalUnionLaw1 {.l₀}    {✓ {l₀}       {l₁s}       l₀∉l₁s}        {✓ {r₀}           {r₁s} r₀∉r₁s} l₀∈l₀s l₀∉l₁s∪l₀r₀s | yes (● l₀≢r₀ l₀∉r₁s .r₀∉r₁s) | (yes refl) =
    let l₀∈l₀r₀s : l₀ ∈ (✓ (● l₀≢r₀ l₀∉r₁s r₀∉r₁s))
        l₀∈l₀r₀s = add1-then-∈𝕃 (✓ r₀∉r₁s)
         in totalUnionLaw2 {X₁ = l₁s} l₀∈l₀r₀s $ l₀∉l₁s∪l₀r₀s
  totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | yes l₀∉r₀s | no x≢l₀ = let x∈l₁s = if-diff-then-somewhere-else-∈𝕃 l₁s x∈l₀s x≢l₀ in totalUnionLaw1 x∈l₁s $ x∉l₀s∪r₀s

  totalUnionLaw3 : ∀ {x : A} {X₁ X₂ : 𝕃 A} → x ∈ totalUnion X₁ X₂ → x ∈ X₁ ⊎ x ∈ X₂
  totalUnionLaw3 = {!!}

instance TotalUnion𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ → TotalUnion 𝐴 (𝕃 𝐴)
TotalUnion.union TotalUnion𝕃 = ModuleTotalUnion𝕃.totalUnion _
TotalUnion.unionLaw1 TotalUnion𝕃 = ModuleTotalUnion𝕃.totalUnionLaw1 _
TotalUnion.unionLaw2 (TotalUnion𝕃 {𝑨} {𝐴} {{x}}) {x₁} {X₁} {X₂} x₂ x₃ = ModuleTotalUnion𝕃.totalUnionLaw2 𝐴 {X₁ = X₁} {X₂ = X₂} x₂ x₃
TotalUnion.unionLaw3 TotalUnion𝕃 = ModuleTotalUnion𝕃.totalUnionLaw3 _

mutual
  data FTerm : 𝕃 VariableName → Set
   where
    variable : (𝑥 : VariableName) → FTerm (𝕃⟦ 𝑥 ⟧)
    function : (𝑓 : FunctionName) → ..{𝑥s : 𝕃 VariableName} {arity : Nat} → (τs : FTerms 𝑥s arity) → FTerm 𝑥s

  data FTerms : 𝕃 VariableName → Nat → Set
   where
    [] : FTerms ∅ zero
    _∷_ : ∀ ..{𝑥s' 𝑥s : 𝕃 VariableName} → FTerm 𝑥s' → {n : Nat} → FTerms 𝑥s n → FTerms (union {m = VariableName} 𝑥s' 𝑥s) (⊹ n)

instance MembershipVariableNameFTerm : ∀ {𝑥s} → Membership VariableName (FTerm 𝑥s)
MembershipVariableNameFTerm = {!!}

record TotalIntersection {ℓ} (m : Set ℓ) (M : Set ℓ) ⦃ _ : Membership m M ⦄ : Set ℓ
 where
  field
    intersection : M → M → M
    intersectionLaw1 : ∀ {x : m} {X₁ X₂ : M} → x ∈ intersection X₁ X₂ → x ∈ X₁
    intersectionLaw2 : ∀ {x : m} {X₁ X₂ : M} → x ∈ intersection X₁ X₂ → x ∈ X₂
    intersectionLaw3 : ∀ {x : m} {X₁ X₂ : M} → x ∈ X₁ × x ∈ X₂ → x ∈ intersection X₁ X₂

open TotalIntersection ⦃ … ⦄

{-# DISPLAY TotalIntersection.intersection _ = intersection #-}

instance Intersection𝕃 : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → TotalIntersection A (𝕃 A)
Intersection𝕃 = {!!}

data HasUniqueValues (A : Set) : List A → Set
 where
  [] : HasUniqueValues A []
  _∷_ : {x : A} → {xs : List A} → x ∉ xs → (uxs : HasUniqueValues A xs) → HasUniqueValues A (x ∷ xs)

record AList (A : Set) (B : Set) : Set
 where
  field
    domain : List A
    uniquedomain : HasUniqueValues A domain
    range : ∀ {x : A} → x ∈ domain → B

open AList

mutual
  subst : AList VariableName (∃ FTerm) → ∃ FTerm → ∃ FTerm
  subst x t@(.(✓ ∅) , variable 𝑥) with 𝑥 ∈? domain x
  … | yes x∈D = range x x∈D
  … | no x∉D = t
  subst x (fst₁ , function 𝑓 {𝑥s = 𝑥s} {arity = a} τs) with substs x a (𝑥s , τs)
  subst x (fst₁ , function 𝑓 {.fst₁} {arity₁} τs) | fst₂ , snd₁ = fst₂ , (function 𝑓 snd₁)

  substs : AList VariableName (∃ FTerm) → (a : Nat) → ∃ (flip FTerms a) → ∃ (flip FTerms a)
  substs x .0 (.∅ , []) = ∅ , []
  substs x .(suc _) (._ , (x₁ ∷ snd₁)) with {!subst x (_ , x₁)!}
  substs x .(suc _) (._ , (x₁ ∷ snd₁)) | sb = {!!}

-- indexed by the number of function symbols contained
data DTerm : Nat → Set
 where
  variable : (𝑥 : VariableName) → DTerm zero
  function : (𝑓 : FunctionName) → {arity : Nat} → (τs : Vec (∃ DTerm) arity) → DTerm (suc (sum (fst <$> vecToList τs)))

mutual
  substD : VariableName → ∃ DTerm → {n : Nat} → DTerm n → ∃ DTerm
  substD x x₁ (variable 𝑥) = ifYes 𝑥 ≟ x then x₁ else _ , variable 𝑥
  substD x x₁ (function 𝑓 τs) with substsD x x₁ τs
  substD x x₁ (function 𝑓 τs) | ss = suc (sum (fst <$> vecToList ss)) , function 𝑓 {_} ss

  substsD : VariableName → ∃ DTerm → {n : Nat} → Vec (Σ Nat DTerm) n → Vec (Σ Nat DTerm) n
  substsD x x₁ [] = []
  substsD x x₁ (x₂ ∷ x₃) with substD x x₁ (snd x₂) | substsD x x₁ x₃
  substsD x x₁ (x₂ ∷ x₃) | fst₁ , snd₁ | sss = (fst₁ , snd₁) ∷ sss

data HDTerm : Set where
  ⟨_⟩ : {n : Nat} → DTerm n → HDTerm

substituteD : (AList VariableName HDTerm) → HDTerm → HDTerm
substituteD = {!!}

amgu : HDTerm → HDTerm → (AList VariableName HDTerm) → Maybe (AList VariableName HDTerm)
amgu ⟨ variable 𝑥 ⟩ ⟨ variable 𝑥₁ ⟩ f = {!!}
amgu ⟨ variable 𝑥 ⟩ ⟨ function 𝑓 τs ⟩ f = {!!}
amgu ⟨ function 𝑓 τs ⟩ ⟨ variable 𝑥 ⟩ f = {!!}
amgu ⟨ function 𝑓 τs₁ ⟩ ⟨ function 𝑓₁ τs ⟩ f = {!!}

-- {-
-- data AList : 𝕃 VariableName → Set
--  where
--   [] : AList ∅
--   _∷_ :
-- -}
-- record JohnUnification {𝑥s₁} (τ₁ : FTerm 𝑥s₁) {𝑥s₂} (τ₂ : FTerm 𝑥s₂) (_ : intersection {m = VariableName} 𝑥s₁ 𝑥s₂ ≡ ∅) : Set where
--   field
--     u₁ u₂ : AList VariableName (∃ FTerm)
--     unification-law₁ : fst (subst u₁ (𝑥s₁ , τ₁)) ≡ fst (subst u₂ (𝑥s₂ , τ₂))
--     unification-law₂ : snd (subst u₁ (𝑥s₁ , τ₁)) ≡ transport FTerm (sym unification-law₁) (snd (subst u₂ (𝑥s₂ , τ₂)))

-- record UnificationEquation (𝑥s : 𝕃 VariableName) : Set
--  where
--   field
--     {lhs-terms} : 𝕃 VariableName
--     lhs : FTerm lhs-terms
--     {rhs-terms} : 𝕃 VariableName
--     rhs : FTerm rhs-terms
--     lhs∪rhs-terms : 𝑥s ≡ union {m = VariableName} lhs-terms rhs-terms

-- open UnificationEquation

-- number-of-variables-that-occur-more-than-once : ∀ {n-eqn} → Vec (∃ λ 𝑥s → UnificationEquation 𝑥s) n-eqn → Nat
-- number-of-variables-that-occur-more-than-once {zero} [] = 0
-- number-of-variables-that-occur-more-than-once {suc n-eqn} x = {!!}

-- number-of-function-symbols : ∀ {𝑥s} → FTerm 𝑥s → Nat
-- number-of-function-symbols = {!!}

-- record UnificationProblem (n-var n-lhs n-eqn : Nat) : Set
--  where
--   field
--     equations : Vec (∃ λ 𝑥s → UnificationEquation 𝑥s) n-eqn
--     n-var-law : number-of-variables-that-occur-more-than-once equations ≤ n-var
--     n-lhs-law : (sum ∘ vecToList $ number-of-function-symbols ∘ lhs ∘ snd <$> equations) ≤ n-lhs

-- instance MembershipUnificationEquationUnificationProblem : ∀ {n-var n-lhs n-eqn 𝑥s} → Membership (UnificationEquation 𝑥s) (UnificationProblem n-var n-lhs n-eqn)
-- MembershipUnificationEquationUnificationProblem = {!!}

-- instance MembershipVariableNameUnificationProblem : ∀ {n-var n-lhs n-eqn} → Membership VariableName (UnificationProblem n-var n-lhs n-eqn)
-- MembershipVariableNameUnificationProblem = {!!}

-- deletable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
-- deletable = {!!}

-- deletable? : ∀ {𝑥s} → (eq : UnificationEquation 𝑥s) → Dec (deletable eq)
-- deletable? = {!!}

-- u-deletable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → deletable εq × εq ∈ up)
-- u-deletable? {n-var} {n-lhs} {zero} up = no {!!}
-- u-deletable? {n-var} {n-lhs} {suc n-eqn} up = {!!}

-- deleteRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var n-lhs (suc n-eqn)} {𝑥s} {εq : UnificationEquation 𝑥s} → deletable εq → εq ∈ up → UnificationProblem n-var n-lhs n-eqn
-- deleteRule = {!!}

-- decomposable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
-- decomposable = {!!}

-- decomposable? : ∀ {𝑥s} → (eq : UnificationEquation 𝑥s) → Dec (decomposable eq)
-- decomposable? = {!!}

-- u-decomposable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var (suc n-lhs) n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → decomposable εq × εq ∈ up)
-- u-decomposable? = {!!}

-- decomposeRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var (suc n-lhs) n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → decomposable εq → εq ∈ up → UnificationProblem n-var n-lhs n-eqn
-- decomposeRule = {!!}

-- swapable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
-- swapable = {!!}

-- swapable? : ∀ {𝑥s} → (eq : UnificationEquation 𝑥s) → Dec (swapable eq)
-- swapable? = {!!}

-- u-swapable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var (suc n-lhs) n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → swapable εq × εq ∈ up)
-- u-swapable? = {!!}

-- swapRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var (suc n-lhs) n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → swapable εq → εq ∈ up → UnificationProblem n-var n-lhs n-eqn
-- swapRule = {!!}

-- eliminatable : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem n-var n-lhs n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → (εq∈up : εq ∈ up) → Set
-- eliminatable = {!!}

-- u-eliminatable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem (suc n-var) n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → ∃ λ (εq∈up : εq ∈ up) → eliminatable {up = up} {εq = εq} εq∈up)
-- u-eliminatable? = {!!}

-- eliminateRule : ∀ {n-var n-lhs n-eqn} {up : UnificationProblem (suc n-var) n-lhs n-eqn} {𝑥s} {εq : UnificationEquation 𝑥s} → {εq∈up : εq ∈ up} → eliminatable {up = up} {εq = εq} εq∈up → UnificationProblem n-var n-lhs n-eqn
-- eliminateRule = {!!}

-- conflictable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
-- conflictable = {!!}

-- conflictable? : ∀ {𝑥s} → (εq : UnificationEquation 𝑥s) → Dec (conflictable εq)
-- conflictable? = {!!}

-- u-conflictable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → conflictable εq × εq ∈ up)
-- u-conflictable? = {!!}

-- checkable : ∀ {𝑥s} → UnificationEquation 𝑥s → Set
-- checkable = {!!}

-- checkable? : ∀ {𝑥s} → (εq : UnificationEquation 𝑥s) → Dec (checkable εq)
-- checkable? = {!!}

-- u-checkable? : ∀ {n-var n-lhs n-eqn} (up : UnificationProblem n-var n-lhs n-eqn) → Dec (∃ λ 𝑥s → ∃ λ (εq : UnificationEquation 𝑥s) → checkable εq × εq ∈ up)
-- u-checkable? = {!!}

-- record HasNegation (A : Set) : Set
--  where
--   field
--     ~ : A → A

-- open HasNegation ⦃ … ⦄

-- {-# DISPLAY HasNegation.~ _ = ~ #-}

-- data Formula : Set
--  where
--   atomic : PredicateName → Terms → Formula
--   logical : Formula →
--             Formula →
--             Formula
--   quantified : VariableName → Formula → Formula

-- formulaAtomic-inj₁ : ∀ {𝑃₁ τs₁ 𝑃₂ τs₂} → Formula.atomic 𝑃₁ τs₁ ≡ atomic 𝑃₂ τs₂ → 𝑃₁ ≡ 𝑃₂
-- formulaAtomic-inj₁ refl = refl

-- formulaAtomic-inj₂ : ∀ {𝑃₁ τs₁ 𝑃₂ τs₂} → Formula.atomic 𝑃₁ τs₁ ≡ atomic 𝑃₂ τs₂ → τs₁ ≡ τs₂
-- formulaAtomic-inj₂ refl = refl

-- formulaLogical-inj₁ : ∀ {φ₁₁ φ₁₂ φ₂₁ φ₂₂} → Formula.logical φ₁₁ φ₁₂ ≡ logical φ₂₁ φ₂₂ → φ₁₁ ≡ φ₂₁
-- formulaLogical-inj₁ refl = refl

-- formulaLogical-inj₂ : ∀ {φ₁₁ φ₁₂ φ₂₁ φ₂₂} → Formula.logical φ₁₁ φ₁₂ ≡ logical φ₂₁ φ₂₂ → φ₁₂ ≡ φ₂₂
-- formulaLogical-inj₂ refl = refl

-- formulaQuantified-inj₁ : ∀ {𝑥₁ φ₁ 𝑥₂ φ₂} → Formula.quantified 𝑥₁ φ₁ ≡ quantified 𝑥₂ φ₂ → 𝑥₁ ≡ 𝑥₂
-- formulaQuantified-inj₁ refl = refl

-- formulaQuantified-inj₂ : ∀ {𝑥₁ φ₁ 𝑥₂ φ₂} → Formula.quantified 𝑥₁ φ₁ ≡ quantified 𝑥₂ φ₂ → φ₁ ≡ φ₂
-- formulaQuantified-inj₂ refl = refl

-- instance EqFormula : Eq Formula
-- Eq._==_ EqFormula (atomic 𝑃₁ τs₁)
--                   (atomic 𝑃₂ τs₂)
--                   = decEq₂ formulaAtomic-inj₁
--                            formulaAtomic-inj₂
--                            (𝑃₁ ≟ 𝑃₂)
--                            (τs₁ ≟ τs₂)
-- Eq._==_ EqFormula (logical φ₁₁ φ₁₂)
--                   (logical φ₂₁ φ₂₂)
--                   = decEq₂ formulaLogical-inj₁ formulaLogical-inj₂ (φ₁₁ ≟ φ₂₁) (φ₁₂ ≟ φ₂₂)
-- Eq._==_ EqFormula (quantified 𝑥₁ φ₁) (quantified 𝑥₂ φ₂) = decEq₂ formulaQuantified-inj₁ formulaQuantified-inj₂ (𝑥₁ ≟ 𝑥₂) (φ₁ ≟ φ₂)
-- Eq._==_ EqFormula (atomic _ _) (logical _ _) = no λ ()
-- Eq._==_ EqFormula (atomic _ _) (quantified _ _) = no λ ()
-- Eq._==_ EqFormula (logical _ _) (atomic _ _) = no λ ()
-- Eq._==_ EqFormula (logical _ _) (quantified _ _) = no λ ()
-- Eq._==_ EqFormula (quantified _ _) (atomic _ _) = no λ ()
-- Eq._==_ EqFormula (quantified _ _) (logical _ _) = no λ ()

-- data IsFormula : Formula → Set
--  where
--   ⟨_⟩ : (φ : Formula) → IsFormula φ

-- record 𝓕ormula (Is𝓕ormula : Formula → Set) : Set
--  where
--   constructor ⟨_⟩
--   field
--     {formula} : Formula
--     is𝓕ormula : Is𝓕ormula formula

-- open 𝓕ormula

-- 𝑃[_♭_] : PredicateName → Terms → Formula
-- 𝑃[_♭_] = atomic

-- {-# DISPLAY atomic = 𝑃[_♭_] #-}

-- record HasNeitherNor (A : Set) : Set
--  where
--   field
--     _⊗_ : A → A → A

-- open HasNeitherNor ⦃ … ⦄

-- instance HasNeitherNorFormula : HasNeitherNor Formula
-- HasNeitherNor._⊗_ HasNeitherNorFormula = logical

-- {-# DISPLAY logical = _⊗_ #-}

-- instance HasNegationFormula : HasNegation Formula
-- HasNegation.~ HasNegationFormula φ = φ ⊗ φ

-- data IsLiteralFormula : Formula → Set
--  where
--   atomic : (𝑃 : PredicateName) → (τs : Terms) → IsLiteralFormula $ 𝑃[ 𝑃 ♭ τs ]
--   logical : (𝑃 : PredicateName) → (τs : Terms) → IsLiteralFormula ∘ ~ $ 𝑃[ 𝑃 ♭ τs ]

-- eqIsLiteralFormula : ∀ {φ} → (lf₁ lf₂ : IsLiteralFormula φ) → lf₁ ≡ lf₂
-- eqIsLiteralFormula (atomic _ _) (atomic _ _) = refl
-- eqIsLiteralFormula (logical _ _) (logical _ _) = refl

-- instance EqIsLiteralFormula : ∀ {φ} → Eq (IsLiteralFormula φ)
-- Eq._==_ EqIsLiteralFormula lf₁ lf₂ = yes $ eqIsLiteralFormula lf₁ lf₂

-- record LiteralFormula : Set
--  where
--   constructor ⟨_⟩
--   field
--     {formula} : Formula
--     isLiteralFormula : IsLiteralFormula formula

-- open LiteralFormula

-- instance EqLiteralFormula : Eq LiteralFormula
-- Eq._==_ EqLiteralFormula (⟨_⟩ {φ₁} lf₁) (⟨_⟩ {φ₂} lf₂)
--  with φ₁ ≟ φ₂
-- … | no φ₁≢φ₂ = no (λ {refl → φ₁≢φ₂ refl})
-- Eq._==_ EqLiteralFormula (⟨_⟩ {φ₁} lf₁) (⟨_⟩ {φ₂} lf₂) | yes refl = case (eqIsLiteralFormula lf₁ lf₂) of λ {refl → yes refl}

-- instance HasNegationLiteralFormula : HasNegation LiteralFormula
-- HasNegation.~ HasNegationLiteralFormula ⟨ atomic 𝑃 τs ⟩ = ⟨ logical 𝑃 τs ⟩
-- HasNegation.~ HasNegationLiteralFormula ⟨ logical 𝑃 τs ⟩ = ⟨ atomic 𝑃 τs ⟩

-- data IsPropositionalFormula : Formula → Set
--  where
--   atomic : (𝑃 : PredicateName) → (τs : Terms) → IsPropositionalFormula $ 𝑃[ 𝑃 ♭ τs ]
--   logical : {φ₁ : Formula} → IsPropositionalFormula φ₁ → {φ₂ : Formula} → IsPropositionalFormula φ₂ → IsPropositionalFormula (φ₁ ⊗ φ₂)

-- instance EqIsPropositionalFormula : ∀ {φ} → Eq (IsPropositionalFormula φ)
-- Eq._==_ EqIsPropositionalFormula (atomic _ _) (atomic _ _ ) = yes refl
-- Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) with φ₁₁ ≟ φ₂₁ | φ₁₂ ≟ φ₂₂
-- Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) | yes refl | yes refl = yes refl
-- Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) | yes refl | no φ₁₂≢φ₂₂ = no λ {refl → φ₁₂≢φ₂₂ refl}
-- Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) | no φ₁₁≢φ₂₁ | _ = no λ {refl → φ₁₁≢φ₂₁ refl}

-- {-
-- -- need to use coinduction to prove this
-- foo : ¬ ∃ λ φ → ∃ λ (p₁ : IsPropositionalFormula φ) → ∃ λ (p₂ : IsPropositionalFormula φ) → p₁ ≢ p₂
-- foo (atomic x x₁ , atomic .x .x₁ , atomic .x .x₁ , snd₁) = snd₁ refl
-- foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical fst₅ fst₆ , snd₁) with fst₃ ≟ fst₅ | fst₄ ≟ fst₆
-- foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical .fst₃ .fst₄ , snd₁) | yes refl | (yes refl) = snd₁ refl
-- foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical .fst₃ fst₆ , snd₁) | yes refl | (no x₁) = foo (fst₂ , fst₄ , fst₆ , λ xs → x₁ xs)
-- foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical fst₅ fst₆ , snd₁) | no x | (yes x₁) = {!!}
-- foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical fst₅ fst₆ , snd₁) | no x | (no x₁) = {!!}
-- foo (quantified x fst₁ , () , fst₃ , snd₁)
-- -}

-- record PropositionalFormula : Set
--  where
--   constructor ⟨_⟩
--   field
--     {formula} : Formula
--     isPropositionalFormula : IsPropositionalFormula formula

-- open PropositionalFormula

-- instance HasNegationPropositionalFormula : HasNegation PropositionalFormula
-- HasNegation.~ HasNegationPropositionalFormula ⟨ φ ⟩ = ⟨ logical φ φ ⟩

-- instance HasNeitherNorPropositionalFormula : HasNeitherNor PropositionalFormula
-- HasNeitherNor._⊗_ HasNeitherNorPropositionalFormula ⟨ φ₁ ⟩ ⟨ φ₂ ⟩ = ⟨ logical φ₁ φ₂ ⟩

-- {-# DISPLAY IsPropositionalFormula.logical = _⊗_ #-}

-- record 𝓐ssertion (A : Set) : Set
--  where
--   no-eta-equality

-- instance 𝓐ssertionList : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (List A)
-- 𝓐ssertionList = record {}

-- instance 𝓐ssertionFormula : 𝓐ssertion Formula
-- 𝓐ssertionFormula = record {}

-- instance 𝓐ssertionLiteralFormula : 𝓐ssertion LiteralFormula
-- 𝓐ssertionLiteralFormula = record {}

-- infix 15 _⊢_

-- record 𝓢equent (A : Set) ⦃ _ : 𝓐ssertion A ⦄ : Set
--  where
--   constructor _⊢_
--   field
--     antecedents : List A
--     consequents : List A

-- open 𝓢equent ⦃ … ⦄

-- instance Eq𝓢equent : {A : Set} ⦃ _ : Eq A ⦄ ⦃ _ : 𝓐ssertion A ⦄ → Eq (𝓢equent A)
-- Eq._==_ Eq𝓢equent (antecedents₁ ⊢ consequents₁) (antecedents₂ ⊢ consequents₂) = {!antecedents₁ ≟ antecedents₂!}

-- instance 𝓐ssertion𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (𝓢equent A)
-- 𝓐ssertion𝓢equent = record {}

-- instance 𝓐ssertion𝓕ormula : {Is𝓕ormula : Formula → Set} → 𝓐ssertion (𝓕ormula Is𝓕ormula)
-- 𝓐ssertion𝓕ormula = record {}

-- infix 15 _╱_

-- record Sequent : Set
--  where
--   constructor _╱_
--   field
--     statement : Formula
--     suppositions : List Formula

-- open Sequent

-- instance EqSequent : Eq Sequent
-- Eq._==_ EqSequent ( φᵗ₁ ╱ φˢs₁ ) ( φᵗ₂ ╱ φˢs₂ ) = decEq₂ (cong statement) (cong suppositions) (φᵗ₁ ≟ φᵗ₂) (φˢs₁ ≟ φˢs₂)

-- instance HasNegationSequent : HasNegation Sequent
-- HasNegation.~ HasNegationSequent ( φᵗ ╱ φˢs ) = ~ φᵗ ╱ φˢs

-- record IsLiteralSequent (Φ : Sequent) : Set
--  where
--   constructor _╱_
--   field
--     isLiteralStatement : IsLiteralFormula (statement Φ)
--     isLiteralSuppositions : All IsLiteralFormula (suppositions Φ)

-- open IsLiteralSequent

-- instance EqIsLiteralSequent : ∀ {Φ} → Eq (IsLiteralSequent Φ)
-- Eq._==_ EqIsLiteralSequent ( φᵗ₁ ╱ φˢs₁ ) ( φᵗ₂ ╱ φˢs₂ ) = decEq₂ (cong isLiteralStatement) (cong isLiteralSuppositions) (φᵗ₁ ≟ φᵗ₂) (φˢs₁ ≟ φˢs₂)

-- record LiteralSequent : Set
--  where
--   constructor ⟨_⟩
--   field
--     {sequent} : Sequent
--     isLiteralSequent : IsLiteralSequent sequent

-- open LiteralSequent

-- pattern ⟪_,_⟫ h s = ⟨_⟩ {h} s
-- pattern ⟪_⟫ h = (⟨_⟩ {h} _)

-- instance EqLiteralSequent : Eq LiteralSequent
-- Eq._==_ EqLiteralSequent ⟪ Φ₁ ⟫ ⟪ Φ₂ ⟫   with Φ₁ ≟ Φ₂
-- Eq._==_ EqLiteralSequent ⟨ !Φ₁ ⟩ ⟨ !Φ₂ ⟩ | yes refl with !Φ₁ ≟ !Φ₂
-- Eq._==_ EqLiteralSequent _ _             | yes refl | yes refl = yes refl
-- Eq._==_ EqLiteralSequent ⟨ Φ₁ ⟩ ⟨ Φ₂ ⟩   | yes refl | no !Φ₁≢!Φ₂ = no λ {refl → !Φ₁≢!Φ₂ refl}
-- Eq._==_ EqLiteralSequent ⟨ Φ₁ ⟩ ⟨ Φ₂ ⟩   | no Φ₁≢Φ₂ = no λ {refl → Φ₁≢Φ₂ refl}

-- instance HasNegationLiteralSequent : HasNegation LiteralSequent
-- HasNegation.~ HasNegationLiteralSequent ⟨ atomic 𝑃 τs ╱ φˢs ⟩ = ⟨ logical 𝑃 τs ╱ φˢs ⟩
-- HasNegation.~ HasNegationLiteralSequent ⟨ logical 𝑃 τs ╱ φˢs ⟩ = ⟨ atomic 𝑃 τs ╱ φˢs ⟩

-- infix 13 _¶_

-- record Problem : Set
--  where
--   constructor _¶_
--   field
--     inferences : List Sequent
--     interest : Sequent

-- open Problem

-- instance EqProblem : Eq Problem
-- EqProblem = {!!}

-- record IsLiteralProblem (𝔓 : Problem) : Set
--  where
--   constructor _¶_
--   field
--     {problem} : Problem
--     isLiteralInferences : All IsLiteralSequent (inferences 𝔓)
--     isLiteralInterest : IsLiteralSequent (interest 𝔓)

-- open IsLiteralProblem

-- instance EqIsLiteralProblem : ∀ {𝔓} → Eq (IsLiteralProblem 𝔓)
-- EqIsLiteralProblem = {!!}

-- record LiteralProblem : Set
--  where
--   constructor ⟨_⟩
--   field
--     {problem} : Problem
--     isLiteralProblem : IsLiteralProblem problem

-- open LiteralProblem

-- instance EqLiteralProblem : Eq LiteralProblem
-- EqLiteralProblem = {!!}

-- record Element : Set
--  where
--   constructor ⟨_⟩
--   field
--     element : Nat

-- instance EqElement : Eq Element
-- Eq._==_ EqElement ⟨ ε₁ ⟩ ⟨ ε₂ ⟩ with ε₁ ≟ ε₂
-- Eq._==_ EqElement ⟨ _ ⟩  ⟨ _ ⟩ | yes refl = yes refl
-- Eq._==_ EqElement ⟨ _ ⟩  ⟨ _ ⟩ | no ε₁≢ε₂ = no λ {refl → ε₁≢ε₂ refl}

-- record Elements : Set
--  where
--   constructor ⟨_⟩
--   field
--     {arity} : Arity
--     elements : Vector Element arity

-- open Elements

-- instance EqElements : Eq Elements
-- Eq._==_ EqElements (⟨_⟩ {𝑎₁} εs₁) (⟨_⟩ {𝑎₂} εs₂)
--  with 𝑎₁ ≟ 𝑎₂
-- … | no 𝑎₁≢𝑎₂ = no λ {refl → 𝑎₁≢𝑎₂ refl}
-- … | yes refl
--  with εs₁ ≟ εs₂
-- … | yes refl = yes refl
-- … | no εs₁≢εs₂ = no λ {refl → εs₁≢εs₂ refl}

-- record TruthValue : Set
--  where
--   constructor ⟨_⟩
--   field
--     truthValue : Bool

-- record Interpretation : Set
--  where
--   field
--     μ⟦_⟧ : VariableName → Element
--     𝑓⟦_⟧ : FunctionName → Elements → Element
--     𝑃⟦_⟧ : PredicateName → Elements → TruthValue

-- open Interpretation

-- mutual

--   τ⇑⟦_⟧ : Interpretation → {i : Size} → Term → Delay i Element
--   τ⇑⟦ I ⟧ (variable 𝑥) = now $ μ⟦ I ⟧ 𝑥
--   τ⇑⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ∘ ⟨_⟩ <$> τs⇑⟦ I ⟧ τs

--   τs⇑⟦_⟧ : Interpretation → {i : Size} → (τs : Terms) → Delay i (Vector Element (arity τs))
--   τs⇑⟦ I ⟧ ⟨ ⟨ [] ⟩ ⟩ = now ⟨ [] ⟩
--   τs⇑⟦ I ⟧ ⟨ ⟨ τ ∷ τs ⟩ ⟩ = τ⇑⟦ I ⟧ τ >>= (λ t → τs⇑⟦ I ⟧ ⟨ ⟨ τs ⟩ ⟩ >>= λ ts → now ⟨ t ∷ vector ts ⟩)

-- τs⇓⟦_⟧ : (I : Interpretation) → (τs : Terms) → τs⇑⟦ I ⟧ τs ⇓
-- τs⇓⟦ I ⟧ ⟨ ⟨ [] ⟩ ⟩ = _ , now⇓
-- τs⇓⟦ I ⟧ ⟨ ⟨ variable 𝑥 ∷ τs ⟩ ⟩ = _ , τs⇓⟦ I ⟧ ⟨ ⟨ τs ⟩ ⟩ ⇓>>=⇓ now⇓
-- τs⇓⟦ I ⟧ ⟨ ⟨ function 𝑓₁ τs₁ ∷ τs₂ ⟩ ⟩ =
--   _ , τs⇓⟦ I ⟧ τs₁ ⇓>>=⇓ now⇓ >>=⇓ (τs⇓⟦ I ⟧ ⟨ ⟨ τs₂ ⟩ ⟩ ⇓>>=⇓ now⇓)

-- τ⇓⟦_⟧ : (I : Interpretation) → (τ : Term) → τ⇑⟦ I ⟧ τ ⇓
-- τ⇓⟦ I ⟧ (variable 𝑥) = _ , now⇓
-- τ⇓⟦ I ⟧ (function 𝑓 τs) = _ , τs⇓⟦ I ⟧ τs ⇓>>=⇓ now⇓

-- τ⟦_⟧ : (I : Interpretation) → {i : Size} → (τ : Term) → Element
-- τ⟦ I ⟧ τ = fst (τ⇓⟦ I ⟧ τ)

-- record HasSatisfaction (A : Set) ⦃ _ : 𝓐ssertion A ⦄ : Set₁
--  where
--   field
--     _⊨_ : Interpretation → A → Set

--   _⊭_ : Interpretation → A → Set
--   _⊭_ I = ¬_ ∘ I ⊨_

-- open HasSatisfaction ⦃ … ⦄

-- {-# DISPLAY HasSatisfaction._⊨_ _ = _⊨_ #-}
-- {-# DISPLAY HasSatisfaction._⊭_ _ = _⊭_ #-}

-- record _≞_/_ (𝓘 : Interpretation) (I : Interpretation) (𝑥 : VariableName) : Set
--  where
--   field
--     μEquality : {𝑥′ : VariableName} → 𝑥′ ≢ 𝑥 → μ⟦ 𝓘 ⟧ 𝑥 ≡ μ⟦ I ⟧ 𝑥′
--     𝑓Equality : (𝑓 : FunctionName) (μs : Elements) → 𝑓⟦ 𝓘 ⟧ 𝑓 μs ≡ 𝑓⟦ I ⟧ 𝑓 μs
--     𝑃Equality : (𝑃 : PredicateName) → (μs : Elements) → 𝑃⟦ 𝓘 ⟧ 𝑃 μs ≡ 𝑃⟦ I ⟧ 𝑃 μs

-- instance HasSatisfactionFormula : HasSatisfaction Formula
-- HasSatisfaction._⊨_ HasSatisfactionFormula I (atomic 𝑃 τs) = 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩ ≡ ⟨ true ⟩
-- HasSatisfaction._⊨_ HasSatisfactionFormula I (logical φ₁ φ₂) = ¬ I ⊨ φ₁ × ¬ I ⊨ φ₂
-- HasSatisfaction._⊨_ HasSatisfactionFormula I (quantified 𝑥 φ) = (𝓘 : Interpretation) → 𝓘 ≞ I / 𝑥 → 𝓘 ⊨ φ

-- instance HasSatisfaction𝓕ormula : {Is𝓕ormula : Formula → Set} → HasSatisfaction (𝓕ormula Is𝓕ormula)
-- HasSatisfaction._⊨_ HasSatisfaction𝓕ormula I ⟪ φ ⟫ = I ⊨ φ

-- instance HasSatisfactionLiteralFormula : HasSatisfaction LiteralFormula
-- HasSatisfaction._⊨_ HasSatisfactionLiteralFormula I ⟨ atomic 𝑃 τs ⟩ = 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩ ≡ ⟨ true ⟩
-- HasSatisfaction._⊨_ HasSatisfactionLiteralFormula I ⟨ logical 𝑃 τs ⟩ = 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩ ≡ ⟨ false ⟩

-- instance HasSatisfactionList : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction $ List A
-- HasSatisfaction._⊨_ HasSatisfactionList I [] = ⊤
-- HasSatisfaction._⊨_ HasSatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs

-- instance 𝓐ssertionSequent : 𝓐ssertion Sequent
-- 𝓐ssertionSequent = record {}

-- instance 𝓐ssertionLiteralSequent : 𝓐ssertion LiteralSequent
-- 𝓐ssertionLiteralSequent = record {}

-- instance 𝓐ssertionProblem : 𝓐ssertion Problem
-- 𝓐ssertionProblem = record {}

-- instance 𝓐ssertionLiteralProblem : 𝓐ssertion LiteralProblem
-- 𝓐ssertionLiteralProblem = record {}

-- instance HasSatisfactionSequent : HasSatisfaction Sequent
-- HasSatisfaction._⊨_ HasSatisfactionSequent I (φᵗ ╱ φˢs) = I ⊨ φˢs → I ⊨ φᵗ

-- instance HasSatisfactionLiteralSequent : HasSatisfaction LiteralSequent
-- HasSatisfaction._⊨_ HasSatisfactionLiteralSequent I Φ = I ⊨ sequent Φ

-- instance HasSatisfactionProblem : HasSatisfaction Problem
-- HasSatisfaction._⊨_ HasSatisfactionProblem I (Φ⁺s ¶ Φ⁻) = I ⊨ Φ⁺s → I ⊨ Φ⁻

-- instance HasSatisfactionLiteralProblem : HasSatisfaction LiteralProblem
-- HasSatisfaction._⊨_ HasSatisfactionLiteralProblem I 𝔓 = I ⊨ problem 𝔓

-- record HasDecidableSatisfaction (A : Set) ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ : Set₁
--  where
--   field
--     _⊨?_ : (I : Interpretation) → (x : A) → Dec (I ⊨ x)

-- open HasDecidableSatisfaction ⦃ … ⦄

-- {-# DISPLAY HasDecidableSatisfaction._⊨?_ _ = _⊨?_ #-}

-- instance HasDecidableSatisfactionFormula : HasDecidableSatisfaction Formula
-- HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionFormula I (atomic 𝑃 τs) = {!!}
-- HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionFormula I (logical φ₁ φ₂) = {!!}
-- HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionFormula I (quantified 𝑥 φ) = {!!}

-- instance HasDecidableSatisfactionLiteralFormula : HasDecidableSatisfaction LiteralFormula
-- HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionLiteralFormula
--   I ⟨ atomic 𝑃 τs ⟩
--  with 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩
-- … | ⟨ true ⟩ = yes refl
-- … | ⟨ false ⟩ = no λ ()
-- HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionLiteralFormula
--   I ⟨ logical 𝑃 τs ⟩
--   with 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩
-- … | ⟨ true ⟩ = no λ ()
-- … | ⟨ false ⟩ = yes refl

-- module _ {A} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄
--  where

--    ⊨_ : A → Set
--    ⊨ x = (I : Interpretation) → I ⊨ x

--    ⊭_ : A → Set
--    ⊭_ = ¬_ ∘ ⊨_

-- record HasDecidableValidation (A : Set) ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ : Set₁
--  where
--   field
--     ⊨?_ : (x : A) → Dec $ ⊨ x

-- instance HasDecidableValidationFormula : HasDecidableValidation Formula
-- HasDecidableValidation.⊨?_ HasDecidableValidationFormula (atomic 𝑃 τs) = {!!}
-- HasDecidableValidation.⊨?_ HasDecidableValidationFormula (logical φ₁ φ₂) = {!!}
-- HasDecidableValidation.⊨?_ HasDecidableValidationFormula (quantified 𝑥 φ) = {!!}

-- instance HasDecidableValidationLiteralFormula : HasDecidableValidation LiteralFormula
-- HasDecidableValidationLiteralFormula = {!!}

-- instance HasDecidableValidationSequent : HasDecidableValidation Sequent
-- HasDecidableValidationSequent = {!!}

-- instance HasDecidableValidationLiteralSequent : HasDecidableValidation LiteralSequent
-- HasDecidableValidationLiteralSequent = {!!}

-- instance HasDecidableValidationProblem : HasDecidableValidation Problem
-- HasDecidableValidationProblem = {!!}

-- instance HasDecidableValidationLiteralProblem : HasDecidableValidation LiteralProblem
-- HasDecidableValidationLiteralProblem = {!!}

-- postulate
--   substituteFormula : (VariableName → Term) → Formula → Formula

-- record Unifier : Set
--  where
--   field
--     unifier-left unifier-right : VariableName → Term

-- open Unifier

-- record _Unifies_and_ (υ : Unifier) (φ₁ φ₂ : Formula) : Set
--  where
--   field
--     unification-law : substituteFormula (unifier-left υ) φ₁ ≡ substituteFormula (unifier-right υ) φ₂

-- record HasSubstantiveDischarge (+ : Set) (- : Set) : Set₁
--  where
--   field
--     _≽_ : + → - → Set

--   _⋡_ : + → - → Set
--   + ⋡ - = ¬ + ≽ -

-- open HasSubstantiveDischarge ⦃ … ⦄

-- {-# DISPLAY HasSubstantiveDischarge._≽_ _ = _≽_ #-}

-- instance HasSubstantiveDischargeList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (List A) A
-- HasSubstantiveDischarge._≽_ HasSubstantiveDischargeList +s - = {!!} -- ∃ λ c → (c ∈ +s) × c ≽ -

-- instance HasSubstantiveDischargeListList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (List A) (List A)
-- HasSubstantiveDischarge._≽_ HasSubstantiveDischargeListList +s -s = {!!} -- ∀ i → i ∈ -s → +s ≽ i

-- instance HasSubstantiveDischargeFormulaFormula : HasSubstantiveDischarge Formula Formula
-- HasSubstantiveDischarge._≽_ HasSubstantiveDischargeFormulaFormula φ₁ φ₂ = ∃ λ υ → υ Unifies φ₁ and φ₂

-- instance HasSubstantiveDischargeSequentSequent : HasSubstantiveDischarge Sequent Sequent
-- HasSubstantiveDischarge._≽_ HasSubstantiveDischargeSequentSequent (+ᵗ ╱ +ᵖs) (-ᵗ ╱ -ᵖs) = {!!} -- +ᵗ ≽ -ᵗ × +ᵖs ≽ -ᵖs -- use "unification into", from John's "Natural Deduction"

-- instance HasSubstantiveDischargeProblemProblem : HasSubstantiveDischarge Problem Problem
-- HasSubstantiveDischarge._≽_ HasSubstantiveDischargeProblemProblem (+s ¶ +) (-s ¶ -) = {!!} -- + ≽ - × +s ≽ -s

-- record HasDecidableSubstantiveDischarge (+ : Set) (- : Set) ⦃ _ : HasSubstantiveDischarge (+) (-) ⦄ : Set₁
--  where
--   field
--     _≽?_ : (+ : +) → (- : -) → Dec $ + ≽ -

-- open HasDecidableSubstantiveDischarge ⦃ … ⦄

-- {-# DISPLAY HasDecidableSubstantiveDischarge._≽?_ _ = _≽?_ #-}

-- instance HasDecidableSubstantiveDischargeList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasDecidableSubstantiveDischarge A A ⦄ ⦃ _ : Eq A ⦄ → HasDecidableSubstantiveDischarge (List A) A
-- HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeList +s - = {!!}

-- instance HasDecidableSubstantiveDischargeListList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasDecidableSubstantiveDischarge A A ⦄ ⦃ _ : Eq A ⦄ → HasDecidableSubstantiveDischarge (List A) (List A)
-- HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeListList +s -s = {!!}

-- instance HasDecidableSubstantiveDischargeFormulaFormula : HasDecidableSubstantiveDischarge Formula Formula
-- HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeFormulaFormula = {!!} -- _≟_

-- instance HasDecidableSubstantiveDischargeSequentSequent : HasDecidableSubstantiveDischarge Sequent Sequent
-- HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeSequentSequent = {!!}

-- instance HasDecidableSubstantiveDischargeProblemProblem : HasDecidableSubstantiveDischarge Problem Problem
-- HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeProblemProblem = {!!}

-- record SubstantiveDischargeIsConsistent (+ : Set) (- : Set) ⦃ _ : HasNegation (-) ⦄ ⦃ _ : HasSubstantiveDischarge (+) (-) ⦄ : Set₁
--  where
--   field
--     ≽-consistent : {+ : +} → { - : - } → + ≽ - → + ⋡ ~ -

-- open SubstantiveDischargeIsConsistent ⦃ … ⦄

-- {-# DISPLAY SubstantiveDischargeIsConsistent.≽-consistent _ = ≽-consistent #-}

-- record SubstantiveDischargeIsReflexive (A : Set) ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
--  where
--   field
--     ≽-reflexive : (x : A) → x ≽ x

-- open SubstantiveDischargeIsReflexive ⦃ … ⦄
-- {-
-- record SubstantiveDischargeIsReflexive (A : Set) ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
--  where
--   field
--     ≽-reflexive : {x : A} → x ≽ x

-- open SubstantiveDischargeIsReflexive ⦃ … ⦄
-- -}
-- {-# DISPLAY SubstantiveDischargeIsReflexive.≽-reflexive _ = ≽-reflexive #-}

-- record HasVacuousDischarge (A : Set) ⦃ _ : HasNegation A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
--  where

--   ◁_ : List A → Set
--   ◁ +s = ∃ λ (s : A) → (+s ≽ s) × (+s ≽ ~ s)

--   ⋪_ : List A → Set
--   ⋪_ = ¬_ ∘ ◁_

-- open HasVacuousDischarge ⦃ … ⦄

-- {-# DISPLAY HasVacuousDischarge.◁_ _ = ◁_ #-}
-- {-# DISPLAY HasVacuousDischarge.⋪_ _ = ⋪_ #-}

-- infixr 1 ,_
-- pattern  ,_ p = _ , p

-- pattern ◁pattern c₁∈xs c₁≽s c₂∈xs c₂≽~s = , (((, (c₁∈xs , c₁≽s)) , (, (c₂∈xs , c₂≽~s))))

-- record HasDecidableVacuousDischarge (A : Set)
--                                     ⦃ _ : HasNegation A ⦄
--                                     ⦃ _ : HasSubstantiveDischarge A A ⦄
--                                     ⦃ _ : HasVacuousDischarge A ⦄
--                                     --⦃ _ : HasDecidableSubstantiveDischarge A A ⦄
--                                     --⦃ _ : SubstantiveDischargeIsConsistent A A ⦄
--                                     --⦃ _ : SubstantiveDischargeIsReflexive A ⦄
--                                     ⦃ _ : Eq A ⦄
--                                     : Set₁
--  where
--   field
--     ◁?_ : (x : List A) → Dec $ ◁ x

-- instance HasDecidableVacuousDischarge𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : Eq A ⦄ ⦃ _ : HasNegation (𝓢equent A) ⦄ ⦃ _ : HasSubstantiveDischarge (𝓢equent A) (𝓢equent A) ⦄ ⦃ _ : HasVacuousDischarge (𝓢equent A) ⦄ → HasDecidableVacuousDischarge (𝓢equent A)
-- HasDecidableVacuousDischarge𝓢equent = {!!}
-- {-
-- instance
--   ◁? [] = no (λ { (_ , (_ , () , _) , _)})
--   ◁? (x ∷ xs) with xs ≽? ~ x
--   ◁? (x ∷ xs) | yes (, ~x!∈xs , ~x!≽~x) = yes $ , (((, (here xs , ≽-reflexive x)) , (, (there _ ~x!∈xs , ~x!≽~x))))
--   ◁? (x ∷ xs) | no xs⋡~x with ◁? xs
--   ◁? (x ∷ xs) | no xs⋡~x | yes (◁pattern c₁∈xs c₁≽s c₂∈xs c₂≽~s) = yes (◁pattern (there _ c₁∈xs) c₁≽s (there _ c₂∈xs) c₂≽~s)
--   ◁? (x ∷ xs) | no xs⋡~x | no ⋪xs = no λ
--     { (◁pattern (here .xs) x≽s (here .xs) c₂≽~s) → {!xs⋡~x!}
--     ; (◁pattern (here .xs) x≽s (there _ c₂∈xs) c₂≽~s) → {!xs⋡~x!}
--     ; (◁pattern (there _ c₁∈xs) c₁≽s c₂∈xxs c₂≽~s) → {!xs⋡~x!} }
-- -}
-- --{-⋪xs (◁pattern {!!} c₁≽s {!!} c₂≽~s)-}
-- open HasDecidableVacuousDischarge ⦃ … ⦄

-- {-# DISPLAY HasDecidableVacuousDischarge.◁?_ _ = ◁?_ #-}

-- instance HasDecidableVacuousDischargeFormula : HasDecidableVacuousDischarge Formula
-- HasDecidableVacuousDischarge.◁?_ HasDecidableVacuousDischargeFormula [] = {!!}
-- HasDecidableVacuousDischarge.◁?_ HasDecidableVacuousDischargeFormula (φ ∷ φs) = {!!}

-- record HasSalvation (A : Set) : Set₁
--  where
--   field
--     -- {isVacuouslyDischargable} : Set
--     -- ⦃ hasVacuousDischarge ⦄ : HasVacuousDischarge isVacuouslyDischargable
--     ▷_ : A → Set

-- open HasSalvation ⦃ … ⦄

-- instance

--   HasSalvation𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasNegation A ⦄ ⦃ _ : HasVacuousDischarge A ⦄ → HasSalvation $ 𝓢equent A
--   HasSalvation.▷_ HasSalvation𝓢equent (φᵖs ⊢ φᵗs) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗs)

-- {-# DISPLAY HasSalvation.▷_ _ = ▷_ #-}

-- record HasDecidableSalvation (A : Set) ⦃ _ : HasSalvation A ⦄ : Set₁
--  where
--   field
--     ▷?_ : (x : A) → Dec $ ▷_ x

-- open HasDecidableSalvation ⦃ … ⦄

-- {-# DISPLAY HasDecidableSalvation.▷?_ _ = ▷?_ #-}

-- ∀[_♭_] : VariableName → Formula → Formula
-- ∀[_♭_] = quantified

-- {-# DISPLAY quantified = ∀[_♭_] #-}

-- _∧_ : Formula → Formula → Formula
-- φ₁ ∧ φ₂ = ~ φ₁ ⊗ ~ φ₂

-- _∨_ : Formula → Formula → Formula
-- φ₁ ∨ φ₂ = ~ (φ₁ ⊗ φ₂)

-- _⊃_ : Formula → Formula → Formula
-- φ₁ ⊃ φ₂ = ~ φ₁ ∨ φ₂

-- _⟷_ : Formula → Formula → Formula
-- φ₁ ⟷ φ₂ = (φ₁ ⊗ (φ₂ ⊗ φ₂)) ⊗ ((φ₁ ⊗ φ₁) ⊗ φ₂) -- TODO check that this is logically equivalent to the more verbose, (φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)

-- data TermCode : Set
--  where
--   variable : VariableName → TermCode
--   function : FunctionName → Arity → TermCode

-- termCode-function-inj₁ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → 𝑓₁ ≡ 𝑓₂
-- termCode-function-inj₁ refl = refl

-- termCode-function-inj₂ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → arity₁ ≡ arity₂
-- termCode-function-inj₂ refl = refl

-- instance
--   EqTermCode : Eq TermCode
--   Eq._==_ EqTermCode (variable 𝑥₁) (variable 𝑥₂) with 𝑥₁ ≟ 𝑥₂
--   … | yes 𝑥₁≡𝑥₂ rewrite 𝑥₁≡𝑥₂ = yes refl
--   … | no 𝑥₁≢𝑥₂ = no (λ { refl → 𝑥₁≢𝑥₂ refl})
--   Eq._==_ EqTermCode (variable x) (function x₁ x₂) = no (λ ())
--   Eq._==_ EqTermCode (function x x₁) (variable x₂) = no (λ ())
--   Eq._==_ EqTermCode (function 𝑓₁ 𝑎₁) (function 𝑓₂ 𝑎₂) = decEq₂ termCode-function-inj₁ termCode-function-inj₂ (𝑓₁ ≟ 𝑓₂) (𝑎₁ ≟ 𝑎₂)

-- mutual
--   encodeTerm : Term → List TermCode
--   encodeTerm (variable 𝑥) = variable 𝑥 ∷ []
--   encodeTerm (function 𝑓 (⟨_⟩ {arity} τs)) = function 𝑓 arity ∷ encodeTerms τs

--   encodeTerms : {arity : Arity} → Vector Term arity → List TermCode
--   encodeTerms ⟨ [] ⟩ = []
--   encodeTerms ⟨ τ ∷ τs ⟩ = encodeTerm τ ++ encodeTerms ⟨ τs ⟩

-- mutual

--   decodeTerm : Nat → StateT (List TermCode) Maybe Term
--   decodeTerm zero = lift nothing
--   decodeTerm (suc n) = do
--     caseM get of λ
--     { [] → lift nothing
--     ; (variable 𝑥 ∷ _) →
--       modify (drop 1) ~|
--       return (variable 𝑥)
--     ; (function 𝑓 arity ∷ _) →
--       modify (drop 1) ~|
--       decodeFunction n 𝑓 arity }

--   decodeFunction : Nat → FunctionName → Arity → StateT (List TermCode) Maybe Term
--   decodeFunction n 𝑓 arity = do
--     τs ← decodeTerms n arity -|
--     return (function 𝑓 ⟨ τs ⟩)

--   decodeTerms : Nat → (arity : Arity) → StateT (List TermCode) Maybe (Vector Term arity)
--   decodeTerms n ⟨ zero ⟩ = return ⟨ [] ⟩
--   decodeTerms n ⟨ suc arity ⟩ = do
--     τ ← decodeTerm n -|
--     τs ← decodeTerms n ⟨ arity ⟩ -|
--     return ⟨ τ ∷ vector τs ⟩

-- .decode-is-inverse-of-encode : ∀ τ → runStateT (decodeTerm ∘ length $ encodeTerm τ) (encodeTerm τ) ≡ (just $ τ , [])
-- decode-is-inverse-of-encode (variable 𝑥) = refl
-- decode-is-inverse-of-encode (function 𝑓 ⟨ ⟨ [] ⟩ ⟩) = {!!}
-- decode-is-inverse-of-encode (function 𝑓 ⟨ ⟨ variable 𝑥 ∷ τs ⟩ ⟩) = {!!}
-- decode-is-inverse-of-encode (function 𝑓 ⟨ ⟨ function 𝑓' τs' ∷ τs ⟩ ⟩) = {!!}

-- module ExampleEncodeDecode where
--   example-Term : Term
--   example-Term =
--     (function ⟨ 2 ⟩
--               ⟨ ⟨ ( variable ⟨ 0 ⟩ ∷
--                   function ⟨ 3 ⟩ ⟨ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ⟩ ∷
--                   variable ⟨ 5 ⟩ ∷ [] )
--                 ⟩ ⟩
--     )

--   -- function ⟨ 2 ⟩ ⟨ 3 ⟩ ∷ variable ⟨ 0 ⟩ ∷ function ⟨ 3 ⟩ ⟨ 1 ⟩ ∷ variable ⟨ 2 ⟩ ∷ variable ⟨ 5 ⟩ ∷ []
--   example-TermCodes : List TermCode
--   example-TermCodes = encodeTerm example-Term

--   example-TermDecode : Maybe (Term × List TermCode)
--   example-TermDecode = runStateT (decodeTerm (length example-TermCodes)) example-TermCodes

--   example-verified : example-TermDecode ≡ (just $ example-Term , [])
--   example-verified = refl

--   example-bad : runStateT (decodeTerm 2) (function ⟨ 2 ⟩ ⟨ 2 ⟩ ∷ variable ⟨ 0 ⟩ ∷ []) ≡ nothing
--   example-bad = refl

-- record TermNode : Set
--  where
--   inductive
--   field
--     children : List (TermCode × TermNode)
--     number : Nat

-- open TermNode

-- _child∈_ : TermCode → TermNode → Set
-- _child∈_ 𝔠 𝔫 = 𝔠 ∈ (fst <$> children 𝔫)

-- _child∉_ : TermCode → TermNode → Set
-- 𝔠 child∉ 𝔫 = ¬ (𝔠 child∈ 𝔫)

-- _child∈?_ : (𝔠 : TermCode) → (𝔫 : TermNode) → Dec $ 𝔠 child∈ 𝔫
-- c child∈? record { children = cs } = c ∈? (fst <$> cs)

-- getChild : {𝔠 : TermCode} → (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode
-- getChild {𝔠} (record { children = [] ; number = number₁ }) ()
-- getChild {._} (record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }) zero = snd₁
-- getChild {𝔠} (𝔫@record { children = x ∷ children₁ ; number = number₁ }) (suc x₁) = getChild record 𝔫 { children = children₁ } x₁

-- addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∉ 𝔫 → TermNode → TermNode
-- addChild {𝔠} 𝔫 𝔠∉𝔫 𝔫' =
--   record 𝔫 { children = (𝔠 , 𝔫') ∷ children 𝔫 }

-- setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode → TermNode
-- setChild {𝔠} record { children = [] ; number = number₁ } () 𝔫'
-- setChild 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (zero) 𝔫' =
--   record 𝔫 { children = ((fst₁ , 𝔫') ∷ children₁) }
-- setChild {𝔠} 𝔫@record { children = (x ∷ children₁) ; number = number₁ } (suc 𝔠∈𝔫) 𝔫' =
--   record 𝔫 { children = (x ∷ children (setChild (record 𝔫 { children = children₁ }) 𝔠∈𝔫 𝔫')) }

-- setGet-ok : ∀ {𝔠} 𝔫 → (𝔠∈𝔫 : 𝔠 child∈ 𝔫) → setChild 𝔫 𝔠∈𝔫 (getChild 𝔫 𝔠∈𝔫) ≡ 𝔫
-- setGet-ok record { children = [] ; number = number₁ } ()
-- setGet-ok record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (zero) = refl
-- setGet-ok record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (suc 𝔠∈𝔫) rewrite setGet-ok (record { children = children₁ ; number = number₁ }) 𝔠∈𝔫 = refl

-- storeTermCodes : List TermCode → Nat → StateT TermNode Identity Nat
-- storeTermCodes [] 𝔑 = return 𝔑
-- storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
--   𝔫 ← get -|
--   case 𝔠 child∈? 𝔫 of λ
--   { (no 𝔠∉tests) →
--     let 𝔑' , 𝔫' = runIdentity $
--                   runStateT
--                     (storeTermCodes 𝔠s $ suc 𝔑)
--                     (record
--                       { children = []
--                       ; number = suc 𝔑 }) in
--     put ((addChild 𝔫 𝔠∉tests 𝔫')) ~|
--     return 𝔑'
--   ; (yes 𝔠∈tests) →
--     let 𝔑' , 𝔫' = runIdentity $
--                   runStateT
--                     (storeTermCodes 𝔠s $ suc 𝔑)
--                     ((getChild 𝔫 𝔠∈tests)) in
--     put ((setChild 𝔫 𝔠∈tests 𝔫')) ~|
--     return 𝔑' }

-- storeTermCodes[] : (𝔫 : TermNode) (𝔑 : Nat) → (runIdentity $ runStateT (storeTermCodes [] 𝔑) 𝔫) ≡ (𝔑 , 𝔫)
-- storeTermCodes[] 𝔫 𝔑 = refl

-- --{-# REWRITE storeTermCodes[] #-}

-- storeTermCodes' : List TermCode → StateT Nat (StateT TermNode Identity) ⊤
-- storeTermCodes' 𝔠s =
--   𝔑 ← get -|
--   tn ← lift get -|
--   (let 𝔑' , tn' = runIdentity $ runStateT (storeTermCodes 𝔠s 𝔑) tn in
--    put 𝔑' ~| lift (put tn') ~| return tt)

-- mutual

--   storeTerm : Term → StateT Nat (StateT TermNode Identity) ⊤
--   storeTerm τ@(variable _) = storeTermCodes' (encodeTerm τ)
--   storeTerm τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTerms τs

--   storeTerms : Terms → StateT Nat (StateT TermNode Identity) ⊤
--   storeTerms ⟨ ⟨ [] ⟩ ⟩ = return tt
--   storeTerms ⟨ ⟨ τ ∷ τs ⟩ ⟩ = storeTerm τ ~| storeTerms ⟨ ⟨ τs ⟩ ⟩ ~| return tt

-- module ExampleStoreTerm where
--   example-Term₁ : Term
--   example-Term₁ =
--     (function ⟨ 2 ⟩
--               ⟨ ⟨ variable ⟨ 0 ⟩
--               ∷ function ⟨ 3 ⟩
--                          ⟨ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ⟩
--               ∷ variable ⟨ 5 ⟩
--               ∷ []
--               ⟩ ⟩
--     )

--   example-Term₂ : Term
--   example-Term₂ =
--     (function ⟨ 2 ⟩
--               ⟨ ⟨ variable ⟨ 0 ⟩
--               ∷ variable ⟨ 2 ⟩
--               ∷ function ⟨ 3 ⟩
--                          ⟨ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ⟩
--               ∷ variable ⟨ 5 ⟩
--               ∷ []
--               ⟩ ⟩
--     )

--   topNode : TermNode
--   topNode = record { children = [] ; number = 0 }

--   example-storeTerm : (⊤ × Nat) × TermNode
--   example-storeTerm = runIdentity $ runStateT (runStateT (storeTerm example-Term₁ >> storeTerm example-Term₂) 0) topNode

-- NodeStateT = StateT TermNode
-- TopNodeState = StateT Nat (NodeStateT Identity)

-- storeLiteralFormulaTerms : LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤
-- storeLiteralFormulaTerms ⟨ atomic 𝑃 τs ⟩ = storeTerms τs
-- storeLiteralFormulaTerms ⟨ logical 𝑃 τs ⟩ = storeTerms τs

-- storeSequentLiteralFormulaTerms : 𝓢equent LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤′
-- storeSequentLiteralFormulaTerms (φˢs ⊢ φᵗ) = sequence $ storeLiteralFormulaTerms <$> ({!φᵗ!} ∷ φˢs)

-- record FindTermNode (A : Set) : Set
--  where
--   field
--     findTermNode : A → TermNode → Maybe TermNode

-- open FindTermNode ⦃ … ⦄

-- instance
--   FindTermNodeTermCode : FindTermNode TermCode
--   FindTermNode.findTermNode FindTermNodeTermCode termCode record { children = [] ; number = number₁ } = nothing
--   FindTermNode.findTermNode FindTermNodeTermCode termCode 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } = ifYes fst₁ ≟ termCode then just snd₁ else findTermNode termCode record 𝔫 { children = children₁ }

--   FindTermNodeTermCodes : FindTermNode (List TermCode)
--   FindTermNode.findTermNode FindTermNodeTermCodes [] node = just node
--   FindTermNode.findTermNode FindTermNodeTermCodes (x ∷ termCodes) node = join $ findTermNode termCodes <$> findTermNode x node

--   FindTermNodeTerm : FindTermNode Term
--   FindTermNode.findTermNode FindTermNodeTerm term node = findTermNode (encodeTerm term) node

-- -- This is starting to get difficult. We need Agda to know that the Term is encoded in the TermNode. Then we can drop the Maybe
-- getInterpretationOfTerm : Term → TermNode → Maybe Element
-- getInterpretationOfTerm τ node = ⟨_⟩ ∘ number <$> findTermNode (encodeTerm τ) node

-- FindTermNodeTermCode-ok : ∀ {𝔠 𝔫} → 𝔠 child∈ 𝔫 → IsJust (findTermNode 𝔠 𝔫)
-- FindTermNodeTermCode-ok {𝔠} {record { children = [] ; number = number₁ }} ()
-- --FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ = case (fst₁ ≟_) 𝔠 , graphAt {B = λ 𝑐 → Dec (fst₁ ≡ 𝑐)} (fst₁ ≟_) 𝔠 of λ { (yes x , snd₂) → {!!} ; (no x , snd₂) → {!!}} --λ { ((yes ===) , (inspect s1)) → {!!} ; ((no =n=) , inspect s2) → {!!} }
-- --FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ = case fst₁ ≟ 𝔠 of λ { (yes refl) → {!!} ; (no x) → {!!}}
-- FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ with fst₁ ≟ 𝔠
-- FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ | yes eq2 = tt
-- FindTermNodeTermCode-ok {.fst₁} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} (zero) | no neq = ⊥-elim (neq refl)
-- FindTermNodeTermCode-ok {𝔠} {𝔫@record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} (suc x₁) | no neq = FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} x₁

-- Justified : ∀ {a} {A : Set a} → (m : Maybe A) → IsJust m → ∃ λ x → m ≡ just x
-- Justified nothing ()
-- Justified (just x) x₁ = _ , refl

-- storeTerm-ok : ∀ τ 𝔫 𝔑 → IsJust (findTermNode τ (snd (runIdentity (runStateT (runStateT (storeTerm τ) 𝔑) 𝔫))))
-- storeTerm-ok (variable 𝑥) 𝔫 𝔑 with variable 𝑥 child∈? 𝔫
-- storeTerm-ok (variable 𝑥) 𝔫 𝔑 | no x with TermCode.variable 𝑥 ≟ variable 𝑥
-- storeTerm-ok (variable 𝑥) 𝔫 𝔑 | no x | yes _ = tt
-- storeTerm-ok (variable 𝑥) 𝔫 𝔑 | no x | no variable𝑥≢variable𝑥 = ⊥-elim (variable𝑥≢variable𝑥 refl)
-- --storeTerm-ok (variable 𝑥) 𝔫 𝔑 | yes vx∈𝔫 rewrite setGet-ok 𝔫 vx∈𝔫 = {!𝔫!}
-- storeTerm-ok (variable 𝑥) record { children = [] ; number = number₁ } 𝔑 | yes ()
-- --storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 rewrite setGet-ok 𝔫 vx∈𝔫 = {!!}
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 rewrite setGet-ok 𝔫 vx∈𝔫 with fst₁ ≟ variable 𝑥
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | yes eq = tt
-- --… | no neq = case vx∈𝔫 of λ { (here .(map fst children₁)) → ⊥-elim (neq refl)  ; (there .fst₁ asdf) → case graphAt FindTermNodeTermCode-ok asdf of λ { (ingraph sss) → {!!} } } -- storeTerm-ok x {!record 𝔫 { children = children₁ }!} 𝔑 -- x record 𝔫 { children = children₁ } 𝔑
-- --… | no neq = case vx∈𝔫 of λ { (here .(map fst children₁)) → ⊥-elim (neq refl)  ; (there .fst₁ asdf) → case inspect $ FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} asdf of λ { (.(FindTermNodeTermCode-ok asdf) , ingraph refl) → {!!}} } -- storeTerm-ok x {!record 𝔫 { children = children₁ }!} 𝔑 -- x record 𝔫 { children = children₁ } 𝔑
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq with vx∈𝔫
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | zero = ⊥-elim (neq refl)
-- --storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | there dfdsf fdsdfs with FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs | graphAt (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }}) fdsdfs
-- --… | frfrrf | ingraph tttttt = transport _ (snd $ Justified (FindTermNode.findTermNode FindTermNodeTermCode (variable 𝑥) (record { children = children₁ ; number = number₁ })) (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs)) _
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | suc fdsdfs rewrite (snd $ Justified (FindTermNode.findTermNode FindTermNodeTermCode (variable 𝑥) (record { children = children₁ ; number = number₁ })) (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs)) = tt
-- storeTerm-ok (function 𝑥 𝑎) 𝔫 𝔑 with (function 𝑥 (arity 𝑎)) child∈? 𝔫
-- storeTerm-ok (function 𝑥 ⟨ ⟨ [] ⟩ ⟩) 𝔫 𝔑 | no x with Eq._==_ EqFunctionName ⟨ name 𝑥 ⟩ ⟨ name 𝑥 ⟩
-- storeTerm-ok (function 𝑥 ⟨ ⟨ [] ⟩ ⟩) 𝔫 𝔑 | no x | (yes refl) = tt
-- … | no neq = ⊥-elim (neq refl)
-- --storeTerm-ok τ₀@(function 𝑓 ⟨ τ₁ ∷ τ₂s ⟩) 𝔫 𝔑 | no 𝔠₁∉𝔫 = {!τ₁!}
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₁∉𝔫 with variable 𝑥 child∈? 𝔫
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) with 𝑓₀ ≟ 𝑓₀
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl with TermCode.variable 𝑥 ≟ variable 𝑥
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl | yes eq = tt
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl | no neq = ⊥-elim (neq refl)
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | no neq = ⊥-elim (neq refl)
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) with 𝑓₀ ≟ 𝑓₀
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl with TermCode.variable 𝑥₁ ≟ variable 𝑥₁
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl | yes 𝔠₁≡𝔠₁ = tt
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl | no 𝔠₁≢𝔠₁ = ⊥-elim (𝔠₁≢𝔠₁ refl)
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | no 𝑓₀≢𝑓₀ = ⊥-elim (𝑓₀≢𝑓₀ refl) -- rewrite setGet-ok 𝔫 𝔠₁∈𝔫
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 with variable 𝑥₁ child∈? 𝔫
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 | yes 𝔠₁∈𝔫 = {!!}
-- storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 | no 𝔠₁∉𝔫 = {!!}
-- storeTerm-ok τ₀@(function 𝑓₀ ⟨ ⟨ function 𝑓₁ τ₁s ∷ τ₂s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₁∉𝔫 = {!!}
-- storeTerm-ok (function 𝑥 x₁) 𝔫 𝔑 | yes x = {!!}

-- mutual

--   storeTermVerifiably' : (τ : Term) → StateT Nat (StateT (Σ TermNode λ n → IsJust (findTermNode τ n)) Identity) ⊤
--   storeTermVerifiably' (variable x) = {!!}
--   storeTermVerifiably' (function x x₁) = {!!}

--   storeTermVerifiably : Term → StateT Nat (StateT TermNode Identity) ⊤
--   storeTermVerifiably τ@(variable _) = storeTermCodes' (encodeTerm τ)
--   storeTermVerifiably τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTermsVerifiably τs

--   storeTermsVerifiably : Terms → StateT Nat (StateT TermNode Identity) ⊤
--   storeTermsVerifiably ⟨ ⟨ [] ⟩ ⟩ = return tt
--   storeTermsVerifiably ⟨ ⟨ τ ∷ τs ⟩ ⟩ = storeTermVerifiably τ ~| storeTermsVerifiably ⟨ ⟨ τs ⟩ ⟩ ~| return tt

-- Theorem1 : {Φ : 𝓢equent (𝓢equent LiteralFormula)} → {!⊨!} Φ ↔ {!▷!} Φ
-- Theorem1 = {!!}
-- {-
-- Theorem1 {Φ@(χs ¶ ι)} = Theorem1a , Theorem1b
--  where
--   Theorem1a : ⊨ Φ → ▷ Φ
--   Theorem1a with ▷? Φ
--   … | yes ▷Φ = const ▷Φ
--   … | no ⋫Φ =
--     let I , I⊨χs , I⊭ι = Lemma1a in
--     λ I→I⊨cs→I⊨i → ⊥-elim $ I⊭ι $ I→I⊨cs→I⊨i I I⊨χs
--    where
--     Lemma1a : ∃ λ I → I ⊨ χs × I ⊭ ι
--     -- To construct the interpretation, consider a unique list, τ₀, τ₁, …, τₙ, of terms in ι ∷ χs. For each term, τ, we find <TODO> interpretations, 𝓘, such that for any I ∈ 𝓘, and any i ∈ 0, …, n, τ⟦ I ⟧ τᵢ = i. For each formula φ ∈ ι ∷ χs, we find <TODO> an interpretation I ∈ 𝓘 such that 𝑃⟦ I ⟧ φ = true when φ ∈ χs and 𝑃⟦ I ⟧ φ = false when φ = ι.
--     -- For all terms in ι ∷ χs, find a coding into Nat that uniquely determines each term. To do this, compute the maximum functional depth of terms, D, the maximal arity of terms, A, the maximal function name, F, and the maximal variable name, V. Each term can then be coded into Fin V + (D₀ = F + F * V + F * V ^ 2 + ... + F * V ^ A) + (D₀ ...
--     -- Encode each term in a discrimination network. Each new term stored is assigned a unique id
--     Lemma1a = {!!}
--      where

--   Theorem1b : ▷ Φ → ⊨ Φ
--   Theorem1b = {!!}
-- -}
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

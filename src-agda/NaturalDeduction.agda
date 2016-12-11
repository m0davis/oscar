{-# OPTIONS --rewriting #-}
module NaturalDeduction
 where

module DelayMishMash where

  open import Level --public
    using (Level) renaming (zero to lzero; suc to lsuc)

  open import Size public

  open import Prelude.Monad renaming (Monad to RawMonad)
  --open import Category.Monad public
  --  using (RawMonad; module RawMonad)

  open import Data.Empty --public
    using (⊥; ⊥-elim)

  open import Data.List --public
    using (List; []; _∷_; map)

  open import Data.Maybe --public
    using (Maybe; just; nothing) renaming (map to fmap)

  open import Data.Product public
    using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
  --infixr 1 _,_

  open import Data.Sum --public
    using (_⊎_; [_,_]′) renaming (inj₁ to inl; inj₂ to inr)

  open import Data.Unit  --public
    using (⊤)

  open import Function --public
    using (_∘_; case_of_)

  open import Relation.Nullary --public
    using (Dec; yes; no)

  open import Relation.Binary --public
    using (Setoid; module Setoid)

  import Relation.Binary.PreorderReasoning
  module Pre = Relation.Binary.PreorderReasoning

  open import Relation.Binary.PropositionalEquality --public
    using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

  --open ≡-Reasoning renaming (begin_ to proof_) public

  open import Relation.Binary.HeterogeneousEquality --public
    using (_≅_; refl; ≡-to-≅; module ≅-Reasoning)
    renaming (sym to hsym; trans to htrans; cong to hcong;
              cong₂ to hcong₂; subst to hsubst)

  hcong₃ : {A : Set}{B : A → Set}{C : ∀ a → B a → Set}{D : ∀ a b → C a b → Set}
           (f : ∀ a b c → D a b c)
           {a a′ : A} → a ≅ a′ →
           {b : B a}{b′ : B a′} → b ≅ b′ →
           {c : C a b}{c′ : C a′ b′} → c ≅ c′ →
           f a b c ≅ f a′ b′ c′
  hcong₃ f refl refl refl = refl

  ≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
  ≅-to-≡ refl = refl

  mutual
    data Delay (i : Size) (A : Set) : Set where
      now    :  A           → Delay i A
      later  :  ∞Delay i A  → Delay i A

    record ∞Delay (i : Size) (A : Set) : Set where
      coinductive
      field
        force : {j : Size< i} → Delay j A

  open ∞Delay public

  never                  :  ∀{i A} → ∞Delay i A
  force (never {i}) {j}  =  later (never {j})

  module Bind where
    mutual
      bindDelay          :  ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
      bindDelay (now    a) f   =  f a
      bindDelay (later a∞) f   =  later (bind∞Delay a∞ f)

      bind∞Delay             :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
      force (bind∞Delay a∞ f)  =  bindDelay (force a∞) f

  _d>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
  _d>>=_ {i} = Bind.bindDelay {i}

  {-
  open import Prelude.Applicative using (Applicative)
  instance delayApplicative : ∀ {i} → Applicative (Delay i)
  Applicative.pure (delayApplicative {i}) x = now x
  Applicative._<*>_ (delayApplicative {i}) (now f) x = x d>>= (now ∘ f)
  Applicative._<*>_ (delayApplicative {i}) (later f) x = {!force f {i}!}
  {-
  Applicative._<*>_ (delayApplicative {i}) f (now x) = {!x!} -- Bind.bindDelay x (λ x₁ → {!!})
  Applicative._<*>_ (delayApplicative {i}) (now f) (later x) = {!!} -- Bind.bindDelay x (λ x₁ → {!!})
  Applicative._<*>_ (delayApplicative {i}) (later f) (later x) = {!!} -- Bind.bindDelay x (λ x₁ → {!!})
  -}
  Applicative.super (delayApplicative {i}) = {!!}
  -}
  {-
  instance delayMonad : ∀ {i} → RawMonad (Delay i)
  delayMonad {i} = record
    { {-return  =  now
    ; -}_>>=_   =  bindDelay {i}
    } where open Bind
  -}

  {-
  module _ {i : Size} where
    open module DelayMonad = RawMonad (delayMonad {i = i})
                             public -- renaming (_⊛_ to _<*>_)
  -}
  open Bind public using () renaming (bind∞Delay to _∞>>=_)

  -- Map for Delay

  dreturn : {i : Size} → {A : Set} → A → Delay i A
  dreturn {i} = Delay.now {i}

  _d<$>_ : ∀ {i A B} (f : A → B) (a : Delay i A) → Delay i B
  f d<$> a = a d>>= λ a → dreturn (f a)

  -- Map for ∞Delay

  _∞<$>_ : ∀ {i A B} (f : A → B) (∞a : ∞Delay i A) → ∞Delay i B
  f ∞<$> ∞a = ∞a ∞>>= λ a → dreturn (f a)
  -- force (f ∞<$> ∞a) = f <$> force ∞a

  -- Double bind

  _=<<2_,_ : ∀ {i A B C} → (A → B → Delay i C) → Delay i A → Delay i B → Delay i C
  f =<<2 x , y = x d>>= λ a → y d>>= λ b → f a b

  mutual
    data _∼_ {i : Size} {A : Set} : (a? b? : Delay ∞ A) → Set where
      ∼now    :  ∀ a                              →  now a     ∼ now a
      ∼later  :  ∀ {a∞ b∞} (eq : a∞ ∞∼⟨ i ⟩∼ b∞)  →  later a∞  ∼ later b∞

    _∼⟨_⟩∼_ = λ {A} a? i b? → _∼_ {i}{A} a? b?

    record _∞∼⟨_⟩∼_ {A} (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
      coinductive
      field
        ∼force : {j : Size< i} → force a∞ ∼⟨ j ⟩∼ force b∞

  _∞∼_ = λ {i} {A} a∞ b∞ → _∞∼⟨_⟩∼_ {A} a∞ i b∞

  open _∞∼⟨_⟩∼_ public

  ∼never : ∀{i A} → (never {A = A}) ∞∼⟨ i ⟩∼ never
  ∼force ∼never = ∼later ∼never

  ∼refl    :  ∀{i A} (a?  : Delay ∞ A)   →  a? ∼⟨ i ⟩∼ a?
  ∞∼refl   :  ∀{i A} (a∞  : ∞Delay ∞ A)  →  a∞ ∞∼⟨ i ⟩∼ a∞

  ∼sym     :  ∀{i A}{a?  b?  : Delay ∞ A }  →  a? ∼⟨ i ⟩∼ b?   →  b? ∼⟨ i ⟩∼ a?
  ∞∼sym    :  ∀{i A}{a∞  b∞  : ∞Delay ∞ A}  →  a∞ ∞∼⟨ i ⟩∼ b∞  →  b∞ ∞∼⟨ i ⟩∼ a∞

  ∼trans   :  ∀{i A}{a? b? c? : Delay ∞ A} →
              a? ∼⟨ i ⟩∼ b? →  b? ∼⟨ i ⟩∼ c? → a? ∼⟨ i ⟩∼ c?
  ∞∼trans  :  ∀{i A}{a∞ b∞ c∞ : ∞Delay ∞ A} →
              a∞ ∞∼⟨ i ⟩∼ b∞ →  b∞ ∞∼⟨ i ⟩∼ c∞ → a∞ ∞∼⟨ i ⟩∼ c∞

  ∼refl (now a)    = ∼now a
  ∼refl (later a∞) = ∼later (∞∼refl a∞)

  ∼force (∞∼refl a∞) = ∼refl (force a∞)

  ∼sym (∼now a)    = ∼now a
  ∼sym (∼later eq) = ∼later (∞∼sym eq)

  ∼force (∞∼sym eq) = ∼sym (∼force eq)

  ∼trans (∼now a)    (∼now .a)    = ∼now a
  ∼trans (∼later eq) (∼later eq′) = ∼later (∞∼trans eq eq′)

  ∼force (∞∼trans eq eq′) = ∼trans (∼force eq) (∼force eq′)

  -- Equality reasoning

  ∼setoid : (i : Size) (A : Set) → Setoid lzero lzero
  ∼setoid i A = record
    { Carrier       = Delay ∞ A
    ; _≈_           = _∼_ {i}
    ; isEquivalence = record
      { refl  = λ {a?} → ∼refl a?
      ; sym   = ∼sym
      ; trans = ∼trans
      }
    }

  ∞∼setoid : (i : Size) (A : Set) → Setoid lzero lzero
  ∞∼setoid i A = record
    { Carrier       = ∞Delay ∞ A
    ; _≈_           = _∞∼_ {i}
    ; isEquivalence = record
      { refl  = λ {a?} → ∞∼refl a?
      ; sym   = ∞∼sym
      ; trans = ∞∼trans
      }
    }

  module ∼-Reasoning {i : Size} {A : Set} where
    open Pre (Setoid.preorder (∼setoid i A)) public
  --    using (begin_; _∎) (_≈⟨⟩_ to _∼⟨⟩_; _≈⟨_⟩_ to _∼⟨_⟩_)
      renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∼⟨_⟩_; begin_ to proof_)

  module ∞∼-Reasoning {i : Size} {A : Set} where
    open Pre (Setoid.preorder (∞∼setoid i A)) public
  --    using (begin_; _∎) (_≈⟨⟩_ to _∼⟨⟩_; _≈⟨_⟩_ to _∼⟨_⟩_)
      renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∞∼⟨_⟩_; begin_ to proof_)

  mutual
    bind-assoc               :  ∀{i A B C} (m : Delay ∞ A)
                                {k : A → Delay ∞ B} {l : B → Delay ∞ C} →
                                ((m d>>= k) d>>= l) ∼⟨ i ⟩∼ (m d>>= λ a → (k a d>>= l))
    bind-assoc (now a)       =  ∼refl _
    bind-assoc (later a∞)    =  ∼later (∞bind-assoc a∞)

    ∞bind-assoc              :  ∀{i A B C} (a∞ : ∞Delay ∞ A)
                                {k : A → Delay ∞ B} {l : B → Delay ∞ C} →
                                ((a∞ ∞>>= k) ∞>>= l) ∞∼⟨ i ⟩∼ (a∞ ∞>>= λ a → (k a d>>= l))
    ∼force (∞bind-assoc a∞)  =  bind-assoc (force a∞)

  bind-cong-l   :  ∀{i A B}{a? b? : Delay ∞ A} →  a? ∼⟨ i ⟩∼ b? →
                   (k : A → Delay ∞ B) → (a? d>>= k) ∼⟨ i ⟩∼ (b? d>>= k)

  ∞bind-cong-l  :  ∀{i A B}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞∼⟨ i ⟩∼ b∞ →
                   (k : A → Delay ∞ B) → (a∞ ∞>>= k) ∞∼⟨ i ⟩∼ (b∞ ∞>>= k)

  bind-cong-r   :  ∀{i A B}(a? : Delay ∞ A){k l : A → Delay ∞ B} →
                   (∀ a → (k a) ∼⟨ i ⟩∼ (l a)) → (a? d>>= k) ∼⟨ i ⟩∼ (a? d>>= l)

  ∞bind-cong-r  :  ∀{i A B}(a∞ : ∞Delay ∞ A){k l : A → Delay ∞ B} →
                   (∀ a → (k a) ∼⟨ i ⟩∼ (l a)) → (a∞ ∞>>= k) ∞∼⟨ i ⟩∼ (a∞ ∞>>= l)

  bind-cong-l (∼now a)    k = ∼refl _
  bind-cong-l (∼later eq) k = ∼later (∞bind-cong-l eq k)

  ∼force (∞bind-cong-l eq k) = bind-cong-l (∼force eq) k

  bind-cong-r (now a)    h = h a
  bind-cong-r (later a∞) h = ∼later (∞bind-cong-r a∞ h)

  ∼force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h

  open import Prelude.Functor using (Functor; _<$>_)

  instance FunctorDelay : {i : Size} → Functor (Delay i)
  Functor.fmap (FunctorDelay {i}) {A} {B} f (now x) = {!!}
  Functor.fmap (FunctorDelay {i}) {A} {B} f (later x) = {!!}

  open import Prelude.Function using (_∘′_)

  map-compose     :  ∀{i A B C} (a? : Delay ∞ A) {f : A → B} {g : B → C} →
                     (g d<$> (f d<$> a?)) ∼⟨ i ⟩∼ ((g ∘ f) d<$> a?)
  map-compose a?  =  bind-assoc a?

  map-cong        :  ∀{i A B}{a? b? : Delay ∞ A} (f : A → B) →
                     a? ∼⟨ i ⟩∼ b? → (f d<$> a?) ∼⟨ i ⟩∼ (f d<$> b?)
  map-cong f eq   =  bind-cong-l eq (now ∘ f)

  data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
    now⇓    :  ∀{a}                                   → now a ⇓ a
    later⇓  :  ∀{a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a  → later a∞ ⇓ a

  _⇓   :  {A : Set} (x : Delay ∞ A) → Set
  x ⇓  =  ∃ λ a → x ⇓ a

  map⇓     :  ∀{A B}{a : A}{a? : Delay ∞ A}(f : A → B) → a? ⇓ a → (f d<$> a?) ⇓ f a

  subst∼⇓  :  ∀{A}{a? a?′ : Delay ∞ A}{a : A} → a? ⇓ a → a? ∼ a?′ → a?′ ⇓ a

  bind⇓    :  ∀{A B}(f : A → Delay ∞ B){?a : Delay ∞ A}{a : A}{b : B} →
              ?a ⇓ a → f a ⇓ b → (?a d>>= f) ⇓ b

  map⇓ f now⇓        = now⇓
  map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

  subst∼⇓ now⇓ (∼now a) = now⇓
  subst∼⇓ (later⇓ p) (∼later eq) = later⇓ (subst∼⇓ p (∼force eq))

  bind⇓ f now⇓ q = q
  bind⇓ f (later⇓ p) q = later⇓ (bind⇓ f p q)

  --infixr 6 _⇒_
  --infixl 1 _,_

module CustomPrelude where

  open import Prelude public
    renaming (_==_ to _≟_) -- TODO ask Agda to rename Eq._==_ to Eq._≟_
    hiding (force) -- needed by ∞Delay

  {-# BUILTIN REWRITE _≡_ #-}

  --{-# DISPLAY Eq._==_ _ = _≟_ #-}

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

  --open import Agda.Builtin.Size public
  open import Size public

  open import Control.Monad.State public
  open import Control.Monad.Identity public
  open import Container.Traversable public

  sequence : ∀ {a b} {A : Set a} {F : Set a → Set b} ⦃ _ : Applicative F ⦄ → List (F A) → F ⊤′
  sequence [] = pure tt
  sequence (x ∷ xs) = x *> sequence xs

  {-
  open import Tactic.Nat
  -}
  open import Tactic.Deriving.Eq public

open CustomPrelude

TruthValue = Bool

-- reification of elements of the domain
Element = Nat

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

Vector : Set → Arity → Set
Vector A = Vec A ∘ arity

record Elements : Set
 where
  constructor ⟨_⟩
  field
    {arity} : Arity
    elements : Vector Element arity

open Elements

instance EqElements : Eq Elements
Eq._==_ EqElements (⟨_⟩ {𝑎₁} εs₁) (⟨_⟩ {𝑎₂} εs₂)
 with 𝑎₁ ≟ 𝑎₂
… | no 𝑎₁≢𝑎₂ = no λ {refl → 𝑎₁≢𝑎₂ refl}
… | yes refl
 with εs₁ ≟ εs₂
… | yes refl = yes refl
… | no εs₁≢εs₂ = no λ {refl → εs₁≢εs₂ refl}

record Interpretation : Set
 where
  field
    μ⟦_⟧ : VariableName → Element
    𝑓⟦_⟧ : FunctionName → Elements → Element
    𝑃⟦_⟧ : PredicateName → Elements → TruthValue

open Interpretation

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

subst∼⇓  :  ∀{A}{a? a?′ : Delay ∞ A}{a : A} → a? ⇓ a → a? ∼ a?′ → a?′ ⇓ a
subst∼⇓ now⇓ (∼now a) = now⇓
subst∼⇓ (later⇓ p) (∼later eq) = later⇓ (subst∼⇓ p (∼force eq))

traverse⇓ : ∀{A}{B}{f? : A → Delay ∞ B}{T : Set → Set}⦃ _ : Traversable T ⦄{X : T A} → (∀ x → f? x ⇓) → ∀ (x : T A) → traverse f? x ⇓
traverse⇓ x₁ x₂ = {!!} , {!!}

app⇓ : ∀{A}{B}{f? : Delay ∞ (A → B)}{f : A → B}{x? : Delay ∞ A}{x : A} → f? ⇓ f → x? ⇓ x → (f? <*> x?) ⇓ f x
app⇓ now⇓ now⇓ = now⇓
app⇓ now⇓ (later⇓ x?) = later⇓ $ map⇓ _ x?
app⇓ (later⇓ f?) now⇓ = later⇓ $ bind⇓ _ f? now⇓
app⇓ (later⇓ ⇓f) (later⇓ ⇓x) = later⇓ $ bind⇓ _ ⇓f $ later⇓ $ bind⇓ _ ⇓x now⇓
{-
Goal: (force f∞ >>= (λ y → later (x∞ ∞>>= (λ x → now (y x))))) ⇓ f .x
-- bind⇓ : {A B : Set}
           (f₁ : A → Delay ∞ B) {?a : Delay ∞ A} {a : A} {b : B}
           → ?a ⇓ a
           → f₁ a ⇓ b
           → (?a >>= f₁) ⇓ b
-- map⇓ : {A B : Set} {a : A} {a? : Delay ∞ A}
          (f₁ : A → B)
          → a? ⇓ a
          → (a? >>= (λ x → now (f₁ x))) ⇓ f₁ a
-- app⇓ : {A B : Set} {f? : Delay ∞ (A → B)} {f = f₁ : A → B} {x? : Delay ∞ A} {x : A}
          → f? ⇓ f₁
          → x? ⇓ x
          → (f? <*> x?) ⇓ f₁ x
-- app⇓ ⇓f ⇓x later⇓ {!(app⇓ ⇓f ⇓x)!} -- (bind⇓ (later ∘ _) f? (later⇓ (app⇓ {!!} x?)))
-}
traverse-vec⇓ : ∀{A}{B}{f? : A → Delay ∞ B}{n} → (∀ x → f? x ⇓) → ∀ (x : Vec A n) → traverse f? x ⇓
traverse-vec⇓ _ [] = [] , now⇓
traverse-vec⇓ {f? = f?} f?⇓ (x ∷ xs)
 with f?⇓ x | traverse-vec⇓ f?⇓ xs
… | fx , fx⇓ | fxs , fxs⇓ = (fx ∷ fxs) , app⇓ (app⇓ {!now⇓ {Vec._∷_}!} fx⇓) fxs⇓
{-
Goal: _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ ⇓ (λ v v₁ → _f_2028 fx fxs v v₁)
_2029 := λ ..{.n} {.A} {.B} {f?} f?⇓ x xs fx fx⇓ fxs fxs⇓ →
  app⇓ (app⇓ (?4 f?⇓ x xs fx fx⇓ fxs fxs⇓) fx⇓) fxs⇓ [blocked by problem 3544]
[3544,3546] (_f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ <*> f? x <*> traverse f? xs) = ((f? x >>= (λ x₁ → now (_∷_ x₁))) <*> traverse f? xs) : Delay ∞ (Vec .B (suc .n))
[3544,3547] (_f_2028 fx fxs fx fxs) = (fx ∷ fxs) : Vec .B (suc .n)

_f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ ⇓ (λ v v₁ → _f_2028 fx fxs v v₁)

_f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ <*> f? x = (f? x >>= (λ x₁ → now (_∷_ x₁)))
Goal: _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ ⇓ (λ v v₁ → _f_2028 fx fxs v v₁)
_f_2028 fx fxs fx fxs = fx ∷ fxs
Two possibilities?
P1:
  Goal: _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ ⇓ (λ v v₁ → v ∷ v₁)
  by similar logic to P2,
  Goal: now _∷_ ⇓ (λ v v₁ → v ∷ v₁)
  Goal: now _∷_ ⇓ _∷_

P2:
  Goal: _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ ⇓ (λ v v₁ → fx ∷ fxs)
  _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ <*> f? x = (f? x >>= (λ x₁ → now (_∷_ x₁)))
  case _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ = now ...
    ... <*> f? x = bindDelay (f? x) $ now ∘ ... = f? x >>= (now ∘ ...) = (f? x >>= (λ x₁ → now (_∷_ x₁)))
    (now ∘ ...) = (λ x₁ → now (_∷_ x₁)) = now ∘ _∷_
    so ... = _∷_
    so _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ = now _∷_
    Goal: now _∷_ ⇓ (λ v v₁ → fx ∷ fxs)
  case _f?_2023 f?⇓ x xs fx fx⇓ fxs fxs⇓ = later ...
    ... <*> f? x = later ∘ bind∞Delay ... $ flip fmap (f? x) =


-}
-- (now (_∷ fxs)) <*> f? x

{-
[3536,3538] (_f?_2017 f?⇓ x xs fx fx⇓ fxs fxs⇓ <*> traverse f? xs) = ((f? x >>= (λ x₁ → now (_∷_ x₁))) <*> traverse f? xs) : Delay ∞ (Vec .B (suc .n))
[3536,3539] (_f_2022 fx fxs fxs) = (fx ∷ fxs) : Vec .B (suc .n)

_f?_2017 f?⇓ x xs fx fx⇓ fxs fxs⇓ ⇓ (λ v → _f_2022 fx fxs v)
(f? x >>= (λ x₁ → now (_∷_ x₁))) ⇓ (λ v → _f_2022 fx fxs v)
(f? x >>= (λ x₁ → now (_∷_ x₁))) ⇓ (λ v → (fx ∷ v))
(f? x >>= (λ x₁ → now (_∷_ x₁))) ⇓ fx ∷_
(f? x >>= (now ∘ _∷_)) ⇓ fx ∷_

fx⇓  : f? x ⇓ fx


_2023 := λ ..{.n} {.A} {.B} {f?} f?⇓ x xs fx fx⇓ fxs fxs⇓ →
           app⇓ (?4 f?⇓ x xs fx fx⇓ fxs fxs⇓) fxs⇓ [blocked by problem 3536]




traverse-vec⇓ {f? = f?} f?⇓ (x ∷ xs) =
  let fx , fx⇓ = f?⇓ x
      fxs , fxs⇓ = traverse-vec⇓ f?⇓ xs
  in
    fx ∷ fxs , app⇓ {f? = {!!}} {f = fx ∷_} {!!} {!!}
-}
-- app⇓ {A = Vec _ _} {B = Vec _ (suc _)} {f? = {!?!}} {f = {!!}} {x? = traverse (λ z → f? z) xs} {x = fst (traverse-vec⇓ f?⇓ xs)} {!!} fxs⇓

{-
_2022 := λ ..{.n} {.A} {.B} {f?} f?⇓ x xs → app⇓ (?4 f?⇓ x xs) (snd (traverse-vec⇓ f?⇓ xs)) [blocked by problem 3529]
[3529,3532] (_f_2018 f?⇓ x xs (fst (traverse-vec⇓ f?⇓ xs))) = (fst (f?⇓ x) ∷ fst (traverse-vec⇓ f?⇓ xs)) : Vec .B (suc .n)
[3529,3531] (_f?_2017 f?⇓ x xs <*> traverse f? xs) = ((f? x >>= (λ {.x} → now) ∘ _∷_) <*> traverse f? xs) : Delay ∞ (Vec .B (suc .n))


_f?_2017 : Delay ∞ (Vec .B .n → Vec .B (suc .n))
_f_2018 : Vec .B .n → Vec .B (suc .n)
_2022 : (_∷_ <$> f? x <*> traverse f? xs) ⇓ (fst (f?⇓ x) ∷ fst (traverse-vec⇓ f?⇓ xs))
_2023 : (_∷_ <$> f? x <*> traverse f? xs) ⇓ (fst (f?⇓ x) ∷ fst (traverse-vec⇓ f?⇓ xs))

———— Errors ————————————————————————————————————————————————
Failed to solve the following constraints:
  _2022 :=
    (λ ..{.n} {.A} {.B} {f?} f?⇓ x xs → app⇓ (?4 f?⇓ x xs) (snd (traverse-vec⇓ f?⇓ xs)))
    [blocked on problem 3529]
  [3529, 3532] _f_2018 f?⇓ x xs (fst (traverse-vec⇓ f?⇓ xs))
               = fst (f?⇓ x) ∷ fst (traverse-vec⇓ f?⇓ xs)
                 : Vec .B (suc .n)
  [3529, 3531] _f?_2017 f?⇓ x xs <*> traverse f? xs
               = (f? x >>= (λ {.x} → now) ∘ _∷_) <*> traverse f? xs
                 : Delay ∞ (Vec .B (suc .n))
-}

{-
Goal:     (
            (.f? x >>= (λ x₁ → now (_∷_ x₁)))
              <*>
            traverse .f? xs
          )
      ⇓
          (
            fst (f?⇓ x) ∷ fst (traverse-vec⇓ f?⇓ xs)
          )
-}

mutual

  τ⟦_⟧ : Interpretation → {i : Size} → Term → Delay i Element
  τ⟦ I ⟧ (variable 𝑥) = now $ μ⟦ I ⟧ 𝑥
  τ⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ∘ (⟨_⟩ {arity τs}) <$> (later $ τs⟦ I ⟧ τs)

  τs⟦_⟧ : Interpretation → {i : Size} → (τs : Terms) → ∞Delay i (Vector Element (arity τs))
  force (τs⟦ I ⟧ τs) = traverse id $ τ⟦ I ⟧ <$> terms τs

mutual

  term-τs : (I : Interpretation) → (τs : Terms) → (later $ τs⟦ I ⟧ τs) ⇓
  term-τs I ⟨ [] ⟩ = [] , later⇓ now⇓
  term-τs I ⟨ τ ∷ τs ⟩ = let t = term-τ I τ
                             ts = term-τs I ⟨ τs ⟩ in
                             (fst t ∷ fst ts) , later⇓ (let t' = snd t
                                                            ts' = snd ts in
                                                            {!
                                                            !})
{-
---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------
let .Prelude.Vec.vmap = _<$>_
    T : {i : Size} → Term → Delay i Nat
    T = τ⟦ I ⟧ in
    Ts : {i : Size} (τs : Terms) → ∞Delay i (Vec Nat (arity (arity τs)))
    Ts = τs⟦ I ⟧
    v : Nat
    v = fst (term-τ I τ)
    *vs : {n : Nat} → (τs : Vec Term n) → Vec Nat n
    *vs = λ (τs : Vec Term _) → fst (term-τs I ⟨ τs ⟩)
in
Goal: ((τ⟦ I ⟧ τ >>= (λ x → now (_∷_ x))) <*>
       traverse (λ x → x) (.Prelude.Vec.vmap τ⟦ I ⟧ τs))
      ⇓ (fst (term-τ I τ) ∷ fst (term-τs I ⟨ τs ⟩))
————————————————————————————————————————————————————————————
ts' : later (τs⟦ I ⟧ ⟨ τs ⟩) ⇓ fst (term-τs I ⟨ τs ⟩)
t'  : τ⟦ I ⟧ τ ⇓ fst (term-τ I τ)
ts  : Σ (Vec Nat .n) (_⇓_ (later (τs⟦ I ⟧ ⟨ τs ⟩)))
t   : Σ Nat (_⇓_ (τ⟦ I ⟧ τ))
τs  : Vec Term .n
τ   : Term
I   : Interpretation
.n  : Nat

Want: (T τ >>= (λ x → now (_∷_ x))) ⇓ _∷_ v          map⇓ _∷_ t'
Goal: ((T τ >>= (λ x → now (_∷_ x))) <*>
       traverse (λ x → x) (T <$> τs))
      ⇓ (v ∷ *vs τs))
————————————————————————————————————————————————————————————
ts' : later (Ts ⟨ τs ⟩) ⇓ *vs τs)
t'  : T τ ⇓ v
ts  : Σ (Vec Nat .n) (_⇓_ (later (Ts ⟨ τs ⟩)))
t   : Σ Nat (_⇓_ (T τ))
τs  : Vec Term .n
τ   : Term
I   : Interpretation
.n  : Nat

-}


  term-τ : (I : Interpretation) → (τ : Term) → τ⟦ I ⟧ τ ⇓
  term-τ I (variable 𝑥) = μ⟦ I ⟧ 𝑥 , now⇓
  term-τ I (function 𝑓 τs) = {!!}



{-
mutual
  τ⟦_⟧ : ∀ {i} → Interpretation → Term → Delay i Element
  τ⟦ I ⟧ (variable 𝑥) = {!!} -- now $ μ⟦ I ⟧ 𝑥
  τ⟦ I ⟧ (function 𝑓 τs) = {!!} -- later {!!} -- now $ {!𝑓⟦ I ⟧ 𝑓 !} -- later $ record { force = {!!} } -- {!(τ⟦_⟧ =<<2 dreturn I , dreturn (terms τs))!} d>>= λ ts → now $ 𝑓⟦ I ⟧ 𝑓 ⟨ ts ⟩

  τs⟦_⟧ : ∀ {i} → Interpretation → Terms → ∞Delay i Elements
  τs⟦ I ⟧ ⟨ [] ⟩ = {!!}
  τs⟦ I ⟧ ⟨ τ ∷ τs ⟩ = {!!} -- τ⟦ I ⟧ τ d>>= (λ x → later (record { force = {!τs⟦ I ⟧ ⟨ τs ⟩!} })) -- τ⟦ I ⟧ d<$> τs
-}
{-
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
-}

{-
termVariable-inj : ∀ {i 𝑥₁ 𝑥₂} → Term.variable {i} 𝑥₁ ≡ variable {i} 𝑥₂ → 𝑥₁ ≡ 𝑥₂
termVariable-inj refl = refl

termFunction-inj₁ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → 𝑓₁ ≡ 𝑓₂
termFunction-inj₁ refl = refl

termFunction-inj₂ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → τ₁s ≡ τ₂s
termFunction-inj₂ refl = refl
-}

{-
mutual

  instance EqTerm : ∀ {i} → Eq (Term {i})
  Eq._==_ EqTerm (variable _) (variable _) = decEq₁ termVariable-inj $ _≟_ _ _
  Eq._==_ (EqTerm {i}) (function 𝑓₁ {j₁} τ₁s) (function 𝑓₂ {j₂} τ₂s) = {!decEq₂ {!termFunction-inj₁!} {!!} (𝑓₁ ≟ 𝑓₂) {!_≟_ {{i}} τ₁s τ₂s!}!} -- decEq₂ termFunction-inj₁ termFunction-inj₂ (_≟_ _ _) (_≟_ _ _)
  Eq._==_ EqTerm (variable _) (function _ _) = no λ ()
  Eq._==_ EqTerm (function _ _) (variable _) = no λ ()

  instance EqTerms : ∀ {i} {j : Size< i} → Eq (Terms {j})
  Eq._==_ EqTerms x y = {!!}
-}
mutual

  instance EqTerm : Eq Term
  EqTerm = {!!}

  instance EqTerms : Eq Terms
  EqTerms = {!!}

data Formula : Set
 where
  atomic : PredicateName → Terms → Formula
  logical : Formula →
            Formula →
            Formula
  quantified : VariableName → Formula → Formula

--instance EqFormula : deriveEqType Formula
--unquoteDef EqFormula = deriveEqDef EqFormula (quote Formula)

instance EqFormula : Eq Formula
Eq._==_ EqFormula = {!!}

record HasNegation (A : Set) : Set
 where
  field
    ~ : A → A

open HasNegation ⦃ … ⦄

{-# DISPLAY HasNegation.~ _ = ~ #-}

record BeFormula (A : Set) : Set
 where
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

-- τ'⟦_⟧ : ∀ {i} → Interpretation → Term → Delay i Element
-- τ'⟦ I ⟧ (variable 𝑥) = now $ μ⟦ I ⟧ 𝑥
-- τ'⟦ I ⟧ (function 𝑓 τs) = {!(τ'⟦ I ⟧ <$> terms τs)!} d>>= λ ts → now $ 𝑓⟦ I ⟧ 𝑓 ⟨ ts ⟩
--
-- τ⟦_⟧ : Interpretation → Term → Element
-- τ⟦ I ⟧ (variable 𝑥) = μ⟦ I ⟧ 𝑥
-- τ⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ⟨ τ⟦ I ⟧ <$> terms τs ⟩

{-
τ⟦_⟧ : Interpretation → {i : Size} → Term {i} → Element
τ⟦ I ⟧ (variable 𝑥) = μ⟦ I ⟧ 𝑥
τ⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ⟨ τ⟦ I ⟧ <$> terms τs ⟩
-}

-- ∀[_♭_] : VariableName → Formula → Formula
-- ∀[_♭_] = quantified
--
-- {-# DISPLAY quantified = ∀[_♭_] #-}
--
-- _∧_ : Formula → Formula → Formula
-- φ₁ ∧ φ₂ = ~ φ₁ ⊗ ~ φ₂
--
-- _∨_ : Formula → Formula → Formula
-- φ₁ ∨ φ₂ = ~ (φ₁ ⊗ φ₂)
--
-- _⊃_ : Formula → Formula → Formula
-- φ₁ ⊃ φ₂ = ~ φ₁ ∨ φ₂
--
-- _⟷_ : Formula → Formula → Formula
-- φ₁ ⟷ φ₂ = (φ₁ ⊗ (φ₂ ⊗ φ₂)) ⊗ ((φ₁ ⊗ φ₁) ⊗ φ₂) -- TODO check that this is logically equivalent to the more verbose, (φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)
--
-- record _≞_/_ (𝓘 : Interpretation) (I : Interpretation) (𝑥 : VariableName) : Set
--  where
--   field
--     μEquality : {𝑥′ : VariableName} → 𝑥′ ≢ 𝑥 → μ⟦ 𝓘 ⟧ 𝑥 ≡ μ⟦ I ⟧ 𝑥′
--     𝑓Equality : (𝑓 : FunctionName) (μs : Elements) → 𝑓⟦ 𝓘 ⟧ 𝑓 μs ≡ 𝑓⟦ I ⟧ 𝑓 μs
--     𝑃Equality : (𝑃 : PredicateName) → (μs : Elements) → 𝑃⟦ 𝓘 ⟧ 𝑃 μs ≡ 𝑃⟦ I ⟧ 𝑃 μs
--
-- _⟪_⟫_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
--         A → (A → B → C) → B → C
-- x ⟪ f ⟫ y = f x y
-- {-
-- infixr 9 _∘₂′_
-- _∘₂′_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
--          (C → D) → (A → B → C) → (A → B → D)
-- _∘₂′_ = _∘′_ ∘ _∘′_
-- {-# INLINE _∘₂′_ #-}
--
-- infixr 9 _∘₂′_
-- _∘₂′_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
--          (C → D) → (A → B → C) → (A → B → D)
-- _∘₂′_ = _∘′_ ∘ _∘′_
-- {-# INLINE _∘₂′_ #-}
-- -}
-- {-
-- infixr 9 _∘₂_
-- _∘₂_ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → B x → C x
--          (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
--          ∀ x → C x (g x)
-- _∘₂_ = _∘′_ ∘ _∘′_
-- {-# INLINE _∘₂′_ #-}
-- -}
--
-- instance
--
--   EqLiteralFormula : Eq LiteralFormula
--   Eq._==_ EqLiteralFormula φ₁ φ₂ = {!!}
--
-- instance
--
--   BeFormulaFormula : BeFormula Formula
--   BeFormula.formula BeFormulaFormula = id
--
--   BeFormulaLiteralFormula : BeFormula LiteralFormula
--   BeFormula.formula BeFormulaLiteralFormula = formula
--
-- instance
--
--   HasNegationLiteralFormula : HasNegation LiteralFormula
--   HasNegation.~ HasNegationLiteralFormula ⟨ atomic 𝑃 τs ⟩ = ⟨ logical 𝑃 τs ⟩
--   HasNegation.~ HasNegationLiteralFormula ⟨ logical 𝑃 τs ⟩ = ⟨ atomic 𝑃 τs ⟩
--
--   HasNegationSequent : {A : Set} ⦃ _ : HasNegation A ⦄ ⦃ _ : BeFormula A ⦄ → HasNegation $ Sequent A
--   HasNegation.~ HasNegationSequent ( φᵗ ╱ φˢs ) = ~ φᵗ ╱ φˢs
--
-- instance
--
--   HasSatisfactionList : {A : Set} ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction $ List A
--   HasSatisfaction._⊨_ HasSatisfactionList I [] = ⊤
--   HasSatisfaction._⊨_ HasSatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs
--
--   HasSatisfactionBeFormula : {A : Set} → ⦃ _ : BeFormula A ⦄ → HasSatisfaction A
--   HasSatisfaction._⊨_ (HasSatisfactionBeFormula ⦃ beFormula ⦄) = λ I φ → I ⊨φ formula beFormula φ
--    where
--     _⊨φ_ : Interpretation → Formula → Set
--     I ⊨φ (atomic 𝑃 τs) = 𝑃⟦ I ⟧ 𝑃 ⟨ τ⟦ I ⟧ <$> terms τs ⟩ ≡ true
--     I ⊨φ (logical φ₁ φ₂) = ¬ I ⊨φ φ₁ × ¬ I ⊨φ φ₂
--     I ⊨φ (quantified 𝑥 φ) = (𝓘 : Interpretation) → 𝓘 ≞ I / 𝑥 → 𝓘 ⊨φ φ
--     {-# DISPLAY _⊨φ_ = _⊨_ #-}
--
--   HasSatisfactionSequent : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSatisfaction $ Sequent A
--   HasSatisfaction._⊨_ HasSatisfactionSequent I (φᵗ ╱ φˢs) = I ⊨ φˢs → I ⊨ φᵗ
--
-- instance
--   postulate
--     HasDecidableSatisfactionFormula : HasDecidableSatisfaction Formula
--
-- instance
--
--   HasValidationBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation A
--   HasValidation.⊨_ HasValidationBeFormula φ = (I : Interpretation) → I ⊨ φ
--
--   HasValidationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation $ Sequent A
--   HasValidation.⊨_ HasValidationSequent Φ = (I : Interpretation) → I ⊨ Φ
--
--   HasValidationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation $ Problem A
--   HasValidation.⊨_ HasValidationProblem (χs ¶ ι) = (I : Interpretation) → I ⊨ χs → I ⊨ ι
--
-- instance
--
--   HasSubstantiveDischargeBeFormulaBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge A A
--   HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeBeFormulaBeFormula ⦃ ⟨ beFormula ⟩ ⦄) = _≡_ on beFormula -- _≡_ on (formula beFormula) -- _≡_
--
--   HasSubstantiveDischargeListBeFormulaBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List A) A
--   HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListBeFormulaBeFormula ⦃ ⟨ beFormula ⟩ ⦄) +s - = beFormula - ∈ (beFormula <$> +s) -- flip _∈_
--
--   HasSubstantiveDischargeListFormulaListFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List A) (List A)
--   HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListFormulaListFormula ⦃ ⟨ beFormula ⟩ ⦄) = flip $ _⊆_ on fmap beFormula -- flip _⊆_
--
--   HasSubstantiveDischargeSequentSequent : ∀ {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (Sequent A) (Sequent A)
--   HasSubstantiveDischarge._≽_ HasSubstantiveDischargeSequentSequent (+ᵗ ╱ +ᵖs) (-ᵗ ╱ -ᵖs) = +ᵗ ≽ -ᵗ × +ᵖs ≽ -ᵖs
--
--   HasSubstantiveDischargeListSequentSequent : ∀ {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List $ Sequent A) (Sequent A)
--   HasSubstantiveDischarge._≽_ HasSubstantiveDischargeListSequentSequent χs ι = ∃ λ c → (c ∈ χs) × c ≽ ι
--
-- instance
--
--   HasVacuousDischargeList : {A : Set} ⦃ _ : HasSubstantiveDischarge (List A) A ⦄ ⦃ _ : HasNegation A ⦄ → HasVacuousDischarge (List A)
--   HasVacuousDischarge.◁_ (HasVacuousDischargeList {A}) xs = ∃ λ (x : A) → xs ≽ x × xs ≽ ~ x
--
--   HasVacuousDischargeSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasNegation A ⦄ → HasVacuousDischarge (Sequent A)
--   HasVacuousDischarge.◁_ HasVacuousDischargeSequent (_ ╱ φˢs) = ∃ λ s → (s ∈ φˢs) × (φˢs ≽ s) × (φˢs ≽ ~ s)
--
-- instance
--
--   HasSalvationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasVacuousDischarge $ List A ⦄ → HasSalvation $ Sequent A
--   HasSalvation.▷_ HasSalvationSequent (φᵗ ╱ φᵖs) = ◁ φᵖs ⊎ φᵖs ≽ φᵗ
--
--   HasSalvationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasVacuousDischarge ∘ List $ Sequent A ⦄ → HasSalvation $ Problem A
--   HasSalvation.▷_ HasSalvationProblem (χs ¶ ι) = ◁ χs ⊎ χs ≽ ι
--
-- instance
--
--   HasDecidableSalvationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasSalvation $ Sequent A ⦄ → HasDecidableSalvation $ Sequent A
--   HasDecidableSalvationSequent = {!!}
--
--   HasDecidableSalvationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasVacuousDischarge ∘ List $ Sequent A ⦄ → HasDecidableSalvation $ Problem A
--   HasDecidableSalvationProblem = {!!}
--
-- data TermCode : Set
--  where
--   variable : VariableName → TermCode
--   function : FunctionName → Arity → TermCode
--
-- termCode-function-inj₁ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → 𝑓₁ ≡ 𝑓₂
-- termCode-function-inj₁ refl = refl
--
-- termCode-function-inj₂ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → arity₁ ≡ arity₂
-- termCode-function-inj₂ refl = refl
--
-- instance
--   EqTermCode : Eq TermCode
--   Eq._==_ EqTermCode (variable 𝑥₁) (variable 𝑥₂) with 𝑥₁ ≟ 𝑥₂
--   … | yes 𝑥₁≡𝑥₂ rewrite 𝑥₁≡𝑥₂ = yes refl
--   … | no 𝑥₁≢𝑥₂ = no (λ { refl → 𝑥₁≢𝑥₂ refl})
--   Eq._==_ EqTermCode (variable x) (function x₁ x₂) = no (λ ())
--   Eq._==_ EqTermCode (function x x₁) (variable x₂) = no (λ ())
--   Eq._==_ EqTermCode (function 𝑓₁ 𝑎₁) (function 𝑓₂ 𝑎₂) = decEq₂ termCode-function-inj₁ termCode-function-inj₂ (𝑓₁ ≟ 𝑓₂) (𝑎₁ ≟ 𝑎₂)
--
-- mutual
--   encodeTerm : Term → List TermCode
--   encodeTerm (variable 𝑥) = variable 𝑥 ∷ []
--   encodeTerm (function 𝑓 (⟨_⟩ {arity} τs)) = function 𝑓 arity ∷ encodeTerms τs
--
--   encodeTerms : {arity : Arity} → Vector Term arity → List TermCode
--   encodeTerms [] = []
--   encodeTerms (τ ∷ τs) = encodeTerm τ ++ encodeTerms τs
--
-- mutual
--
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
--
--   decodeFunction : Nat → FunctionName → Arity → StateT (List TermCode) Maybe Term
--   decodeFunction n 𝑓 arity = do
--     τs ← decodeTerms n arity -|
--     return (function 𝑓 ⟨ τs ⟩)
--
--   decodeTerms : Nat → (arity : Arity) → StateT (List TermCode) Maybe (Vector Term arity)
--   decodeTerms n ⟨ zero ⟩ = return []
--   decodeTerms n ⟨ suc arity ⟩ = do
--     τ ← decodeTerm n -|
--     τs ← decodeTerms n ⟨ arity ⟩ -|
--     return (τ ∷ τs)
--
-- .decode-is-inverse-of-encode : ∀ τ → runStateT (decodeTerm ∘ length $ encodeTerm τ) (encodeTerm τ) ≡ (just $ τ , [])
-- decode-is-inverse-of-encode (variable 𝑥) = refl
-- decode-is-inverse-of-encode (function 𝑓 ⟨ [] ⟩) = {!!}
-- decode-is-inverse-of-encode (function 𝑓 ⟨ variable 𝑥 ∷ τs ⟩) = {!!}
-- decode-is-inverse-of-encode (function 𝑓 ⟨ function 𝑓' τs' ∷ τs ⟩) = {!!}
--
-- module ExampleEncodeDecode where
--   example-Term : Term
--   example-Term =
--     (function ⟨ 2 ⟩
--               ⟨ variable ⟨ 0 ⟩ ∷
--                 function ⟨ 3 ⟩ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ∷
--                 variable ⟨ 5 ⟩ ∷ [] ⟩
--     )
--
--   -- function ⟨ 2 ⟩ ⟨ 3 ⟩ ∷ variable ⟨ 0 ⟩ ∷ function ⟨ 3 ⟩ ⟨ 1 ⟩ ∷ variable ⟨ 2 ⟩ ∷ variable ⟨ 5 ⟩ ∷ []
--   example-TermCodes : List TermCode
--   example-TermCodes = encodeTerm example-Term
--
--   example-TermDecode : Maybe (Term × List TermCode)
--   example-TermDecode = runStateT (decodeTerm (length example-TermCodes)) example-TermCodes
--
--   example-verified : example-TermDecode ≡ (just $ example-Term , [])
--   example-verified = refl
--
--   example-bad : runStateT (decodeTerm 2) (function ⟨ 2 ⟩ ⟨ 2 ⟩ ∷ variable ⟨ 0 ⟩ ∷ []) ≡ nothing
--   example-bad = refl
--
-- record TermNode : Set
--  where
--   inductive
--   field
--     children : List (TermCode × TermNode)
--     number : Nat
--
-- open TermNode
--
-- _child∈_ : TermCode → TermNode → Set
-- _child∈_ 𝔠 𝔫 = 𝔠 ∈ (fst <$> children 𝔫)
--
-- _child∉_ : TermCode → TermNode → Set
-- 𝔠 child∉ 𝔫 = ¬ (𝔠 child∈ 𝔫)
--
-- _child∈?_ : (𝔠 : TermCode) → (𝔫 : TermNode) → Dec $ 𝔠 child∈ 𝔫
-- c child∈? record { children = cs } = c ∈? (fst <$> cs)
--
-- getChild : {𝔠 : TermCode} → (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode
-- getChild {𝔠} (record { children = [] ; number = number₁ }) ()
-- getChild {._} (record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }) (here .(map fst children₁)) = snd₁
-- getChild {𝔠} (𝔫@record { children = x ∷ children₁ ; number = number₁ }) (there .(fst x) x₁) = getChild record 𝔫 { children = children₁ } x₁
--
-- addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∉ 𝔫 → TermNode → TermNode
-- addChild {𝔠} 𝔫 𝔠∉𝔫 𝔫' =
--   record 𝔫 { children = (𝔠 , 𝔫') ∷ children 𝔫 }
--
-- setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode → TermNode
-- setChild {𝔠} record { children = [] ; number = number₁ } () 𝔫'
-- setChild 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (here .(map fst children₁)) 𝔫' =
--   record 𝔫 { children = ((fst₁ , 𝔫') ∷ children₁) }
-- setChild {𝔠} 𝔫@record { children = (x ∷ children₁) ; number = number₁ } (there .(fst x) 𝔠∈𝔫) 𝔫' =
--   record 𝔫 { children = (x ∷ children (setChild (record 𝔫 { children = children₁ }) 𝔠∈𝔫 𝔫')) }
--
-- setGet-ok : ∀ {𝔠} 𝔫 → (𝔠∈𝔫 : 𝔠 child∈ 𝔫) → setChild 𝔫 𝔠∈𝔫 (getChild 𝔫 𝔠∈𝔫) ≡ 𝔫
-- setGet-ok record { children = [] ; number = number₁ } ()
-- setGet-ok record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (here .(map fst children₁)) = refl
-- setGet-ok record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (there ._ 𝔠∈𝔫) rewrite setGet-ok (record { children = children₁ ; number = number₁ }) 𝔠∈𝔫 = refl
--
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
--
-- storeTermCodes[] : (𝔫 : TermNode) (𝔑 : Nat) → (runIdentity $ runStateT (storeTermCodes [] 𝔑) 𝔫) ≡ (𝔑 , 𝔫)
-- storeTermCodes[] 𝔫 𝔑 = refl
--
-- --{-# REWRITE storeTermCodes[] #-}
--
-- storeTermCodes' : List TermCode → StateT Nat (StateT TermNode Identity) ⊤
-- storeTermCodes' 𝔠s =
--   𝔑 ← get -|
--   tn ← lift get -|
--   (let 𝔑' , tn' = runIdentity $ runStateT (storeTermCodes 𝔠s 𝔑) tn in
--    put 𝔑' ~| lift (put tn') ~| return tt)
--
-- mutual
--
--   storeTerm : Term → StateT Nat (StateT TermNode Identity) ⊤
--   storeTerm τ@(variable _) = storeTermCodes' (encodeTerm τ)
--   storeTerm τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTerms τs
--
--   storeTerms : Terms → StateT Nat (StateT TermNode Identity) ⊤
--   storeTerms ⟨ [] ⟩ = return tt
--   storeTerms ⟨ τ ∷ τs ⟩ = storeTerm τ ~| storeTerms ⟨ τs ⟩ ~| return tt
--
-- module ExampleStoreTerm where
--   example-Term₁ : Term
--   example-Term₁ =
--     (function ⟨ 2 ⟩
--               ⟨ variable ⟨ 0 ⟩
--               ∷ function ⟨ 3 ⟩
--                          ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩
--               ∷ variable ⟨ 5 ⟩
--               ∷ []
--               ⟩
--     )
--
--   example-Term₂ : Term
--   example-Term₂ =
--     (function ⟨ 2 ⟩
--               ⟨ variable ⟨ 0 ⟩
--               ∷ variable ⟨ 2 ⟩
--               ∷ function ⟨ 3 ⟩
--                          ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩
--               ∷ variable ⟨ 5 ⟩
--               ∷ []
--               ⟩
--     )
--
--   topNode : TermNode
--   topNode = record { children = [] ; number = 0 }
--
--   example-storeTerm : (⊤ × Nat) × TermNode
--   example-storeTerm = {!runIdentity $ runStateT (runStateT (storeTerm example-Term₁ >> storeTerm example-Term₂) 0) topNode!}
--
-- NodeStateT = StateT TermNode
-- TopNodeState = StateT Nat (NodeStateT Identity)
--
-- storeLiteralFormulaTerms : LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤
-- storeLiteralFormulaTerms ⟨ atomic 𝑃 τs ⟩ = storeTerms τs
-- storeLiteralFormulaTerms ⟨ logical 𝑃 τs ⟩ = storeTerms τs
--
-- storeSequentLiteralFormulaTerms : Sequent LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤′
-- storeSequentLiteralFormulaTerms (φᵗ ╱ φˢs) = sequence $ storeLiteralFormulaTerms <$> (φᵗ ∷ φˢs)
--
-- record FindTermNode (A : Set) : Set
--  where
--   field
--     findTermNode : A → TermNode → Maybe TermNode
--
-- open FindTermNode ⦃ … ⦄
--
-- instance
--   FindTermNodeTermCode : FindTermNode TermCode
--   FindTermNode.findTermNode FindTermNodeTermCode termCode record { children = [] ; number = number₁ } = nothing
--   FindTermNode.findTermNode FindTermNodeTermCode termCode 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } = ifYes fst₁ ≟ termCode then just snd₁ else findTermNode termCode record 𝔫 { children = children₁ }
--
--   FindTermNodeTermCodes : FindTermNode (List TermCode)
--   FindTermNode.findTermNode FindTermNodeTermCodes [] node = just node
--   FindTermNode.findTermNode FindTermNodeTermCodes (x ∷ termCodes) node = join $ findTermNode termCodes <$> findTermNode x node
--
--   FindTermNodeTerm : FindTermNode Term
--   FindTermNode.findTermNode FindTermNodeTerm term node = findTermNode (encodeTerm term) node
--
-- -- This is starting to get difficult. We need Agda to know that the Term is encoded in the TermNode. Then we can drop the Maybe
-- getInterpretationOfTerm : Term → TermNode → Maybe Element
-- getInterpretationOfTerm τ node = number <$> findTermNode (encodeTerm τ) node
--
-- FindTermNodeTermCode-ok : ∀ {𝔠 𝔫} → 𝔠 child∈ 𝔫 → IsJust (findTermNode 𝔠 𝔫)
-- FindTermNodeTermCode-ok {𝔠} {record { children = [] ; number = number₁ }} ()
-- --FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ = case (fst₁ ≟_) 𝔠 , graphAt {B = λ 𝑐 → Dec (fst₁ ≡ 𝑐)} (fst₁ ≟_) 𝔠 of λ { (yes x , snd₂) → {!!} ; (no x , snd₂) → {!!}} --λ { ((yes ===) , (inspect s1)) → {!!} ; ((no =n=) , inspect s2) → {!!} }
-- --FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ = case fst₁ ≟ 𝔠 of λ { (yes refl) → {!!} ; (no x) → {!!}}
-- FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ with fst₁ ≟ 𝔠
-- FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ | yes eq2 = tt
-- FindTermNodeTermCode-ok {.fst₁} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} (here .(map fst children₁)) | no neq = ⊥-elim (neq refl)
-- FindTermNodeTermCode-ok {𝔠} {𝔫@record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} (there .fst₁ x₁) | no neq = FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} x₁
--
-- Justified : ∀ {a} {A : Set a} → (m : Maybe A) → IsJust m → ∃ λ x → m ≡ just x
-- Justified nothing ()
-- Justified (just x) x₁ = _ , refl
--
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
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | here fdsdfs = ⊥-elim (neq refl)
-- --storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | there dfdsf fdsdfs with FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs | graphAt (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }}) fdsdfs
-- --… | frfrrf | ingraph tttttt = transport _ (snd $ Justified (FindTermNode.findTermNode FindTermNodeTermCode (variable 𝑥) (record { children = children₁ ; number = number₁ })) (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs)) _
-- storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | there dfdsf fdsdfs rewrite (snd $ Justified (FindTermNode.findTermNode FindTermNodeTermCode (variable 𝑥) (record { children = children₁ ; number = number₁ })) (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs)) = tt
-- storeTerm-ok (function 𝑥 𝑎) 𝔫 𝔑 with (function 𝑥 (arity 𝑎)) child∈? 𝔫
-- storeTerm-ok (function 𝑥 ⟨ [] ⟩) 𝔫 𝔑 | no x with Eq._==_ EqFunctionName ⟨ name 𝑥 ⟩ ⟨ name 𝑥 ⟩
-- storeTerm-ok (function 𝑥 ⟨ [] ⟩) 𝔫 𝔑 | no x | (yes refl) = tt
-- … | no neq = ⊥-elim (neq refl)
-- --storeTerm-ok τ₀@(function 𝑓 ⟨ τ₁ ∷ τ₂s ⟩) 𝔫 𝔑 | no 𝔠₁∉𝔫 = {!τ₁!}
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥 ∷ [] ⟩) 𝔫 𝔑        | no 𝔠₁∉𝔫 with variable 𝑥 child∈? 𝔫
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥 ∷ [] ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) with 𝑓₀ ≟ 𝑓₀
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥 ∷ [] ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl with TermCode.variable 𝑥 ≟ variable 𝑥
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥 ∷ [] ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl | yes eq = tt
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥 ∷ [] ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl | no neq = ⊥-elim (neq refl)
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥 ∷ [] ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | no neq = ⊥-elim (neq refl)
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ [] ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) with 𝑓₀ ≟ 𝑓₀
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ [] ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl with TermCode.variable 𝑥₁ ≟ variable 𝑥₁
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ [] ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl | yes 𝔠₁≡𝔠₁ = tt
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ [] ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl | no 𝔠₁≢𝔠₁ = ⊥-elim (𝔠₁≢𝔠₁ refl)
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ [] ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | no 𝑓₀≢𝑓₀ = ⊥-elim (𝑓₀≢𝑓₀ refl) -- rewrite setGet-ok 𝔫 𝔠₁∈𝔫
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 with variable 𝑥₁ child∈? 𝔫
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 | yes 𝔠₁∈𝔫 = {!!}
-- storeTerm-ok (function 𝑓₀ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 | no 𝔠₁∉𝔫 = {!!}
-- storeTerm-ok τ₀@(function 𝑓₀ ⟨ function 𝑓₁ τ₁s ∷ τ₂s ⟩) 𝔫 𝔑 | no 𝔠₁∉𝔫 = {!!}
-- storeTerm-ok (function 𝑥 x₁) 𝔫 𝔑 | yes x = {!!}
--
-- mutual
--
--   storeTermVerifiably' : (τ : Term) → StateT Nat (StateT (Σ TermNode λ n → IsJust (findTermNode τ n)) Identity) ⊤
--   storeTermVerifiably' (variable x) = {!!}
--   storeTermVerifiably' (function x x₁) = {!!}
--
--   storeTermVerifiably : Term → StateT Nat (StateT TermNode Identity) ⊤
--   storeTermVerifiably τ@(variable _) = storeTermCodes' (encodeTerm τ)
--   storeTermVerifiably τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTermsVerifiably τs
--
--   storeTermsVerifiably : Terms → StateT Nat (StateT TermNode Identity) ⊤
--   storeTermsVerifiably ⟨ [] ⟩ = return tt
--   storeTermsVerifiably ⟨ τ ∷ τs ⟩ = storeTermVerifiably τ ~| storeTermsVerifiably ⟨ τs ⟩ ~| return tt
--
-- Theorem1 : {Φ : Problem LiteralFormula} → ⊨ Φ ↔ ▷ Φ
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
--
--   Theorem1b : ▷ Φ → ⊨ Φ
--   Theorem1b = {!!}
--
-- negationEliminationRule : (I : Interpretation) (φ : Formula) → I ⊨ ~ (~ φ) → I ⊨ φ
-- negationEliminationRule I φ (¬[I⊭φ×I⊭φ] , _) with I ⊨? φ
-- … | yes I⊨φ = I⊨φ
-- … | no I⊭φ = ⊥-elim $ ¬[I⊭φ×I⊭φ] $ I⊭φ , I⊭φ
--
-- -- justifieds simplification and ... more?
-- simplificationRule₁ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ Formula.logical φ₁ φ₂ → I ⊨ Formula.logical φ₁ φ₁
-- simplificationRule₁ I φ₁ φ₂ x = (fst x) , (fst x)
--
-- simplificationRule₂ : (I : Interpretation) (φ₁ φ₂ : Formula) → I ⊨ Formula.logical φ₁ φ₂ → I ⊨ Formula.logical φ₂ φ₂
-- simplificationRule₂ I φ₁ φ₂ x = snd x , snd x
--
-- -- logical (logical (logical p p) q) (logical (logical p p) q)
-- conditionalizationRule : (I : Interpretation) (p q : Formula) → I ⊨ q → I ⊨ (p ⊃ q ╱ (p ∷ []) )
-- conditionalizationRule I p q ⊨q (_ , _) = let prf = λ { (_ , ⊭q) → ⊭q ⊨q} in prf , prf
-- --let ⊨p = {!-⊨p p (here [])!} in (λ { (x , ~q) → ~q ⊨q}) , (λ { (x , y) → y ⊨q})
--
-- modusPonens : (I : Interpretation) (p q : Formula) → I ⊨ p → I ⊨ (p ⊃ q) → I ⊨ q
-- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) with I ⊨? q
-- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | yes x = x
-- modusPonens I p q P (~[~p&~p&~q] , ~[~p&~p&~q]²) | no x = ⊥-elim (~[~p&~p&~q] ((λ { (x₁ , y) → y P}) , (λ x₁ → x x₁)))
--
-- -- -- -- -- -- data SkolemFormula {ι : Size} (α : Alphabet) : Set where
-- -- -- -- -- --   atomic : Predication α → SkolemFormula α
-- -- -- -- -- --   logical : {ι¹ : Size< ι} → SkolemFormula {ι¹} α → {ι² : Size< ι} → SkolemFormula {ι²} α → SkolemFormula {ι} α
--
-- -- -- -- -- -- record Alphabet₊ᵥ (α : Alphabet) : Set where
-- -- -- -- -- --   constructor α₊ᵥ⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- --     .one-variable-is-added : (number ∘ variables $ alphabet) ≡ suc (number ∘ variables $ α)
-- -- -- -- -- --     .there-are-no-functions-of-maximal-arity : number (functions alphabet) zero ≡ zero
-- -- -- -- -- --     .shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → number (functions alphabet) (suc ytira₁) ≡ number (functions α) ytira₀
-- -- -- -- -- -- open Alphabet₊ᵥ
--
-- -- -- -- -- -- record Alphabet₊ₛ (α : Alphabet) : Set where
-- -- -- -- -- --   constructor α₊ₛ⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- open Alphabet₊ₛ
--
-- -- -- -- -- -- {-
-- -- -- -- -- --   toSkolemFormula
-- -- -- -- -- --   ∀x(F x v₀ v₁) ⟿ F v₀ v₁ v₂
-- -- -- -- -- --   ∃x(F x v₀ v₁) ⟿ F (s₀͍₂ v₀ v₁) v₀ v₁
-- -- -- -- -- --   ∀x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F v₀ (s₀͍₂ v₁ v₂) v₂
-- -- -- -- -- --   ∃x(F x (s₀͍₂ v₀ v₁) v₁) ⟿ F (s₀͍₂ v₀ v₁) (s₁͍₂ v₁ v₂) v₂
-- -- -- -- -- --   F v₀ ⊗ G v₀ ⟿ F v₀ ⊗ G v₀
-- -- -- -- -- --   ∀x(F x v₀ v₁) ⊗ ∀x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₂ v₃ ⊗ G v₁ (s₀͍₂ v₀ v₃) v₃
--
-- -- -- -- -- --   ∀x(F x v₀ v₁) ⊗ ∃x(G x (s₀͍₂ x v₁) v₁) ⟿ F v₀ v₁ v₂ ⊗ G (s₀͍₁ v₂) (s₁͍₂ (s₀͍₂ v₂) v₂) v₂
--
-- -- -- -- -- --   Φ₀ = ∃x(G x (s₀͍₂ x v₁) v₁) has alphabet of 2 variables, skolem functions: 0, 0, 1
-- -- -- -- -- --   this is existential {α₊ₛ} Φ₁, where
-- -- -- -- -- --     Φ₁ = G (s₀͍₂ v₀ v₁) (s₁͍₂ (s₀͍₂ v₀ v₁)) v₁
-- -- -- -- -- --     α₊ₛ = ⟨ 2 , 0 ∷ 0 ∷ 2 ∷ [] ⟩
--
-- -- -- -- -- --   maybe Φ₋₁ = ∀y∃x(G x (s₀͍₂ x v₀) v₀)
-- -- -- -- -- --    and  Φ₋₂ = ∀z∀y∃x(G x (s₀͍₂ x z) z), finally having no free variables, but nevertheless having skolem functions! these are user-defined functions, so this notion of Alphabet is somehow wrong. we have also left out constants (i.e. user-defined skolem-functions of arity 0)
--
-- -- -- -- -- --   Instead, take the alphabet as defining
-- -- -- -- -- --     a stack of free variables
-- -- -- -- -- --     a matrix (triangle?) of skolem functions
--
-- -- -- -- -- --   Let's try to reverse Φ₁ from a Skolem to a 1st-order formula. Is there a unique way to do it?
-- -- -- -- -- --   Φ₀' = ∀x(G (s₀͍₂ x v₀) (s₁͍₂ (s₀͍₂ x v₀)) v₀
--
-- -- -- -- -- --   Nope!
--
--
-- -- -- -- -- --   toSkolemFormula of
--
--
--
-- -- -- -- -- -- -}
--
-- -- -- -- -- -- -- toSkolemFormula (logical Φ₁ Φ₂) ⟿
-- -- -- -- -- -- --   let α' , φ₁ = toSkolemFormula Φ₁
-- -- -- -- -- -- --       Φ₂' = transcodeToAugmentedAlphabet Φ₂ α'
-- -- -- -- -- -- --       α'' , φ₂' = toSkolemFormula Φ₂'
-- -- -- -- -- -- --       φ₁' = transcodeToAugmentedAlphabet φ₁ α''
--
-- -- -- -- -- -- {-
-- -- -- -- -- -- given Δv = #varibles α' - #variables α
-- -- -- -- -- -- for every variable v in α, v in Φ, v stays the same in Φ'
-- -- -- -- -- -- for the added variable v⁺ in α₊ - α, v⁺ in Φ, v⁺ ⟿ v⁺ + Δv in transcode (universal {α₊} Φ)
-- -- -- -- -- -- α'₊ = α' + 1 variable
-- -- -- -- -- -- -}
--
-- -- -- -- -- -- -- record AddVariable (A : Alphabet → Set) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     addVariableToAlphabet : {α : Alphabet} → A α → {α₊ : Alphabet} → Alphabet₊ᵥ α₊ → A α₊
--
-- -- -- -- -- -- -- instance
-- -- -- -- -- -- --   AddVariableFirstOrderFormula : AddVariable FirstOrderFormula
-- -- -- -- -- -- --   AddVariableFirstOrderFormula = {!!}
--
-- -- -- -- -- -- -- #variables = number ∘ variables
--
-- -- -- -- -- -- -- #functions_ofArity_ : Alphabet → Nat → Nat
-- -- -- -- -- -- -- #functions α⟨ V⟨ #variables ⟩ , S⟨ #functions ⟩ ⟩ ofArity arity = if′ lessNat arity (suc #variables) then #functions (natToFin arity) else 0
--
-- -- -- -- -- -- -- record _⊇_ (α' α : Alphabet) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     at-least-as-many-variables : #variables α' ≥ #variables α
-- -- -- -- -- -- --     at-least-as-many-functions : ∀ {arity} → arity < #variables α → #functions α' ofArity arity ≥ #functions α ofArity arity
--
-- -- -- -- -- -- -- record AddAlphabet (α-top α-bottom : Alphabet) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     alphabet : Alphabet
--
-- -- -- -- -- -- -- record Transcodeable (A : Alphabet → Set) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     transcode : {α' α : Alphabet} → ⦃ _ : α' ⊇ α ⦄ → A α → A α'
--
-- -- -- -- -- -- -- open Transcodeable ⦃ … ⦄
--
-- -- -- -- -- -- -- record TransferAlphabet {α' α : Alphabet} (α'⊇α : α' ⊇ α) (α₊ : Alphabet₊ᵥ α) (Φ : FirstOrderFormula (alphabet α₊)) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- --     firstOrderFormula : FirstOrderFormula alphabet
--
--
-- -- -- -- -- -- -- instance
-- -- -- -- -- -- --   TranscodeablePredication : Transcodeable Predication
-- -- -- -- -- -- --   TranscodeablePredication = {!!}
--
-- -- -- -- -- -- --   TranscodeableAlphabet+Variable : Transcodeable Alphabet₊ᵥ
-- -- -- -- -- -- --   TranscodeableAlphabet+Variable = {!!}
--
-- -- -- -- -- -- --   TranscodeableSkolemFormula : Transcodeable SkolemFormula
-- -- -- -- -- -- --   TranscodeableSkolemFormula = {!!}
--
-- -- -- -- -- -- --   TranscodeableFirstOrderFormula : Transcodeable FirstOrderFormula
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (atomic p) = atomic (transcode p)
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (logical Φ₁ Φ₂) = logical (transcode Φ₁) (transcode Φ₂)
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula {α'} {α} ⦃ α'⊇α ⦄ (universal {α₊} Φ) = {!!} -- universal {_} {_} {transcode α₊} (transcode Φ)
--
-- -- -- -- -- -- --   Transcodeable.transcode TranscodeableFirstOrderFormula (existential Φ) = {!!}
--
-- -- -- -- -- -- -- --(α' α : Alphabet) (α'⊇α : α' ⊇ α) (α₊ : Alphabet+Variable α) (Φ : FirstOrderFormula (alphabet α₊)) → Σ _ λ (α''' : Alphabet) → FirstOrderFormula α'''
--
-- -- -- -- -- -- -- --FirstOrderFormula (alphabet α₊)
-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -}
--
-- -- -- -- -- -- -- -- --transcodeIntoAugmentedAlphabet :
--
--
--
-- -- -- -- -- -- -- -- --toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)
--
-- -- -- -- -- -- -- -- --record IsEquivalentFormulas {α₀ : Alphabet} (φ₀ : SkolemFormula α₀) {α₁ : Alphabet} (Φ₁ : FirstOrderFormula α₁) : Set where
-- -- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- -- --    .atomicCase : {p : Predication α₀} → φ₀ ≡ atomic p → Φ₁ ≡ atomic p
--
--
--
--
-- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- record Alphabet+Alphabet (α₀ α₁ α₂ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     alphabet :
--
-- -- -- -- -- -- -- -- -- -- ∀xφ₁(x) ⊗ φ₂ ⟿ ∀x(φ₁ ⊗ φ₂)
--
-- -- -- -- -- -- -- -- -- -- hasQuantifiers : FirstOrderFormula α → Bool
--
-- -- -- -- -- -- -- -- -- --record Skolemization {α : Alphabet} (φ : FirstOrderFormula α) : Set where
-- -- -- -- -- -- -- -- -- --  field
-- -- -- -- -- -- -- -- -- --    alphabet : Alphabet
-- -- -- -- -- -- -- -- -- --    skolemization : SkolemFormula alphabet
--
-- -- -- -- -- -- -- -- -- record _IsAugmentationOf_ (α₁ α₀ : Alphabet) : Set where
--
-- -- -- -- -- -- -- -- -- record AugmentedAlphabet (α : Alphabet) : Set where
-- -- -- -- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- --     alphabet : Alphabet
-- -- -- -- -- -- -- -- --     ..laws : alphabet ≡ α
-- -- -- -- -- -- -- -- -- open AugmentedAlphabet
--
-- -- -- -- -- -- -- -- -- trivialAugmentation : (α : Alphabet) → AugmentedAlphabet α
-- -- -- -- -- -- -- -- -- trivialAugmentation = {!!}
--
-- -- -- -- -- -- -- -- -- record DisjointRelativeUnion {α : Alphabet} (α¹ α² : AugmentedAlphabet α) : Set where
-- -- -- -- -- -- -- -- --   constructor ⟨_⟩
-- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- --     augmentation : AugmentedAlphabet α
-- -- -- -- -- -- -- -- --     .laws : {!!}
-- -- -- -- -- -- -- -- -- open DisjointRelativeUnion
--
-- -- -- -- -- -- -- -- -- disjointRelativeUnion : {α : Alphabet} → (α¹ α² : AugmentedAlphabet α) → DisjointRelativeUnion α¹ α²
-- -- -- -- -- -- -- -- -- disjointRelativeUnion = {!!}
--
-- -- -- -- -- -- -- -- -- -- inAugmentedAlphabet : {α : Alphabet} → (α¹ : AugmentedAlphabet α) → SkolemFormula α → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- -- -- -- inAugmentedAlphabet = {!!}
--
-- -- -- -- -- -- -- -- -- -- toSkolemFormula : {α : Alphabet} → FirstOrderFormula α → Σ _ λ (α¹ : AugmentedAlphabet α) → SkolemFormula (alphabet α¹)
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (atomic 𝑃) = trivialAugmentation α₀ , atomic 𝑃
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) with toSkolemFormula φ₁ | toSkolemFormula φ₂
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (logical φ₁ φ₂) | α¹ , Φ₁ | α² , Φ₂ = augmentation (disjointRelativeUnion α¹ α²) , logical {!inAugmentedAlphabet (augmentation (disjointRelativeUnion α¹ α²)) Φ₁!} {!Φ₂!}
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (universal x) = {!!}
-- -- -- -- -- -- -- -- -- -- toSkolemFormula {α₀} (existential x) = {!!}
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}
--
-- -- -- -- -- -- -- -- -- -- -- -- -- --VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- --FunctionArity = Fin ∘ suc ∘ size
-- -- -- -- -- -- -- -- -- -- -- -- -- --FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- --     |v| : Nat -- number of variables
-- -- -- -- -- -- -- -- -- -- -- -- -- --     |f| : Fin (suc |v|) → Nat -- number of functions of each arity, |v| through 0
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- open Alphabet
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- VariableName = Fin ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FunctionArity = Fin ∘ suc ∘ |v|
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FunctionName = λ alphabet ytira → Fin (|f| alphabet ytira)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   variable : VariableName alphabet → Term alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {arity : FunctionArity alphabet} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              FunctionName alphabet (natToFin (|v| alphabet) - arity) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∀ {j : Size< i} → Vec (Term {j} alphabet) (finToNat arity) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Term {i} alphabet
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PredicateArity = Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PredicateName = Nat
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a zeroth-order formula? (i.e. no quantifiers)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data NQFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → NQFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → NQFormula {j} alphabet → {k : Size< i} → NQFormula {k} alphabet → NQFormula {i} alphabet
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentedByVariable (alphabet₀ alphabet₁ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     one-variable-is-added : |v| alphabet₁ ≡ suc (|v| alphabet₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     function-domain-is-zero-at-new-variable : |f| alphabet₁ zero ≡ 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     shifted-function-matches : ∀ {ytira₀ ytira₁} → finToNat ytira₁ ≡ finToNat ytira₀ → |f| alphabet₁ (suc ytira₁) ≡ |f| alphabet₀ ytira₀
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record AugmentVariables (alphabet₀ : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     alphabet₁ : Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     augmentation : AugmentedByVariable alphabet₀ alphabet₁
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open AugmentVariables
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : (alphabet : Alphabet) → AugmentVariables alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables ⟨ |v| , |f| ⟩ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   { alphabet₁ = ⟨ suc |v| , (λ { zero → zero ; (suc ytira) → |f| ytira}) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ; augmentation =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     { one-variable-is-added = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; function-domain-is-zero-at-new-variable = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ; shifted-function-matches = cong |f| ∘ finToNat-inj } }
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- |f|₀ = |f|₀ + 1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions ⟨ |v| , |f| ⟩ = ⟨ |v| , (λ { zero → suc (|f| zero) ; (suc ytira) → |f| (suc ytira) }) ⟩
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data QFormula {i : Size} (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   atomic : PredicateName → ∀ {arity} → Vec (Term alphabet) arity → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   logical : {j : Size< i} → QFormula {j} alphabet → {k : Size< i} → QFormula {k} alphabet → QFormula {i} alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   universal : QFormula (alphabet₁ (augmentVariables alphabet)) → QFormula alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   existential : QFormula (augmentFunctions alphabet) → QFormula alphabet
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Assignment (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     μ : VariableName alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑓 : ∀ {arity} → FunctionName alphabet arity → Vec Domain (finToNat arity) → Domain
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm : ∀ {i alphabet} → Assignment alphabet → Term {i} alphabet → Domain
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm ⟨ μ , _ ⟩ (variable x) = μ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateTerm 𝑎@(⟨ μ , 𝑓 ⟩) (function f x) = 𝑓 f (evaluateTerm 𝑎 <$> x)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Interpretation (alphabet : Alphabet) : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constructor ⟨_,_⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Assignment
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑎 : Assignment alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝑃 : PredicateName → ∀ {arity} → Vec Domain arity → Bool
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula : ∀ {i alphabet} → Interpretation alphabet → NQFormula {i} alphabet → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula ⟨ 𝑎 , 𝑃 ⟩ (atomic name terms) = 𝑃 name $ evaluateTerm 𝑎 <$> terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evaluateNQFormula I (logical formula₁ formula₂) = not (evaluateNQFormula I formula₁) && not (evaluateNQFormula I formula₂)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula : ∀ {alphabet₀} → QFormula alphabet₀ → Σ _ λ alphabet₁ → NQFormula alphabet₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (atomic name terms) = alphabet₀ , atomic name terms
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (logical formula₁ formula₂) with toNQFormula formula₁ | toNQFormula formula₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- … | alphabet₁ , nqFormula₁ | alphabet₂ , nqFormula₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (universal formula) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toNQFormula {alphabet₀} (existential formula) = {!!}
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record IsADisjointUnionOfNQFormulas
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {alphabet₁ alphabet₂ alphabet₁₊₂ : Alphabet}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁ : NQFormula alphabet₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₂ : NQFormula alphabet₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (formula₁₊₂ : NQFormula alphabet₁₊₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     alphabet-size : |v| alphabet₁₊₂ ≡ |v| alphabet₁ + |v| alphabet₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --|f| alphabet₁₊₂ ytira
--
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ----record AlphabetSummed  (alphabet₀ alphabet₁ : Alphabet)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets : Alphabet → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --addAlphabets ⟨ |v|₁ , |f|₁ ⟩ ⟨ |v|₂ , |f|₂ ⟩ = ⟨ (|v|₁ + |v|₂) , (λ x → if′ finToNat x ≤? |v|₁ && finToNat x ≤? |v|₂ then {!!} else {!!}) ⟩
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sup : ∀ {alphabet₁} → Formula alphabet₁ → ∀ {alphabet₂} → Formula alphabet₂ → Σ _ λ alphabet₁₊₂ → Formula alphabet₁₊₂ × Formula alphabet₁₊₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sup {⟨ |v|₁ , |a|₁ , |f|₁ ⟩} φ₁ {⟨ |v|₂ , |a|₂ , |f|₂ ⟩} φ₂ = {!!}
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf : ∀ {alphabet} → Formula alphabet → Σ _ λ alphabet+ → Formula₀ alphabet+
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pnf = {!!}
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --universal (P 0) = ∀ x → P x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (∀ x ∃ y (P x y)) ∨ (∀ x ∃ y (P x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- P x₀ (s₀͍₁ x₀) ∨ P x₁ (s₁͍₁ x₁)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
--
--
--
--
--
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| : (arity : Arity) → Vec ℕ (suc |a|) → Vec ℕ (++arity (max arity |a|))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   extended|f| = {!!}
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a variable to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables : Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentVariables = {!!}
--
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
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ⊗ b ≡ False a and False b
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- now, we can define
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ¬a = a ⊗ a ≡ False a and False a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∨ b = ¬(a ⊗ b) ≡ False (False a and False b) and False (False a and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a ∧ b = ¬(¬a ∨ ¬b) = ¬(¬(¬a ⊗ ¬b)) = ¬a ⊗ ¬b = False (False a and False a) and False (False b and False b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- a → b = ¬a ∨ b = (a ⊗ a) ∨ b = ¬((a ⊗ a) ⊗ b) = ((a ⊗ a) ⊗ b) ⊗ ((a ⊗ a) ⊗ b)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- conversion to prenex
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∀xF ⊗ G ⟿ ∃x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∃xF ⊗ G ⟿ ∀x(F ⊗ wk(G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∀xG ⟿ ∃x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F ⊗ ∃xG ⟿ ∀x(wk(F) ⊗ G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ========================
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (a ⊗ ∀xB) ⊗ c ⟿ ∃x(wk(a) ⊗ B) ⊗ c ⟿ ∀x((wk(a) ⊗ B) ⊗ wk(c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
--
--
--
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
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- = case arity <? |a| of λ { false → {!!} ; true → {!!} }
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- add a function of a given arity to the alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions : Arity → Alphabet → Alphabet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- augmentFunctions arity ⟨ |v| , |a| , |f| ⟩ = ⟨ |v| , max arity |a| , augmentF arity |f| ⟩
--
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Alphabet : Set where
--
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data DomainSignifier : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   free : Nat → DomainSignifier
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartiallyAppliedFunction : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   constant : PartiallyAppliedFunction 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : ∀ {n} → PartiallyAppliedFunction 0 → PartiallyAppliedFunction (suc n)
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Term = PartiallyAppliedFunction 0
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PartialyAppliedPredicate : Nat → Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   statement : PartialyAppliedPredicate 0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   partial : ∀
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Language : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
--
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Name = String
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Function : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     name : Name
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     number-of-arguments : Nat
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Vec
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Function : Set where
--
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Term : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   function : Function →
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data Sentence : Set where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   predication : Name →
--
-- -- -- -- -- -- {-
--
-- -- -- -- -- -- record Variables : Set where
-- -- -- -- -- --   constructor V⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     number : Nat
-- -- -- -- -- -- open Variables
--
-- -- -- -- -- -- record Functions (υ : Variables) : Set where
-- -- -- -- -- --   constructor S⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     number : Fin (suc (number υ)) → Nat
-- -- -- -- -- -- open Functions
--
-- -- -- -- -- -- record Alphabet : Set where
-- -- -- -- -- --   constructor α⟨_,_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     variables : Variables
-- -- -- -- -- --     functions : Functions variables
-- -- -- -- -- -- open Alphabet
--
-- -- -- -- -- -- record Variable (α : Alphabet) : Set where
-- -- -- -- -- --   constructor v⟨_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     name : Fin (number (variables α))
-- -- -- -- -- -- open Variable
--
-- -- -- -- -- -- record Function (α : Alphabet) : Set where
-- -- -- -- -- --   constructor s⟨_,_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     arity : Fin ∘ suc ∘ number ∘ variables $ α
-- -- -- -- -- --     name : Fin $ number (functions α) arity
-- -- -- -- -- -- open Function
--
-- -- -- -- -- -- data Term (𝑽 : Nat) : Set where
-- -- -- -- -- --   variable : Fin 𝑽 → Term 𝑽
-- -- -- -- -- --   function : (𝑓 : Function α) → {ι₋₁ : Size< ι₀} → Vec (Term {ι₋₁} α) (finToNat (arity 𝑓)) →
-- -- -- -- -- --              Term {ι₀} α
--
-- -- -- -- -- -- record Predication (alphabet : Alphabet) : Set where
-- -- -- -- -- --   constructor P⟨_,_,_⟩
-- -- -- -- -- --   field
-- -- -- -- -- --     name : Nat
-- -- -- -- -- --     arity : Nat
-- -- -- -- -- --     terms : Vec (Term alphabet) arity
-- -- -- -- -- -- open Predication
-- -- -- -- -- -- -}
--
--
-- -- module NotUsed where
--
-- --   -- thought it might be easier to use this
-- --   module UsingContainerList where
--
-- --     record TermNode : Set
-- --      where
-- --       inductive
-- --       field
-- --         children : List (TermCode × TermNode)
-- --         number : Nat
--
-- --     open TermNode
--
-- --     _child∈_ : TermCode → TermNode → Set
-- --     _child∈_ 𝔠 𝔫 = Any ((𝔠 ≡_) ∘ fst) (children 𝔫)
--
-- --   -- this still has a lambda problem, albeit weirder
-- --   module RememberChildren where
--
-- --     record TermNode : Set
-- --      where
-- --       inductive
-- --       field
-- --         tests : List TermCode
-- --         children : ∀ {𝔠} → 𝔠 ∈ tests → TermNode
-- --         number : Nat
-- --     open TermNode
--
-- --     addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 ∉ tests 𝔫 → TermNode → TermNode
-- --     addChild {𝔠} 𝔫 𝔠∉tests𝔫 𝔫' =
-- --       record 𝔫
-- --       { tests = 𝔠 ∷ tests 𝔫
-- --       ; children = λ
-- --         { (here _) → 𝔫'
-- --         ; (there _ 𝔠'∈tests) → children 𝔫 𝔠'∈tests }}
--
-- --     setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 ∈ tests 𝔫 → TermNode → TermNode
-- --     setChild {𝔠} 𝔫 𝔠∈tests𝔫 𝔫' =
-- --       record 𝔫
-- --       { children = λ {𝔠'} 𝔠'∈tests𝔫' → ifYes 𝔠' ≟ 𝔠 then 𝔫' else children 𝔫 𝔠'∈tests𝔫' }
--
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
--
-- --     topNode : TermNode
-- --     topNode = record { tests = [] ; children = λ () ; number = 0 }
--
-- --     example-store : TermNode
-- --     example-store = snd ∘ runIdentity $ runStateT (storeTermCodes example-TermCodes 0) topNode
--
-- --     foo : TermNode × TermNode
-- --     foo =
-- --       {!example-store!} ,
-- --       {!snd ∘ runIdentity $ runStateT (storeTermCodes example-TermCodes 10) example-store!}
--
-- --   -- using a lambda for the children results in extra unnecessary structure when adding to an existing node; perhaps using an explicit mapping? or use another field to state what codes are present in the mapping?
-- --   module NoParents where
--
-- --     mutual
--
-- --       record TermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           children : TermCode → Maybe TermNode -- Map TermCode TermNode
-- --           self : TermCode
-- --           number : Nat
--
-- --       record TopTermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           children : TermCode → Maybe TermNode
--
-- --     open TermNode
-- --     open TopTermNode
--
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
--
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
--
-- --     initialTopNode : TopTermNode
-- --     initialTopNode = record { children = const nothing }
--
-- --     example-store : TopTermNode
-- --     example-store = snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 0) initialTopNode
--
-- --     foo : TopTermNode × TopTermNode
-- --     foo =
-- --       {!example-store!} ,
-- --       {!snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 10) example-store!}
--
-- --   -- it's tricky to keep the parents up to date when the children change (viz adolescence)
-- --   module FirstTryWithParent where
-- --     mutual
--
-- --       record TermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           parent : TopTermNode ⊎ TermNode
-- --           self : TermCode
-- --           children : TermCode → Maybe TermNode -- Map TermCode TermNode
-- --           number : Nat
--
-- --       record TopTermNode : Set
-- --        where
-- --         inductive
-- --         field
-- --           children : TermCode → Maybe TermNode
--
-- --     open TermNode
-- --     open TopTermNode
--
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
--
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
--
-- --     initialTopNode : TopTermNode
-- --     initialTopNode = record { children = const nothing }
--
-- --     example-store : TopTermNode
-- --     example-store = snd ∘ runIdentity $ runStateT (storeTermCodesAtTop example-TermCodes 0) initialTopNode
--
-- --     foo : TopTermNode
-- --     foo = {!example-store!}

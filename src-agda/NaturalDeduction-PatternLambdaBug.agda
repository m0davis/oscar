{-# OPTIONS --rewriting #-}
--{-# OPTIONS --show-implicit #-}
module NaturalDeduction-PatternLambdaBug
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
{-
  instance FunctorDelay : {i : Size} → Functor (Delay i)
  Functor.fmap (FunctorDelay {i}) {A} {B} f (now x) = {!!}
  Functor.fmap (FunctorDelay {i}) {A} {B} f (later x) = {!!}
-}
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

termVariable-inj : ∀ {𝑥₁ 𝑥₂} → Term.variable 𝑥₁ ≡ variable 𝑥₂ → 𝑥₁ ≡ 𝑥₂
termVariable-inj refl = refl

termFunction-inj₁ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → 𝑓₁ ≡ 𝑓₂
termFunction-inj₁ refl = refl

termFunction-inj₂ : ∀ {𝑓₁ 𝑓₂ τ₁s τ₂s} → Term.function 𝑓₁ τ₁s ≡ function 𝑓₂ τ₂s → τ₁s ≡ τ₂s
termFunction-inj₂ refl = refl


foo : ∀ a → (ts1 ts2 : Vec Term (arity a)) → (τ₁≡τ₂ : Terms.⟨ ts1 ⟩ ≡ (⟨_⟩ {a} ts2)) → _≡_ {lzero} {Vec Term (arity a)} ts1 ts2
foo a ts1 .ts1 refl = refl

mutual

  EqTerm⇑ : ∀ {i} → (x y : Term) → Delay i ∘ Dec $ x ≡ y
  EqTerm⇑ (variable _) (variable _) = now (decEq₁ termVariable-inj $ _≟_ _ _)
  EqTerm⇑ (function 𝑓₁ τ₁s) (function 𝑓₂ τ₂s) = EqTerms⇑ τ₁s τ₂s >>= λ τ₁s≟τ₂s → now $ decEq₂ termFunction-inj₁ termFunction-inj₂ (𝑓₁ ≟ 𝑓₂) τ₁s≟τ₂s
  EqTerm⇑ (variable _) (function _ _) = now $ no λ ()
  EqTerm⇑ (function _ _) (variable _) = now $ no λ ()

  EqTerms⇑ : ∀ {i} → (x y : Terms) → Delay i ∘ Dec $ x ≡ y
  EqTerms⇑ (⟨_⟩ {𝑎₁} τ₁s) (⟨_⟩ {𝑎₂} τ₂s)
   with 𝑎₁ ≟ 𝑎₂
  … | no 𝑎₁≢𝑎₂ = now $ no λ {τ₁≡τ₂ → 𝑎₁≢𝑎₂ (cong arity τ₁≡τ₂)}
  … | yes refl = EqVecTerm⇑ τ₁s τ₂s >>= λ { (yes refl) → now $ yes refl ; (no τ₁s≢τ₂s) → now $ no (λ ⟨τ₁s⟩≡⟨τ₂s⟩ → τ₁s≢τ₂s (foo ⟨ arity 𝑎₁ ⟩ τ₁s τ₂s ⟨τ₁s⟩≡⟨τ₂s⟩)) }

  EqVecTerm⇑ : ∀ {i} {n} → (x y : Vec Term n) → Delay i ∘ Dec $ x ≡ y
  EqVecTerm⇑ [] [] = now (yes refl)
  EqVecTerm⇑ (τ₁ ∷ τ₁s) (τ₂ ∷ τ₂s) =
    EqTerm⇑ τ₁ τ₂ >>= λ
    { (yes refl) → EqVecTerm⇑ τ₁s τ₂s >>= λ
                   { (yes refl) → now $ yes refl
                   ; (no τ₁s≢τ₂s) → now $ no λ τ₁₁s≡τ₁₂s → τ₁s≢τ₂s $ vcons-inj-tail τ₁₁s≡τ₁₂s }
    ; (no τ₁≢τ₂) → now $ no λ τ₁₁s≡τ₂₂s → τ₁≢τ₂ $ vcons-inj-head τ₁₁s≡τ₂₂s }

EqVecTerm⇓ : ∀ {n} → (x y : Vec Term n) → EqVecTerm⇑ x y ⇓
EqVecTerm⇓ [] [] = _ , now⇓
EqVecTerm⇓ (variable 𝑥₁ ∷ τ₁s) (variable 𝑥₂ ∷ τ₂s)
 with 𝑥₁ ≟ 𝑥₂
… | yes refl with EqVecTerm⇓ τ₁s τ₂s
EqVecTerm⇓ (variable 𝑥₁ ∷ τ₁s) (variable .𝑥₁ ∷ .τ₁s) | yes refl | (yes refl , snd₁) = _ , snd₁ >>=⇓ now⇓
EqVecTerm⇓ (variable 𝑥₁ ∷ τ₁s) (variable .𝑥₁ ∷ τ₂s) | yes refl | (no x , snd₁) = _ , snd₁ >>=⇓ now⇓
EqVecTerm⇓ (variable 𝑥₁ ∷ τ₁s) (variable 𝑥₂ ∷ τ₂s) | no 𝑥₁≢𝑥₂ = _ , now⇓
EqVecTerm⇓ (variable x ∷ τ₁s) (function x₁ x₂ ∷ τ₂s) = _ , now⇓
EqVecTerm⇓ (function x x₁ ∷ τ₁s) (variable x₂ ∷ τ₂s) = _ , now⇓
EqVecTerm⇓ (function 𝑓₁ (⟨_⟩ {𝑎₁} τ₁s) ∷ τ₁₂s) (function 𝑓₂ (⟨_⟩ {𝑎₂} τ₂s) ∷ τ₂₂s)
 with 𝑎₁ ≟ 𝑎₂ | 𝑓₁ ≟ 𝑓₂
… | no 𝑎₁≢𝑎₂ | no 𝑓₁≢𝑓₂  = _ , now⇓
… | no 𝑎₁≢𝑎₂ | yes refl  = _ , now⇓
… | yes refl | no 𝑓₁≢𝑓₂
 with EqVecTerm⇓ τ₁s τ₂s
… | (no τ₁s≢τ₂s , τ⇓)  = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
… | (yes refl , τ⇓)    = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
EqVecTerm⇓ (function 𝑓₁ (⟨_⟩ {𝑎₁} τ₁s) ∷ τ₁₂s) (function 𝑓₂ (⟨_⟩ {𝑎₂} τ₂s) ∷ τ₂₂s) | yes refl | yes refl
 with EqVecTerm⇓ τ₁s τ₂s | EqVecTerm⇓ τ₁₂s τ₂₂s
… | (no τ₁s≢τ₂s , τ⇓) | (no τ₁₂s≢τ₂₂s , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
… | (yes refl , τ⇓)   | (no τ₁₂s≢τ₂₂s , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ (τs⇓ >>=⇓ now⇓)
… | (no τ₁s≢τ₂s , τ⇓) | (yes refl , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ now⇓
… | (yes refl , τ⇓)   | (yes refl , τs⇓) = _ , τ⇓ >>=⇓ now⇓ >>=⇓ now⇓ >>=⇓ (τs⇓ >>=⇓ now⇓)

EqTerms⇓ : (x y : Terms) → EqTerms⇑ x y ⇓
EqTerms⇓ (⟨_⟩ {𝑎₁} τ₁s) (⟨_⟩ {𝑎₂} τ₂s)
 with 𝑎₁ ≟ 𝑎₂
… | no 𝑎₁≢𝑎₂ = _ , now⇓
… | yes refl
 with EqVecTerm⇓ τ₁s τ₂s
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

mutual

  τ⇑⟦_⟧ : Interpretation → {i : Size} → Term → Delay i Element
  τ⇑⟦ I ⟧ (variable 𝑥) = now $ μ⟦ I ⟧ 𝑥
  τ⇑⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ∘ ⟨_⟩ <$> τs⇑⟦ I ⟧ τs

  τs⇑⟦_⟧ : Interpretation → {i : Size} → (τs : Terms) → Delay i (Vector Element (arity τs))
  τs⇑⟦ I ⟧ ⟨ [] ⟩ = now []
  τs⇑⟦ I ⟧ ⟨ τ ∷ τs ⟩ = τ⇑⟦ I ⟧ τ >>= (λ t → τs⇑⟦ I ⟧ ⟨ τs ⟩ >>= λ ts → now (t ∷ ts))

τs⇓⟦_⟧ : (I : Interpretation) → (τs : Terms) → τs⇑⟦ I ⟧ τs ⇓
τs⇓⟦ I ⟧ ⟨ [] ⟩ = _ , now⇓
τs⇓⟦ I ⟧ ⟨ variable 𝑥 ∷ τs ⟩ = _ , τs⇓⟦ I ⟧ ⟨ τs ⟩ ⇓>>=⇓ now⇓
τs⇓⟦ I ⟧ ⟨ function 𝑓₁ τs₁ ∷ τs₂ ⟩ =
  _ , τs⇓⟦ I ⟧ τs₁ ⇓>>=⇓ now⇓ >>=⇓ (τs⇓⟦ I ⟧ ⟨ τs₂ ⟩ ⇓>>=⇓ now⇓)

τ⇓⟦_⟧ : (I : Interpretation) → (τ : Term) → τ⇑⟦ I ⟧ τ ⇓
τ⇓⟦ I ⟧ (variable 𝑥) = _ , now⇓
τ⇓⟦ I ⟧ (function 𝑓 τs) = _ , τs⇓⟦ I ⟧ τs ⇓>>=⇓ now⇓

τ⟦_⟧ : (I : Interpretation) → {i : Size} → (τ : Term) → Element
τ⟦ I ⟧ τ = fst (τ⇓⟦ I ⟧ τ)

data Formula : Set
 where
  atomic : PredicateName → Terms → Formula
  logical : Formula →
            Formula →
            Formula
  quantified : VariableName → Formula → Formula

formulaAtomic-inj₁ : ∀ {𝑃₁ τs₁ 𝑃₂ τs₂} → Formula.atomic 𝑃₁ τs₁ ≡ atomic 𝑃₂ τs₂ → 𝑃₁ ≡ 𝑃₂
formulaAtomic-inj₁ refl = refl

formulaAtomic-inj₂ : ∀ {𝑃₁ τs₁ 𝑃₂ τs₂} → Formula.atomic 𝑃₁ τs₁ ≡ atomic 𝑃₂ τs₂ → τs₁ ≡ τs₂
formulaAtomic-inj₂ refl = refl

formulaLogical-inj₁ : ∀ {φ₁₁ φ₁₂ φ₂₁ φ₂₂} → Formula.logical φ₁₁ φ₁₂ ≡ logical φ₂₁ φ₂₂ → φ₁₁ ≡ φ₂₁
formulaLogical-inj₁ refl = refl

formulaLogical-inj₂ : ∀ {φ₁₁ φ₁₂ φ₂₁ φ₂₂} → Formula.logical φ₁₁ φ₁₂ ≡ logical φ₂₁ φ₂₂ → φ₁₂ ≡ φ₂₂
formulaLogical-inj₂ refl = refl

formulaQuantified-inj₁ : ∀ {𝑥₁ φ₁ 𝑥₂ φ₂} → Formula.quantified 𝑥₁ φ₁ ≡ quantified 𝑥₂ φ₂ → 𝑥₁ ≡ 𝑥₂
formulaQuantified-inj₁ refl = refl

formulaQuantified-inj₂ : ∀ {𝑥₁ φ₁ 𝑥₂ φ₂} → Formula.quantified 𝑥₁ φ₁ ≡ quantified 𝑥₂ φ₂ → φ₁ ≡ φ₂
formulaQuantified-inj₂ refl = refl

instance EqFormula : Eq Formula
Eq._==_ EqFormula (atomic 𝑃₁ τs₁) (atomic 𝑃₂ τs₂)  = decEq₂ formulaAtomic-inj₁ formulaAtomic-inj₂ (𝑃₁ ≟ 𝑃₂) (τs₁ ≟ τs₂)
Eq._==_ EqFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂)  = decEq₂ formulaLogical-inj₁ formulaLogical-inj₂ (φ₁₁ ≟ φ₂₁) (φ₁₂ ≟ φ₂₂)
Eq._==_ EqFormula (quantified 𝑥₁ φ₁) (quantified 𝑥₂ φ₂)  = decEq₂ formulaQuantified-inj₁ formulaQuantified-inj₂ (𝑥₁ ≟ 𝑥₂) (φ₁ ≟ φ₂)
Eq._==_ EqFormula (atomic _ _) (logical _ _) = no λ ()
Eq._==_ EqFormula (atomic _ _) (quantified _ _) = no λ ()
Eq._==_ EqFormula (logical _ _) (atomic _ _)  = no λ ()
Eq._==_ EqFormula (logical _ _) (quantified _ _)  = no λ ()
Eq._==_ EqFormula (quantified _ _) (atomic _ _)  = no λ ()
Eq._==_ EqFormula (quantified _ _) (logical _ _)  = no λ ()

record HasNegation (A : Set) : Set
 where
  field
    ~ : A → A

open HasNegation ⦃ … ⦄

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

record HasDecidableSatisfaction (A : Set) ⦃ _ : HasSatisfaction A ⦄ : Set₁
 where
  field
    _⊨?_ : (I : Interpretation) → (x : A) → Dec (I ⊨ x)

open HasDecidableSatisfaction ⦃ … ⦄

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

𝑃[_♭_] : PredicateName → Terms → Formula
𝑃[_♭_] = atomic

_⊗_ : Formula → Formula → Formula
_⊗_ = logical

instance

  HasNegationFormula : HasNegation Formula
  HasNegation.~ HasNegationFormula φ = φ ⊗ φ

data IsLiteral : Formula → Set
 where
  atomic : (𝑃 : PredicateName) → (τs : Terms) → IsLiteral $ 𝑃[ 𝑃 ♭ τs ]
  logical : (𝑃 : PredicateName) → (τs : Terms) → IsLiteral ∘ ~ $ 𝑃[ 𝑃 ♭ τs ]

eqIsLiteral : ∀ {φ} → (lf₁ lf₂ : IsLiteral φ) → lf₁ ≡ lf₂
eqIsLiteral (atomic 𝑃 τs) (atomic .𝑃 .τs) = refl
eqIsLiteral (logical 𝑃 τs) (logical .𝑃 .τs) = refl

instance EqIsLiteral : ∀ {φ} → Eq (IsLiteral φ)
Eq._==_ EqIsLiteral lf₁ lf₂ = yes (eqIsLiteral lf₁ lf₂)

record LiteralFormula : Set
 where
  constructor ⟨_⟩
  field
    {formula} : Formula
    isLiteral : IsLiteral formula

open LiteralFormula

instance EqLiteralFormula : Eq LiteralFormula
Eq._==_ EqLiteralFormula (⟨_⟩ {φ₁} lf₁) (⟨_⟩ {φ₂} lf₂)
 with φ₁ ≟ φ₂
… | no φ₁≢φ₂ = no (λ {refl → φ₁≢φ₂ refl})
Eq._==_ EqLiteralFormula (⟨_⟩ {φ₁} lf₁) (⟨_⟩ {φ₂} lf₂) | yes refl = case (eqIsLiteral lf₁ lf₂) of λ {refl → yes refl}

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

record HasVacuousDischarge (+ : Set) : Set₁
 where
  field
    ◁_ : + → Set

open HasVacuousDischarge ⦃ … ⦄

record HasSalvation (A : Set) : Set₁
 where
  field
    {isVacuouslyDischargable} : Set
    ⦃ hasVacuousDischarge ⦄ : HasVacuousDischarge isVacuouslyDischargable
    ▷_ : A → Set

open HasSalvation ⦃ … ⦄

record HasDecidableSalvation (A : Set) : Set₁
 where
  field
    ⦃ hasSalvation ⦄ : HasSalvation A
    ▷?_ : (x : A) → Dec $ ▷_ x

open HasDecidableSalvation ⦃ … ⦄

∀[_♭_] : VariableName → Formula → Formula
∀[_♭_] = quantified

_∧_ : Formula → Formula → Formula
φ₁ ∧ φ₂ = ~ φ₁ ⊗ ~ φ₂

_∨_ : Formula → Formula → Formula
φ₁ ∨ φ₂ = ~ (φ₁ ⊗ φ₂)

_⊃_ : Formula → Formula → Formula
φ₁ ⊃ φ₂ = ~ φ₁ ∨ φ₂

_⟷_ : Formula → Formula → Formula
φ₁ ⟷ φ₂ = (φ₁ ⊗ (φ₂ ⊗ φ₂)) ⊗ ((φ₁ ⊗ φ₁) ⊗ φ₂) -- TODO check that this is logically equivalent to the more verbose, (φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)

record _≞_/_ (𝓘 : Interpretation) (I : Interpretation) (𝑥 : VariableName) : Set
 where
  field
    μEquality : {𝑥′ : VariableName} → 𝑥′ ≢ 𝑥 → μ⟦ 𝓘 ⟧ 𝑥 ≡ μ⟦ I ⟧ 𝑥′
    𝑓Equality : (𝑓 : FunctionName) (μs : Elements) → 𝑓⟦ 𝓘 ⟧ 𝑓 μs ≡ 𝑓⟦ I ⟧ 𝑓 μs
    𝑃Equality : (𝑃 : PredicateName) → (μs : Elements) → 𝑃⟦ 𝓘 ⟧ 𝑃 μs ≡ 𝑃⟦ I ⟧ 𝑃 μs

instance

  BeFormulaFormula : BeFormula Formula
  BeFormula.formula BeFormulaFormula = id

  BeFormulaLiteralFormula : BeFormula LiteralFormula
  BeFormula.formula BeFormulaLiteralFormula = formula

instance

  HasNegationLiteralFormula : HasNegation LiteralFormula
  HasNegation.~ HasNegationLiteralFormula ⟨ atomic 𝑃 τs ⟩ = ⟨ logical 𝑃 τs ⟩
  HasNegation.~ HasNegationLiteralFormula ⟨ logical 𝑃 τs ⟩ = ⟨ atomic 𝑃 τs ⟩

  HasNegationSequent : {A : Set} ⦃ _ : HasNegation A ⦄ ⦃ _ : BeFormula A ⦄ → HasNegation $ Sequent A
  HasNegation.~ HasNegationSequent ( φᵗ ╱ φˢs ) = ~ φᵗ ╱ φˢs

instance

  HasSatisfactionList : {A : Set} ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction $ List A
  HasSatisfaction._⊨_ HasSatisfactionList I [] = ⊤
  HasSatisfaction._⊨_ HasSatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs

  HasSatisfactionBeFormula : {A : Set} → ⦃ _ : BeFormula A ⦄ → HasSatisfaction A
  HasSatisfaction._⊨_ (HasSatisfactionBeFormula ⦃ beFormula ⦄) = λ I φ → I ⊨φ formula beFormula φ
   where
    _⊨φ_ : Interpretation → Formula → Set
    I ⊨φ (atomic 𝑃 τs) = 𝑃⟦ I ⟧ 𝑃 ⟨ τ⟦ I ⟧ <$> terms τs ⟩ ≡ true
    I ⊨φ (logical φ₁ φ₂) = ¬ I ⊨φ φ₁ × ¬ I ⊨φ φ₂
    I ⊨φ (quantified 𝑥 φ) = (𝓘 : Interpretation) → 𝓘 ≞ I / 𝑥 → 𝓘 ⊨φ φ

  HasSatisfactionSequent : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSatisfaction $ Sequent A
  HasSatisfaction._⊨_ HasSatisfactionSequent I (φᵗ ╱ φˢs) = I ⊨ φˢs → I ⊨ φᵗ

instance
  postulate
    HasDecidableSatisfactionFormula : HasDecidableSatisfaction Formula

instance

  HasValidationBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation A
  HasValidation.⊨_ HasValidationBeFormula φ = (I : Interpretation) → I ⊨ φ

  HasValidationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation $ Sequent A
  HasValidation.⊨_ HasValidationSequent Φ = (I : Interpretation) → I ⊨ Φ

  HasValidationProblem : {A : Set} ⦃ _ : BeFormula A ⦄ → HasValidation $ Problem A
  HasValidation.⊨_ HasValidationProblem (χs ¶ ι) = (I : Interpretation) → I ⊨ χs → I ⊨ ι

instance

  HasSubstantiveDischargeBeFormulaBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge A A
  HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeBeFormulaBeFormula ⦃ ⟨ beFormula ⟩ ⦄) = _≡_ on beFormula -- _≡_ on (formula beFormula) -- _≡_

  HasSubstantiveDischargeListBeFormulaBeFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List A) A
  HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListBeFormulaBeFormula ⦃ ⟨ beFormula ⟩ ⦄) +s - = beFormula - ∈ (beFormula <$> +s) -- flip _∈_

  HasSubstantiveDischargeListFormulaListFormula : {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List A) (List A)
  HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListFormulaListFormula ⦃ ⟨ beFormula ⟩ ⦄) = flip $ _⊆_ on fmap beFormula -- flip _⊆_

  HasSubstantiveDischargeSequentSequent : ∀ {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (Sequent A) (Sequent A)
  HasSubstantiveDischarge._≽_ HasSubstantiveDischargeSequentSequent (+ᵗ ╱ +ᵖs) (-ᵗ ╱ -ᵖs) = +ᵗ ≽ -ᵗ × +ᵖs ≽ -ᵖs

  HasSubstantiveDischargeListSequentSequent : ∀ {A : Set} ⦃ _ : BeFormula A ⦄ → HasSubstantiveDischarge (List $ Sequent A) (Sequent A)
  HasSubstantiveDischarge._≽_ HasSubstantiveDischargeListSequentSequent χs ι = ∃ λ c → (c ∈ χs) × c ≽ ι

instance

  HasVacuousDischargeList : {A : Set} ⦃ _ : HasSubstantiveDischarge (List A) A ⦄ ⦃ _ : HasNegation A ⦄ → HasVacuousDischarge (List A)
  HasVacuousDischarge.◁_ (HasVacuousDischargeList {A}) xs = ∃ λ (x : A) → xs ≽ x × xs ≽ ~ x

  HasVacuousDischargeSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasNegation A ⦄ → HasVacuousDischarge (Sequent A)
  HasVacuousDischarge.◁_ HasVacuousDischargeSequent (_ ╱ φˢs) = ∃ λ s → (s ∈ φˢs) × (φˢs ≽ s) × (φˢs ≽ ~ s)

instance

  HasSalvationSequent : {A : Set} ⦃ _ : BeFormula A ⦄ ⦃ _ : HasNegation A ⦄ {-⦃ _ : HasVacuousDischarge $ List A ⦄-} → HasSalvation $ Sequent A
  HasSalvation.isVacuouslyDischargable (HasSalvationSequent {A}) = List A
  HasSalvation.hasVacuousDischarge HasSalvationSequent = HasVacuousDischargeList
  HasSalvation.▷_ HasSalvationSequent (φᵗ ╱ φᵖs) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗ)

foo1 : ∀ {A} → ⦃ b : BeFormula A ⦄ ⦃ _ : HasNegation A ⦄ (statement₁ : A) → Σ A
      (λ x →
         Σ (BeFormula.formula b x ∈ [])
         (λ _ → BeFormula.formula b (~ x) ∈ []))
      ⊎ (BeFormula.formula b statement₁ ∈ []) →
      ⊥
foo1 statement₁ (left (fst₁ , () , snd₁))
foo1 statement₁ (right ())

foo2 : ∀ {A} → ⦃ b : BeFormula A ⦄ ⦃ _ : HasNegation A ⦄ (statement₁ : A) → ▷ (statement₁ ╱ []) →
      ⊥
foo2 statement₁ (left (fst₁ , () , snd₁))
foo2 statement₁ (right ())

instance

  HasDecidableSalvationSequent : {A : Set} ⦃ bf : BeFormula A ⦄ ⦃ hs : HasNegation A ⦄
                                 → HasDecidableSalvation $ Sequent A
  HasDecidableSalvation.hasSalvation HasDecidableSalvationSequent = HasSalvationSequent
  (HasDecidableSalvation.▷? HasDecidableSalvationSequent) (statement₁ ╱ []) = no ((foo2 statement₁)) -- (foo2 statement₁) -- (λ { (left x₂) → ? ; (right x₂) → ?}) -- no (λ { (left _) → ? ; (right _) → ?}) -- λ x → {!!} -- (λ { (left _) → {!!} ; (right _) → {!!}})
  (HasDecidableSalvation.▷? HasDecidableSalvationSequent) (statement₁ ╱ (x₂ ∷ suppositions₁)) = {!!}

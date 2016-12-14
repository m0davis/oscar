
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

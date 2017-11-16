
module Delay where

open import OscarPrelude

mutual

  data Delay (i : Size) (A : Set) : Set where
    now    :  A           → Delay i A
    later  :  ∞Delay i A  → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

private
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

traverse-list⇓ : ∀{A}{B} (f? : A → Delay ∞ B) → (∀ x → f? x ⇓) → (xs : List A) → traverse f? xs ⇓
traverse-list⇓ f? f?⇓ [] = [] , now⇓
traverse-list⇓ f? f?⇓ (x ∷ xs)
 with f?⇓ x | traverse-list⇓ f? f?⇓ xs
… | y , y⇓ | ys , ys⇓ = y ∷ ys , app⇓ (map⇓ _ y⇓) ys⇓

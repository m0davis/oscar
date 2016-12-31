
module SimpleTermUnification where

open import OscarPrelude

data Term (n : Nat) : Set where
  var : Fin n → Term n
  leaf : Term n
  _fork_ : Term n → Term n → Term n

|> : ∀ {m n} → (r : Fin m → Fin n) → Fin m → Term n
|> r = var ∘ r

_<|_ : ∀ {m n} → (f : Fin m → Term n) → Term m → Term n
f <| var x = f x
f <| leaf = leaf
f <| (t₁ fork t₂) = (f <| t₁) fork (f <| t₂)

<|-assoc : ∀ {m n o} (f : Fin n → Term o) (g : Fin m → Term n) (x : Term m) → f <| (g <| x) ≡ (λ y → f <| g y) <| x
<|-assoc f g (var x) = refl
<|-assoc f g leaf = refl
<|-assoc f g (x₁ fork x₂) rewrite <|-assoc f g x₁ | <|-assoc f g x₂ = refl

_≗_ : ∀ {m n} → (f g : Fin m → Term n) → Set
f ≗ g = ∀ x → f x ≡ g x

infixr 9 _⋄_
_⋄_ : ∀ {l m n} → (f : Fin m → Term n) → (g : Fin l → Term m) → Fin l → Term n
(f ⋄ g) = (f <|_) ∘ g

⋄-assoc : ∀ {l m n o} (f : Fin n → Term o) (g : Fin m → Term n) (h : Fin l → Term m) → (f ⋄ (g ⋄ h)) ≗ ((f ⋄ g) ⋄ h)
⋄-assoc f g h x = <|-assoc f g (h x)

⋄-assoc' : ∀ {l m n o} (f : Fin n → Term o) (g : Fin m → Term n) (h : Fin l → Term m) → (f ⋄ (g ⋄ h)) ≡ ((f ⋄ g) ⋄ h)
⋄-assoc' f g h = {!⋄-assoc f g h!}

thin : ∀ {n} → (x : Fin (suc n)) → (y : Fin n) → Fin (suc n)
thin {n} zero y = suc y
thin {zero} (suc x) ()
thin {suc n} (suc x) zero = zero
thin {suc n} (suc x) (suc y) = suc (thin x y)

thick : ∀ {n} → (x y : Fin (suc n)) → Maybe (Fin n)
thick {n} zero zero = nothing
thick {n} zero (suc y) = just y
thick {zero} (suc ()) zero
thick {suc n} (suc x) zero = just zero
thick {zero} (suc ()) (suc y)
thick {suc n} (suc x) (suc y) = suc <$> thick x y

check : ∀ {n} → (x : Fin (suc n)) (t : Term (suc n)) → Maybe (Term n)
check x (var y) = var <$> thick x y
check x leaf = just leaf
check x (t₁ fork t₂) = _fork_ <$> check x t₁ <*> check x t₂

_for_ : ∀ {n} → (t' : Term n) (x : Fin (suc n)) → Fin (suc n) → Term n
(t' for x) y with thick x y
… | just y' = var y'
… | nothing = t'

data AList (n : Nat) : Nat → Set where
  anil : AList n n
  _asnoc_/_ : ∀ {m} → (σ : AList n m) → (t' : Term m) → (x : Fin (suc m)) → AList n (suc m)

sub : ∀ {n m} → (σ : AList n m) → Fin m → Term n
sub anil = var
sub (σ asnoc t' / x) = sub σ ⋄ (t' for x)

flexFlex : ∀ {m} → (x y : Fin m) → ∃ (flip AList m)
flexFlex {zero} () _
flexFlex {suc m} x y with thick x y
… | just y' = m , (anil asnoc var y' / x)
… | nothing = suc m , anil

flexRigid : ∀ {m} → (x : Fin m) (t : Term m) → Maybe (∃ (flip AList m))
flexRigid {zero} () _
flexRigid {suc m} x t with check x t
… | just t' = just $ m , anil asnoc t' / x
… | nothing = nothing

amgu : ∀ {m} → (s t : Term m) (acc : ∃ (flip AList m)) → Maybe (∃ (flip AList m))
amgu {m} leaf leaf acc = just acc
amgu {m} leaf (_ fork _) _ = nothing
amgu {m} (_ fork _) leaf _ = nothing
amgu {m} (s₁ fork s₂) (t₁ fork t₂) acc = amgu s₁ t₁ acc >>= amgu s₂ t₂
amgu {m} (var x) (var y) (.m , anil) = just $ flexFlex x y
amgu {m} (var x) t (.m , anil) = flexRigid x t
amgu {m} t (var x) (.m , anil) = flexRigid x t
amgu {suc m} s t (n , (σ asnoc r / z)) = amgu ((r for z) <| s) ((r for z) <| t) (n , σ) >>= λ {(n' , σ') → just $ n' , σ' asnoc r / z}

mgu : ∀ {m} → (s t : Term m) → Maybe (∃ (flip AList m))
mgu {m} s t = amgu s t (m , anil)

f : Fin 4 → Term 5
f n = var (thin (suc n) n) fork var (thin (suc n) n)

g : Fin 4 → Term 5
g n = var (suc n)

fs : Term 5
fs = f 0 fork (f 1 fork (f 2 fork f 3))

gs : Term 5
gs = g 0 fork (g 1 fork (g 2 fork g 3))

foo : Set
foo = {!mgu fs gs!}

Property : Nat → Set₁
Property m = ∀ {n} → (Fin m → Term n) → Set

Unifies : ∀ {m} → (s t : Term m) → Property m
Unifies s t f = f <| s ≡ f <| t

_∧_ : ∀ {m} → (P Q : Property m) → Property m
(P ∧ Q) f = P f × Q f

_⇔_ : ∀ {m} → (P Q : Property m) → Property m
(P ⇔ Q) f = (P f → Q f) × (Q f → P f)

Nothing : ∀ {m} (P : Property m) → Set
Nothing {m} P = ∀ {n} → (f : Fin m → Term n) → ¬ P f

infixl 3 _[-⋄_]_
_[-⋄_]_ : ∀ {m n} (P : Property m) (f : Fin m → Term n) → Property n
(P [-⋄ f ] g) = P (g ⋄ f)

_≤ₛ_ : ∀ {m n n'} (f : Fin m → Term n) (g : Fin m → Term n') → Set
f ≤ₛ g = ∃ λ f' → f ≗ (f' ⋄ g)

Max : ∀ {m} (P : Property m) → Property m
Max {m} P f = P f × ∀ {n} → (f' : Fin m → Term n) → P f' → f' ≤ₛ f

DClosed : ∀ {m} (P : Property m) → Set
DClosed {m} P = ∀ {n n'} (f : Fin m → Term n) (g : Fin m → Term n') → f ≤ₛ g → P g → P f

Lemma1 : ∀ {l} {P Q : Property l} {m n o}
           {p : Fin m → Term n}
           {q : Fin n → Term o}
           {a : Fin l → Term m}
         → DClosed P
         → Max (P [-⋄ a ]_) p
         → Max (Q [-⋄ (p ⋄ a)]_) q
         → Max ((P ∧ Q) [-⋄ a ]_) (q ⋄ p)
Lemma1 {P = P} {Q} {p = p} {q} {a} DCP maxP maxQ =
  let Qqpa : Q (q ⋄ p ⋄ a)
      Qqpa = fst maxQ
      Qqpa' : Q ((q ⋄ p) ⋄ a)
      Qqpa' = {!⋄-assoc q p a!}
      Pqpa : P (q ⋄ p ⋄ a)
      Pqpa = DCP (λ z → q <| (p <| a z)) (λ z → p <| a z) (q , (λ x → refl)) (fst maxP)
      lem3 : ∀ {n} → {f : Fin _ → Term n} → P (f ⋄ a) → Q (f ⋄ a) → f ≤ₛ (q ⋄ p)
      lem3 = {!!}
  in ({!!} , {!maxQ!}) , {!!}
  where
  Ppa : P (p ⋄ a)
  Ppa = fst maxP

  pMax : ∀ {n} {p' : Fin _ → Term n} → P (p' ⋄ a) → p' ≤ₛ p
  pMax {n} {p'} Pp'a = snd maxP p' Pp'a

data Step (n : Nat) : Set where
  left : Term n → Step n
  right : Term n → Step n

_+ₛ_ : ∀ {n} → (ps : List (Step n)) → (t : Term n) → Term n
[] +ₛ t = t
(left r ∷ ps) +ₛ t = (ps +ₛ t) fork r
(right l ∷ ps) +ₛ t = l fork (ps +ₛ t)

theorem-6 : ∀ m → (s t : Term m) → (r : Maybe (∃ (flip AList m))) → mgu s t ≡ r → Either (∃ λ n → ∃ λ σ → Max (Unifies s t) (sub σ) × r ≡ just (n , σ)) (Nothing (Unifies s t) × r ≡ nothing)
theorem-6 = {!!}

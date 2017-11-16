
```agda
module Happy where

open import Agda.Builtin.Equality

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

ex11 : ∀ {A B C D : Set} (f : A → B) (g : B → C) (h : C → D) → (h ∘ g) ∘ f ≡ h ∘ g ∘ f
ex11 f g h = refl
```

g ∘ f ≡

To show that (h ∘ g) ∘ f ≡ h ∘ (g ∘ f),

notice that
h ∘ g ≡ λ x → g (f x)

(h ∘ g) ∘ f ≡ ((λ x → h x) ∘ (λ x → g x)) ∘ (λ x → f x)

                    (            h ∘ g   ) ∘ f
                    |v-----------∥-^ ∥   | | |          ; by definition of _∘_ h g
            ≡       (λ x →       h  (g x)) ∘ f
              v-----∥--------------------∥-^ ∥          ; by definition of _∘_ (λ x → h (g x)) f
            ≡ λ x → (λ x →       h  (g x))  (f x)
            ≡ λ x → (λ y → h (g y)) (f x)       ; renaming variables
            ≡ λ x →        h (g (f x))                 ; β-reduction

and
h ∘ (g ∘ f) ≡ λ x → h ((g ∘ f) x)          ; def
            ≡ λ x → h ((λ x → g (f x)) x)  ; def
            ≡ λ x → h (       g (f x)   )  ; β-reduction

so they is eq


For exercise 1.2

we have

module _ (A B : Set) where
  pr₁ : A × B → A
  pr₁ (a , b) = a

  pr₂ : A × B → B
  pr₂ (a , b) = b

  rec : ∀ (C : Set) (A → B → C) → A × B → C
  rec C g ab = g (pr₁ ab) (pr₂ ab)

we want to show now that g (pr₁ ab) (pr₂ ab) : C

we assume that C : Set, g : A → B → C, ab : A × B

so pr₁ ab : A and pr₂ ab : B
   g : A → B → C,
so g (pr₁ ab) : B → C
   g (pr₁ ab) (pr₂ ab) : C


in the case of Σ,

  A : Set
  B : A → Set
  pr₁ : Σ A B → A
  pr₂ : (s : Σ A B) → B (pr₁ s)
  then we want
  rec : (C : Set) ((x : A) → B x → C) → Σ A B → C
  so define
  rec C g s = g (pr₁ s) (pr₂ s)
  to verify now that g (pr₁ s) (pr₂ s) : C
  we have
    s : Σ A B
    pr₁ s : A
    pr₂ s : B (pr₁ s)

    g : (x : A) → B x → C
    pr₁ s : A
    -----------------------
    g (pr₁ s) : B (pr₁ s) → C


    g (pr₁ s) : B (pr₁ s) → C
    pr₂ s     : B (pr₁ s)
    --------------------------
    g (pr₁ s) (pr₂ s) : C

exercise 1.3

  module _ (A B : Set) where
    postulate
      _≡_ : A × B → A × B → Set
      pr₁ : A × B → A
      pr₂ : A × B → B
      uniq : (x : A × B) → (pr₁ x , pr₂ x) ≡ x

    ind : (C : A × B → Set) ((x : A) (y : B) → C (x , y)) → (x : A × B) → C x
    ind C g x = g (pr₁ x) (pr₂ x)

    now it suffices to verify
      g (pr₁ x) (pr₂ x) : C x
    we have g : (x : A) (y : B) → C (x , y)
            pr₁ x : A
            pr₂ x : B
    so
      g (pr₁ x) (pr₂ x) : C (pr₁ x , pr₂ x)
    notice that
      uniq x : (pr₁ x , pr₂ x) ≡ x
    so
      C (pr₁ x , pr₂ x) ≡? C x
    so
      g (pr₁ x) (pr₂ x) : C x


exercise 1.4

  rec' C c₀ cₛ n        = snd (iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) n)

  to show correctness,

  let
    D : N → U
    D = (λ n → rec' C c₀ cₛ 0 :≡ c₀ × rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n))

  DL : U
  DL = rec' C c₀ cₛ 0 :≡ c₀
  DR : N → U
  DR n = rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n)

  Dreduced : N → U
  Dreduced n = DL × DR n

  trivD : ∀ n → D n ≡ Dreduced n
  otherD : ∀ n → Dreduced n → D n

  want to show

  foo : ∀ n → D n
  foo = indN D d0 dns
    where
      d0 : D 0
      d0 = d0' , d0''

      d0' : rec' C c₀ cₛ 0 :≡ c₀

      d0'' :
        rec' C c₀ cₛ 0 :≡ c₀ ∋ ⁇
        snd (iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) n)

        ,
        ⁇

      dns : (n : N) → D n → D (succ n)
      dns n dn = ⁇

  now a bunch of equations
  rec' C c₀ cₛ n :≡ iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) n
  iter (N × C) x f 0 :≡ x

  rec' C c₀ cₛ 0 :≡ snd (iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) n)

  ?rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n)
  ?rec' C c₀ cₛ 0 :≡ c₀
  rec' C c₀ cₛ 0 :≡ c₀ × rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n)
  D 0

  suppose D n
  rec' C c₀ cₛ 0 :≡ c₀ × rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n)
  rec' C c₀ cₛ 0 :≡ c₀
  rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n)

  D (succ n)

  want to show

  D 0 :≡ rec' C c₀ cₛ 0 :≡ c₀ × rec' C c₀ cₛ (succ 0) :≡ cₛ 0 (rec' C c₀ cₛ 0)
      note that rec' C c₀ cₛ 0 :≡ snd (iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) 0)
                               :≡ snd (0 , c₀)
                               :≡ c₀
                rec' C c₀ cₛ (succ 0) :≡ snd (iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) (succ 0))
                iter (N × C) (0 , c₀) (λ (n' , c') → (succ n' , cₛ n' c')) (succ 0) :≡ (λ (n' , c') → (succ n' , cₛ n' c')) ()



      :≡ rec' C c₀ cₛ 0 :≡ c₀ × rec' C c₀ cₛ (succ 0) :≡ cₛ 0 (rec' C c₀ cₛ 0)

  indN (λ n → rec' C c₀ cₛ 0 :≡ c₀ × rec' C c₀ cₛ (succ n) :≡ cₛ n (rec' C c₀ cₛ n))

  to show that the second defining equation holds, we want to show that

  if rec' C c₀ cₛ (succ n) = cₛ n (rec' C c₀ cₛ n)
  then rec' C c₀ cₛ (succ (succ n)) = cₛ (succ n) (rec' C c₀ cₛ (succ n))

  we want to compute

  indN (λ n → rec' C c₀ cₛ 0 ≡ c₀ × rec' C c₀ cₛ (succ n) = cₛ n (rec' C c₀ cₛ n))

  let D = λ n → rec' C c₀ cₛ 0 ≡ c₀ × rec' C c₀ cₛ (succ n) = cₛ n (rec' C c₀ cₛ n)
  D 0 = rec' C c₀ cₛ 0 ≡ c₀ × rec' C c₀ cₛ (succ 0) ≡ cₛ n (rec' C c₀ cₛ 0)
      = c₀ ≡ c₀ × snd (iter (N × C) (0 , c₀) (λ (n' , c') → cₛ n' c') (succ 0)) ≡ cₛ n c₀
      = c₀ ≡ c₀ × snd ((λ (n' , c') → cₛ n' c') (iter (N × C) (0 , c₀) 0)) ≡ cₛ n c₀
      = c₀ ≡ c₀ × snd ((λ (n' , c') → cₛ n' c') (0 , c₀)) ≡ cₛ n c₀
      = c₀ ≡ c₀ × snd ((λ (n' , c') → cₛ 0 c₀) (0 , c₀)) ≡ cₛ n c₀


  proof
    rec' C c₀ cₛ (succ (succ n))
      = snd (iter (N × C) (0 , c₀) (λ (n' , c') → cₛ n' c') (succ (succ n)))
      = snd ((λ (n' , c') → cₛ n' c') (iter (N × C) (0 , c₀) (λ (n' , c') → cₛ n' c') (succ n)))
      = snd ((λ (n' , c') → cₛ n' c') (iter (N × C) (0 , c₀) (λ (n' , c') → cₛ n' c') (succ n)))


  rec' C c₀ cₛ n        = snd (iter (N × C) ?0 (λ (n' , c') → ?1) ?2)

  ?0 : N × C
  ?1 : N × C
  ?2 : N

  we guessed N × C. Now we guess ?2 = n

  rec' C c₀ cₛ n        = snd (iter (N × C) ?0 (λ (n' , c') → ?1) n)

  we want rec' C c₀ cₛ 0 = c₀, so
    c₀ = snd (iter (N × C) ?0 (λ (n' , c') → ?1) 0)
       = snd ?0

  we want rec' C c₀ cₛ (succ n) = cₛ n (rec' C c₀ cₛ n) , so
    cₛ n (rec' C c₀ cₛ n) = snd (iter (N × C) ?0 (λ (n' , c') → ?1) (succ n))
                          = snd ((λ (n' , c') → ?1) (iter (N × C) ?0 (λ (n' , c') → ?1) n))


  if ?2 = 0, then ?0 = (⁇ , c₀)
  if ?2 = succ n,

  ∀ n → rec' C c₀ cₛ n = rec C c₀ cₛ n
  rec' C c₀ cₛ 0 = rec C c₀ cₛ 0 = c₀
  ∀ n → rec' C c₀ cₛ n = rec C c₀ cₛ n → rec' C c₀ cₛ (succ n) = rec C c₀ cₛ (succ n) = cₛ n (rec C c₀ cₛ n) = cₛ n (rec' C c₀ cₛ n)

  rec' C c₀ cₛ 0        = c₀
  rec' C c₀ cₛ (succ n) =

  C' n = λ n → rec' C c₀ cₛ n =ₙ iter C c₀ (cₛ n) n

  C' 0 ≡ rec' C c₀ cₛ 0 =ₙ iter C c₀ (cₛ 0) 0
       ≡

  rec' C c₀ cₛ 0 = iter C c₀ (cₛ 0) 0 = c₀

  rec  C c₀ cₛ 0 = c₀
  rec' C c₀ cₛ 0 = iter C c₀ (cₛ 0) 0 = c₀
  rec  C c₀ cₛ (succ n) = cₛ n (rec C c₀ cₛ n)
  rec' C c₀ cₛ (succ n) = iter C c₀ (cₛ (succ n)) (succ n)
                        = cₛ (succ n) (iter C c₀ (cₛ (succ n)) n)

exercise 1.10

```agda
open import Agda.Builtin.Nat

RECN : Set → Set
RECN C = C → (Nat → C → C) → Nat → C

recN : (C : Set) → RECN C
recN C c₀ cₛ 0 = c₀
recN C c₀ cₛ (suc n) = cₛ n (recN C c₀ cₛ n)

ack : Nat → Nat → Nat
ack 0 = suc
ack (suc m) 0 = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

ack′ : Nat → Nat → Nat
ack′ 0 = suc
ack′ 1 0 = 2
ack′ 1 (suc n) = suc (ack′ 1 n)
ack′ (suc (suc m)) 0 = ack′ (suc m) 1
ack′ (suc (suc m)) (suc n) = ack′ (suc m) (ack′ (suc (suc m)) n)


open import Data.Product

{-
0 ack b = suc b
a ack 0 = a-1 ack 1
a ack b = a-1 ack (a ack b-1)

ack is not associative

when reading/understanding a language, it is vitally important to know whether a given operator is associative. this is grammar. i almost feel like this is something lacking in the type system

  C  : Set
  c₀ : C
  cₛ : Nat → C → C
  recN C c₀ cₛ n = cₛ (n - 1) (recN C c₀ cₛ (n - 1))                                                    -- unfold once
                              ^-------------=======^
                 = cₛ (n - 1) (cₛ (n - 2) (recN C c₀ cₛ (n - 2)))                                       -- unfold once
                                          ^-------------=======^
                 = cₛ (n - 1) [cₛ (n - n̂) (recN C c₀ cₛ (n - n̂))]                                       -- elipsise outer
                 = cₛ (n - 1) [cₛ (n - n̂) {recN C c₀ cₛ 0      }]                                       -- elipsise inner
                 = cₛ (n - 1) [cₛ (n - n̂) {c₀                  }]                                       -- eval
                 = cₛ (n - 1) [cₛ ṅ       {c₀                  }]                                       -- eval
  base : C <---- use as zeroeth argument to recursion
  base = c₀
         ^------ use as first argument to recursion
  iterator : (n : Nat) → (Nat → C → C) → Fin n → C → C
  iterator n cₛ ṅ = cₛ (toNat ṅ)
  iteration : Fin n → C → C
  iteration = iterator n cₛ -- λ ṅ → cₛ (toNat ṅ)
                         ^------------------------- use as second argument to recursion
                       ^--------------------------- use as third argument to recursion

  iterator n̂ = cₛ (n - n̂)


                 = cₛ (n - 1) [cₛ 0       (recN C c₀ cₛ 0      )]                                       -- eschateval
                 = cₛ (n - 1) [cₛ 0       c₀                    ]                                       -- eval






                 = cₛ (n - 1) (            recN C c₀ cₛ (n - 1) )                                       -- ununfold and align
                 = cₛ (n - 1) (̂            recN C c₀ cₛ (n - n̂) )̂                                       -- elipsise
                 = cₛ (n - 1) (̂            recN C c₀ cₛ 0       )̂                                       -- eval
                 = cₛ (n - 1) (̂            recN C c₀ cₛ 0       )̂                                       -- eval

  recN C c₀ cₛ n = cₛ (n - 1) (                  recN C c₀ cₛ (n - 1)       )
                 = cₛ (n - 1) (... (cₛ (n - n') (recN C c₀ cₛ (n - n'))) ...)
                 = cₛ (n - 1) (... (cₛ 0        (recN C c₀ cₛ 0       )) ...)
                 = cₛ (n - 1) (... (cₛ 0        c₀                     ) ...)

  recN C c₀ cₛ n = cₛ (n - 1) (                  recN C c₀ cₛ (n - 1)       )
                 = cₛ (n - 1) (... (cₛ (n - n') (recN C c₀ cₛ (n - n'))) ...)
                 = cₛ (n - 1) (... (cₛ 0        (recN C c₀ cₛ 0       )) ...)
                 = cₛ (n - 1) (... (cₛ 0        c₀                     ) ...)

  ack m n = ack (m - 1) (                          ack m (n - 1))
          = ack (m - 1) (             ack (m - 1) (ack m (n - 2)))
          = ack (m - 1) (ack (m - 1) (ack (m - 1) (ack m (n - 3))))
          = ack (m - 1) (ack (m - 1) (ack (m - 1) (ack m (n - 3))))

  ack 0 n = suc n
  ack m 0 = ack (m - 1) 1
  ack m n = ack (m - 1) (ack m (n - 1))
                        ^----=-=======^                                                                -- unfold once n
          = ack (m - 1) (ack (m - 1) (ack m (n - 2)))
                                     ^----=-=======^                                                   -- unfold once n
          = ack (m - 1) (ack (m - 1) (ack (m - 1) (ack m (n - 3))))
                                     ^----=======-===============^                                     -- unfold once m
          = ack (m - 1) (ack (m - 1) (ack (m - 2) (ack (m - 1) (ack m (n - 3) - 1))))
                        ^----=======-===============================================^                  --
          = ack (m - 1) (ack (m - 2) (ack (m - 1) (ack (m - 2) (ack (m - 1) (ack m (n - 3) - 1)) - 1)))
           ^----=======-===============================================================================^
          = ack (m - 2) (ack (m - 1) (ack (m - 2) (ack (m - 1) (ack (m - 2) (ack (m - 1) (ack m (n - 3) - 1)) - 1)) - 1))
          = ack (m - 2) (ack (m - 1) (... (ack (m - 2) (ack (m - 1) (...

  let ack! m n = ack 0 (ack 1 (ack 2 (... (ack (m - 1) n) ...)))
  let ack!′ m i n = ack! m (n - 1)
  let ack!! m i n = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (i - 1) (ack m (n - i))) ...)))
  let ack⁉ m n = ack!! m n n
               = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (n - 1) (ack m (n - n))) ...)))
               = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (n - 1) (ack m 0)) ...)))
               = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (n - 1) (ack (m - 1) 1)) ...)))
               = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (n - 1) (ack⁉ (m - 1) 1)) ...)))
               = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (n - 1) (ack!! (m - 1) 1 1)) ...)))
               = ack!′ m 0 (ack!′ m 1 (ack!′ m 2 (... (ack!′ m (n - 1) (ack!! (m - 1) 1 1)) ...)))
  ack! m 0 = ack 0 (ack 1 (ack 2 (... (ack (m - 2) (ack (m - 1) 0)) ...)))
  ack! m 0 = ack 0 (ack 1 (ack 2 (... (ack (m - 2) (ack (m - 2) 1)) ...)))
           = ack! (m - 1) (ack (m - 2) 1)
  ack



          = ack (m - 2) (ack (m - 1) ((ack (m - 2) (ack (m - 1) (ack (m - 2) (ack (m - 1) (ack m (n - 3) - 1)) - 1))) - 1))




          = ack (m - 2) (ack (m - 1) (ack (m - 2) (ack (m - 3) (ack (m - 2) (ack (m - 3) (ack (m - 2) (ack (m - 1) (n - 3) - 1)) - 1))) - 1))




from the third equation

  ack (suc m) (suc n) = ack m (ack (suc m) n)

we can derive

  ack m n = ack m₋₁ (ack m₋₁ (ack m₋₁ (... (ack m₋₁ 0))))
          = ack m₋₁ (ack m₋₁ (ack m₋₁ (... (ack m₋₁ 0))))

so if we are given

  ack m₋₁ : Nat → Nat

we can derive

  ack m : Nat → Nat

by n applications of ack m₋₁ to the base of 0

that is to say, we have a generator for successors of the first argument to ack

ack-m : (ack-m₋₁ : Nat → Nat) → Nat → Nat
ack-m ack-m₋₁ 0 = ack-m₋₁ 0
ack-m ack-m₋₁ (suc n) = ack-m₋₁ (ack-m n) -- reversing these is fine too

let's split this up

ack-m' : (ack-m₋₁0 : Nat) (ack-m₋₁ : Nat → Nat) → Nat → Nat
ack-m' ack-m₋₁0 ack-m₋₁ 0       = ack-m₋₁0
ack-m' ack-m₋₁0 ack-m₋₁ (suc n) = ack-m₋₁ (ack-m' ack-m₋₁0 ack-m₋₁ n)
                                = (λ _ → ack-m₋₁) n (ack-m' ack-m₋₁0 ack-m₋₁ n)

so
ack-m' : Nat → (Nat → Nat) → Nat → Nat
ack-m' ack-m₋₁0 ack-m₋₁ n = recN Nat ack-m₋₁0 (λ _ → ack-m₋₁) n

we can reformulate it as

ack-3 : (Nat → Nat) → Nat → Nat → Nat
ack-3 ack-m₋₁ ack-m₋₁0 n = recN Nat ack-m₋₁0 (λ _ → ack-m₋₁) n

ack-3' : Nat → (Nat × (Nat → Nat)) → (Nat × (Nat → Nat))
ack-3' n (ack-m₋₁0 , ack-m₋₁) = let ack-m = recN Nat ack-m₋₁0 (λ _ → ack-m₋₁) n in ack-m 0 , ack-m

now let's take into account the second equation

  ack (suc m) 0 = ack m 1

so

  ack (suc (suc m)) 0 = ack (suc m) 1
                      =



ack-23 : (Nat → Nat) → (Nat → Nat) → Nat → Nat
ack-23 ack-m₋₁ ack-m₋₂ n = ack-3 ack-m₋₁ (ack-m₋₂ 0) n
                         = recN Nat (ack-m₋₂ 0) (λ _ → ack-m₋₁) n


-}

ack-3[ : Nat → (Nat → Nat) → Nat → Nat
ack-3[ ack-m₋₁0 ack-m₋₁ n = recN Nat ack-m₋₁0 (λ _ → ack-m₋₁) n

-- another formulation
ack-3′ : Nat → (Nat → Nat) → Nat → Nat
ack-3′ n ack-m₋₁ ack-m₋₁0 = recN Nat ack-m₋₁0 (λ _ → ack-m₋₁) n

ack-3' : (Nat × (Nat → Nat)) → (Nat × (Nat → Nat))
ack-3' (ack-m₋₁0 , ack-m₋₁) = let ack-m = recN Nat ack-m₋₁0 (λ _ → ack-m₋₁) in ack-m 0 , ack-m

-- but a much simpler version is to say
ack-3 : (Nat → Nat) → (Nat → Nat)
ack-3 ack-m₋₁ = recN Nat (ack-m₋₁ 1) (λ _ → ack-m₋₁)

-- now we want to build-up ack-3s ... we want to build-up m of them (m = 0 --> suc)

acker : Nat → Nat → Nat
acker m n = recN (Nat → Nat) suc (λ _ → ack-3) m n

ack' : Nat → Nat → Nat
ack' =
  recN (Nat → Nat) suc (λ _ ack-m₋₁ → recN Nat (ack-m₋₁ 1) (λ _ → ack-m₋₁))
  -- recN (RECN (Nat → Nat → Nat)) {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  -- recN (RECN (Nat → Nat)) (recN (Nat → Nat)) {!!} 1 suc λ x x₁ x₂ → {!!}
  -- recN (Nat → Nat)
  -- recN (RECN (Nat → Nat))
  -- recN {!!} {!!} {!!} {!!}
  -- recN (RECN (Nat → Nat)) {!!} {!!} {!!} {!!} {!!} {!!} {!!}
{-
prv-ack : ∀ m n → ack m n ≡ ack' m n
prv-ack 0 n = refl
prv-ack (suc zero) zero = refl
prv-ack (suc (suc m)) zero = {!!}
prv-ack (suc m) (suc n) = {!!}
-}
```

exercise 1.14

```agda
module _ (A : Set) where

  ind=A : (C : (x y : A) → x ≡ y → Set) → (∀ (x : A) → C x x refl) → ∀ x y → (p : x ≡ y) → C x y p
  ind=A C c x .x refl = c x

  ex1-14 : (x : A) (p : x ≡ x) → p ≡ refl
  -- ex1-14 x refl = refl
  ex1-14 x refl = ind=A (λ x₁ y x₂ → refl {A = {!x₁ ≡ y!}} ≡ refl) (λ x₁ → refl {x = refl {A = {!!}}}) x x refl
  -- ex1-14 x p = ind=A (λ x₁ y x₂ → p ≡ refl) (λ x₁ → {!p!}) x x p
  -- ex1-14 x p = {!ind=A (λ {x' .x' refl → x' ≡ x'}) (λ x → refl {x = x}) x x p!}
  -- ex1-14 x p = ind=A (λ {x y refl → y ≡ y}) (λ x → ?) x x p
```

chapter 2

```agda
module lemma-2-1-2 where

  lemma-2-1-2 : ∀ (A : Set) (x : A) y z → x ≡ y → y ≡ z → x ≡ z
  lemma-2-1-2 _ _ _ _ = λ {refl refl → refl}

  lemma-2-1-2a : ∀ (A : Set) (x : A) y z → x ≡ y → y ≡ z → x ≡ z
  lemma-2-1-2a _ _ _ _ = λ {refl refl → refl}

  foo1 : ∀ (A : Set) → Set
  foo1 A = A

  foo2 : ∀ (A : Set) → Set
  foo2 A = A

  chk : lemma-2-1-2 ≡ lemma-2-1-2a
  chk = {!refl!}

  chkf : foo1 ≡ foo2
  chkf = refl
```

disallowed by path induction?

```agda
module PathInductionDis where
  postulate
    A : Set
    a : A
    C : a ≡ a → Set

  prove-this : C refl → ∀ (x : a ≡ a) → C x
  prove-this crefl refl = crefl -- works b/c we can convince agda that anything of type a ≡ a must be refl. Can we do it in --cubical?

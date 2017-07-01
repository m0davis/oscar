
module Oscar.Class1 where

open import Oscar.Prelude renaming (_∘_ to _∘′_)
open import Oscar.R
open import Oscar.Data

unhide : ∀ {a} {A : Set a} {b} {B : A → Set b} → ({x : A} → B x) → (x : A) → B x
unhide f x = f {x}

hide : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → {x : A} → B x
hide f {x} = f x

infixr 9 ◆-syntax
◆-syntax : ∀
  {𝔞} {A : Ø 𝔞}
  {𝔟} {B : A → Ø 𝔟}
  {𝔠} {C : ∀ a → B a → Ø 𝔠} →
  ⦃ _ : 𝓡₃,₁ A B C ⦄
  → ∀ (a : A)
      (b : B a)
    → C a b
◆-syntax a b = 𝓻₃,₁,₀ a b

syntax ◆-syntax f g = g ◆ f

infixr 9 ◇-syntax
◇-syntax : ∀
  {𝔦} {I : Ø 𝔦}
  {𝔞} {A : Ø 𝔞}
  {𝔟} {B : A → I → Ø 𝔟}
  {𝔠} {C : ∀ a → (∀ i → B a i) → Ø 𝔠} →
  ⦃ _ : 𝓡₃,₁ A (λ f → (i : I) → B f i) (λ f g → C f g) ⦄
  → ∀ (f : A)
      (g : {i : I} → B f i)
    → C f (unhide g)
◇-syntax a b = 𝓻₃,₁,₀ a (unhide b)

syntax ◇-syntax f g = g ◇ f

infixr 9 ∙-syntax
∙-syntax : ∀
  {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
  {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
  {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
  {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
  {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
  {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
  ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄
  → ∀ {⓪ ⑴} ⑵ {⑶} ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
∙-syntax ⑵ ⑷ = 𝓻₆,₁,₀ _ _ ⑵ _ ⑷

syntax ∙-syntax ⑵ ⑷ = ⑷ ∙ ⑵

infixr 9 ∘-syntax
∘-syntax : ∀
  {𝔬₀}
  {𝔬₁} {𝔒₁ : Ø 𝔬₀ → Ø 𝔬₁}
  {𝔬₂} {𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂}
  {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴ → Ø 𝔬₃}
  {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → ⓪ → Ø 𝔬₄}
  {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → (∀ x → 𝔒₄ ⓪ ⑴ ⑵ ⑶ x) → Ø 𝔬₅}
  ⦃ _ : 𝓡₆,₁ (Ø 𝔬₀) 𝔒₁ 𝔒₂ 𝔒₃ (λ ⓪ ⑴ ⑵ ⑶ → (x : ⓪) → 𝔒₄ ⓪ ⑴ ⑵ ⑶ x) 𝔒₅ ⦄
  → ∀ {⓪ ⑴} ⑵ {⑶} (⑷ : ∀ {x : ⓪} → 𝔒₄ ⓪ ⑴ ⑵ ⑶ x) → 𝔒₅ ⓪ ⑴ ⑵ ⑶ (unhide ⑷)
∘-syntax ⑵ ⑷ = 𝓻₆,₁,₀ _ _ ⑵ _ (unhide ⑷)

syntax ∘-syntax ⑵ ⑷ = ⑷ ∘ ⑵

instance

  FunctionComposition3 : ∀
    {𝔞} {A : Ø 𝔞}
    {𝔟} {B : A → Ø 𝔟}
    {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
    → 𝓡₃,₁
      ((a : A) → B a)
      (λ _ → (a : A) → (b : B a) → C b)
      (λ f g → (a : A) → C (f a))
  𝓡₃,₁.𝓻₃,₁,₀ FunctionComposition3 f g x = g x (f x)

  FunctionComposition6 : ∀ {𝔞 𝔟 𝔠} →
    𝓡₆,₁
      (Ø 𝔞)
      (λ A → A → Ø 𝔟)
      (λ A B → (a : A) → B a)
      (λ A B f → ∀ a → B a → Ø 𝔠)
      (λ A B f C → (a : A) (b : B a) → C a b)
      (λ A B f C g → (a : A) → C a (f a))
  𝓡₆,₁.𝓻₆,₁,₀ FunctionComposition6 A B f C g x = g (x) (f x)

open Substitunction

instance

  SubstitunctionComposition3 : ∀ {𝔭} {𝔓 : Ø 𝔭} {l m n} →
    𝓡₃,₁
      (Substitunction 𝔓 l m)
      (λ f → Substitunction 𝔓 m n)
      (λ f g → Substitunction 𝔓 l n)
  𝓡₃,₁.𝓻₃,₁,₀ SubstitunctionComposition3 f g = {!!}

  SubstitunctionComposition6 : ∀ {𝔭} {𝔓 : Ø 𝔭} →
    𝓡₆,₁
      ¶
      (λ l → ¶)
      (λ l m → Substitunction 𝔓 l m)
      (λ l m f → ¶)
      (λ l m f n → Substitunction 𝔓 m n)
      (λ l m f n g → Substitunction 𝔓 l n)
  𝓡₆,₁.𝓻₆,₁,₀ SubstitunctionComposition6 l m f n g = {!!}

postulate Substitist : ¶ → ¶ → Set

instance

  SubstitistComposition3 : ∀ {l m n} →
    𝓡₃,₁
      (Substitist l m)
      (λ f → Substitist m n)
      (λ f g → Substitist l n)
  𝓡₃,₁.𝓻₃,₁,₀ SubstitistComposition3 f g = {!!}

  SubstitistComposition6 :
    𝓡₆,₁
      ¶
      (λ l → ¶)
      (λ l m → Substitist l m)
      (λ l m f → ¶)
      (λ l m f n → Substitist m n)
      (λ l m f n g → Substitist l n)
  𝓡₆,₁.𝓻₆,₁,₀ SubstitistComposition6 l m f n g = {!!}

test-fc : ∀ {a b c}
         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
         ((x : A) → C (f x))
test-fc g f = g ∘ f
-- unhide g ◆ f
-- g ◇ f
-- unhide g ∙ f
-- g ∘ f

test-substitunction : ∀ {P : Set} {l m} → Substitunction P l m → ∀ {n} → Substitunction P m n → Substitunction P l n
test-substitunction f g = {!!}
-- g ◆ f
-- (λ {w} → g w) ◇ f
-- g ∙ f

test-substitist : ∀ {l m} → Substitist l m → ∀ {n} → Substitist m n → Substitist l n
test-substitist f g = {!!}
-- g ∙ f
-- g ◆ f

test-substitist-associativity : ∀
  {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
  → Proposequality⟦ Substitist _ _ ⟧ ((h ∙ g) ∙ f) (h ∙ g ∙ f)
--  → Proposequality ((h ∙ g) ∙ f) (h ∙ g ∙ f)
test-substitist-associativity = {!!}

postulate
  A B C D : Set
  f : A → B
  g : B → C
  h : C → D

foo : A → D
foo = {!!}
-- unhide h ∙ unhide g ∙ f
-- unhide h ◆ unhide g ◆ f
-- h ◇ g ◇ f
-- h ∘ g ∘ f

postulate
  K L M N : ¶
  f' : Substitunction A K L
  g' : Substitunction A L M
  h' : Substitunction A M N

bar : Substitunction A K N
bar = h' ◆ g' ◆ f'
-- h' ∙ g' ∙ f'

postulate
  f'' : Substitist K L
  g'' : Substitist L M
  h'' : Substitist M N

qux : Substitist K N
qux = h'' ∙ g'' ∙ f''
-- h'' ◆ g'' ◆ f''

-- -- module _ {𝔬₀} (𝔒₀ : Ø 𝔬₀) where
-- --   record 𝓘dentity : Ø 𝔬₀ where
-- --     field ID : 𝑹₀ 𝔒₀

-- --   module _ {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁) where
-- --     module _ {𝔬₂} (𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂) where
-- --       record 𝓒omposition9r : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
-- --         infixr 9 _∙_
-- --         field _∙_ : ∀ (x₀ : 𝔒₀) (x₁ : 𝔒₁ x₀) → 𝔒₂ x₀ x₁

-- -- record 𝓒omposition9r'
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟₀} (B₀ : A → Ø 𝔟₀)
-- --   {𝔟₁} (B₁ : A → Ø 𝔟₁)
-- --   {𝔠} (C : ∀ {a} → B₀ a → B₁ a → Ø 𝔠)
-- --   : Ø 𝔞 ∙̂ 𝔟₀ ∙̂ 𝔟₁ ∙̂ 𝔠 where
-- --   field composer9r' : ∀
-- --                 (a : A)
-- --                 (b₀ : (a : A) → B₀ a)
-- --                 (b₁ : (a : A) → B₁ a)
-- --                 → C (b₀ a) (b₁ a)

-- -- record R4
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟} (B : A → Ø 𝔟)
-- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- --   field r4 : ∀ (a : A)
-- --                (b : B a)
-- --                (c : C b)
-- --                → D c

-- -- record R3'
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟} (B : A → Ø 𝔟)
-- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 where
-- --   field r3' : ∀ (a : A)
-- --                 (b : (a : A) → B a)
-- --                 → C (b a)

-- -- instance

-- --   R3'Composition : ∀
-- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- --     R3'
-- --       A
-- --       (λ x → B x)
-- --       (λ {x} f → (g : ∀ {x} (y : B x) → C y) → C f)
-- --   R3'.r3' R3'Composition x f g = g (f x)

-- -- open R3' ⦃ … ⦄

-- -- infixr 9 _r∙_
-- -- _r∙_ : ∀
-- --   {𝔞} {A : Ø 𝔞}
-- --   {𝔟} {B : A → Ø 𝔟}
-- --   {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --   ⦃ _ : R3' A B C ⦄
-- --   → ∀ (c : {a : A} → (b : B a) → C b)
-- --       (b : (a : A) → B a)
-- --       (a : A)
-- --       → C (b a)
-- -- (c r∙ b) a = r3' a b -- c (b a)

-- -- test-r3' : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- test-r3' g f x = {!!} -- (g r∙ f) x

-- -- record R4'
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟} (B : A → Ø 𝔟)
-- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- --   field r4' : ∀ (a : A)
-- --                 (b : B a)
-- --                 (c : B a → C b)
-- --                 → D (c b)

-- -- record S4
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟} (B : A → Ø 𝔟)
-- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- --   field s4 : ∀ (a : A)
-- --                (b : (a : A) → B a)
-- --                (c : (a : A) → (b : B a) → C b)
-- --                → D (c a (b a))

-- -- open S4 ⦃ … ⦄


-- -- record S4''
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟} (B : A → Ø 𝔟)
-- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- --   field s4'' : ∀ (a : A)
-- --                  (b : (a : A) → B a)
-- --                  (c : (a : A) → C (b a))
-- --                  → D (c a)

-- -- open S4'' ⦃ … ⦄

-- -- test-s4'' : ∀
-- --   {𝔞} (A : Ø 𝔞)
-- --   {𝔟} (B : A → Ø 𝔟)
-- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- --   ⦃ _ : S4'' A B C D ⦄
-- --   → ∀ (a : A)
-- --       (b : (a : A) → B a)
-- --       (c : (a : A) → C (b a))
-- --       → D (c a)
-- -- test-s4'' A B C D a b c = s4'' a b c

-- -- open R4 ⦃ … ⦄

-- -- test-r4s4 : ∀
-- --     {𝔞} {A : Ø 𝔞}
-- --     {𝔟} {B : A → Ø 𝔟}
-- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --     ⦃ _ : R4
-- --             A
-- --             (λ _ → (a : A) → B a)
-- --             (λ {_} _ → {a : A} → (b : B a) → C b)
-- --             (λ {a} {b} c → C (b a)) ⦄
-- --     → (a : A)
-- --       (b : (a : A) → B a)
-- --       (c : {a : A} → (b : B a) → C b)
-- --       → C (b a)
-- -- test-r4s4 ⦃ i ⦄ a b c = r4 a b (λ {w} → c {w})
-- -- {-
-- -- instance
-- --   R4S4 : ∀
-- --     {𝔞} {A : Ø 𝔞}
-- --     {𝔟} {B : A → Ø 𝔟}
-- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --     → R4
-- --         A
-- --         (λ _ → (a : A) → B a)
-- --         (λ {_} _ → {a : A} → (b : B a) → C b)
-- --         (λ {a} {b} c → C (b a))
-- --   R4.r4 R4S4 a b c = c {a} (b a)
-- -- -}
-- -- instance
-- --   R4S4' : ∀
-- --     {𝔞} {A : Ø 𝔞}
-- --     {𝔟} {B : A → Ø 𝔟}
-- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --     → R4
-- --         A
-- --         (λ _ → (a : A) → B a)
-- --         (λ {_} _ → (a : A) → (b : B a) → C b)
-- --         (λ {a} {b} c → C (b a))
-- --   R4.r4 R4S4' a b c = c a (b a)

-- -- test-r4s4' : ∀
-- --     {𝔞} {A : Ø 𝔞}
-- --     {𝔟} {B : A → Ø 𝔟}
-- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --     → (a : A)
-- --       (b : (a : A) → B a)
-- --       (c : {a : A} → (b : B a) → C b)
-- --       → C (b a)
-- -- test-r4s4' a b c = {!!} -- test-r4s4 a b c
-- -- -- r4 a b (λ w → c {w})

-- -- unhide : ∀ {a} {A : Set a} {b} {B : A → Set b} → ({x : A} → B x) → (x : A) → B x
-- -- unhide x x₁ = x {x₁}


-- -- test-r42 : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- test-r42 g f x = r4 x f (unhide g)
-- -- -- s4 x f (λ a b → g b)
-- -- --test-s4 g f x = (g s∙ f) x

-- -- copy-r4s4 : ∀
-- --   {𝔞} {A : Ø 𝔞}
-- --   {𝔟} {B : A → Ø 𝔟}
-- --   {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --   {𝔡} {D : ∀ {a} {b : B a} → C b → Ø 𝔡}
-- --   ⦃ _ : R4 A B C D ⦄
-- --   → ∀ (a : A)
-- --       (b : B a)
-- --       (c : C b)
-- --       → D c
-- -- copy-r4s4 a b c = r4 a b c

-- -- adapt-r4 : ∀
-- --   {𝔞} {A : Ø 𝔞}
-- --   {𝔟} {B : A → Ø 𝔟}
-- --   {𝔠} {C : A → ∀ {a} → B a → Ø 𝔠}
-- --   {𝔡} {D : ∀ {a} {b : B a} → C a b → Ø 𝔡}
-- --   ⦃ _ : R4 A B (λ {x} y → (x' : A) → C x' y) (λ {x} {y} z → D (z x)) ⦄
-- --   → ∀ (a : A)
-- --       (b : B a)
-- --       (c : {x : A} → C x b)
-- --       → D c
-- -- adapt-r4 a b c = r4 a b (unhide c)


-- -- test-r4 : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- test-r4 g f x = adapt-r4 x f g


-- -- infixr 9 _s∙_
-- -- _s∙_ : ∀
-- --   {𝔞} {A : Ø 𝔞}
-- --   {𝔟} {B : A → Ø 𝔟}
-- --   {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- --   {𝔡} {D : ∀ {a} {b : B a} → C b → Ø 𝔡}
-- --   ⦃ _ : S4 A B C D ⦄
-- --   → ∀ (c : {a : A} → (b : B a) → C b)
-- --       (b : (a : A) → B a)
-- --       (a : A)
-- --       → D (c {a} (b a))
-- -- (c s∙ b) a = s4 a b (λ _ → c)
-- -- -- r4 a b (λ w → c {w})
-- --   --

-- -- instance

-- --   S4Composition : ∀
-- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- --     S4
-- --       A
-- --       (λ x → B x)
-- --       (λ {x} f → C f)
-- --       (λ {x} {f} g → C f)
-- --   S4.s4 S4Composition a₁ b₁ c₁ = c₁ a₁ (b₁ a₁)

-- -- test-s4 : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- test-s4 g f x = s4 x f (λ a b → g b)
-- -- --test-s4 g f x = (g s∙ f) x

-- -- {-
-- -- _∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
-- --         (g : ∀ {x} (y : B x) → C x y) (f : ∀ x → B x) →
-- --         ∀ x → C x (f x)
-- -- (g ∘ f) x = g (f x)
-- -- -}

-- -- instance

-- --   FunctionComposition' : ∀
-- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- --     𝓒omposition9r'
-- --       A
-- --       (λ x → (y : B x) → C y)
-- --       (λ x → B x)
-- --       (λ {x} g f → C f)
-- --   𝓒omposition9r'.composer9r' FunctionComposition' x g f = g x (f x)

-- -- {-
-- -- record 𝓒omposition4
-- --   {𝔬₀} (𝔒₀ : Ø 𝔬₀)
-- --   {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁)
-- --   {𝔬₂} (𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂)
-- --   {𝔬₃} (𝔒₃ : ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴ → Ø 𝔬₃)
-- --   : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
-- --   infixr 9 _∙''_
-- --   field
-- --     composition4 : ∀ ⓪ ⑴ ⑵ → 𝔒₃ ⓪ ⑴ ⑵

-- -- instance FunctionComposition4
-- -- -}

-- -- open 𝓘dentity ⦃ … ⦄
-- -- open 𝓒omposition9r ⦃ … ⦄
-- -- open 𝓒omposition9r' ⦃ … ⦄

-- -- composer' : ∀
-- --   {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- --   {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- --   {𝔬₁'} {𝔒₁' : 𝔒₀ → Ø 𝔬₁'}
-- --   {𝔬₂} {𝔒₂ : ∀ {⓪} → 𝔒₁ ⓪ → 𝔒₁' ⓪ → Ø 𝔬₂}
-- --   ⦃ _ : 𝓒omposition9r' 𝔒₀ 𝔒₁ 𝔒₁' 𝔒₂ ⦄
-- --   → (g : {x : 𝔒₀} → 𝔒₁ x)
-- --                 (f : (x : 𝔒₀) → 𝔒₁' x)
-- --                 (x : 𝔒₀)
-- --                 → 𝔒₂ (g {x}) (f x)
-- -- composer' g f x = composer9r' x (λ x → g {x}) f

-- -- test-composer : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- test-composer g f x = composer' g f x


-- -- instance
-- --   IdentityI : ∀ {A : Set} → 𝓘dentity ({x : A} → A)
-- --   𝓘dentity.ID IdentityI {x} = x

-- -- instance

-- --   FunctionComposition : ∀
-- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- --     𝓒omposition9r
-- --       ({x : A} (y : B x) → C y)
-- --       (λ g → (x : A) → B x)
-- --       (λ g f → (x : A) → C (f x))
-- --   𝓒omposition9r._∙_ FunctionComposition g f x = g (f x)

-- -- compos : ∀
-- --   {𝔬} {𝔒 : Ø 𝔬}
-- --   {𝔤} {𝔊 : 𝔒 → Ø 𝔤}
-- --   {𝔣} {𝔉 : 𝔒 → Ø 𝔣}
-- --   {𝔤∙𝔣} {𝔊∙𝔉 : ∀ {o} → {-𝔊 o → -}𝔉 o → Ø 𝔤∙𝔣}
-- --   ⦃ _ : 𝓒omposition9r ({x : 𝔒} → 𝔊 x) (λ g → (x : 𝔒) → 𝔉 x) (λ g f → (x : 𝔒) → 𝔊∙𝔉 {-x-} {-(g {x}) -} (f x)) ⦄
-- --   → (g : ({x : 𝔒} → 𝔊 x))
-- --   → (f : (x : 𝔒) → 𝔉 x)
-- --   → (x : 𝔒) → 𝔊∙𝔉 {-x (g {x})-} (f x)
-- -- compos g f x = (λ {_} → g {_}) ∙ f $ x

-- -- infixr 9 _∘'_
-- -- _∘'_ = compos

-- -- instance

-- --   Function'Composition : ∀
-- --     {a} {A : Ø a} {b} {B : Ø b} {c} {C : Ø c} →
-- --     𝓒omposition9r
-- --       (B → C)
-- --       (λ g → A → B)
-- --       (λ g f → A → C)
-- --   𝓒omposition9r._∙_ Function'Composition g f x = g (f x)

-- -- -- {a} {A : Ø a} {b} {B : A → A → Ø b}
-- -- postulate
-- --   A : Set
-- --   B : A → A → Set

-- -- instance

-- --   TransitiveAB : ∀
-- --     {x y z : A} →
-- --     𝓒omposition9r
-- --       (B y z)
-- --       (λ g → B x y)
-- --       (λ g f → B x z)
-- --   𝓒omposition9r._∙_ TransitiveAB f g = {!!}

-- -- test-c : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- --test-c g f x = _∙'_ g f x -- ({!g!} ∙ f) $ x
-- -- test-c {A = A} {B} {C} g f x = (composer' g f x) --  (λ {_} → g {_}) f) $ x
-- -- --test-c {A = A} {B} {C} g f x = (compos {𝔊∙𝔉 = λ {-o x₁-} x₂ → C x₂} g f $ x) --  (λ {_} → g {_}) f) $ x
-- -- -- test-c g f x = _∙_ (λ {_} → g {_}) f $ x -- ({!g!} ∙ f) $ x
-- -- -- _∙_ ⦃ FunctionComposition ⦄
-- -- --test-c g f x = ((λ {_} → g {_}) ∙ f) $ x

-- -- test-c' : ∀ {a b c}
-- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- --          ((x : A) → C (f x))
-- -- test-c' g f x = (g ∘ f) x

-- -- test-c2 : ∀ {x y z} → B y z → B x y → B x z
-- -- test-c2 g f = g ∙ f

-- -- test-c3 : ∀ {A B C : Set} (g : B → C) (f : A → B) → A → C
-- -- test-c3 g f = g ∙ f

-- -- test-c3' : ∀ {A B C : Set} (g : B → C) (f : A → B) → A → C
-- -- test-c3' g f = g ∘ f






-- -- -- comp! : ∀ {a b c}
-- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- --         ((x : A) → C (f x))
-- -- -- comp! {a} {b} {c} {A} {B} {C} g f x = 𝓻₄,₁,₀ x f (λ {_} → g {_})



-- -- -- module _
-- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂} {𝔮₁}
-- -- --     (𝔔₁ : ∀ x → 𝔒₂ x → Ø 𝔮₁)
-- -- --   {𝔬₃} {𝔒₃ : ∀ {x} → 𝔒₂ x → Ø 𝔬₃} {𝔮₂}
-- -- --     (𝔔₂ : ∀ {x} (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₂)
-- -- --   {𝔮₃}
-- -- --     (𝔔₃ : (x : 𝔒₁) → ∀ {y : 𝔒₂ x} → 𝔒₃ y → Ø 𝔮₃)
-- -- --   where
-- -- --   Transitive! = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ y) (λ x _ _ z _ → 𝔔₃ x z)
-- -- --   𝓣ransitive! = ∀ {x} {y : 𝔒₂ x} → 𝔔₁ x y → ∀ {z : 𝔒₃ y} → 𝔔₂ y z → 𝔔₃ x z
-- -- --   𝓽ransitive! = ⦃ _ : Transitive! ⦄ → 𝓣ransitive!

-- -- -- {-
-- -- -- instance

-- -- --   CT1 : ∀ {a b c} →
-- -- --     Transitive! {𝔒₁ = Ø a} {𝔒₂ = λ A → A → Ø b}
-- -- --       (λ A B → (x : A) → B x) {𝔒₃ = λ {A} B → {x : A} → B x → Ø c} -- (x : A) → B x
-- -- --       (λ {A} B C → {x : A} (y : B x) → C y )
-- -- --       (λ A {B} C → (x : A) → C {!!})
-- -- --   CT1 = {!!}
-- -- -- -}

-- -- -- module _
-- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₁}
-- -- --     (𝔔₁ : 𝔒₁ → 𝔒₂ → Ø 𝔮₁)
-- -- --   {𝔬₃} {𝔒₃ : Ø 𝔬₃} {𝔮₂}
-- -- --     (𝔔₂ : 𝔒₂ → 𝔒₃ → Ø 𝔮₂)
-- -- --   {𝔮₃}
-- -- --     (𝔔₃ : 𝔒₁ → 𝔒₃ → Ø 𝔮₃)
-- -- --   where
-- -- --   Transitive!' = Transitive! 𝔔₁ 𝔔₂ (λ x → 𝔔₃ x)
-- -- --   Transitive' = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ y) (λ x _ _ z _ → 𝔔₃ x z)
-- -- --   𝓣ransitive' = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- --   𝓽ransitive' = ⦃ _ : Transitive' ⦄ → 𝓣ransitive'

-- -- -- module _
-- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂} {𝔮₁}
-- -- --     (𝔔₁ : (x : 𝔒₁) → 𝔒₂ x → Ø 𝔮₁)
-- -- --   {𝔬₃} {𝔒₃ : ∀ {x} → 𝔒₂ x → Ø 𝔬₃} {𝔮₂}
-- -- --     (𝔔₂ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₂)
-- -- --   {𝔮₃}
-- -- --     (𝔔₃ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₃)
-- -- --   where
-- -- --   Transitive'' = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ _ y) (λ x _ _ z _ → 𝔔₃ x _ z)
-- -- -- --  𝓣ransitive'' = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- --  𝓽ransitive'' = ⦃ _ : Transitive'' ⦄ → 𝓣ransitive''

-- -- -- instance Transitive''Function : ∀ {𝔬 𝔭 𝔮} →
-- -- --            Transitive''
-- -- --              {𝔒₁ = Ø 𝔬} {𝔒₂ = λ x → Ø 𝔭}
-- -- --                (λ x y → x → y)
-- -- --              {𝔒₃ = λ {x} y → Ø 𝔮}
-- -- --                (λ x y z → y → z)
-- -- --                (λ x y z → x → z)
-- -- -- 𝓡₆,₁.𝓻₆,₁,₀ Transitive''Function ⓪ ⑴ f ⑶ g x = {!!} -- g (f x)

-- -- -- module _ where
-- -- -- -- {-
-- -- -- --   A : Set a
-- -- -- --   B : A → Set b
-- -- -- --   f : (x : A) → B x
-- -- -- --   C : {x : A} → B x → Set c
-- -- -- --   g : {x : A} (y : B x) → C y
-- -- -- --   Goal : (x : A) → C (f x)
-- -- -- -- -}

-- -- -- -- CompFunction = {!!}

-- -- -- instance

-- -- --   CompFunction : ∀
-- -- --     {a b c} →
-- -- --     𝓡₆,₁
-- -- --       (Ø a)
-- -- --       (λ A → A → Ø b)
-- -- --       (λ A B → (x : A) → B x)
-- -- --       (λ A B f → {x : A} → B x → Ø c)
-- -- --       (λ A B f C → {x : A} (y : B x) → C y)
-- -- --       (λ A B f C g → (x : A) → C (f x))
-- -- --   𝓡₆,₁.𝓻₆,₁,₀ CompFunction A B f C g x = g (f x)

-- -- -- transitive : ∀
-- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- --   ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄
-- -- --   → ∀ {⓪ ⑴} ⑵ {⑶} ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
-- -- -- transitive ⑵ = 𝓻₆,₁,₀ _ _ ⑵ _

-- -- -- _∘'_ : ∀ {a b c}
-- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- --         ((x : A) → C (f x))
-- -- -- _∘'_ {a} {b} {c} {A} {B} {C} g f = 𝓻₆,₁,₀ _ _ _ _ (λ {_} → g {_})

-- -- -- instance

-- -- --   CompFunction' : ∀
-- -- --     {a b c} →
-- -- --     𝓡₇,₁
-- -- --       (Ø a)
-- -- --       (λ A → A → Ø b)
-- -- --       (λ A B → (x : A) → B x)
-- -- --       (λ A B f → {x : A} → B x → Ø c)
-- -- --       (λ A B f C → {x : A} (y : B x) → C y)
-- -- --       (λ A B f C g → A)
-- -- --       (λ A B f C g x → C (f x))
-- -- --   𝓡₇,₁.𝓻₇,₁,₀ CompFunction' A B f C g x = g (f x)

-- -- -- _∘''_ : ∀ {a b c}
-- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- --         ((x : A) → C (f x))
-- -- -- _∘''_ {a} {b} {c} {A} {B} {C} g f x = 𝓻₇,₁,₀ A B f (λ {v} → C {v}) (λ {v} → g {v}) x -- transitive ⦃ Transitive''Function ⦄ ? ? -- f g -- g f

-- -- -- instance

-- -- --   CompFunction6' : ∀
-- -- --     {a b c} →
-- -- --     𝓡₆,₁
-- -- --       (Ø a)
-- -- --       (λ A → A → Ø b)
-- -- --       (λ A B → (x : A) → B x)
-- -- --       (λ A B f → {x : A} → B x → Ø c)
-- -- --       (λ A B f C → {x : A} (y : B x) → C y)
-- -- --       (λ A B f C g → (x : A) → C (f x))
-- -- --   𝓡₆,₁.𝓻₆,₁,₀ CompFunction6' A B f C g x = g (f x)

-- -- -- _∘6'_ : ∀ {a b c}
-- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- --         ((x : A) → C (f x))
-- -- -- _∘6'_ {a} {b} {c} {A} {B} {C} g f =
-- -- --   transitive f (λ {v} → g {v})

-- -- --   -- 𝓻₆,₁,₀ A B f (λ {v} → C {v}) (λ {v} → g {v}) -- transitive ⦃ Transitive''Function ⦄ ? ? -- f g -- g f

-- -- -- -- module _
-- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂} {𝔮₁}
-- -- -- --     (𝔔₁ : (x : 𝔒₁) → 𝔒₂ x → Ø 𝔮₁)
-- -- -- --   {𝔬₃} {𝔒₃ : ∀ {x} → 𝔒₂ x → Ø 𝔬₃} {𝔮₂}
-- -- -- --     (𝔔₂ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₂)
-- -- -- --   {𝔮₃}
-- -- -- --     (𝔔₃ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₃)
-- -- -- --   where
-- -- -- --   Comp = 𝓡₆,₁ 𝔒₁ (λ A → 𝔒₂ A) 𝔔₁ _ (λ _ y 𝔔₁xy → 𝔔₂ _ y) (λ _ _ f z _ → 𝔔₃ _ _ z)
-- -- -- -- --  𝓣ransitive'' = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- --  𝓽ransitive'' = ⦃ _ : Transitive'' ⦄ → 𝓣ransitive''

-- -- -- -- -- instance CompFunction : ∀ {a b c} →
-- -- -- -- --            Comp
-- -- -- -- --              {𝔒₁ = Ø a} {𝔒₂ = λ A → A → Ø b}
-- -- -- -- --                (λ A B → (x : A) → B x)
-- -- -- -- --              {𝔒₃ = λ {A} B → {x : A} → B x → Ø c}
-- -- -- -- --                (λ A B C → {x : A} → (y : B x) → C y)
-- -- -- -- --                (λ A B C → {!!})
-- -- -- -- -- CompFunction = {!!}
-- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ CompFunction A B f C g x = {!!} -- g (f x)
-- -- -- -- -- -- A ⑴ f ⑶ g x

-- -- -- -- -- -- module _
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- --     (𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃)
-- -- -- -- -- --   where
-- -- -- -- -- --   Transitive = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ y) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- --   𝓣ransitive = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- --   𝓽ransitive = ⦃ _ : Transitive ⦄ → 𝓣ransitive

-- -- -- -- -- -- --instance TransitiveFunction : ∀ {𝔬} {𝔒 : Ø 𝔬} → Transitive {𝔮₁ = 𝔬} (λ x y → x → y) (λ x y → x → y) (λ x y → x → y)
-- -- -- -- -- -- --𝓡₆,₁.𝓻₆,₁,₀ TransitiveFunction ⓪ ⑴ f ⑶ g x = g (f x)

-- -- -- -- -- -- instance Transitive'Function : ∀ {𝔬} → Transitive' {𝔮₁ = 𝔬} (λ (x : Ø 𝔬) (y : Ø 𝔬) → x → y) {𝔮₂ = 𝔬} (λ x (y : Ø 𝔬) → x → y) {𝔮₃ = 𝔬} (λ x y → x → y)
-- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ Transitive'Function ⓪ ⑴ f ⑶ g x = g (f x)

-- -- -- -- -- -- test-trans' : (f : ¶ → 𝟙) (g : 𝟙 → 𝟘) → ¶ → 𝟘
-- -- -- -- -- -- test-trans' f g = transitive f g


-- -- -- -- -- -- module _
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- --   where
-- -- -- -- -- --   Reflexive = 𝓡₂,₁ _ (λ x → 𝔔 x x)
-- -- -- -- -- --   Antireflexive = 𝓡₂,₁ _ (λ x → 𝔔 x x → 𝟘)
-- -- -- -- -- --   Symmetric = 𝓡₄,₁ _ _ 𝔔 (λ x y _ → 𝔔 y x)
-- -- -- -- -- --   𝓢ymmetric = ∀ {x y} → 𝔔 x y → 𝔔 y x
-- -- -- -- -- --   Antisymmetric = 𝓡₄,₁ _ _ 𝔔 (λ x y _ → 𝔔 y x → 𝟘)
-- -- -- -- -- --   𝓐ntisymmetric = ∀ {x y} → 𝔔 x y → 𝔔 y x → 𝟘
-- -- -- -- -- --   Transitive′ = Transitive 𝔔 𝔔 𝔔
-- -- -- -- -- --   𝓣ransitive′ = 𝓣ransitive 𝔔 𝔔 𝔔
-- -- -- -- -- --   𝓽ransitive′ = ⦃ _ : Transitive′ ⦄ → 𝓣ransitive′
-- -- -- -- -- --   record Equivalence : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- --     field ⦃ Reflexive⌶ ⦄ : Reflexive
-- -- -- -- -- --     field ⦃ Symmetric⌶ ⦄ : Symmetric
-- -- -- -- -- --     field ⦃ Transitive⌶ ⦄ : Transitive′
-- -- -- -- -- --   record StrictOrdering : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- --     field ⦃ Antireflexive⌶ ⦄ : Antireflexive
-- -- -- -- -- --     field ⦃ Antisymmetric⌶ ⦄ : Antisymmetric
-- -- -- -- -- --     field ⦃ Transitive⌶ ⦄ : Transitive′

-- -- -- -- -- -- instance ReflexiveProposextensequality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → Reflexive Proposextensequality⟦ 𝔓 ⟧
-- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ ReflexiveProposextensequality _ _ = ∅

-- -- -- -- -- -- instance ReflexiveProposequality : ∀ {𝔬} {𝔒 : Ø 𝔬} → Reflexive Proposequality⟦ 𝔒 ⟧
-- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ ReflexiveProposequality _ = ∅

-- -- -- -- -- -- instance AntireflexiveProposantiequality : ∀ {𝔬} {𝔒 : Ø 𝔬} → Antireflexive Proposantiequality⟦ 𝔒 ⟧
-- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ AntireflexiveProposantiequality ⓪ x = x ∅

-- -- -- -- -- -- module _
-- -- -- -- -- --   {𝔬} (𝔒 : Ø 𝔬)
-- -- -- -- -- --   where
-- -- -- -- -- --   Next = 𝓡₂,₁ 𝔒 (λ _ → 𝔒)

-- -- -- -- -- -- foo = {!Next ¶!}
-- -- -- -- -- -- bar = {!Reflexive Proposequality⟦ ¶ ⟧!}

-- -- -- -- -- -- instance Next¶ : Next ¶
-- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ Next¶ = ↑_

-- -- -- -- -- -- next : ∀
-- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- --   ⦃ _ : 𝓡₂,₁ 𝔒₀ 𝔒₁ ⦄
-- -- -- -- -- --   → ∀ ⓪ → 𝔒₁ ⓪
-- -- -- -- -- -- next = 𝓻₂,₁,₀

-- -- -- -- -- -- reflexive : ∀
-- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- --   ⦃ _ : 𝓡₂,₁ 𝔒₀ 𝔒₁ ⦄
-- -- -- -- -- --   → ∀ {⓪} → 𝔒₁ ⓪
-- -- -- -- -- -- reflexive {⓪} = 𝓻₂,₁,₀ _

-- -- -- -- -- -- test-next₁ : ¶
-- -- -- -- -- -- test-next₁ = next 3

-- -- -- -- -- -- test-reflexive₁ : ∀ (x : ¶) → x ≡ x
-- -- -- -- -- -- test-reflexive₁ = reflexive

-- -- -- -- -- -- test-reflexive₂ : ∀ {f : ¶ → ¶} → f ≡̇ f
-- -- -- -- -- -- test-reflexive₂ = reflexive

-- -- -- -- -- -- test-antireflexive₁ : 3 ≢ 3 → 𝟘
-- -- -- -- -- -- test-antireflexive₁ = next _

-- -- -- -- -- -- symmetric : ∀
-- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- --   ⦃ _ : 𝓡₄,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄
-- -- -- -- -- --   → ∀ {⓪ ⑴} ⑵ → 𝔒₃ ⓪ ⑴ ⑵
-- -- -- -- -- -- symmetric = 𝓻₄,₁,₀ _ _

-- -- -- -- -- -- module _
-- -- -- -- -- --   𝔬 𝔮
-- -- -- -- -- --   where
-- -- -- -- -- --   Transitivity′ =
-- -- -- -- -- --     𝓡₉,₁
-- -- -- -- -- --       (Ø 𝔬)
-- -- -- -- -- --       (λ 𝔒 → 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- --       (λ _ 𝔔 → Transitive′ 𝔔)
-- -- -- -- -- --       _ _ (λ _ 𝔔 _ → 𝔔)
-- -- -- -- -- --       _ (λ _ 𝔔 _ _ y _ → 𝔔 y)
-- -- -- -- -- --       (λ _ 𝔔 _ x _ _ z _ → 𝔔 x z)

-- -- -- -- -- -- -- infixr 9 _∙_
-- -- -- -- -- -- transitivity′ : ∀
-- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- --   {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- --   {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- --   {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- --   ⦃ _ : 𝓡₉,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ ⦄ →
-- -- -- -- -- --   ∀ {⓪ ⑴} ⦃ ⑵ ⦄ {⑶ ⑷} ⑸ {⑹} ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺
-- -- -- -- -- -- transitivity′ ⑸ = 𝓻₉,₁,₀ _ _ _ _ _ ⑸ _

-- -- -- -- -- -- module _
-- -- -- -- -- --   {𝔬} (𝔒 : Ø 𝔬) 𝔮
-- -- -- -- -- --   where
-- -- -- -- -- --   Relation = 𝓡₃,₁ 𝔒 (λ _ → 𝔒) (λ _ _ → Ø 𝔮)
-- -- -- -- -- --   𝓡elation = 𝔒 → 𝔒 → Ø 𝔮

-- -- -- -- -- --   record Equivalent : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- --     infix 4 _≋_
-- -- -- -- -- --     field _≋_ : 𝓡elation
-- -- -- -- -- --     field Equivalence⌶ : Equivalence _≋_

-- -- -- -- -- --   record StrictOrder : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- --     infix 6 _<_
-- -- -- -- -- --     field _<_ : 𝓡elation
-- -- -- -- -- --     field StrictOrdering⌶ : StrictOrdering _<_

-- -- -- -- -- -- relation : ∀
-- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- --   ⦃ _ : 𝓡₃,₁ 𝔒₀ 𝔒₁ 𝔒₂ ⦄
-- -- -- -- -- --   → ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴
-- -- -- -- -- -- relation = 𝓻₃,₁,₀

-- -- -- -- -- -- open Equivalence ⦃ … ⦄
-- -- -- -- -- -- open Equivalent ⦃ … ⦄
-- -- -- -- -- -- open StrictOrder ⦃ … ⦄

-- -- -- -- -- -- module _
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- --     {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- --   {𝔮}
-- -- -- -- -- --     (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- --   where
-- -- -- -- -- --   Associative = 𝓡₈,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y) (λ _ _ f _ g _ h → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h))
-- -- -- -- -- --   𝓐ssociative = ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h)

-- -- -- -- -- -- module _
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- --     (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₃)
-- -- -- -- -- --   where
-- -- -- -- -- --   Extensional = 𝓡₁₀,₁ _ _ _ _ (λ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂))
-- -- -- -- -- --   𝓔xtensional = ∀ {x y} {f₁ f₂ : 𝔐 x y} → 𝔔₁ f₁ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → 𝔔₂ g₁ g₂ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂)

-- -- -- -- -- -- --  record EXTENSIONAL (x : 𝔒) (y : ∀ x → (λ _ → 𝔒) x) (f₁ : ∀ x y → (λ x y → 𝔐 x y) x y) : Ø _ where
-- -- -- -- -- -- {-
-- -- -- -- -- --   record EXTENSIONAL (x : 𝔒) (y : ∀ x → 𝔒) (f₁ : ∀ x y → 𝔐 x y) (f₂ : 𝔐 x y) (𝔔₁f₁f₂ : 𝔔₁ f₁ f₂) (z : 𝔒) (g₁ : 𝔐 y z) (g₂ : 𝔐 y z) (𝔔₂g₁g₂ : 𝔔₂ g₁ g₂) (ext : 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂))
-- -- -- -- -- --     : Ø _ where
-- -- -- -- -- -- -}
-- -- -- -- -- -- {-
-- -- -- -- -- --   record EXTENSIONAL (x : 𝔒) (y : 𝔒) (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) (𝔔₁f₁f₂ : 𝔔₁ f₁ f₂) (z : 𝔒) (g₁ : 𝔐 y z) (g₂ : 𝔐 y z) (𝔔₂g₁g₂ : 𝔔₂ g₁ g₂)
-- -- -- -- -- --     : Ø _ where
-- -- -- -- -- -- --    field
-- -- -- -- -- -- --      extensional : ∀ {x y} → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂)

-- -- -- -- -- --   record EXTENSIONAL'
-- -- -- -- -- --     {𝔬₀} (𝔒₀ : Ø 𝔬₀)
-- -- -- -- -- --     {𝔬₁} (𝔒₁ :
-- -- -- -- -- --     (y : 𝔒) (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) (𝔔₁f₁f₂ : 𝔔₁ f₁ f₂) (z : 𝔒) (g₁ : 𝔐 y z) (g₂ : 𝔐 y z) (𝔔₂g₁g₂ : 𝔔₂ g₁ g₂)
-- -- -- -- -- --     : Ø _ where
-- -- -- -- -- -- -}

-- -- -- -- -- -- --  record EXTENSIONAL _ _ _ _ (_ : ∀ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (_ : ∀ _ y _ _ _ z → 𝔐 y z) _ (_ : ∀ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (_ : ∀ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂))
-- -- -- -- -- -- --    : Ø _ where
-- -- -- -- -- --   -- _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂)) : Ø _ where



-- -- -- -- -- -- -- module _
-- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- --     (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 y z → Ø 𝔮₃)
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   𝓔xtensionality = 𝓡₉ _ _ _ _ (λ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- --   𝓮xtensionality = ∀ {x y} {f₁ f₂ : 𝔐 x y} → 𝔔₁ f₁ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → 𝔔₂ g₁ g₂ → 𝔔₃ f₁ f₂ g₁ g₂
-- -- -- -- -- -- --   record Extensionality : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where field extensionality : 𝓮xtensionality
-- -- -- -- -- -- --   open Extensionality ⦃ … ⦄ public

-- -- -- -- -- -- -- postulate
-- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- --   B : Set
-- -- -- -- -- -- --   instance eqA : Equivalent A ∅̂
-- -- -- -- -- -- --   instance eqB : Equivalent B ∅̂
-- -- -- -- -- -- --   instance refA : Reflexive {𝔒 = A} _≋_
-- -- -- -- -- -- --   instance refB : Reflexive {𝔒 = B} _≋_
-- -- -- -- -- -- --   --instance eqB : Equivalent B ∅̂
-- -- -- -- -- -- --   --instance soA : StrictOrder A ∅̂
-- -- -- -- -- -- --   --instance soB : StrictOrder B ∅̂

-- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- --testA= x y = reflexive ⦃ eqA .Equivalent.Equivalence⌶ .Equivalence.Reflexive⌶ ⦄
-- -- -- -- -- -- -- testA= x y = reflexive
-- -- -- -- -- -- -- -- 𝓻₂,₁,₀


-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- {𝔬₉} {𝔒₉ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → Ø 𝔬₉}

-- -- -- -- -- -- -- 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ 𝔒₉
-- -- -- -- -- -- -- ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ ⑻
-- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- --   𝔬 𝔮
-- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- --  𝓔quality = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓡elation 𝔔


-- -- -- -- -- -- -- -- -- --  record Equivalent : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- --    field ⦃ Relation⌶ ⦄ : Relation
-- -- -- -- -- -- -- -- -- --    field ⦃ Equivalence⌶ ⦄ : Equivalence 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- --   record Equivalent : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- --     infix 4 _≋_
-- -- -- -- -- -- -- -- --     field _≋_ : 𝓡elation
-- -- -- -- -- -- -- -- --     field instance Equivalence⌶ : Equivalence _≋_

-- -- -- -- -- -- -- -- --   Equality :
-- -- -- -- -- -- -- -- --   𝓔quality = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓡elation 𝔔

-- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- --   B : Set
-- -- -- -- -- -- -- -- --   instance eqA : Equivalent A ∅̂
-- -- -- -- -- -- -- -- --   instance eqB : Equivalent B ∅̂

-- -- -- -- -- -- -- -- -- open Equivalent ⦃ … ⦄

-- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- testA= x y = 𝓻₂,₁,₀ x
-- -- -- -- -- -- -- -- -- -- 𝓻₂,₁,₀

-- -- -- -- -- -- -- -- -- --  instance orA : StrictOrdering A
-- -- -- -- -- -- -- -- -- --  instance orB : StrictOrdering B
-- -- -- -- -- -- -- -- --   -- relA< : Relation A ∅̂
-- -- -- -- -- -- -- -- --   -- relA= : Relation A ∅̂
-- -- -- -- -- -- -- -- -- --  instance ltI : Antisymmetric (𝓻₃,₁,₀ ⦃ relA< ⦄)
-- -- -- -- -- -- -- -- -- --  instance eqI : Symmetric (𝓻₃,₁,₀ ⦃ relA= ⦄)


-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- --   LA1 LA2 : List A
-- -- -- -- -- -- -- -- -- --   Nat : Set

-- -- -- -- -- -- -- -- -- -- want:

-- -- -- -- -- -- -- -- -- --   : (x y : Nat) → x ≋ y
-- -- -- -- -- -- -- -- -- --   : (x y : Nat) → x < y
-- -- -- -- -- -- -- -- -- --   : (x y : List A) → x < (x + y)
-- -- -- -- -- -- -- -- -- --   : (x y : List A) → x < (x + y)
-- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} (𝔒 : Ø 𝔬) 𝔮
-- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- --   Equality = 𝓡₆,₁ (Relation 𝔒 𝔮) (λ _ → 𝔒 → 𝔒 → Ø 𝔮) (λ _ 𝔔 → Symmetric 𝔔) (λ _ _ _ → 𝔒) (λ _ _ _ _ → 𝔒) (λ _ 𝔔 _ → 𝔔)
-- -- -- -- -- -- -- -- -- -- --  𝓔quality = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Symmetric 𝔔 ⦄ → 𝓡elation 𝔔

-- -- -- -- -- -- -- -- -- -- _≋_ : ∀
-- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄ →
-- -- -- -- -- -- -- -- -- --   ∀ {{⓪}} {⑴} {{⑵}} ⑶ ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
-- -- -- -- -- -- -- -- -- -- _≋_ = 𝓻₆,₁,₀ _ _ _

-- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- --   instance relA< : Relation A ∅̂
-- -- -- -- -- -- -- -- -- --   instance relA= : Relation A ∅̂
-- -- -- -- -- -- -- -- -- --   instance ltI : Antisymmetric (𝓻₃,₁,₀ ⦃ relA< ⦄)
-- -- -- -- -- -- -- -- -- --   instance eqI : Symmetric (𝓻₃,₁,₀ ⦃ relA= ⦄)

-- -- -- -- -- -- -- -- -- -- instance ⌶Equality : Equality A ∅̂
-- -- -- -- -- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ ⌶Equality r q s x y = {!𝓻₃,₁,₀ ⦃ r ⦄!} -- 𝓻₃,₁,₀ ⦃ r ⦄ x y

-- -- -- -- -- -- -- -- -- -- -- instance ⌶Equality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮} → Equality 𝔒 𝔮
-- -- -- -- -- -- -- -- -- -- -- 𝓡₅,₁.𝓻₅,₁,₀ ⌶Equality r s x y = {!!} -- 𝓻₃,₁,₀ ⦃ r ⦄ x y


-- -- -- -- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- -- -- -- testA= x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- _≤_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Relation 𝔒 𝔮 ⦄
-- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Antisymmetric 𝓻₃,₁,₀ ⦄
-- -- -- -- -- -- -- -- -- -- -- -- --       → 𝔒 → 𝔒 → Ø 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- _≤_ = 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Relation 𝔒 𝔮 ⦄
-- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Symmetric 𝓻₃,₁,₀ ⦄
-- -- -- -- -- -- -- -- -- -- -- -- --       → 𝔒 → 𝔒 → Ø 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ = 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- -- -- -- --   instance relA< : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- --   instance relA= : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- --   instance ltI : Antisymmetric (𝓻₃,₁,₀ ⦃ relA< ⦄)
-- -- -- -- -- -- -- -- -- -- -- -- --   instance eqI : Symmetric (𝓻₃,₁,₀ ⦃ relA= ⦄)

-- -- -- -- -- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- -- -- -- -- testA= x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- testA< : (x y : A) → x ≤ x
-- -- -- -- -- -- -- -- -- -- -- -- -- testA< x y = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- ∀ {x y} → 𝔔 x y → 𝔔 x y → Ø 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- --     {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   Associative = 𝓡₈,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y) (λ _ _ f _ g _ h → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h))
-- -- -- -- -- -- -- -- -- -- -- -- --   𝓐ssociative = ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h)

-- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- --   𝔬 𝔪 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   Associativity = 𝓡₁₃,₁
-- -- -- -- -- -- -- -- -- -- -- -- --   𝓐ssociativity = λ
-- -- -- -- -- -- -- -- -- -- -- -- --     {𝔒 : Ø 𝔬} {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- --       (𝒯 : ∀ {x y} → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 x z)
-- -- -- -- -- -- -- -- -- -- -- -- --       (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : Associative 𝒯 𝔔 ⦄
-- -- -- -- -- -- -- -- -- -- -- -- --       → 𝓐ssociative 𝒯 𝔔

-- -- -- -- -- -- -- -- -- -- -- -- --   Transitivity = 𝓡₉,₁ (Ø 𝔬) (λ 𝔒 → 𝔒 → 𝔒 → Ø 𝔮) (λ _ 𝔔 → Transitive′ 𝔔) _ _ (λ _ 𝔔 _ → 𝔔) _ (λ _ 𝔔 _ _ y _ → 𝔔 y) (λ _ 𝔔 _ x _ _ z _ → 𝔔 x z)
-- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓣ransitive′ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- --     {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝒯 : ∀ {x y} → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 x z)
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- --   𝔬 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   Transitivity = 𝓡₉,₁ (Ø 𝔬) (λ 𝔒 → 𝔒 → 𝔒 → Ø 𝔮) (λ _ 𝔔 → Transitive′ 𝔔) _ _ (λ _ 𝔔 _ → 𝔔) _ (λ _ 𝔔 _ _ y _ → 𝔔 y) (λ _ 𝔔 _C x _ _ z _ → 𝔔 x z)
-- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓣ransitive′ 𝔔

-- -- -- -- -- -- -- -- -- -- -- -- -- ➊ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₂,₁ 𝔒₀ 𝔒₁ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪} → 𝔒₁ ⓪
-- -- -- -- -- -- -- -- -- -- -- -- -- ➊ = 𝓻₂,₁,₀ _

-- -- -- -- -- -- -- -- -- -- -- -- -- ➋ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₄,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⑵ → 𝔒₃ ⓪ ⑴ ⑵
-- -- -- -- -- -- -- -- -- -- -- -- -- ➋ = 𝓻₄,₁,₀ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- infixl 21 _⟨➋➊⟩_
-- -- -- -- -- -- -- -- -- -- -- -- -- _⟨➋➊⟩_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⑵ {⑶} ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
-- -- -- -- -- -- -- -- -- -- -- -- -- _⟨➋➊⟩_ ⑵ = 𝓻₆,₁,₀ _ _ ⑵ _

-- -- -- -- -- -- -- -- -- -- -- -- -- infixr 9 _∙_
-- -- -- -- -- -- -- -- -- -- -- -- -- _∙_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₉,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⦃ ⑵ ⦄ {⑶ ⑷} ⑸ {⑹} ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺
-- -- -- -- -- -- -- -- -- -- -- -- -- _∙_ ⑸ = 𝓻₉,₁,₀ _ _ _ _ _ ⑸ _

-- -- -- -- -- -- -- -- -- -- -- -- -- instance ⌶Transitivity : ∀ {𝔬} {𝔮} → Transitivity 𝔬 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝓡₉,₁.𝓻₉,₁,₀ ⌶Transitivity ⓪ _≋_ ⑵ x y x≋y z y≋z = let instance _ = ⑵ in x≋y ⟨➋➊⟩ y≋z

-- -- -- -- -- -- -- -- -- -- -- -- -- module TestTransitivityInTransitive′
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ : 𝓣ransitivity _ _ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ xy yz = xy ⟨➋➊⟩ yz

-- -- -- -- -- -- -- -- -- -- -- -- --   test∙ : 𝓣ransitivity _ _ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- --   test∙ xy yz = xy ∙ yz

-- -- -- -- -- -- -- -- -- -- -- -- --   test : 𝓣ransitivity _ _ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- --   test xy yz = {!_∙_!}

-- -- -- -- -- -- -- -- -- -- -- -- -- module TestTransitivityInTransitive
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ : ⦃ _ : Transitive 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓣ransitive 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ xy yz = xy ⟨➋➊⟩ yz

-- -- -- -- -- -- -- -- -- -- -- -- --   test∙ : ⦃ _ : Transitive 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓣ransitive 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- --   test∙ xy yz = {!xy ∙ yz!} -- fails, correctly. _∙_

-- -- -- -- -- -- -- -- -- -- -- -- --   test : ⦃ _ : Transitive 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓣ransitive 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- --   test xy yz = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪} {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝒯
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Associativity = 𝓡₂,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Symmetricity = 𝓡₄,₁ _ _ 𝔔 (λ x y _ → 𝔔 y x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Transitivity = 𝓡₆,₁ _ _ 𝔔 _ (λ _ y _ → 𝔔 y) (λ x _ _ z _ → 𝔔 x z)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₉} {𝔒₉ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → Ø 𝔬₉}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ 𝔒₉
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ ⑻
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓓iagonal = 𝓡₂,₁ _ (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓓iagonal' = ∀ {x} → 𝔔 x x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓓iagonal3 : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → Ø _ -- 𝔬 ∙̂ 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓓iagonal3 𝔔 = 𝓡₂,₁ _ (_ ∋ λ x → 𝔔 x x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- infix 4 _≋_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₄,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄ → ∀ {x₀ x₁} x₂ → 𝔒₃ x₀ x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ = 𝓻₄,₁,₀ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓡elation₁ = 𝓡₂,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓻elation₁ = ∀ x y → 𝔔 x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔒 : Ø 𝔬)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓟rop₂ = 𝓡₂ 𝔒 (λ _ → 𝔒) (λ _ _ → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓹rop₂ = 𝔒 → 𝔒 → Ø 𝔮

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- prop
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Prop₂ : Ø 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓟rop₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     prop₂ : 𝓹rop₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     prop₂ = 𝓻₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Prop₂ ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔒 : Ø 𝔬)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓤nit = 𝓡₀ 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓾nit = 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Unit : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓤nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit : 𝓾nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit = 𝓻₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓤nit² = 𝓡₀,₂ 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Unit² : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓤nit²
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₀ : 𝓾nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₀ = 𝓻₀,₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₁ : 𝓾nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₁ = 𝓻₀,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓶agma = 𝔒 → 𝔒 → 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓜agma₁ = 𝓡₂ 𝔒 (λ _ → 𝔒) (λ _ _ → 𝔒)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Magma₁ : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓜agma₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     infixr 9 _∙_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _∙_ : 𝓶agma
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _∙_ = 𝓻₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓜agma₂ = 𝓡₂,₂ 𝔒 (λ _ → 𝔒) (λ _ _ → 𝔒)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Magma₂ : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓜agma₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     infixl 6 _+_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _+_ : 𝓶agma
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _+_ = 𝓻₂,₂,₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     infixl 8 _*_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _*_ : 𝓶agma
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _*_ = 𝓻₂,₂,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Unit ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Unit² ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Magma₁ ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Magma₂ ⦃ … ⦄ public hiding (⋆)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓓iagonal = 𝓡₁ _ (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓭iagonal = ∀ {x} → 𝔔 x x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Diagonal : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓓iagonal
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     diagonal : 𝓭iagonal
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     diagonal = 𝓻₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Diagonal ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μ : 𝔒₁ → 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓡emap = 𝓡₃ _ _ (λ x y → 𝔔₁ x y) (λ x y _ → 𝔔₂ (μ x) (μ y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓻emap = ∀ {x y} → 𝔔₁ x y → 𝔔₂ (μ x) (μ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Remap : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓡emap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap : 𝓻emap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap = 𝓻₃ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open 𝓡₃ ⋆ public using () renaming (r3' to remap!)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open 𝓡₃ ⦃ … ⦄ public using () renaming (r3' to OhRemap)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     threemap' : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₂} {𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₃} {𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : 𝓡₃ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄ → ∀ {x₀ x₁} x₂ → 𝔒₃ x₀ x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     threemap' = 𝓻₃ _ _



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Remap ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {μ : 𝔒₁ → 𝔒₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   REMAP : ⦃ _ : 𝓡emap 𝔔₁ 𝔔₂ μ ⦄ → 𝓻emap 𝔔₁ 𝔔₂ μ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   REMAP = 𝓻₃ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μ : 𝔒₁ → 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓡emap2 = 𝓡₄ μ _ _ (λ _ x y → 𝔔₁ x y) (λ _ x y _ → 𝔔₂ (μ x) (μ y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓻emap2 = ∀ {x y} → 𝔔₁ x y → 𝔔₂ (μ x) (μ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Remap2 : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓡emap2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap2 : 𝓻emap2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap2 = {!𝓻₃ _ _!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Remap2 ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record REMAPR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x y : 𝔒₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μx μy : 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     REMAP : 𝔔₁ x y → 𝔔₂ μx μy
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open REMAPR ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record REMAPR2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x y : 𝔒₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μ : 𝔒₁ → 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     REMAP2 : 𝔔₁ x y → 𝔔₂ (μ x) (μ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open REMAPR2 ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓢ymmetry = 𝓡₃ _ _ 𝔔₁ (λ x y _ → 𝔔₂ y x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓼ymmetry = ∀ {x y} → 𝔔₁ x y → 𝔔₂ y x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Symmetry : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓢ymmetry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     symmetry : 𝓼ymmetry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     symmetry = 𝓻₃ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓜ap = 𝓡₃ _ _ 𝔔₁ (λ x y _ → 𝔔₂ x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓶ap = ∀ {x y} → 𝔔₁ x y → 𝔔₂ x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Map : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓜ap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map : 𝓶ap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map = 𝓻₃ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Map' ⦃ _ : 𝓜ap ⦄ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map' : 𝓶ap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map' 𝔔₁xy = 𝓻₃ _ _ 𝔔₁xy
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Map'' ⦃ ⋆ : 𝓜ap ⦄ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where map'' = λ {x y} 𝔔₁xy → 𝓻₃ ⦃ ⋆ ⦄ x y 𝔔₁xy
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Symmetry ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Map ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Map' ⦃ … ⦄ public
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Map'' ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity! :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (∀ {𝔬₀} (𝔒₀ : Ø 𝔬₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₂} (𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₃} (𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₄} (𝔒₄ : ∀ x₀ x₁ x₂ → 𝔒₃ x₀ x₁ x₂ → Ø 𝔬₄)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₅} (𝔒₅ : ∀ x₀ x₁ x₂ x₃ → 𝔒₄ x₀ x₁ x₂ x₃ → Ø 𝔬₅)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ -- Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity! R = R 𝔒 (λ _ → 𝔒) ((λ x y → 𝔔₁ x y)) _ (λ _ y _ z → 𝔔₂ y z) (λ x _ _ z _ → 𝔔₃ x z) -- R _ _ (λ x y → 𝔔₁ x y) _ (λ _ y _ z → 𝔔₂ y z) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity = 𝓣ransitivity! 𝓡₅ -- 𝓡₅ _ _ (λ x y → 𝔔₁ x y) _ (λ _ y _ z → 𝔔₂ y z) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓽ransitivity = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity-I₁ = 𝓣ransitivity! 𝓡₅-I₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity-I₂ = 𝓣ransitivity! 𝓡₅-I₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Transitivity : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓣ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity : 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity 𝔔₁xy = 𝓻₅ _ _ 𝔔₁xy _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity' : ⦃ _ : 𝓣ransitivity ⦄ → 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity' f g = 𝓻₅ _ _ f _ g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Transitivity-I₁ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⋆ : 𝓣ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance _ = ⋆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₁ : 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₁ 𝔔₁xy = 𝓻₅ _ _ 𝔔₁xy _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Transitivity-I₂ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⋆ : 𝓣ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance _ = ⋆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₂ : 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₂ 𝔔₁xy = 𝓻₅ _ _ 𝔔₁xy _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Transitivity ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Transitivity-I₁ ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Transitivity-I₂ ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity'' : ⦃ _ : 𝓣ransitivity 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓽ransitivity 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity'' f g = 𝓻₅ _ _ f _ g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''2 : ⦃ _ : 𝓣ransitivity 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓽ransitivity 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''2 f g = 𝓻₅ _ _ f _ g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''3 : ⦃ _ : 𝓣ransitivity 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓽ransitivity 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''3 f g = 𝓻₅ _ _ f _ g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓒ongruity⋆ = 𝓡₆ _ _ (λ (A : Ø a) (B : Ø b) → A → B) _ _ (λ _ _ _ x y → 𝔔 x y) (λ _ _ f x y _ → 𝔔 (f x) (f y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓬ongruity⋆ = ∀ {A : Ø a} {B : Ø b} → (f : A → B) → ∀ {x y} → 𝔔 x y → 𝔔 (f x) (f y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Congruity⋆ : Ø 𝔮 ∙̂ ↑̂ (a ∙̂ b) where field congruity⋆ : 𝓬ongruity⋆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Congruity⋆ ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓒ongruity = 𝓡₄ (_ → _) _ _ (λ _ x y → 𝔔₁ x y) (λ f x y _ → 𝔔₂ (f x) (f y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓬ongruity = ∀ (f : _ → _) → ∀ {x y} → 𝔔₁ x y → 𝔔₂ (f x) (f y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Congruity : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where field congruity : 𝓬ongruity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Congruity ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ((o : 𝔒) → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ((o : 𝔒) → 𝔓 o → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓒̇ongruity = 𝓡₄ ((o : 𝔒) → 𝔓 o → 𝔓 o) _ _ (λ _ x y → 𝔔₁ x y) (λ f x y _ → 𝔔₂ f x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓬̇ongruity = ∀ (f : (o : 𝔒) → 𝔓 o → 𝔓 o) → ∀ {x y : (o : 𝔒) → 𝔓 o} → 𝔔₁ x y → 𝔔₂ f x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Ċongruity : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where field ċongruity : 𝓬̇ongruity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Ċongruity ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → ∀ {z} (g₁ g₂ : 𝔐 y z) → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality = 𝓡₉ _ _ _ _ (λ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality = ∀ {x y} {f₁ f₂ : 𝔐 x y} → 𝔔₁ f₁ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → 𝔔₂ g₁ g₂ → 𝔔₃ f₁ f₂ g₁ g₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Extensionality : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where field extensionality : 𝓮xtensionality
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Extensionality ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔔₁ x y → 𝔔₁ x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} {f₁ f₂ : 𝔔₁ x y} → 𝔔₂ f₁ f₂ → ∀ {z} → 𝔔₁ y z → 𝔔₁ y z → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₄ : ∀ {x y} {f₁ f₂ : 𝔔₁ x y} {q₂ : 𝔔₂ f₁ f₂} {z} {g₁ g₂ : 𝔔₁ y z} → 𝔔₃ q₂ g₁ g₂ → Ø 𝔮₄)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality = 𝓡₉ _ _ _ _ (λ x y (f₁ : 𝔔₁ x y) (f₂ : 𝔔₁ x y) → 𝔔₂ f₁ f₂) _ (λ _ y _ _ _ z → 𝔔₁ y z) _ (λ x y _ _ q₂ _ g₁ g₂ → 𝔔₃ q₂ g₁ g₂) (λ _ _ _ _ _ _ _ _ q₃ → 𝔔₄ q₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality = ∀ {x y} {f₁ f₂ : 𝔔₁ x y} → (q₂ : 𝔔₂ f₁ f₂) → ∀ {z} {g₁ g₂ : 𝔔₁ y z} → (q₃ : 𝔔₃ q₂ g₁ g₂) → 𝔔₄ q₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Extensionality : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ ∙̂ 𝔮₄ where field extensionality : 𝓮xtensionality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality′ = 𝓔xtensionality 𝔐 𝔔₁ (λ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ {_ _ f₁ f₂ _ _ g₁ g₂} _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality′ = 𝓮xtensionality 𝔐 𝔔₁ (λ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ {_ _ f₁ f₂ _ _ g₁ g₂} _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

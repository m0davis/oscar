
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Theory.Checked where
```

```agda
open import Type.Prelude

transportFin : ∀ n n' {eq} → transport Fin eq (zero {n = n}) ≡ zero {n = n'}
transportFin n .n {refl} = refl
```

```agda
open import Type.DeBruijn
open import Type.Theory.Checked.Metaformulaturez
```

```agda
pattern ,_ s = _ ,, s

alphabet : Vec (∃ Vec Nat) _
alphabet =

  {- ΠF  -} , (0 ∷ 1 ∷ [])             ∷
  {- ΠI  -} , (0 ∷ 1 ∷ [])             ∷
  {- ΠE  -} , (0 ∷ 0 ∷ [])             ∷

  {- ΣF  -} , (0 ∷ 1 ∷ [])             ∷
  {- ΣI  -} , (0 ∷ 0 ∷ [])             ∷
  {- ΣE  -} , (1 ∷ 2 ∷ 0 ∷ [])         ∷

  {- +F  -} , (0 ∷ 0 ∷ [])             ∷
  {- +Iˡ -} , (0 ∷ [])                 ∷
  {- +Iʳ -} , (0 ∷ [])                 ∷
  {- +E  -} , (1 ∷ 1 ∷ 1 ∷ 0 ∷ [])     ∷

  {- 𝟘F  -} , []                       ∷
  {- 𝟘E  -} , (1 ∷ 0 ∷ [])             ∷

  {- 𝟙F  -} , []                       ∷
  {- 𝟙I  -} , []                       ∷
  {- 𝟙E  -} , (1 ∷ 0 ∷ 0 ∷ [])         ∷

  {- ℕF  -} , []                       ∷
  {- ℕIᶻ -} , []                       ∷
  {- ℕIˢ -} , (0 ∷ [])                 ∷
  {- ℕE  -} , (1 ∷ 0 ∷ 2 ∷ 0 ∷ [])     ∷

  {- =F  -} , (0 ∷ 0 ∷ 0 ∷ [])         ∷
  {- =I  -} , (0 ∷ [])                 ∷
  {- =E  -} , (3 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷

  []

open Meta alphabet

pattern #0 = zero
pattern #1 = suc #0
pattern #2 = suc #1
pattern #3 = suc #2
pattern #4 = suc #3
pattern #5 = suc #4

pattern Πf A B   = Meta.𝓉 #0 (A ∷ B ∷ [])
pattern Πi A b   = Meta.𝓉 #1 (A ∷ b ∷ [])
pattern Πe f x   = Meta.𝓉 #2 (f ∷ x ∷ [])
pattern Σf A B   = Meta.𝓉 #3 (A ∷ B ∷ [])
pattern Σi a b   = Meta.𝓉 #4 (a ∷ b ∷ [])
pattern Σe C g p = Meta.𝓉 #5 (C ∷ g ∷ p ∷ [])
```

```agda
{-# DISPLAY Meta.index≾ _ = index≾ #-}
{-# DISPLAY Meta._≾_ _ = _≾_ #-}
{-# DISPLAY Meta.diff≾ _ = diff≾ #-}
{-# DISPLAY Meta.Expression _ = Expression #-}
{-# DISPLAY Meta.weakenExpressionFrom _ = weakenExpressionFrom #-}
{-# DISPLAY Meta.instantiateExpressionAt _ = instantiateExpressionAt #-}
{-# DISPLAY Meta.Abstractions _ = Abstractions #-}
{-# DISPLAY Meta.shift≾ _ = shift≾ #-}
{-# DISPLAY Meta._,⋆_ _ = _,⋆_ #-}
```

```agda
data _ctx : ∀ {N} → 0 ≾ N → Set
data _⊢_∶_ {N} (Γ : 0 ≾ N) : Expression N → Expression N → Set
data _⊢_≝_∶_ {N} (Γ : 0 ≾ N) : Expression N → Expression N → Expression N → Set

open Typechecked _⊢_∶_

infix 3 _ctx
infix 4 _⊢_∶_
data _ctx where
  ε : ε ctx
  _,_ : ∀ {N} {Γ : 0 ≾ N} → Γ ctx → ∀ {ℓ} {A : Expression N} → Γ ⊢ A ∶ 𝒰 ℓ → Γ , A ctx

ΠF-inj₂ : ∀ {N} {Γ : 0 ≾ N}
        → ∀ {A B f}
        → Γ ⊢ f ∶ Πf A B
        → ∃ λ ℓ → Γ , A ⊢ B ∶ 𝒰 ℓ

wfctx₁ : ∀ {N} {Γ : 0 ≾ N} {a A}
       → Γ ⊢ a ∶ A
       → Γ ctx

well-typed₁ : ∀ {N} {Γ : 0 ≾ N} {c C}
            → Γ ⊢ c ∶ C
            → ∃ λ ℓ → Γ ⊢ C ∶ 𝒰 ℓ

data _⊢_∶_ {N} (Γ : 0 ≾ N) where
  𝓋 : ∀ v {φ}
    → Γ ctx
```

Is it a problem to have this kind of green slime?

```agda
    → (let v' : Fin (finToNat (diff≾ Γ))
           v' = transport Fin (by (diff≾-eq Γ)) v)
    → index≾ Γ v' ≡ φ
```

Once I get to actually trying to use this constructor (e.g. in `ΣE` below), the difficulty trying to fulfill this requirement makes me think that it is.

```agda
    → Γ ⊢ 𝓋 v ∶ φ
  𝒰I : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
  𝒰C : ∀ {ℓ A}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ A ∶ 𝒰 (suc ℓ)
  ΠF : ∀ {ℓ A B}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ Πf A B ∶ 𝒰 ℓ
  ΠI : ∀ {A B b}
     → Γ , A ⊢ b ∶ B
     → Γ ⊢ Πi A b ∶ Πf A B
  ΠE : ∀ {A a B f}
     → (Γ⊢f∶ΠfAB : Γ ⊢ f ∶ Πf A B)
     → (Γ⊢a∶A : Γ ⊢ a ∶ A)
     → ∀ {B[a]}
     → tcInstantiateAt {Δ = ε} (ΠF-inj₂ Γ⊢f∶ΠfAB .snd) Γ⊢a∶A ≡ B[a]
     → Γ ⊢ Πe f a ∶ B[a]
  ΣF : ∀ {A B ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ Σf A B ∶ 𝒰 ℓ
  ΣI : ∀ {ℓ A a B b}
     → (Γ,A⊢B∶𝒰 : Γ , A ⊢ B ∶ 𝒰 ℓ)
     → (Γ⊢a∶A : Γ ⊢ a ∶ A)
     → Γ ⊢ b ∶ tcInstantiateAt {Δ = ε} Γ,A⊢B∶𝒰 Γ⊢a∶A
     → Γ ⊢ Σi a b ∶ Σf A B
  ΣE : ∀ {ℓ A B C g p}
     → (let z : suc N ≿ N
            z = Σf A B ∷ [])
     → (Γ,ΣfAB⊢C∶𝒰 : Γ ,∷⋆ z ⊢ C ∶ 𝒰 ℓ)
     → (let Γ,ΣfAB⊢ΣfAB∶𝒰 : Γ , Σf A B ⊢ Σf {!A!} {!B!} ∶ 𝒰 ℓ
            Γ,ΣfAB⊢ΣfAB∶𝒰 = {!(well-typed₁ (_⊢_∶_.𝓋 0 (wfctx₁ Γ,ΣfAB⊢C∶𝒰) refl) .snd)!})
            -- transport (λ z → Γ , Σf A B ⊢ index≾ (Γ , Σf A B) z ∶ 𝒰 _) (transportFin #0 #0) (well-typed₁ (_⊢_∶_.𝓋 0 (wfctx₁ Γ,ΣfAB⊢C∶𝒰) refl) .snd)
     → (let Γ,ΣfAB,A,B⊢C∶𝒰 : Γ , Σf A B , _ , _ ⊢ {!C!} ∶ 𝒰 ℓ
            Γ,ΣfAB,A,B⊢C∶𝒰 = {!!})
     → (let Γ,A,B⊢Σiab∶ΣfAB : Γ , A , B ⊢ Σi (𝓋 1) (𝓋 0) ∶ Σf _ _
            Γ,A,B⊢Σiab∶ΣfAB = ΣI {!!} {!!} {!!})
     → Γ , A , B ⊢ g ∶ tcInstantiateAt {Δ = ε , A , B} Γ,ΣfAB,A,B⊢C∶𝒰 Γ,A,B⊢Σiab∶ΣfAB
     → (Γ⊢p∶ΣfAB : Γ ⊢ p ∶ Σf A B)
     → ∀ {C[p]} → tcInstantiateAt {Δ = ε} Γ,ΣfAB⊢C∶𝒰 Γ⊢p∶ΣfAB ≡ C[p]
     → Γ ⊢ Σe C g p ∶ C[p]

data _⊢_≝_∶_ {N} (Γ : 0 ≾ N) where

ΠF-inj₂ = {!!}

wfctx₁ = {!!}

well-typed₁ = {!!}
```

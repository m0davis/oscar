
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.deprecated.Term.Layer0.Checked where
```

```agda
open import Type.Prelude

transportFin : ∀ n n' {eq} → transport Fin eq (zero {n = n}) ≡ zero {n = n'}
transportFin n .n {refl} = refl
```

```agda
open import Type.Universe
open import Type.deprecated.Term.Layer-2.DeBruijn
open import Type.deprecated.Term.Layer-1 hiding (module K)
```

```agda
pattern ,_ s = _ ,, s
import Type.deprecated.Term.Layer-1.Kernel as K
open import Type.deprecated.Term.Layer-1.Kernel.TypeChecked alphabet as KTC
```

```agda
{-# DISPLAY K.Expression _ = Expression #-}
{-# DISPLAY K.index≾ _ = index≾ #-}
{-# DISPLAY K._≾_ _ = _≾_ #-}
{-# DISPLAY K._≿_ _ = _≿_ #-}
{-# DISPLAY K.diff≾ _ = diff≾ #-}
{-# DISPLAY K.weakenExpressionFrom _ = weakenExpressionFrom #-}
{-# DISPLAY K.weakenExpressionByFrom _ = weakenExpressionByFrom #-}
{-# DISPLAY K.instantiateExpressionAt _ = instantiateExpressionAt #-}
{-# DISPLAY K.Abstractions _ = Abstractions #-}
{-# DISPLAY K.shift≾ _ = shift≾ #-}
{-# DISPLAY K._<<<_ _ = _<<<_ #-}
{-# DISPLAY K._<><_ _ = _<><_ #-}
{-# DISPLAY K._<>>_ _ = _<>>_ #-}
{-# DISPLAY K._,[_] _ = _,[_] #-}
{-# DISPLAY K.context≤ _ = context≤ #-}
{-# DISPLAY K.context≥ _ = context≥ #-}
{-# DISPLAY K.shift≾ _ = shift≾ #-}
{-# DISPLAY K.shift≿ _ = shift≿ #-}
{-# DISPLAY K.shift≾By _ = shift≾By #-}

-- {-# DISPLAY K._>>>_ _ = _>>>_ #-}
```

```agda
data _ctx : ∀ {N} → 0 ≾ N → Set
data _⊢_∶_ {N} (Γ : 0 ≾ N) : Expression N → Expression N → Set
data _⊢_≝_∶_ {N} (Γ : 0 ≾ N) : Expression N → Expression N → Expression N → Set

open Typechecked _ctx _⊢_∶_

infix 3 _ctx
infix 4 _⊢_∶_
data _ctx where
  ε : ε ctx
  _,_ : ∀ {N} {Γ : 0 ≾ N} → Γ ctx → ∀ {ℓ} {A : Expression N} → Γ ⊢ A ∶ 𝒰 ℓ → Γ , A ctx

ΠF-inj₂ : ∀ {N} {Γ : 0 ≾ N}
        → ∀ {A B f}
        → Γ ⊢ f ∶ Πf A B
        → ∃ λ ℓ → Γ , A ⊢ B ∶ 𝒰 ℓ

syntactic : Syntactic
open Syntactic syntactic

ΣF-inj₂ : ∀ {N} {Γ : 0 ≾ N} {ℓ A B}
        → Γ ⊢ Σf A B ∶ 𝒰 ℓ
        → ∃ λ ℓ
        → Γ ⊢ A ∶ 𝒰 ℓ × Γ , A ⊢ B ∶ 𝒰 ℓ

weaken⊢ : ∀ {N} {Γ : 0 ≾ N} {a A ℓ W}
        → Γ ⊢ W ∶ 𝒰 ℓ
        → Γ ⊢ a ∶ A
        → Γ , W ⊢ weakenExpressionFrom zero a ∶ weakenExpressionFrom zero A

weaken⊢ByFrom′ : ∀ {M} {Γ : 0 ≾ M}
               → ∀ {N} {Δ : M ≾ N}
               → ∀ {X} {Ξ : X ≿ M}
               → ∀ {a A}
               → Γ <<< Δ ⊢ a ∶ A         -- infixl
               → Γ <>< Ξ ctx
               → ∃ λ (wk : _ → _)
               → Γ <>< (Ξ <>> Δ) ⊢ wk a ∶ wk A

weaken⊢ByFrom' : ∀ {M} {Γ : 0 ≾ M}
               → ∀ {N} {Δ : N ≿ M}
               → ∀ {X} {Ξ : M ≾ X}
               → ∀ {a A}
               → Γ <>< Δ ⊢ a ∶ A         -- infixl
               → Γ <<< Ξ ctx
               → ∃ λ (wk : _ → _)
               → Γ <<< (Ξ <<> Δ) ⊢ wk a ∶ wk A


{-
              → (Γ <>> Ξ) ><< Δ ⊢ wk a ∶ wk A -- infixl
              → Γ <>< (Ξ ><> Δ) ⊢ wk a ∶ wk A -- infixr
              → Γ <>< (Ξ <>> Δ) ⊢ wk a ∶ wk A -- infixr
              → Γ <<< (Ξ ><< Δ) ⊢ wk a ∶ wk A -- infixr

    AB
     x

    ≾≾≾≾≾≾≾≾≾≾≾≾≾≾≾
                               ≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿
    -------------------------------------------------------------
    ≾≾≾≾≾≾≾≾≾≾≾≾≾≾≾

    Γ          Δ
    ≾≾≾≾≾≾≾≾≾≾≾≾≾≾≾
    L          M   n
               Ξ
               ≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿
               M                           N
    ---------------------------------------------------------
    ≾≾≾≾≾≾≾≾≾≾≾≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≾≾≾≾ <><
    ≾≾≾≾≾≾≾≾≾≾≾≾≾≾≾≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿≿ <<>

    MMMMMMMMMMMMMMMM
               NNNNNNNNNNNNNNNNNN



              <><   M ≾ N        <>< O ≿ N             = M ≾ O
              <>>   N ≾ M        <>>
              <<>
              ><>   M ≾ N        ><> O ≿ N             = O ≿ M

              >><   N ≿ M        >>< Expression N      = suc N ≿ M
              ><<   Expression M ><< suc M ≾ N         =     M ≾ N

              ,     M ≾ N , Expression N = M ≾ suc N
              ∷     Expression M ∷ N ≿ suc M = N ≿ M

              >>>   N ≿ M        >>> O ≿ N             = O ≿ M
              <<<   M ≾ N        <<< N ≾ O             = M ≾ O
-}

split/ctx : ∀ {M N} {Γ : 0 ≾ M} {Δ : N ≿ M}
          → Γ <>< Δ ctx
          → Γ ctx

var : ∀ {N} {Γ : 0 ≾ N}
      → Γ ctx
      → Fin N
      → ∃ λ φ
      → ∃ λ ℓ
      → Γ ⊢ φ ∶ 𝒰 ℓ

var₁⋆ : ∀ {M} {Γ : 0 ≾ M} {N} {Δ : M ≾ N}
      → Γ <<< Δ ctx
      → Fin M
      → ∃ λ φ
      → ∃ λ ℓ
      → Γ ⊢ φ ∶ 𝒰 ℓ

var₁ : ∀ {M} {Γ : 0 ≾ M} {N} {Δ : N ≿ M}
     → Γ <>< Δ ctx
     → Fin M
     → ∃ λ φ
     → ∃ λ ℓ
     → Γ ⊢ φ ∶ 𝒰 ℓ

Γ,A,B⊢Σiab∶ΣfAB
  : ∀ {N} {Γ : 0 ≾ N} {ℓ A B C}
  → (Γ,ΣfAB⊢C∶𝒰 : Γ , Σf A B ⊢ C ∶ 𝒰 ℓ)
  → Γ , A , B ⊢ Σi (𝓋 1) (𝓋 0) ∶ Σf _
                                     _

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
     → (let ℓ : Universe
            ℓ = _
            Γ,A⊢B∶𝒰 : Γ , A ⊢ B ∶ 𝒰 ℓ
            Γ,A⊢B∶𝒰 = ΠF-inj₂ Γ⊢f∶ΠfAB .snd)
     → tcInstantiateAt {Δ = ε} Γ,A⊢B∶𝒰 Γ⊢a∶A ≡ B[a]
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
  ΣE
     : ∀ {ℓ A B C g p}
     → (Γ,ΣfAB⊢C∶𝒰 : Γ , Σf A B ⊢ C ∶ 𝒰 ℓ) -- Γ , z ∶ Σf A B ⊢ C ∶ 𝒰 ℓ
     → (let Γ,ΣfAB/ctx : Γ , Σf A B ctx
            Γ,ΣfAB/ctx = wfctx₁ Γ,ΣfAB⊢C∶𝒰
            ∃ℓ→Γ⊢ΣfAB∶𝒰 : ∃ λ ℓ → Γ ⊢ Σf A B ∶ 𝒰 ℓ
            ∃ℓ→Γ⊢ΣfAB∶𝒰 = case Γ,ΣfAB/ctx of λ { (_ , Γ⊢ΣfAB∶𝒰) → , Γ⊢ΣfAB∶𝒰}
            ∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 : ∃ λ ℓ → Γ ⊢ A ∶ 𝒰 ℓ × Γ , A ⊢ B ∶ 𝒰 ℓ
            ∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 = ΣF-inj₂ (∃ℓ→Γ⊢ΣfAB∶𝒰 .snd)
            Γ,A⊢B∶𝒰 : Γ , A ⊢ B ∶ 𝒰 _
            Γ,A⊢B∶𝒰 = ∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 .snd .snd
            Γ,A,B/ctx : Γ , A , B ctx
            Γ,A,B/ctx = {!!}
            Γ,A,B⊢Σiab∶ΣfAB : Γ , A , B ⊢ Σi (𝓋 1) (𝓋 0) ∶ Σf _ _
            Γ,A,B⊢Σiab∶ΣfAB = Γ,A,B⊢Σiab∶ΣfAB Γ,ΣfAB⊢C∶𝒰
            Γ,A,B,ΣfAB⊢C∶𝒰 : Γ , A , B , Σf _ _ ⊢ _ ∶ 𝒰 ℓ
            Γ,A,B,ΣfAB⊢C∶𝒰 = {!weaken⊢ByFrom {Γ = Γ} {Δ = Σf A B ∷ []} {Ξ = ε , A , B} Γ,ΣfAB⊢C∶𝒰 Γ,A,B/ctx!}
            Γ,ΣfAB,A,B⊢C∶𝒰 : Γ , Σf A B , _ , _ ⊢ _ ∶ 𝒰 ℓ
            Γ,ΣfAB,A,B⊢C∶𝒰 = {!!}
       )
     → Γ , A , B ⊢ g ∶ tcInstantiateAt {Γ = Γ} {Δ = ε , A , B} {A = Σf A B} Γ,ΣfAB,A,B⊢C∶𝒰 {!Γ,A,B⊢Σiab∶ΣfAB!} -- Γ , a ∶ A , b ∶ B ⊢ g ∶ C [ ΣI a b / z ]
     → (Γ⊢p∶ΣfAB : Γ ⊢ p ∶ Σf A B)
     → Γ ⊢ Σe C g p ∶ {!!} -- C [ p / z ]

slimy'→unslimy' : ∀ {N} {Γ : 0 ≾ N} {ℓ} {A : Expression N}
                    {B C : Expression (suc N)}
                    (Γ,ΣfAB⊢C∶𝒰 : Γ , 𝓉 #ΣF (A ∷ B ∷ []) ⊢ C ∶ 𝒰 ℓ)
                    ℓΣ
                    (eq1 : suc (suc N) ≡ N - N + suc (suc N))
                    (eq2 : suc (N - N + suc (suc N)) ≡ suc N - N + suc (suc N))
                    (w : Expression (suc N) → Expression (suc N - N + suc (suc N))) →
                  Γ <<<
                  (ε , A , B , weakenExpressionFrom 0 (weakenExpressionFrom 0 A))
                  <><
                  transport (_≿ suc (suc (suc N))) eq2
                  (shift≿ {N = N - N + suc (suc N)} (transport (_≿ suc (suc N)) eq1 []))
                  ⊢ w B ∶
                  w
                  (𝒰 ℓΣ) →
                  Γ , A , B , weakenExpressionFrom 1 (weakenExpressionFrom 0 A) ⊢
                  weakenExpressionFrom 2 (weakenExpressionFrom 1 B) ∶ 𝒰 ℓΣ
slimy'→unslimy' {N} Γ,ΣfAB⊢C∶𝒰 ℓΣ eq1 eq2 w x with transport (_≿ suc (suc N)) eq1 []
… | t1 with transport (_≿ suc (suc N)) (sym eq1) t1
… | t1' = {!!}

Γ,A,B⊢Σiab∶ΣfAB {N} {Γ} {ℓ} {A} {B} {C} Γ,ΣfAB⊢C∶𝒰 =
  ΣI {ℓ = _}
    (slimy'→unslimy' Γ,ΣfAB⊢C∶𝒰 _ auto auto weakener slimy') -- slimy'→unslimy' Γ,ΣfAB⊢C∶𝒰 weakener slimy'
    (𝓋 1 {_} Γ,A,B/ctx {!!})
    (𝓋 0 {_} Γ,A,B/ctx {!!})
  where
  Γ,ΣfAB/ctx : Γ , Σf A B ctx
  Γ,ΣfAB/ctx = wfctx₁ Γ,ΣfAB⊢C∶𝒰
  ∃ℓ→Γ⊢ΣfAB∶𝒰 : ∃ λ ℓ → Γ ⊢ Σf A B ∶ 𝒰 ℓ
  ∃ℓ→Γ⊢ΣfAB∶𝒰 = case Γ,ΣfAB/ctx of λ { (_ , Γ⊢ΣfAB∶𝒰) → , Γ⊢ΣfAB∶𝒰}
  ∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 : ∃ λ ℓ → Γ ⊢ A ∶ 𝒰 ℓ × Γ , A ⊢ B ∶ 𝒰 ℓ
  ∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 = ΣF-inj₂ (∃ℓ→Γ⊢ΣfAB∶𝒰 .snd)
  Γ,A⊢B∶𝒰 : Γ , A ⊢ B ∶ 𝒰 _
  Γ,A⊢B∶𝒰 = ∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 .snd .snd
  Γ,A,B/ctx : Γ , A , B ctx
  Γ,A,B/ctx = {!!}
  weakener : Expression (suc N) → Expression (suc N - N + suc (suc N))
  weakener = weaken⊢ByFrom' {Γ = Γ} {Δ = A ∷ []} {Ξ = ε , A , B} Γ,A⊢B∶𝒰 Γ,A,B/ctx .fst
  slimy = weaken⊢ByFrom′ {Γ = Γ} {Δ = ε , A} {Ξ = A ∷ B ∷ []} Γ,A⊢B∶𝒰 Γ,A,B/ctx .snd
  slimy' : Γ <<< ((ε , A , B) <<> (A ∷ [])) ⊢
             weakener B ∶
             weakener (𝒰 (∃ℓ→Γ⊢A∶𝒰×Γ,A⊢B∶𝒰 .fst))
  slimy' = weaken⊢ByFrom' {Γ = Γ} {Δ = A ∷ []} {Ξ = ε , A , B} Γ,A⊢B∶𝒰 Γ,A,B/ctx .snd
  eq : ∀ Z e → transport (_≿ Z) e [] ≡ []
  eq Z = λ {refl → refl}
  lamslimy' : (e1 : suc (suc N) ≡ suc (suc N)) (e2 : suc (suc (suc N)) ≡ suc (suc (suc N))) → 0 ≾ suc (suc (suc N))
  lamslimy' e1 e2 = Γ <<< (ε , A , B , weakenExpressionFrom 0 (weakenExpressionFrom 0 A)) <>< transport (_≿ suc (suc (suc N))) e2 (shift≿ (transport (_≿ suc (suc N)) e1 []))

data _⊢_≝_∶_ {N} (Γ : 0 ≾ N) where

ΠF-inj₂ = {!!}

ΣF-inj₂ (𝒰C x) = ΣF-inj₂ x
ΣF-inj₂ (ΣF ⊢A ⊢B) = , (⊢A ,, ⊢B)

index≾₀ : ∀ {N} (Γ : 0 ≾ N)
        → Fin N
        → Expression N
index≾₀ Γ x = {!!}

weaken⊢ Γ⊢W∶𝒰 Γ⊢a∶A = {!!}

<><→<<< : ∀ {M N O}
        → {Γ : M ≾ N}
        → (Δ : N ≾ O)
        → Γ <>< [] <>> Δ ≡ {!Γ <<< Δ!} -- FIXME requires slime
<><→<<< = {!!}

weaken⊢ByFrom′ {Ξ = K.[]} x x₁ = {!!}
weaken⊢ByFrom′ {Γ = Γ} {Δ = Δ} {Ξ = x₂ K.∷ Ξ} x x₁ = {!Γ <>< (x₂ ∷ Ξ) <>> Δ!}

weaken⊢ByFrom' = {!!}

split/ctx = {!!}

var (Γ , δ) zero = , , weaken⊢ δ δ
var (Γ , δ) (suc x) = , , weaken⊢ δ (var Γ x .snd .snd)

var₁⋆ {Δ = ε} = var
var₁⋆ {Δ = Δ , δ} (Γ,Δ/ctx , _) = var₁⋆ {Δ = Δ} Γ,Δ/ctx

var₁ {Δ = Δ} Γ,Δ/ctx = var (split/ctx {Δ = Δ} Γ,Δ/ctx)

syntactic .KTC.Typechecked.Syntactic.wfctx₁ = wfctx₁' where
  wfctx₁' : ∀ {N} {Γ : 0 ≾ N} {a A}
          → Γ ⊢ a ∶ A
          → Γ ctx
  wfctx₁' (𝓋 v x x₁) = x
  wfctx₁' (𝒰I x) = x
  wfctx₁' (𝒰C x) = wfctx₁ x
  wfctx₁' (ΠF x x₁) = wfctx₁ x
  wfctx₁' (ΠI x) = case wfctx₁ x of (λ { (x , x₂) → x})
  wfctx₁' (ΠE x x₁ x₂) = wfctx₁ x₁
  wfctx₁' (ΣF x x₁) = wfctx₁ x
  wfctx₁' (ΣI x x₁ x₂) = wfctx₁ x₁
  wfctx₁' (ΣE x x₁ x₂) = wfctx₁ x₂
syntactic .KTC.Typechecked.Syntactic.well-typed₁ = {!!}
syntactic .KTC.Typechecked.Syntactic.weaken = {!!}
syntactic .KTC.Typechecked.Syntactic.substitute = {!!}
```
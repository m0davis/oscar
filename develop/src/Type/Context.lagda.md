
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Context where
```

```agda
open import Type.Prelude
open import Type.Formula
open import Type.Variable
```

```agda
infixl 15 _,_∶_
data Context : Set where
  ε : Context
  _,_∶_ : Context → Variable → Formula → Context
```

Combinators for contexts.

```agda
infixl 15 _,_
_,_ : Context → Context → Context
Γ , ε = Γ
Γ , (Δ , x ∶ A) = Γ , x ∶ A , Δ

lengthContext : Context → Nat
lengthContext ε = zero
lengthContext (Γ , _ ∶ _) = suc (lengthContext Γ)

indexContext : (Γ : Context) → Fin (lengthContext Γ) → Variable × Formula
indexContext Γ x with lengthContext Γ | graphAt lengthContext Γ
indexContext ε () | .0 | ingraph refl
indexContext (Γ , x ∶ φ) zero | .(suc (lengthContext Γ)) | ingraph refl = x ,, φ
indexContext (Γ , _ ∶ _) (suc i) | .(suc (lengthContext Γ)) | ingraph refl = indexContext Γ i
```

simultaneous substitution over a context

```agda
_[_⋆←⋆_]Ctx : Context → ∀ {N} → Vec Formula N → Vec Variable N → Context
ε [ _ ⋆←⋆ _ ]Ctx = ε
(Γ , x ∶ φ) [ σs ⋆←⋆ vs ]Ctx = {!!} , {!!} ∶ {!!}
```

-- Appendix A.2 appeals to a side-condition on `ctx-EXT` that the added variable be distinct from the other variables listed in the context.

```agda
instance

  DistinctnessContext : Distinctness Context
  DistinctnessContext .Distinctness._∉_ v ε = ⊤
  DistinctnessContext .Distinctness._∉_ v (Γ , x ∶ A) = v ≢ x × v ∉ Γ
```

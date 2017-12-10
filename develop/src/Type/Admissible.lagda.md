
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Admissible where
```

```agda
open import Type.Prelude
open import Type.Formula
open import Type.Universe
open import Type.Variable
open import Type.Context
open import Type.Outing
```

admissible rules

```agda
-- uniqueness principle for Σ (possibly not correctly stated)
ΣU : ∀ {Γ A x B c y z}
   → Γ ⊢ c ∶ ΣF A (x ↦₁ B)
   → Γ ⊢ c ≝ ΣE (z ↦₁ 𝓋 z) (x , y ↦₂ ΣI (𝓋 x) (𝓋 y)) c ∶ ΣF A (x ↦₁ B)
ΣU x₁ = ≝-symmetry {!!}

-- typing judgements are of well-formed contexts
wfctx₁ : ∀ {Γ c C}
          → Γ ⊢ c ∶ C
          → Γ ctx
wfctx₁ (var Γctx _ _) = Γctx
wfctx₁ (≝-subst Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (𝒰I Γctx) = Γctx
wfctx₁ (𝒰C Γ⊢) = wfctx₁ Γ⊢
wfctx₁ (ΠF Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (ΠI Γ,x∶A⊢) with wfctx₁ Γ,x∶A⊢
… | ctx-EXT Γ⊢ _ = wfctx₁ Γ⊢
wfctx₁ (ΠE Γ⊢ _ _) = wfctx₁ Γ⊢
wfctx₁ (ΣF Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (ΣI _ Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (ΣE _ _ Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (+F Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (+Iˡ _ _ Γ⊢) = wfctx₁ Γ⊢
wfctx₁ (+Iʳ _ _ Γ⊢) = wfctx₁ Γ⊢
wfctx₁ (+E _ _ _ Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (𝟘F Γctx) = Γctx
wfctx₁ (𝟘E _ Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (𝟙F Γctx) = Γctx
wfctx₁ (𝟙I Γctx) = Γctx
wfctx₁ (𝟙E _ _ Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (ℕF Γctx) = Γctx
wfctx₁ (ℕIᶻ Γctx) = Γctx
wfctx₁ (ℕIˢ Γ⊢) = wfctx₁ Γ⊢
wfctx₁ (ℕE _ _ _ Γ⊢ _) = wfctx₁ Γ⊢
wfctx₁ (=F Γ⊢ _ _) = wfctx₁ Γ⊢
wfctx₁ (=I Γ⊢) = wfctx₁ Γ⊢
wfctx₁ (=E _ _ Γ⊢ _ _ _) = wfctx₁ Γ⊢

-- TODO fromterm and fromctx deserve to be renamed and/or refactored

fromterm : ∀ {Γ c C}
         → Γ ⊢ c ∶ C
         → ∃ λ ℓ → Γ ⊢ C ∶ 𝒰 ℓ
fromterm x = {!!}

fromctx : ∀ {Γ x A c C}
        → Γ , x ∶ A ⊢ c ∶ C
        → ∃ λ ℓ → Γ ⊢ A ∶ 𝒰 ℓ
fromctx x₁ = fromterm (var {!!} {!!} {!!})


≝-project₁ : ∀ {Γ a b A}
          → Γ ⊢ a ≝ b ∶ A
          → Γ ⊢ a ∶ A
≝-project₂ : ∀ {Γ a b A}
          → Γ ⊢ a ≝ b ∶ A
          → Γ ⊢ b ∶ A

≝-project₁ (≝-reflexivity Γ⊢a∶A) = Γ⊢a∶A
≝-project₁ (≝-symmetry Γ⊢b≝a∶A) = ≝-project₂ Γ⊢b≝a∶A
≝-project₁ (≝-transitivity Γ⊢a≝b∶A _) = ≝-project₁ Γ⊢a≝b∶A
≝-project₁ (≝-subst Γ⊢a≝b∶B Γ⊢B≝A∶𝒰) = ≝-subst (≝-project₁ Γ⊢a≝b∶B) Γ⊢B≝A∶𝒰
≝-project₁ (ΠI Γ,x∶A⊢b≝b'∶B) = ΠI (≝-project₁ Γ,x∶A⊢b≝b'∶B)
≝-project₁ (ΠE Γ,x∶A⊢b∶B Γ⊢a∶A _ B[a]≡B') = ΠE (ΠI Γ,x∶A⊢b∶B) Γ⊢a∶A B[a]≡B'
≝-project₁ (ΠU Γ⊢f∶ΠFAB) = Γ⊢f∶ΠFAB
≝-project₁ (ΣI Γ⊢x∶A⊢B∶𝒰 Γ⊢a≝a'∶A Γ⊢b≝b'∶B[a]) = ΣI Γ⊢x∶A⊢B∶𝒰 (≝-project₁ Γ⊢a≝a'∶A) (≝-project₁ Γ⊢b≝b'∶B[a])
≝-project₁ (ΣE Γ,z∶ΣFAB⊢C∶𝒰 x₂ x₃ x₄ x₅ x₆) = ΣE Γ,z∶ΣFAB⊢C∶𝒰 x₂ (ΣI (snd (fromctx x₂)) x₃ x₄) x₅
≝-project₁ (+Iˡ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₁ (+Iʳ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₁ (+Eˡ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (+Eʳ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (𝟙E x x₁ x₂) = {!!}
≝-project₁ (ℕIˢ Γ⊢a≝b∶A) = {!!}
≝-project₁ (ℕEᶻ x x₁ x₂ x₃) = {!!}
≝-project₁ (ℕEˢ x x₁ x₂ x₃ x₄ x₅) = {!!}
≝-project₁ (=I Γ⊢a≝b∶A) = {!!}
≝-project₁ (=E x₁ x₂ x₃ x₄ x₅) = {!!}

≝-project₂ (≝-reflexivity Γ⊢a∶A) = Γ⊢a∶A
≝-project₂ (≝-symmetry Γ⊢b≝a∶A) = ≝-project₁ Γ⊢b≝a∶A
≝-project₂ (≝-transitivity Γ⊢a≝b∶A Γ⊢a≝b∶A₁) = {!!}
≝-project₂ (≝-subst Γ⊢a≝b∶A Γ⊢a≝b∶A₁) = {!!}
≝-project₂ (ΠI Γ⊢a≝b∶A) = {!!}
≝-project₂ (ΠE x₁ x₂ x₃ x₄) = {!!}
≝-project₂ (ΠU x₁) = {!!}
≝-project₂ (ΣI x₁ Γ⊢a≝b∶A Γ⊢a≝b∶A₁) = ΣI {!!} {!!} {!!}
≝-project₂ (ΣE x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (+Iˡ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₂ (+Iʳ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₂ (+Eˡ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (+Eʳ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (𝟙E x x₁ x₂) = {!!}
≝-project₂ (ℕIˢ Γ⊢a≝b∶A) = {!!}
≝-project₂ (ℕEᶻ x x₁ x₂ x₃) = {!!}
≝-project₂ (ℕEˢ x x₁ x₂ x₃ x₄ x₅) = {!!}
≝-project₂ (=I Γ⊢a≝b∶A) = {!!}
≝-project₂ (=E x₁ x₂ x₃ x₄ x₅) = {!!}

wkg₁ : ∀ {Δ} {Γ} {x A B b ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , Δ ⊢ b ∶ B
     → x ∉ Γ -- the weakening variable must not be confused for anything in its suffix
     → ∀ {Γ'}
     → Γ , x ∶ A , Δ ≡ Γ'
     → Γ' ⊢ b ∶ B

wkg₂ : ∀ {Γ} {Δ : Context} {x A B b c ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , Δ ⊢ b ≝ c ∶ B
     → x ∉ Γ
     → ∀ {Γ'}
     → Γ , x ∶ A , Δ ≡ Γ'
     → Γ' ⊢ b ≝ c ∶ B

wkg₁ = {!!}

wkg₂ = {!!}
```

```agda
subst₁ : ∀ {Γ Δ a A b B x}
       → Γ ⊢ a ∶ A
       → Γ , x ∶ A , Δ ⊢ b ∶ B
       → Γ , (Δ [ a ∷ [] ⋆←⋆ x ∷ [] ]Ctx) ⊢ b [ a ←₁ x ] ∶ B [ a ←₁ x ]

subst₂ : ∀ {Γ Δ a A b b' B x}
       → Γ ⊢ a ∶ A
       → Γ , x ∶ A , Δ ⊢ b ≝ b' ∶ B
       → Γ , (Δ [ a ∷ [] ⋆←⋆ x ∷ [] ]Ctx) ⊢ b [ a ←₁ x ] ≝ b' [ a ←₁ x ] ∶ B [ a ←₁ x ]

subst₁ = {!!}

subst₂ = {!!}
```

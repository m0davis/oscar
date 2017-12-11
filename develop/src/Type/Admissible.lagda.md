
```agda
-- {-# OPTIONS --allow-unsolved-metas #-}
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
-- wfctx₁ (+Iˡ Γ⊢ _ _) = wfctx₁ Γ⊢ -- TODO investigate why this leads to termination-check failure
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
```

```agda
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

subst₁ : ∀ {Γ Δ a A b B x}
       → Γ ⊢ a ∶ A
       → Γ , x ∶ A , Δ ⊢ b ∶ B
       → Γ , (Δ [ a ∷ [] ⋆←⋆ x ∷ [] ]Ctx) ⊢ b [ a ←₁ x ] ∶ B [ a ←₁ x ]

subst₂ : ∀ {Γ Δ a A b b' B x}
       → Γ ⊢ a ∶ A
       → Γ , x ∶ A , Δ ⊢ b ≝ b' ∶ B
       → Γ , (Δ [ a ∷ [] ⋆←⋆ x ∷ [] ]Ctx) ⊢ b [ a ←₁ x ] ≝ b' [ a ←₁ x ] ∶ B [ a ←₁ x ]

typed₁ : ∀ {Γ c C}
         → Γ ⊢ c ∶ C
         → Γ ⊩ C

ctxHead⊩ : ∀ {Γ x A}
         → Γ , x ∶ A ctx
         → Γ ⊩ A

≝-project₁ : ∀ {Γ a b A}
          → Γ ⊢ a ≝ b ∶ A
          → Γ ⊢ a ∶ A

≝-project₂ : ∀ {Γ a b A}
          → Γ ⊢ a ≝ b ∶ A
          → Γ ⊢ b ∶ A

wkg₁ = {!!}

wkg₂ = {!!}

subst₁ = {!!}

subst₂ = {!!}

typed₁ x = {!!}

ctxHead⊩ (ctx-EXT Γ⊢A∶𝒰 x∉Γ) = ⟨ _ ∋ Γ⊢A∶𝒰 ⟩

lift⊩ : ∀ {Γ A ℓ ℓ'}
      → ℓ' ≥ ℓ
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ A ∶ 𝒰 ℓ'
lift⊩ (diff! zero) Γ⊢A∶𝒰ℓ = Γ⊢A∶𝒰ℓ
lift⊩ (diff! (suc k)) Γ⊢A∶𝒰ℓ = 𝒰C (lift⊩ auto Γ⊢A∶𝒰ℓ)

≝-project₁ (≝-reflexivity Γ⊢a∶A) = Γ⊢a∶A
≝-project₁ (≝-symmetry Γ⊢b≝a∶A) = ≝-project₂ Γ⊢b≝a∶A
≝-project₁ (≝-transitivity Γ⊢a≝b∶A _) = ≝-project₁ Γ⊢a≝b∶A
≝-project₁ (≝-subst Γ⊢a≝b∶B Γ⊢B≝A∶𝒰) = ≝-subst (≝-project₁ Γ⊢a≝b∶B) Γ⊢B≝A∶𝒰
≝-project₁ (ΠI Γ,x∶A⊢b≝b'∶B) = ΠI (≝-project₁ Γ,x∶A⊢b≝b'∶B)
≝-project₁ (ΠE Γ,x∶A⊢b∶B Γ⊢a∶A _ B[a]≡B') = ΠE (ΠI Γ,x∶A⊢b∶B) Γ⊢a∶A B[a]≡B'
≝-project₁ (ΠU Γ⊢f∶ΠFAB) = Γ⊢f∶ΠFAB
≝-project₁ (ΣI Γ⊢x∶A⊢B∶𝒰 Γ⊢a≝a'∶A Γ⊢b≝b'∶B[a]) = ΣI Γ⊢x∶A⊢B∶𝒰 (≝-project₁ Γ⊢a≝a'∶A) (≝-project₁ Γ⊢b≝b'∶B[a])
≝-project₁ (ΣE Γ,z∶ΣFAB⊢C∶𝒰 Γ,x∶A,y∶B⊢g∶C[ΣIxy] Γ⊢a∶A Γ⊢b∶B[a] C[ΣIab]≡A _) = ΣE Γ,z∶ΣFAB⊢C∶𝒰 Γ,x∶A,y∶B⊢g∶C[ΣIxy] (ΣI (ctxHead⊩ (wfctx₁ Γ,x∶A,y∶B⊢g∶C[ΣIxy]) .proof) Γ⊢a∶A Γ⊢b∶B[a]) C[ΣIab]≡A
≝-project₁ (+Iˡ Γ⊢A∶𝒰 Γ⊢B∶𝒰 Γ⊢a≝a'∶A) = +Iˡ Γ⊢A∶𝒰 Γ⊢B∶𝒰 (≝-project₁ Γ⊢a≝a'∶A)
≝-project₁ (+Iʳ Γ⊢A∶𝒰 Γ⊢B∶𝒰 Γ⊢b≝b'∶A) = +Iʳ Γ⊢A∶𝒰 Γ⊢B∶𝒰 (≝-project₁ Γ⊢b≝b'∶A)
≝-project₁ (+Eˡ Γ,z∶+FAB⊢C∶𝒰 Γ,x∶A⊢l∶C[+Iˡx] Γ,y∶B⊢r∶C[+Iʳy] Γ⊢a∶A _ C[+Iˡa]≡D) =
  let Γ⊩A = ctxHead⊩ (wfctx₁ Γ,x∶A⊢l∶C[+Iˡx])
      Γ⊩B = ctxHead⊩ (wfctx₁ Γ,y∶B⊢r∶C[+Iʳy])
      ℓᴬ = Γ⊩A .universe
      ℓᴮ = Γ⊩B .universe
  in
  +E Γ,z∶+FAB⊢C∶𝒰 Γ,x∶A⊢l∶C[+Iˡx] Γ,y∶B⊢r∶C[+Iʳy]
     (+Iˡ (lift⊩ (max≥₁ ℓᴬ ℓᴮ) (Γ⊩A .proof))
          (lift⊩ (max≥₂ ℓᴬ ℓᴮ) (Γ⊩B .proof))
          Γ⊢a∶A)
     C[+Iˡa]≡D
≝-project₁ (+Eʳ Γ,z∶+FAB⊢C∶𝒰 Γ,x∶A⊢l∶C[+Iˡx] Γ,y∶B⊢r∶C[+Iʳy] Γ⊢b∶B _ C[+Iʳb]≡D) =
  let Γ⊩A = ctxHead⊩ (wfctx₁ Γ,x∶A⊢l∶C[+Iˡx])
      Γ⊩B = ctxHead⊩ (wfctx₁ Γ,y∶B⊢r∶C[+Iʳy])
      ℓᴬ = Γ⊩A .universe
      ℓᴮ = Γ⊩B .universe
  in
  +E Γ,z∶+FAB⊢C∶𝒰 Γ,x∶A⊢l∶C[+Iˡx] Γ,y∶B⊢r∶C[+Iʳy]
     (+Iʳ (lift⊩ (max≥₁ ℓᴬ ℓᴮ) (Γ⊩A .proof))
          (lift⊩ (max≥₂ ℓᴬ ℓᴮ) (Γ⊩B .proof))
          Γ⊢b∶B)
     C[+Iʳb]≡D
≝-project₁ (𝟙E Γ,z∶𝟙F⊢C∶𝒰 Γ⊢b∶C[𝟙I] C[𝟙I]≡A) = 𝟙E Γ,z∶𝟙F⊢C∶𝒰 Γ⊢b∶C[𝟙I] (𝟙I (wfctx₁ Γ⊢b∶C[𝟙I])) C[𝟙I]≡A
≝-project₁ (ℕIˢ Γ⊢a≝b∶A) = ℕIˢ (≝-project₁ Γ⊢a≝b∶A)
≝-project₁ (ℕEᶻ Γ,z∶ℕF⊢C∶𝒰 Γ⊢cᶻ∶C[ℕIᶻ] Γ,z∶ℕF,f∶C⊢cˢ∶C[ℕIˢz] C[ℕIᶻ]≡A) = ℕE Γ,z∶ℕF⊢C∶𝒰 Γ⊢cᶻ∶C[ℕIᶻ] Γ,z∶ℕF,f∶C⊢cˢ∶C[ℕIˢz] (ℕIᶻ (wfctx₁ Γ⊢cᶻ∶C[ℕIᶻ])) C[ℕIᶻ]≡A
≝-project₁ (ℕEˢ Γ,z∶ℕF⊢C∶𝒰 Γ⊢cᶻ∶C[ℕIᶻ] Γ,z∶ℕF,f∶C⊢cˢ∶C[ℕIˢz] Γ⊢n∶ℕF _ C[ℕIˢn]≡A) = ℕE Γ,z∶ℕF⊢C∶𝒰 Γ⊢cᶻ∶C[ℕIᶻ] Γ,z∶ℕF,f∶C⊢cˢ∶C[ℕIˢz] (ℕIˢ Γ⊢n∶ℕF) C[ℕIˢn]≡A
≝-project₁ (=I Γ⊢a≝a'∶A) = =I (≝-project₁ Γ⊢a≝a'∶A)
≝-project₁ (=E C c a c[a]≡b C[a,a,=I]≡A) = =E C c a a (=I a) C[a,a,=I]≡A

ap : ∀ {Γ x a A b B b' B'}
   → Γ ⊢ a ∶ A
   → Γ , x ∶ A ⊢ b ∶ B
   → b [ a ←₁ x ] ≡ b'
   → B [ a ←₁ x ] ≡ B'
   → Γ ⊢ b' ∶ B'

≝-project₂ (≝-reflexivity Γ⊢a∶A) = Γ⊢a∶A
≝-project₂ (≝-symmetry Γ⊢b≝a∶A) = ≝-project₁ Γ⊢b≝a∶A
≝-project₂ (≝-transitivity Γ⊢a≝b∶A Γ⊢b≝c∶A₁) = ≝-project₂ Γ⊢b≝c∶A₁
≝-project₂ (≝-subst Γ⊢a≝b∶A Γ⊢A≝B∶𝒰) = ≝-subst (≝-project₂ Γ⊢a≝b∶A) Γ⊢A≝B∶𝒰
≝-project₂ (ΠI Γ,x∶A⊢b≝b'∶B) = ΠI (≝-project₂ Γ,x∶A⊢b≝b'∶B)
≝-project₂ (ΠE Γ,x∶A⊢b∶B Γ⊢a∶A _ B[a]≡B') = {!!}
≝-project₂ (ΠU Γ⊢f∶ΠFAB) = {!!}
≝-project₂ (ΣI Γ⊢x∶A⊢B∶𝒰 Γ⊢a≝a'∶A Γ⊢b≝b'∶B[a]) = ΣI {!!} {!!} {!!}
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

ap Γ⊢a∶A Γ,x∶A⊢b∶B b[a]≡b' B[a]≡B' = {!!}
```


open import Oscar.Prelude
open import Oscar.Class.Amgu
open import Oscar.Class.Thickandthin
open import Oscar.Class.IsDecidable
open import Oscar.Class.Bind
open import Oscar.Class.Fmap
open import Oscar.Class.Smap
open import Oscar.Data.¶
open import Oscar.Data.Descender
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Substitist
open import Oscar.Data.Fin
open import Oscar.Data.Maybe
open import Oscar.Data.Decidable
open import Oscar.Data.Proposequality
open import Oscar.Data.Vec
open import Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality
import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality
import Oscar.Property.Thickandthin.FinTermProposequalityMaybeProposequality
import Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality
import Oscar.Property.Monad.Maybe
import Oscar.Class.IsDecidable.¶
import Oscar.Property.Functor.SubstitunctionExtensionTerm
import Oscar.Class.Surjection.⋆

module Oscar.Class.Amgu.Term∃SubstitistMaybe where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  flexFlex : ∀ {m} → Fin m → Fin m → ∃ Substitist m
  flexFlex {↑ m} x y with check[ Maybe ] x y
  … | ↑ y' = m , (x , i y') , ∅
  … | ∅ = ↑ m , ∅
  flexFlex {∅} ()

  flexRigid : ∀ {m} → Fin m → Term m → Maybe (∃ Substitist m)
  flexRigid {↑ m} x t with check[ Maybe ] x t
  … | ↑ t' = ↑ (m , (x , t') , ∅)
  … | ∅ = ∅
  flexRigid {∅} () _

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  module _ ⦃ _ : IsDecidable 𝔓 ⦄ where

    mutual

      instance

        ⋆amguTerm : Amgu Term (∃_ ∘ Substitist) Maybe
        ⋆amguTerm .Amgu.amgu leaf leaf acc = ↑ acc
        ⋆amguTerm .Amgu.amgu leaf (function _ _) acc = ∅
        ⋆amguTerm .Amgu.amgu leaf (s' fork t') acc = ∅
        ⋆amguTerm .Amgu.amgu (s' fork t') leaf acc = ∅
        ⋆amguTerm .Amgu.amgu (s' fork t') (function _ _) acc = ∅
        ⋆amguTerm .Amgu.amgu (s1 fork s2) (t1 fork t2) acc = amgu s2 t2 =<< amgu s1 t1 acc
        ⋆amguTerm .Amgu.amgu (function fn₁ ts₁) leaf acc = ∅
        ⋆amguTerm .Amgu.amgu (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc
         with fn₁ ≟ fn₂
        … | ↓ _ = ∅
        … | ↑ _
         with n₁ ≟ n₂
        … | ↓ _ = ∅
        … | ↑ ∅ = amgu ts₁ ts₂ acc
        ⋆amguTerm .Amgu.amgu (function fn₁ ts₁) (_ fork _) acc = ∅
        ⋆amguTerm .Amgu.amgu (i x) (i y) (m , ∅) = ↑ flexFlex x y
        ⋆amguTerm .Amgu.amgu (i x) t     (m , ∅) = flexRigid x t
        ⋆amguTerm .Amgu.amgu t     (i x) (m , ∅) = flexRigid x t
        ⋆amguTerm .Amgu.amgu s     t  (n , _,_ {n = m} (z , r) σ) = fmap′ (λ {(n' , σ') → n' , (z , r) , σ'}) (amgu {x = m} (§ (r for z) $ s) (§ (r for z) $ t) (n Σ., σ))

        ⋆amguVecTerm : ∀ {N} → Amgu (Terms N) (∃_ ∘ Substitist) Maybe
        ⋆amguVecTerm .Amgu.amgu ∅ ∅ acc = ↑ acc
        ⋆amguVecTerm .Amgu.amgu (t₁ , t₁s) (t₂ , t₂s) acc = amgu t₁s t₂s =<< amgu t₁ t₂ acc

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  module _ ⦃ _ : IsDecidable 𝔓 ⦄ where

    mgu : ∀ {m} → Term m → Term m → Maybe $ ∃ Substitist m
    mgu {m} s t = amgu s t (m Σ., ∅)

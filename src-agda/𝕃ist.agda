{-# OPTIONS --allow-unsolved-metas #-}
module 𝕃ist where

open import OscarPrelude
open import Successor
open import Membership
open import DecidableMembership renaming (DecidableMembership to RDecidableMembership)

data 𝕃 {𝑨} (𝐴 : Set 𝑨) : Set 𝑨
data _∉𝕃_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) : 𝕃 𝐴 → Set 𝑨

data 𝕃 {𝑨} (𝐴 : Set 𝑨) where
  ∅ : 𝕃 𝐴
  ✓ : {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → x₀ ∉𝕃 x₁s → 𝕃 𝐴

instance Successor𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} → {x₀ : 𝐴} → {x₁s : 𝕃 𝐴} → Successor (x₀ ∉𝕃 x₁s) (𝕃 𝐴)
Successor.⊹ Successor𝕃 = ✓

data _∉𝕃_ {𝑨} {𝐴 : Set 𝑨} (𝔞 : 𝐴) where
  ∅ : 𝔞 ∉𝕃 ∅
  ● : ∀ {x₀} → 𝔞 ≢ x₀ → ∀ {x₁s} → 𝔞 ∉𝕃 x₁s → (x₀∉x₁s : x₀ ∉𝕃 x₁s) → 𝔞 ∉𝕃 ✓ x₀∉x₁s

data _∈𝕃_ {𝑨} {𝐴 : Set 𝑨} : (𝔞 : 𝐴) → 𝕃 𝐴 → Set {-𝑨-} where
  here : (𝔞 : 𝐴) {xs : 𝕃 𝐴} (𝔞∉xs : 𝔞 ∉𝕃 xs) → 𝔞 ∈𝕃 (✓ 𝔞∉xs)
  there : {x : 𝐴} {xs : 𝕃 𝐴} (x∉xs : x ∉𝕃 xs) {𝔞 : 𝐴} → 𝔞 ∈𝕃 xs → 𝔞 ∈𝕃 ✓ x∉xs

∈→¬∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → x ∈𝕃 xs → ¬ x ∉𝕃 xs
∈→¬∉ {𝑨} {𝐴} {.𝔞} {.(✓ {_} {_} {𝔞} {xs} 𝔞∉xs)} (here 𝔞 {xs = xs} 𝔞∉xs) (● {x₀ = .𝔞} x {x₁s = .xs} x₂ .𝔞∉xs) = x refl
∈→¬∉ {𝑨} {𝐴} {x₁} {.(✓ {_} {_} {x} {∅} ∅)} (there {x = x} {xs = .∅} ∅ {𝔞 = .x₁} ()) (● {x₀ = .x} x₃ {x₁s = .∅} ∅ .∅)
∈→¬∉ {𝑨} {𝐴} {.𝔞} {.(✓ {_} {_} {x} {✓ {_} {_} {𝔞} {x₁s} x∉xs} (● {_} {_} {_} {𝔞} x₁ {x₁s} x∉xs₁ x∉xs))} (there {x = x} {xs = .(✓ {_} {_} {𝔞} {x₁s} x∉xs)} (● {x₀ = .𝔞} x₁ {x₁s = x₁s} x∉xs₁ x∉xs) {𝔞 = .𝔞} (here 𝔞 {xs = .x₁s} .x∉xs)) (● {x₀ = .x} x₃ {x₁s = .(✓ {_} {_} {𝔞} {x₁s} x∉xs)} (● {x₀ = .𝔞} x₂ {x₁s = .x₁s} x₄ .x∉xs) .(● {_} {_} {_} {𝔞} x₁ {x₁s} x∉xs₁ x∉xs)) = x₂ refl
∈→¬∉ {𝑨} {𝐴} {x} {.(✓ {_} {_} {x₁} {✓ {_} {_} {x₀} {x₁s} x∉xs} (● {_} {_} {_} {x₀} x₂ {x₁s} x∉xs₁ x∉xs))} (there {x = x₁} {xs = .(✓ {_} {_} {x₀} {x₁s} x∉xs)} (● {x₀ = x₀} x₂ {x₁s = x₁s} x∉xs₁ x∉xs) {𝔞 = .x} (there {x = .x₀} {xs = .x₁s} .x∉xs {𝔞 = .x} x₃)) (● {x₀ = .x₁} x₄ {x₁s = .(✓ {_} {_} {x₀} {x₁s} x∉xs)} (● {x₀ = .x₀} x₅ {x₁s = .x₁s} x₆ .x∉xs) .(● {_} {_} {_} {x₀} x₂ {x₁s} x∉xs₁ x∉xs)) = ∈→¬∉ x₃ x₆

∉→¬∈ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → x ∉𝕃 xs → ¬ x ∈𝕃 xs
∉→¬∈ {𝑨} {𝐴} {x} {.∅} ∅ ()
∉→¬∈ {𝑨} {𝐴} {.𝔞} {.(✓ {_} {_} {𝔞} {x₁s} x₁)} (● {x₀ = .𝔞} x {x₁s = x₁s} x₂ x₁) (here 𝔞 {xs = .x₁s} .x₁) = x refl
∉→¬∈ {𝑨} {𝐴} {x} {.(✓ {_} {_} {x₀} {x₁s} x₁)} (● {x₀ = x₀} x₂ {x₁s = x₁s} x₃ x₁) (there {x = .x₀} {xs = .x₁s} .x₁ {𝔞 = .x} x₄) = ∉→¬∈ x₃ x₄

private
  foo : ∀ {𝑨} {𝐴 : Set 𝑨} {x x₀ : 𝐴} (x₁ : _≡_ {𝑨} {𝐴} x x₀) (x₂ : _∈𝕃_ {𝑨} {𝐴} x (✓ {_} {_} {x₀} {∅} ∅) → ⊥) → ⊥
  foo {𝑨} {𝐴} {x} {.x} refl x₂ = x₂ (here x ∅)

  foo₂ : (𝑨 : Level)
    (𝐴   : Set 𝑨                   )
    (x₀  : 𝐴                       )
    (x₁s : 𝕃 𝐴                     )
    (x₁  : x₀ ∉𝕃 x₁s                )
    (x   : 𝐴                       )
    (x₂  : 𝐴                       )
    (x₃  : x₂ ≡ x₀ → ⊥             )
    (x₄  : x₂ ∉𝕃 x₁s                )
    (x₅  : ¬ (x ∈𝕃 ✓ (● x₃ x₄ x₁)) )
    (x₆  : x ≡ x₂) → ⊥
  foo₂ 𝑨 𝐴 x₀ x₁s x₁ x .x x₃ x₄ x₅ refl = x₅ (here x (● x₃ x₄ x₁)) -- x₅ (here x (● x₃ x₄ x₁))

  foo₃ : (𝑨   : Level)
       (𝐴   : Set 𝑨                   )
       (x₀  : 𝐴                       )
       (x₁s : 𝕃 𝐴                     )
       (x₁  : x₀ ∉𝕃 x₁s                )
       (x   : 𝐴                       )
       (x₂  : 𝐴                       )
       (x₃  : x₂ ≡ x₀ → ⊥             )
       (x₄  : x₂ ∉𝕃 x₁s                )
       (x₅  : ¬ (x ∈𝕃 ✓ (● x₃ x₄ x₁)) )
       (x₆  : x ≡ x₀)
       → ⊥
  foo₃ 𝑨 𝐴 x₀ x₁s x₁ .x₀ x₂ x₃ x₄ x₅ refl = x₅ (there (● x₃ x₄ x₁) (here x₀ x₁))

¬∈→∉ : ∀ {𝑨} {𝐴 : Set 𝑨} {x : 𝐴} {xs : 𝕃 𝐴} → ¬ x ∈𝕃 xs → x ∉𝕃 xs
¬∈→∉ {𝑨} {𝐴} {x} {∅} x₁ = ∅
¬∈→∉ {𝑨} {𝐴} {x} {✓ {x₀ = x₀} {x₁s = .∅} ∅} x₂ = ● (λ {x₁ → foo x₁ x₂}) ∅ ∅
¬∈→∉ {𝑨} {𝐴} {x} {✓ {x₀ = x₂} {x₁s = .(✓ {_} {_} {x₀} {x₁s} x₁)} (● {x₀ = x₀} x₃ {x₁s = x₁s} x₄ x₁)} x₅ = ● (λ {x₆ → foo₂ 𝑨 𝐴 x₀ x₁s x₁ x x₂ x₃ x₄ x₅ x₆}) (● (λ {x₆ → foo₃ 𝑨 𝐴 x₀ x₁s x₁ _ x₂ x₃ x₄ x₅ x₆}) (¬∈→∉ (λ z → x₅ (there (● x₃ x₄ x₁) (there x₁ z)))) x₁) (● x₃ x₄ x₁)

pattern tail= x₁s = ✓ {x₁s = x₁s} _
pattern 𝕃⟦_⟧ x₀ = ✓ {x₀ = x₀} ∅
pattern _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s = ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _)

--{-# DISPLAY ✓ {x₀ = x₀} (● {x₁} _ {x₂s} _ _) = _₀∷₁_∷⟦_⟧ x₀ x₁ x₂s #-}

pattern _↶_↷_ x₀∉x₂s x₀≢x₁ x₁∉x₂s = ● x₀≢x₁ x₀∉x₂s x₁∉x₂s
pattern _₀∷₁⟦_⟧ x₀ x₁s = ● {x₀} _ {x₁s} _ _

instance Membership𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} → Membership 𝐴 (𝕃 𝐴)
Membership._∉_ Membership𝕃 x xs = x ∉𝕃 xs
Membership._∈_ Membership𝕃 x xs = ¬ x ∉𝕃 xs
fst (Membership.xor-membership Membership𝕃) x₁ x₂ = x₁ x₂
snd (Membership.xor-membership Membership𝕃) x₁ x₂ = x₂ x₁

{-# DISPLAY _∉𝕃_ = _∉_ #-}

private

  add-1-preserves-∈𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} {x₁s : 𝕃 𝐴} (x₀∉x₁s : x₀ ∉ x₁s) {x : 𝐴} → x ∈ x₁s → x ∈ ✓ x₀∉x₁s
  add-1-preserves-∈𝕃 x₀∉x₁s x₁ (● x₃ x₄ x₂) = x₁ x₄

_∉𝕃?_ : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ → (x : 𝐴) (xs : 𝕃 𝐴) → Dec (x ∉𝕃 xs)
_∉𝕃?_ x ∅ = yes ∅
_∉𝕃?_ x 𝕃⟦ x₀ ⟧ with x ≟ x₀
… | yes refl = no λ {(● x₂ _ .∅) → x₂ refl}
… | no x≢x₀ = yes (● x≢x₀ ∅ ∅)
_∉𝕃?_ x (✓ {x₀ = x₀} (● {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s)) with x ≟ x₀
… | yes refl = no λ { (● x₃ _ _) → x₃ refl}
… | no x≢x₀ with x ≟ x₁
… | yes refl = no λ { ((_ ↶ x≢x ↷ _) ↶ _ ↷ _) → x≢x refl }
… | no x≢x₁ with x ∉𝕃? x₂s
_∉𝕃?_ x₁ (✓ {x₂} (● {x₀} x₃ {.∅} x₄ x₀∉x₁s)) | no x≢x₀ | (no x≢x₁) | (yes ∅) = yes (● x≢x₀ (● x≢x₁ ∅ x₀∉x₁s) (● _ _ x₀∉x₁s))
_∉𝕃?_ x₁ (✓ {x₄} (● {x₃} x₅ {.(✓ asdf)} x₆ x₀∉x₁s)) | no x≢x₀ | (no x≢x₁) | (yes (● x₂ asdf₁ asdf)) = yes (● x≢x₀ (● x≢x₁ (● x₂ asdf₁ asdf) x₀∉x₁s) (● x₅ x₆ x₀∉x₁s))
… | no x∈x₂s = no λ { (● {_} x₃ {.(✓ x₁∉x₂s)} (● x₄ x∉x₀s .x₁∉x₂s) .(● x₀≢x₁ x₀∉x₂s x₁∉x₂s)) → x∈x₂s x∉x₀s}

¬∉→∈ : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ {x : 𝐴} {xs : 𝕃 𝐴} → ¬ x ∉𝕃 xs → x ∈𝕃 xs
¬∉→∈ {𝑨} {𝐴} {x} {∅} x₁ = ⊥-elim (x₁ ∅)
¬∉→∈ {𝑨} {𝐴} {x} {✓ {x₀ = x₀} {x₁s = ∅} ∅} x₂ with x ≟ x₀
¬∉→∈ {𝑨} {𝐴} {x} {✓ {x₀ = x₀} {x₁s = ∅} ∅} x₂ | yes refl = here x ∅
¬∉→∈ {𝑨} {𝐴} {x} {✓ {x₀ = x₀} {x₁s = ∅} ∅} x₂ | no x≢x₀ = ⊥-elim (x₂ (● x≢x₀ ∅ ∅))
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s with a ≟ x₀
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s | yes refl = here a (● {_} {_} {_} {x₁} x₀≢x₁ {x₂s} x₀∉x₂s x₁∉x₂s)
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s | no a≢x₀ with a ≟ x₁
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s | no a≢x₀ | yes refl = there (● x₀≢x₁ x₀∉x₂s x₁∉x₂s) (here a {x₂s} x₁∉x₂s)
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s | no a≢x₀ | no a≢x₁ with a ∉𝕃? x₂s
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s | no a≢x₀ | no a≢x₁ | yes a∉x₂s = ⊥-elim (¬a∉x₀s (● a≢x₀ (● a≢x₁ a∉x₂s x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s)))
¬∉→∈ {𝑨} {𝐴} {a} {✓ {x₀ = x₀} {x₁s = ✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s} (● {x₀ = ._} x₀≢x₁ {x₁s = ._} x₀∉x₂s ._)} ¬a∉x₀s | no a≢x₀ | no a≢x₁ | no ¬a∉x₂s = there (● x₀≢x₁ x₀∉x₂s x₁∉x₂s) (there x₁∉x₂s (¬∉→∈ ¬a∉x₂s))

instance DecidableMembership𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ → RDecidableMembership 𝐴 (𝕃 𝐴)
RDecidableMembership._∉?_ DecidableMembership𝕃 = _∉𝕃?_
RDecidableMembership._∈?_ DecidableMembership𝕃 x X with _∉𝕃?_ x X
… | yes x∉X = no (λ x₁ → x₁ x∉X)
… | no x∈X = yes x∈X

x∈singleton→x=singleton : ∀ {𝑨} {𝐴 : Set 𝑨} {x₀ : 𝐴} ⦃ _ : Eq 𝐴 ⦄ {x₀∉∅ : _∉_ ⦃ Membership𝕃 ⦄ x₀ 𝕃.∅} {x : 𝐴} → x ∈ ✓ x₀∉∅ → x ≡ x₀
x∈singleton→x=singleton {𝑨} {𝐴} {x₀} {∅} {x} x₁ with x ≟ x₀
x∈singleton→x=singleton {𝑨} {𝐴} {x₀} {∅} {x} x₁ | yes refl = refl
x∈singleton→x=singleton {𝑨} {𝐴} {x₀} {∅} {x} x∈x₀ | no x≢x₀ = ⊥-elim (x∈x₀ (● x≢x₀ ∅ ∅))

foo₄ : (𝑨        : Level                                  )
        (𝐴        : Set 𝑨                                 )
        (x₁       : 𝐴                                     )
        (x₂s      : 𝕃 𝐴                                   )
        (x₁∉x₂s   : x₁ ∉ x₂s                              )
        (x₀       : 𝐴                                     )
        (x₀≢x₁    : x₀ ≡ x₁ → ⊥                           )
        (x₀∉x₂s   : x₀ ∉ x₂s                              )
        (x        : 𝐴                                     )
        (x∈x₀∉x₁s : x ∉ ✓ (● x₀≢x₁ x₀∉x₂s x₁∉x₂s) → ⊥     )
        (x≢x₀     : x ≡ x₀ → ⊥                            )
        (x≢x₁     : x ≡ x₁ → ⊥                            )
        (x∉x₂s    : x ∉ x₂s                               )
        (x₂       : x ≡ x₀                                ) → ⊥
foo₄ 𝑨 𝐴 x₁ x₂s x₁∉x₂s x₀ x₀≢x₁ x₀∉x₂s .x₀ x∈x₀∉x₁s x≢x₀ x≢x₁ x∉x₂s refl = x≢x₀ refl

if-diff-then-somewhere-else-∈𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ {x₀ : 𝐴} (x₁s : 𝕃 𝐴) {x₀∉x₁s : x₀ ∉ x₁s} {x : 𝐴} → x ∈ ✓ x₀∉x₁s → x ≢ x₀ → x ∈ x₁s
if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} ∅ {∅} {x} x∈x₀∉∅ x≢x₀ ∅ = x≢x₀ (x∈singleton→x=singleton x∈x₀∉∅)
if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} (✓ {x₀ = x₁} {x₁s = x₂s} x₁∉x₂s) {● x₀≢x₁ x₀∉x₂s ._} {x} x∈x₀∉x₁s x≢x₀ (● x≢x₁ x∉x₂s _) = x∈x₀∉x₁s (● (λ {x₂ → foo₄ 𝑨 𝐴 x₁ x₂s x₁∉x₂s x₀ x₀≢x₁ x₀∉x₂s _ x∈x₀∉x₁s x≢x₀ x≢x₁ x∉x₂s x₂}) (● x≢x₁ x∉x₂s x₁∉x₂s) (● x₀≢x₁ x₀∉x₂s x₁∉x₂s))

--if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} .∅  {x₀∉x₁s} {x} x∈x₀s x≢x₀ ∅ = {!!}
--if-diff-then-somewhere-else-∈𝕃 {𝑨} {𝐴} {x₀} ._  {x₀∉x₁s} {x} x∈x₀s x≢x₀ (● {x₀ = x₁} x≢x₁ {x₁s = x₂s} x∉x₂s x₁∉x₂s) = {!!}

record TotalUnion {ℓ} (m : Set ℓ) (M : Set ℓ) ⦃ _ : Membership m M ⦄ : Set ℓ
 where
  field
    union : M → M → M
    unionLaw1 : ∀ {x : m} {X₁ X₂ : M} → x ∈ X₁ → x ∈ union X₁ X₂
    unionLaw2 : ∀ {x : m} {X₁ X₂ : M} → x ∈ X₂ → x ∈ union X₁ X₂
    unionLaw3 : ∀ {x : m} {X₁ X₂ : M} → x ∈ union X₁ X₂ → x ∈ X₁ ⊎ x ∈ X₂

open TotalUnion ⦃ … ⦄ public

{-# DISPLAY TotalUnion.union _ = union #-}

add1-then-∈𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ {x₀ : 𝐴} (x₁s : 𝕃 𝐴) {x₀∉x₁s : x₀ ∉ x₁s} → x₀ ∈ ✓ {x₀ = x₀} x₀∉x₁s
add1-then-∈𝕃 {𝑨} {𝐴} {{x}} {x₀} x₁s {.x₁} (● {x₀ = .x₀} x₂ {x₁s = .x₁s} x₃ x₁) = x₂ refl

private

  module ModuleTotalUnion𝕃 {ℓ} (A : Set ℓ) ⦃ _ : Eq A ⦄ where
    -- TODO aribtrarily moves from l₀s to r₀s, so a union of 10 and 2 elements takes longer than a union of 2 and 10 elements
    totalUnion : 𝕃 A → 𝕃 A → 𝕃 A
    totalUnion ∅ ∅ = ∅
    totalUnion ∅ r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) = r₀s
    totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) ∅ = l₀s
    totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) with l₀ ∉? r₀s
    totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) | no l₀∈r₀s = totalUnion l₁s r₀s
    totalUnion l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s) r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s) | yes l₀∉r₀s = totalUnion l₁s (✓ l₀∉r₀s)

    totalUnionLaw2 : ∀ {x : A} {X₁ X₂ : 𝕃 A} → x ∈ X₂ → x ∈ totalUnion X₁ X₂
    totalUnionLaw2 {x₁} {∅} {∅} x₂ x₃ = x₂ x₃
    totalUnionLaw2 {x₁} {∅} {✓ x₂} x₃ x₄ = x₃ x₄
    totalUnionLaw2 {x₁} {✓ x₂} {∅} x₃ x₄ = x₃ ∅
    totalUnionLaw2 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈r₀s x∉l₀s∪r₀s with l₀ ∉? r₀s
    totalUnionLaw2 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈r₀s x∉l₀s∪r₀s | no l₀∈r₀s = totalUnionLaw2 {X₁ = l₁s} x∈r₀s $ x∉l₀s∪r₀s
    totalUnionLaw2 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈r₀s x∉l₀s∪r₀s | yes l₀∉r₀s = (totalUnionLaw2 {X₁ = l₁s} $ add-1-preserves-∈𝕃 l₀∉r₀s x∈r₀s) $ x∉l₀s∪r₀s

    totalUnionLaw1 : ∀ {x : A} {X₁ X₂ : 𝕃 A} → x ∈ X₁ → x ∈ totalUnion X₁ X₂
    totalUnionLaw1 {x₁} {∅} {∅} x₂ x₃ = x₂ x₃
    totalUnionLaw1 {x₁} {∅} {✓ {x₀ = x₀} {x₁s = X₂} x₂} x₃ x₄ = x₃ ∅
    totalUnionLaw1 {x₁} {✓ {x₀ = x₀} {x₁s = X₁} x₂} {∅} x₃ x₄ = x₃ x₄
    totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s with l₀ ∉? r₀s
    totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | no l₀∈r₀s with x ≟ l₀
    totalUnionLaw1 {.l₀} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | no l₀∈r₀s | yes refl = totalUnionLaw2 {X₁ = l₁s} l₀∈r₀s $ x∉l₀s∪r₀s
    totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | no l₀∈r₀s | no x≢l₀ = let x∈l₁s = if-diff-then-somewhere-else-∈𝕃 l₁s x∈l₀s x≢l₀ in totalUnionLaw1 x∈l₁s $ x∉l₀s∪r₀s
    -- with x ≟ l₀
    -- = {!!}
    totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | yes l₀∉r₀s with x ≟ l₀
  --totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} l₀∈l₀s l₀∉l₀s∪r₀s | yes l₀∉r₀s | yes refl = {!l₀∉r₀s!}
    totalUnionLaw1 {.l₀}    {✓ {l₀}       {l₁s}       l₀∉l₁s}        {✓ {r₀}           {r₁s} r₀∉r₁s} l₀∈l₀s l₀∉l₁s∪l₀r₀s | yes (● l₀≢r₀ l₀∉r₁s .r₀∉r₁s) | (yes refl) =
      let l₀∈l₀r₀s : l₀ ∈ (✓ (● l₀≢r₀ l₀∉r₁s r₀∉r₁s))
          l₀∈l₀r₀s = add1-then-∈𝕃 (✓ r₀∉r₁s)
           in totalUnionLaw2 {X₁ = l₁s} l₀∈l₀r₀s $ l₀∉l₁s∪l₀r₀s
    totalUnionLaw1 {x} {l₀s@(✓ {x₀ = l₀} {x₁s = l₁s} l₀∉l₁s)} {r₀s@(✓ {x₀ = r₀} {x₁s = r₁s} r₀∉r₁s)} x∈l₀s x∉l₀s∪r₀s | yes l₀∉r₀s | no x≢l₀ = let x∈l₁s = if-diff-then-somewhere-else-∈𝕃 l₁s x∈l₀s x≢l₀ in totalUnionLaw1 x∈l₁s $ x∉l₀s∪r₀s

    totalUnionLaw3 : ∀ {x : A} {X₁ X₂ : 𝕃 A} → x ∈ totalUnion X₁ X₂ → x ∈ X₁ ⊎ x ∈ X₂
    totalUnionLaw3 = {!!}

instance TotalUnion𝕃 : ∀ {𝑨} {𝐴 : Set 𝑨} ⦃ _ : Eq 𝐴 ⦄ → TotalUnion 𝐴 (𝕃 𝐴)
TotalUnion.union TotalUnion𝕃 = ModuleTotalUnion𝕃.totalUnion _
TotalUnion.unionLaw1 TotalUnion𝕃 = ModuleTotalUnion𝕃.totalUnionLaw1 _
TotalUnion.unionLaw2 (TotalUnion𝕃 {𝑨} {𝐴} {{x}}) {x₁} {X₁} {X₂} x₂ x₃ = ModuleTotalUnion𝕃.totalUnionLaw2 𝐴 {X₁ = X₁} {X₂ = X₂} x₂ x₃
TotalUnion.unionLaw3 TotalUnion𝕃 = ModuleTotalUnion𝕃.totalUnionLaw3 _

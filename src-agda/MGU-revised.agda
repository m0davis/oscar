
module MGU-revised where

--open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Agda.Primitive
open import Agda.Builtin.Equality

open import Prelude.Product using (Σ; _,_; fst; snd; _×_; curry; uncurry)
open import Prelude.Equality using (eqReasoningStep; _∎; sym; trans; cong)
open import Prelude.Function using (_∘_)
open import Prelude.Empty using (⊥)
open import Prelude.Sum using (left; right) renaming (Either to _⊎_)
open import Prelude.Maybe using (Maybe; just; nothing)

private
  ∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃ = Σ _

open import Prelude using (_$_)

open import Relation.Binary

open import Prolegomenon

import Relation.Binary.Indexed as I

record Unificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  field
    monoidTransformer : MonoidTransformer ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

  open MonoidTransformer monoidTransformer public renaming
    (_≈ˢ_ to _=ᵗ_
    ;Carrierˢ to T
    ;Carrierᵐ to S
    ;_≈ᵐ_ to _=ˢ_)

  Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
  Property {ℓ} = S → Set ℓ

  Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
  Nothing P = ∀ s → P s → ⊥

  IsUnifier : (t₁ t₂ : T) → Property
  IsUnifier t₁ t₂ s = s ◃ t₁ =ᵗ s ◃ t₂

  field
    unify : (t₁ t₂ : T) → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (IsUnifier t₁ t₂)

record PairUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  field
    monoidTransformer : MonoidTransformer ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

  open MonoidTransformer monoidTransformer public renaming
    (_≈ˢ_ to _=ᵗ_
    ;Carrierˢ to T
    ;Carrierᵐ to S
    ;_≈ᵐ_ to _=ˢ_)

  Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
  Property {ℓ} = S × S → Set ℓ

  Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
  Nothing P = ∀ u → P u → ⊥

  IsUnifier : (t₁ t₂ : T) → Property
  IsUnifier t₁ t₂ u = let (s₁ , s₂) = u in s₁ ◃ t₁ =ᵗ s₂ ◃ t₂

  field
    unify : (t₁ t₂ : T)
          → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (IsUnifier t₁ t₂)

module MakePairUnificationoidFromUnificationoid where

  postulate
    ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Level
    unificationoid : Unificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

  open Unificationoid unificationoid

  pairUnificationoid : PairUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
  PairUnificationoid.monoidTransformer pairUnificationoid = monoidTransformer
  PairUnificationoid.unify pairUnificationoid t₁ t₂ with unify t₁ t₂
  PairUnificationoid.unify pairUnificationoid t₁ t₂ | left x = left (λ {(s₁ , s₂) x₁ → x {!!} {!!}})
  PairUnificationoid.unify pairUnificationoid t₁ t₂ | right (s₁ , snd₁) = {!!}

  {-
    s ◃ swap ◃ t₁ = s ◃ t₂
    swap ∙ swap = ε
    want: x , y s.t. x ◃ t₁ = x ◃ t₂
    easy: x = s ∙ swap, y = s

    harder:
    s₁ ◃ t₁ = s₂ ◃ t₂
    want: x s.t. x ◃ t₁ = x ◃ t₂
  -}

record MostGeneralUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  infix 4 _≠ᵗ_
  field
    unificationoid : Unificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

  open Unificationoid unificationoid public

  _≤_ : (s₋ : S) (s₊ : S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
  _≤_ s₋ s₊ = ∃ λ s → s ∙ s₊ =ˢ s₋

  _≠ᵗ_ : T → T → Set ℓ⁼ᵗ
  _≠ᵗ_ t₁ t₂ = t₁ =ᵗ t₂ → ⊥

  _<_ : (s₋ : S) (s₊ : S) → Set (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)
  _<_ s₋ s₊ = s₋ ≤ s₊ × (∀ t → (s₊ ◃ t) ≠ᵗ t → (s₋ ◃ t) ≠ᵗ t) × ∃ λ t → (s₋ ◃ t) ≠ᵗ t × (s₊ ◃ t) =ᵗ t
  --the set of T that are changed by a applying substitution is strictly less with s₊ than with s₋. That is, s₋ makes more changes than s₊.
  --that is, if s₊ makes a change to t then so does s₋, but there is some t s.t. s₋ makes a change but s₊ does not

  MostGenerally : ∀ {ℓ} (P : Property {ℓ}) → Property
  MostGenerally P s₊ = P s₊ × ∀ s₋ → P s₋ → s₋ ≤ s₊

  field
    isMguIfUnifier : (t₁ t₂ : T) → (ru : ∃ λ s → unify t₁ t₂ ≡ right s) →
      Prelude.case ru of (λ {((u , _) , _) → MostGenerally (IsUnifier t₁ t₂) u})

  mgu : (t₁ t₂ : T) → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (MostGenerally $ IsUnifier t₁ t₂)
  mgu t₁ t₂ with unify t₁ t₂ | Prelude.graphAt (unify t₁) t₂
  mgu t₁ t₂ | left x | ef = left x
  mgu t₁ t₂ | right x | Prelude.ingraph eq with isMguIfUnifier t₁ t₂ (x , eq)
  mgu t₁ t₂ | right (fst₁ , snd₁) | (Prelude.ingraph eq) | dfsd = right (fst₁ , dfsd)

record PairMostGeneralUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  field
    monoidTransformer : MonoidTransformer ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

  open MonoidTransformer monoidTransformer public renaming
    (_≈ˢ_ to _=ᵗ_
    ;Carrierˢ to T
    ;Carrierᵐ to S
    ;_≈ᵐ_ to _=ˢ_)

  Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
  Property {ℓ} = S × S → Set ℓ

  Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
  Nothing P = ∀ u → P u → ⊥

  IsUnifier : (t₁ t₂ : T) → Property
  IsUnifier t₁ t₂ u = let (s₁ , s₂) = u in s₁ ◃ t₁ =ᵗ s₂ ◃ t₂

  infix 4 _≤_
  _≤_ : (s₋ : S × S) (s₊ : S × S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
  _≤_ u₋ u₊ =
    let s₋₁ , s₋₂ = u₋
        s₊₁ , s₊₂ = u₊ in
    ∃ λ s → s ∙ s₊₁ =ˢ s₋₁ × s ∙ s₊₂ =ˢ s₋₂

  MostGenerally : ∀ {ℓ} (P : Property {ℓ}) → Property
  MostGenerally P u₊ = P u₊ × ∀ u₋ → P u₋ → u₋ ≤ u₊

  field
    mgu : (t₁ t₂ : T)
          → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (MostGenerally (IsUnifier t₁ t₂))

record Isomorphic {a} {A : Set a} {ℓᵃ} {_=ᵃ_ : A → A → Set ℓᵃ} (isEquivalenceᵃ : IsEquivalence _=ᵃ_)  {b} {B : Set b} {ℓᵇ} {_=ᵇ_ : B → B → Set ℓᵇ} (isEquivalenceᵇ : IsEquivalence _=ᵇ_) : Set (a ⊔ ℓᵃ ⊔ b ⊔ ℓᵇ) where
  field
    toA : B → A
    toB : A → B
    rtA : (x : A) → toA (toB x) =ᵃ x
    rtB : (x : B) → toB (toA x) =ᵇ x
    isoA : (x₁ x₂ : A) → x₁ =ᵃ x₂ → toB x₁ =ᵇ toB x₂
    isoB : (x₁ x₂ : B) → x₁ =ᵇ x₂ → toA x₁ =ᵃ toA x₂

record Splittable ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  field
    mostGeneralUnificationoid : MostGeneralUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

  open MostGeneralUnificationoid mostGeneralUnificationoid public

  S-independent : (t₁ t₂ : T) → Set (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)
  S-independent t₁ t₂ = ∀ t₁s s → s ◃ t₁ =ᵗ t₁s → MostGenerally (λ s → s ◃ t₁ =ᵗ t₁s) s → s ◃ t₂ =ᵗ t₂

  S-Invertable : Property
  S-Invertable s = s ∙ s =ˢ ε

  Swapifies : (t₁ t₂ : T) → Property
  Swapifies t₁ t₂ s = s ◃ t₁ =ᵗ t₂ × s ◃ t₂ =ᵗ t₁

  UnifiesOnLeft : (t₁ t₂ : T) → Property
  UnifiesOnLeft t₁ t₂ s = s ◃ t₁ =ᵗ t₂

  RelativeIdentity : T → Property
  RelativeIdentity t s = s ◃ t =ᵗ t

  field
    make-S-independent :
      (t₁ t₂ : T) →
        ∃ λ swap₁ → S-Invertable swap₁ ×
                    ∃ λ t₁′ → MostGenerally (Swapifies t₁ t₁′) swap₁ ×
                              ∃ λ s₁ → MostGenerally (UnifiesOnLeft t₁ t₁′) s₁ ×
                                       RelativeIdentity t₂ s₁

    Tᵢ : Prelude.List Prelude.Nat → Set
    toTᵢ : T → ∃ Tᵢ

  pairUnification : PairMostGeneralUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
  PairMostGeneralUnificationoid.monoidTransformer pairUnification = monoidTransformer
  PairMostGeneralUnificationoid.mgu pairUnification t₁ t₂ with make-S-independent t₁ t₂
  PairMostGeneralUnificationoid.mgu pairUnification t₁ t₂ | (swap₁ , swap₁∙swap₁=ε , t₁′ , ((swap₁◃t₁=t₁′ , swap₁◃t₁′=t₁) , mgswap) , slip₁ , (slip₁◃t₁=t₁′ , mgleft) , slip₁◃t₂=t₂) with mgu t₁′ t₂
--  … | (left NoT₁T₂) =
  PairMostGeneralUnificationoid.mgu pairUnification t₁ t₂ | (swap₁ , swap₁∙swap₁=ε , t₁′ , ((swap₁◃t₁=t₁′ , swap₁◃t₁′=t₁) , mgswap) , slip₁ , (slip₁◃t₁=t₁′ , mgleft) , slip₁◃t₂=t₂) | (left NoT₁T₂) =
    left
    λ {(s₁ , s₂) s₁◃t₁=s₂◃t₂ →
    {!let (s₁′ , s₂′ , s₁′◃t₁=s₂′◃t₂ , s₁′∙swap₁◃t₂=swap₁◃t₂ , s₂′∙swap₁∙s₂′◃t₂=swap₁∙s₂′◃t₂) = helper!}}
    {-
    NoT₁T₂ (slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ∙ swap₁)
      (let t₁′▹s₂=t₁′ : {!!} -- s₂ ◃ t₁′ =ᵗ t₁′
           t₁′▹s₂=t₁′ = {!!} in {!!})}
    -}
         -- ? s₂ (s₁ ◃ t₁) (symˢ t₁▹s₁=t₂▹s₂ , (λ s₁₋ t₂▹s₁₋=t₁▹s₁ → {!!} , {!!})) in {!!})}) -- mgur s₂ (t₁ ▹ s₁) (symˢ t₁▹s₁=t₂▹s₂ , ?)
  PairMostGeneralUnificationoid.mgu pairUnification t₁ t₂ | (swap₁ , swap₁∙swap₁=ε , t₁′ , ((swap₁◃t₁=t₁′ , swap₁◃t₁′=t₁) , mgswap) , slip₁ , (slip₁◃t₁=t₁′ , mgleft) , slip₁◃t₂=t₂) | (right (s , s◃t₁′=s◃t₂ , mgur)) = right $ (s ∙ slip₁ , s) , {!!} , (λ {(s₁′ , s₂′) s₁′◃t₁=s₂′◃t₂ → {!!}})

  {-
  goal
  slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ∙ swap₁ ◃ t₁′        =ᵗ slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ∙ swap₁ ◃ t₂
  by slip₁◃t₁=t₁′
  slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ∙ swap₁ ∙ slip₁ ◃ t₁ =ᵗ slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ∙ swap₁ ◃ t₂
  conjecture: swap₁ ∙ slip₁ ◃ t₁ = t₁
  conjecture: s₁ ∙ swap₁ ◃ t₂ = swap₁ ◃ t₂
  slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ◃ t₁ =ᵗ slip₁ ∙ s₂ ∙ swap₁ ∙ swap₁ ◃ t₂
  by swap₁∙swap₁=ε
  slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ◃ t₁ =ᵗ slip₁ ∙ s₂ ◃ t₂
  by s₁◃t₁=s₂◃t₂
  slip₁ ∙ s₂ ∙ swap₁ ∙ s₂ ◃ t₂ =ᵗ slip₁ ∙ s₂ ◃ t₂
  conjecture: s₂ ∙ swap₁ ∙ s₂ ◃ t₂ = swap₁ ∙ s₂ ◃ t₂
  slip₁ ∙ swap₁ ∙ s₂ ◃ t₂ =ᵗ slip₁ ∙ s₂ ◃ t₂
  conjecture: swap₁ ∙ s₂ ◃ t₂ = slip₁ ∙ s₂ ◃ t₂
  slip₁ ∙ slip₁ ∙ s₂ ◃ t₂ =ᵗ slip₁ ∙ s₂ ◃ t₂
  conjecture: slip₁ ∙ slip₁ = slip₁
  slip₁ ∙ s₂ ◃ t₂ =ᵗ slip₁ ∙ s₂ ◃ t₂

  goal : ?0 ◃ t₁′ = ?0 ◃ t₂

  e.g.
  f(x,g(y),z) = f(g(y),x,h(z))
  s₁ = x → g(y) , z → h(z) ; s₂ = x → g(y)
  s = x → a ; y → b ; z → c
  t₁′ = f(a,g(b),c)
  S = a → g(y) , x → g(b) , c → h(z)
  s⁻¹ = a → x , b → y , c → z
  s₁ ∙ s⁻¹ = a → g(y) , b → y , c → h(z)
  s₂ ∙ s₁ ∙ s⁻¹ = a → g(y) , b → y , c → h(z) , x → g(y)
  S = s ∙ s₂ ∙ s₁ ∙ s⁻¹ = a → g(b) , b → b , c → h(c) , x → g(b) , y → b , z → c
  t₁′ ▹ S = f(g(b),g(b),h(c))
  t₂ ▹ S = f(g(b),g(b),h(c))

  f(x,g(y),z) = f(g(y),x,h(z))
  s₁ = x → g(x) , y → x , z → h(z) ; s₂ = y → x , x → g(x)
  s = x → a ; y → b ; z → c
  t₁′ = f(a,g(b),c)
  s⁻¹ = a → x , b → y , c → z
  s₁ ∙ s⁻¹ = a → g(x) , b → x , c → h(z) , x → g(x) , y → x , z → h(z)
  s₂ ∙ s₁ ∙ s⁻¹ = a → g(g(x)) , b → g(x) , c → h(z) , x → g(g(x)) , y → g(x) , z → h(z)
  s ∙ s₂ ∙ s₁ ∙ s⁻¹ = a → g(g(a)) , b → g(a) , c → h(c) , x → g(g(a)) , y → g(a) , z → h(c)

  s⁻¹          = a → x    , b → y , c → z
  s₁ ∙ s⁻¹     = a → g(x) , b → x , c → h(z) , x → g(x) , y → x , z → h(z)
  s ∙ s₁ ∙ s⁻¹ = a → g(a) , b → a , c → h(c) , x → g(a) , y → a , z → h(c)

  s₁′          = a → g(a) , b → a , c → h(c)
  s₂′          = y → a , x → g(a) , z → c

  let swap₁ = x → a , y → b , z → c , a → x , b → y , c → z -- take variables common to t₁ and t₂, and swap them for variables outside of either (and outside of s₁ or s₂?)
        s₁ ∙ swap₁ = x → a , y → b , z → c , a → g(x) , b → x , c → h(z)
  s₁′ = swap₁ ∙ s₁ ∙ swap₁ = a → g(a) , b → a , c → h(c)
  s₁′ = swap₁ ∙ s₁ ∙ swap₁
  let slip₁ = x → a , y → b , z → c
  let s₂′ = slip₁ ∙ s₂ = y → a , x → g(a) , z → c
  s₂′ ∙ s₁′ = a → g(a) , b → a , c → h(c) , y → a , x → g(a) , z → c
  slip₁ ∙ s₂ ∙ swap₁ ∙ s₁ ∙ swap₁

  f(g(g(a)),g(g(a)),h(c)) = f(g(g(a)),g(g(a)),h(h(c)))

  f(x,g(y),z) = f(g(y),x,h(z))
  -}
  {-
  … | (t₁' , s-independent , s , t₁'= , s⁻¹ , t₁=) with mgu t₁' t₂
  … | (left NoT₁T₂) = left $ λ {(s₁ , s₂) t₁▹s₁=t₂▹s₂ → NoT₁T₂ {!≈ˢ-over-▹-⟶-≈ᵐ!} {!isMonoidTransformer!}}
  … | (right x) = right {!!}
  -}

{-
  suppose t₁ ▹ s₁ = t₂ ▹ s₂
  given:
    t₁' ▹ * ≠ t₂ ▹ *

  t₁ = t₁' ▹ s
  try s = the most general such

  t₁ = t₁' ▹ s⁻¹
  t₁' = t₁ ▹ s
  t₁ ▹ s₁ = t₂ ▹ s₂
  s ∙ s⁻¹ = ε

  t₁' ▹ s⁻¹ ▹ s₁ = t₂ ▹ s₂

  finx x = s₁

  t₁ ▹ x = t₂ ▹ s⁻¹ ▹ x
  t₁' ▹ x = t₂ ▹ x
  t₁ ▹ s ▹ x = t₂ ▹ x
  t₁ ▹ s ▹ x = t₂ ▹ s⁻¹ ▹ s ▹ x
-}

data STerm (A : Set) : Set where
  ι : A → STerm A
  _fork_ : STerm A → STerm A → STerm A
  leaf : STerm A

sub : {V : Set} → (V → Maybe (STerm V)) → STerm V → STerm V
sub σ (ι x) with σ x
sub σ (ι x) | nothing = ι x
sub σ (ι x) | just x₁ = x₁
sub σ (t fork t₁) = sub σ t fork sub σ t₁
sub σ leaf = leaf

{-
  Sᵢ : List (V × T) → S
  Tᵢ : List V → T
  indexS : S → ∃ Sᵢ
  indexT : T → ∃ Tᵢ
  _▹ᵢ_ : {vs : List V} {vts : List (V × T)} → Tᵢ vs → Sᵢ vts → ∃ λ
  (t : T) (s : S) → t ▹ s
  (V → T) → T → T

  getTermIndexedByAVariable : (v : V) (t : T) → T → T
  getTermFromIndexedTerm :

  v ∈ variables s → t ▹ s
-}

record IsSeparableInto {sx s x} (SX : Set sx) (S : Set s) (X : Set x) : Set (s ⊔ x ⊔ sx) where
  field
    separate : SX → S × X
    combine : S × X → SX
    iso : ∀ sx → combine (separate sx) ≡ sx

record IsSeparableInto₂ {sx s x} (SX : Set sx) (X : Set x) (S : X → Set s) : Set (s ⊔ x ⊔ sx) where
  field
    separate : SX → Σ X S
    combine : Σ X S → SX
    iso : ∀ sx → combine (separate sx) ≡ sx

record Separableoid sx s x : Set (lsuc (sx ⊔ s ⊔ x)) where
  field
    SX : Set sx
    S : Set s
    X : Set x
    separable : IsSeparableInto SX S X

-- record FreeVariableoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ ℓᵛ ℓ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
--   field
--     monoidTransformer : MonoidTransformer ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ

--   open MonoidTransformer monoidTransformer public renaming
--     (_≈ˢ_ to _=ᵗ_
--     ;Carrierˢ to T
--     ;Carrierᵐ to S
--     ;_≈ᵐ_ to _=ˢ_)

--   field
--     termVariableoid : Setoid ℓᵛ ℓ⁼ᵛ
--     termStructureoid :

--   open Setoid Variable public using () renaming
--     (Carrier to V
--     ;_≈_ to _=ᵛ_)

--   field
--     termVariables : Term → Pred Variable ℓᵛ

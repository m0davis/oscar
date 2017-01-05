
module MGU where

--open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Agda.Primitive
open import Agda.Builtin.Equality

open import Prelude.Product using (Σ; _,_; fst; snd; _×_; curry; uncurry)
open import Prelude.Equality using (_≡_; eqReasoningStep; _∎; sym; trans; cong)
open import Prelude.Function using (_∘_)
open import Prelude.Empty using (⊥)
open import Prelude.Sum using () renaming (Either to _⊎_)
open import Prelude.Maybe using (Maybe; just; nothing)

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ = Σ _

open import Prelude using (_$_)

open import Relation.Binary
open import Algebra
open import Category.Applicative.Predicate

--record IsTermSubstitution {ℓᵗ} {ℓ⁼ᵗ} {ℓˢ} {ℓ⁼ˢ}

record TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  field
    Term : Setoid ℓᵗ ℓ⁼ᵗ
    Substitution : Monoid ℓˢ ℓ⁼ˢ

  open Setoid Term public using () renaming
    (Carrier to T
    ;_≈_ to _=ᵗ_)

  open Monoid Substitution public using () renaming
    (Carrier to S
    ;_≈_ to _=ˢ_
    ;_∙_ to _∙_
    ;ε to ∅)

  infixl 6 _▹_
  field
    _▹_ : T → S → T
    ▹-=ˢ-to-ᵗ : ∀ {s s′} → s =ˢ s′ → (t : T) → t ▹ s =ᵗ t ▹ s′
    ▹-=ᵗ-to-=ˢ : ∀ {s s′} → ((t : T) → t ▹ s =ᵗ t ▹ s′) → s =ˢ s′
    ▹-extracts-∙ : (t : T) (s₁ s₂ : S) → t ▹ s₁ ∙ s₂ =ᵗ t ▹ s₁ ▹ s₂

open import Relation.Unary
import Relation.Binary.Indexed as I

open import Relation.Nullary

record 𝓩ero (A : Set) : Set where
  field
    𝓩 : A

open 𝓩ero ⦃ … ⦄

instance 𝓩eroLevel : 𝓩ero Level
𝓩ero.𝓩 𝓩eroLevel = lzero

open import Agda.Builtin.Nat
instance 𝓩eroNat : 𝓩ero Nat
𝓩ero.𝓩 𝓩eroNat = zero

record IsSeparableInto {sx s x} (SX : Set sx) (S : Set s) (X : Set x) : Set (s ⊔ x ⊔ sx) where
  field
    break : SX → S × X
    combine : S → X → SX
    iso : ∀ sx → uncurry combine (break sx) ≡ sx

record Separableoid sx s x : Set (lsuc (sx ⊔ s ⊔ x)) where
  field
    SX : Set sx
    S : Set s
    X : Set x
    separable : IsSeparableInto SX S X

_AND_ = _×_

NOT_ = ¬_

_NAND_ : ∀ {a b} (A : Set a) (B : Set b) → Set ((a ⊔ b))
_NAND_ A B = (NOT A) × (NOT B)

_OR_ : ∀ {a b} (A : Set a) (B : Set b) → Set ((a ⊔ b))
_OR_ A B = NOT (A NAND B)

_XOR_ : ∀ {a b} (A : Set a) (B : Set b) → Set ((a ⊔ b))
_XOR_ A B = (A OR B) AND (NOT (A AND B))

asdf : (A B : Set) → Dec A → A XOR B → Prelude.Either A (¬ ¬ B)
asdf A B x (¬[¬A×¬B] , ¬[A×B]) with x
asdf A B x (¬[¬A×¬B] , ¬[A×B]) | yes p = _⊎_.left p
asdf A B x (¬[¬A×¬B] , ¬[A×B]) | no ¬p = _⊎_.right (λ {x₁ → ¬[¬A×¬B] (¬p , x₁)})

import Data.Empty
frf : Dec Data.Empty.⊥
frf = no (λ x → x)

{-
record LAW (A : Set) (B : Set) (E : EITHER A B) : Set where
  open import Data.Empty
  open EITHER E
  ¬A→B : ¬ A → ¬ ¬ B
  ¬A→B ¬a ¬b with e
  ... | ei = ei (λ {(a , ¬b) → ¬a a})
-}

record FiniteMembership : Set where

open import Data.List


module _ {ℓ} {A : Set ℓ} where

  listMembers : List A → Pred A ℓ
  listMembers [] x₁ = Prelude.⊥′
  listMembers (x ∷ xs) y = (y ≡ x) OR (listMembers xs y)

  _∈L_ : A → List A → Set ℓ
  x ∈L xs = x ∈ listMembers xs

  data _inL_ (y : A) : List A → Set where
    [] : ∀ {xs} → y inL (y ∷ xs)
    _∷_ : ∀ {x xs} → (ys : y inL xs) → y inL (x ∷ xs)

  ListMembers : List A → Pred A lzero
  ListMembers xs = _inL xs

  _∈LL_ : A → List A → Set
  x ∈LL xs = x ∈ ListMembers xs

  toLL : (y : A) (xs : List A) → y ∈L xs → y ∈LL xs
  toLL y [] x = Prelude.⊥′-elim x
  toLL y (x ∷ xs) y∈Lxxs = {!!} -- toLL y xs x₁

record Boolean (True : Set) (False : Set) : Set where
  field
    bool : True XOR False

{-
record L {ℓ} (A : Set ℓ) : Set ℓ where
  inductive
  field
    EMPTY : Set
    empty : L A
    head : A XOR ⊥
    tail : {!!}
-}
{-
    head : A XOR Prelude.⊥
    tail :
    empty : Prelude.⊥′
    list : EITHER Prelude.⊥′ (L A)
-}
record FreeVariableoid ℓᵛ∈ᵗ ℓᵛ∈ˢ⁺ ℓᵛ∈ˢ⁻ ℓᵛ ℓ⁼ᵛ ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
       (termSubstitution : TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ)
  : Set (lsuc (ℓᵛ∈ᵗ ⊔ ℓᵛ∈ˢ⁺ ⊔ ℓᵛ∈ˢ⁻ ⊔ ℓᵛ ⊔ ℓ⁼ᵛ ⊔ ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  open TermSubstitution termSubstitution
  field
    Variable : Setoid ℓᵛ ℓ⁼ᵛ
    TermStructure : Set

  open Setoid Variable public using () renaming
    (Carrier to V
    ;_≈_ to _=ᵛ_)

  field
    termVariables : T → Pred V ℓᵛ∈ᵗ
    termStructure : T → Set
    substitutionSourceVariables : S → Pred V ℓᵛ∈ˢ⁺
    substitutionTargetVariables : S → Pred V ℓᵛ∈ˢ⁻

  _ᵛ∈ᵗ_ : V → T → Set ℓᵛ∈ᵗ
  _ᵛ∈ᵗ_ v t = v ∈ termVariables t

  field
    termNumberOfVariables : (t : T) → ∃ λ (vs : List V) → (∀ v → (v ∈L vs → v ᵛ∈ᵗ t) × (v ᵛ∈ᵗ t → v ∈L vs))
    elementsDefineVariables : (t : T) → V

  _ᵛ∈ˢ⁺_ : V → S → Set ℓᵛ∈ˢ⁺
  _ᵛ∈ˢ⁺_ v s = v ∈ substitutionSourceVariables s

  _ᵛ∈ˢ⁻_ : V → S → Set ℓᵛ∈ˢ⁻
  _ᵛ∈ˢ⁻_ v s = v ∈ substitutionTargetVariables s

  field
    foo : ∀ {v t s} → v ᵛ∈ᵗ t → ¬ v ᵛ∈ˢ⁺ s → v ᵛ∈ᵗ (t ▹ s)
    isSep : IsSeparableInto T TermStructure V

  data D : Set where

record CorrectTermSubstitution ℓᵛ∈ᵗ ℓᵛ∈ˢ⁺ ℓᵛ∈ˢ⁻ ℓᵛ ℓ⁼ᵛ ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
       (termSubstitution : TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ)
  : Set (lsuc (ℓᵛ∈ᵗ ⊔ ℓᵛ∈ˢ⁺ ⊔ ℓᵛ∈ˢ⁻ ⊔ ℓᵛ ⊔ ℓ⁼ᵛ ⊔ ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
  open TermSubstitution termSubstitution
  field
    Variable : Setoid ℓᵛ ℓ⁼ᵛ

  open Setoid Variable public using () renaming
    (Carrier to V
    ;_≈_ to _=ᵛ_)

  field
    termVariables : T → Pred V ℓᵛ∈ᵗ
    substitutionSourceVariables : S → Pred V ℓᵛ∈ˢ⁺
    substitutionTargetVariables : S → Pred V ℓᵛ∈ˢ⁻

  _ᵛ∈ᵗ_ : V → T → Set ℓᵛ∈ᵗ
  _ᵛ∈ᵗ_ v t = v ∈ termVariables t

  _ᵛ∈ˢ⁺_ : V → S → Set ℓᵛ∈ˢ⁺
  _ᵛ∈ˢ⁺_ v s = v ∈ substitutionSourceVariables s

  _ᵛ∈ˢ⁻_ : V → S → Set ℓᵛ∈ˢ⁻
  _ᵛ∈ˢ⁻_ v s = v ∈ substitutionTargetVariables s

  field
    foo : ∀ {v t s} → v ᵛ∈ᵗ t → ¬ v ᵛ∈ˢ⁺ s → v ᵛ∈ᵗ (t ▹ s)

  data D : Set where

data IsRight {a b} {A : Set a} {B : Set b} (e : _⊎_ A B) : Set (a ⊔ b) where
  right : B → IsRight e

module MostGeneralMGU where

  record Unificationoid {ℓᵗ} {ℓ⁼ᵗ} {ℓˢ} {ℓ⁼ˢ}
         (termSubstitution : TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ)
    : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
    open TermSubstitution termSubstitution
    Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
    Property {ℓ} = S → Set ℓ

    Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
    Nothing P = ∀ s → P s → ⊥

    IsUnifier : (t₁ t₂ : T) → Property
    IsUnifier t₁ t₂ s = t₁ ▹ s =ᵗ t₂ ▹ s

    field
      unify : (t₁ t₂ : T) → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (IsUnifier t₁ t₂)

    unifier : (t₁ t₂ : T) → Maybe S
    unifier t₁ t₂ with unify t₁ t₂
    unifier t₁ t₂ | _⊎_.left x = nothing
    unifier t₁ t₂ | _⊎_.right (x , _) = just x

    unifier-is-correct : (t₁ t₂ : T) → Nothing (IsUnifier t₁ t₂) → unifier t₁ t₂ ≡ nothing
    unifier-is-correct = {!!}

  record IsMostGeneralUnification ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
         {termSubstitution : TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ}
         (unificationoid : Unificationoid termSubstitution)
    : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
    open TermSubstitution termSubstitution
    open Unificationoid unificationoid

    _≤_ : (s₋ : S) (s₊ : S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
    _≤_ s₋ s₊ = ∃ λ s → s ∙ s₊ =ˢ s₋

    MostGenerally : ∀ {ℓ} (P : Property {ℓ}) → Property
    MostGenerally P s₊ = ∀ s₋ → P s₋ → s₋ ≤ s₊

    field
      isMguIfUnifier : (t₁ t₂ : T) → (ru : IsRight (unify t₁ t₂)) →
        Prelude.case ru of λ {((right (u , _))) → MostGenerally (IsUnifier t₁ t₂) u}
      --mgu : (t₁ t₂ : T) → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (MostGenerally $ IsUnifier t₁ t₂)

    mgu : (t₁ t₂ : T) → Maybe S
    mgu = unifier

  record MostGeneralUnificationoid ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
         (termSubstitution : TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ)
    : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
    open TermSubstitution termSubstitution
    Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
    Property {ℓ} = S → Set ℓ

    Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
    Nothing P = ∀ s → P s → ⊥

    IsUnifier : (t₁ t₂ : T) → Property
    IsUnifier t₁ t₂ s = t₁ ▹ s =ᵗ t₂ ▹ s

    _≤_ : (s₋ : S) (s₊ : S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
    _≤_ s₋ s₊ = ∃ λ s → s ∙ s₊ =ˢ s₋

    MostGenerally : ∀ {ℓ} (P : Property {ℓ}) → Property
    MostGenerally P s₊ = P s₊ × ∀ s₋ → P s₋ → s₋ ≤ s₊

    field
      mgu : (t₁ t₂ : T) → Nothing (IsUnifier t₁ t₂) ⊎ ∃ (MostGenerally $ IsUnifier t₁ t₂)

  record PairUnification ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ
         (termSubstitution : TermSubstitution ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ)
    : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
    open TermSubstitution termSubstitution
    Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
    Property {ℓ} = S → S → Set ℓ

    Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
    Nothing P = ∀ s₁ s₂ → P s₁ s₂ → ⊥

    IsUnifier : (t₁ t₂ : T) → Property
    IsUnifier t₁ t₂ s₁ s₂ = t₁ ▹ s₁ =ᵗ t₂ ▹ s₂

    infix 4 _≤_
    _≤_ : (s₋ : S) (s₊ : S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
    _≤_ s₋ s₊ = ∃ λ s → s ∙ s₊ =ˢ s₋

    infix 4 _<!_
    _<!_ : (s₋ : S) (s₊ : S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
    _<!_ s₋ s₊ = s₋ ≤ s₊ × (s₋ =ˢ s₊ → ⊥)

    _≤₂_ : (s₋ : S × S) (s₊ : S × S) → Set (ℓˢ ⊔ ℓ⁼ˢ)
    _≤₂_ s₋ s₊ =
      let s₋₁ , s₋₂ = s₋
          s₊₁ , s₊₂ = s₊ in
      ∃ λ s → s ∙ s₊₁ =ˢ s₋₁ × s ∙ s₊₂ =ˢ s₋₂

    MostGenerally : ∀ {ℓ} (P : Property {ℓ}) → Property
    MostGenerally P s₊₁ s₊₂ = P s₊₁ s₊₂ × ∀ s₋₁ s₋₂ → P s₋₁ s₋₂ →
      ((s₋₁ <! s₊₁) ⊎
       (s₋₂ <! s₊₂)) ⊎
       (s₋₁ ≤ s₊₁ × s₋₂ ≤ s₊₂)

{-
  mgu f(x,y) f(y,x)

  x → w , y → z || x → z , y → w

  mgu f(x,y) f(g(y),x)

  x → g(z) || y → z , x → y

  mgu f(x,y) f(y,z)

  x → y , y → z || ∅              ≥₂
  x → w , y → z || y → w          ≥₂
  x → w , y → v || y → w , z → v  ≥₂
  y → v || y → x , z → v  ≥₂
  ∅ || y → x , z → y

  x → w , y → v , z → v || y → w , z → v
  x → y , y → f(z) || z → f(z)



  f(x  , g(x,y)     ,w)
  x → g(z)
  w →? v


  f(g(z), g(g(z),y) ,v)
  v →? w

  possible unifers:
  x → g(z)    , w → v      ||
  x → g(h(a)) , w → v      || z → h(a)
  x → g(z)                 || z → h(y) , v → w


-}

    field
      mgu : (t₁ t₂ : T)
            → Nothing (IsUnifier t₁ t₂) ⊎ (∃ $ ∃ ∘ MostGenerally (IsUnifier t₁ t₂))



-- record Something ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
--   field
--     Terminus : Setoid ℓᵗ ℓ⁼ᵗ
--     Simplex : Monoid ℓˢ ℓ⁼ˢ

--   open Setoid Terminus public using () renaming
--     (Carrier to T
--     ;_≈_ to _=T=_)

--   open Monoid Simplex public using () renaming
--     (Carrier to S
--     ;_≈_ to _=S=_
--     ;_∙_ to _∙_
--     ;ε to ∅)

--   infixl 6 _▹_
--   field
--     _▹_ : T → S → T
--     -- equivalence of S implies substitutivity in (T,▹)
--     ▹-=S=-to-=T= : ∀ {s s′} → s =S= s′ → (t : T) → t ▹ s =T= t ▹ s′
--     -- applications of simplexi are equivalent across all termini only when the simplexi are equivalent
--     -- that is, equivalence of S is as compact is it can be while still respecting equivalence in (T,▹)
--     ▹-=T=-to-=S= : ∀ {s s′} → ((t : T) → t ▹ s =T= t ▹ s′) → s =S= s′
--     -- S extracts to ▹ in (T,∙)
--     ▹-∙-compositional : (t : T) (s₁ s₂ : S) → t ▹ s₁ ∙ s₂ =T= t ▹ s₁ ▹ s₂

-- -- module NotIndexed where

-- --   record MGU ℓᵗ ℓ⁼ᵗ ℓˢ ℓ⁼ˢ : Set (lsuc (ℓᵗ ⊔ ℓ⁼ᵗ ⊔ ℓˢ ⊔ ℓ⁼ˢ)) where
-- --     infixr 8 _◃_
-- --     --infixr 9 _◇_
-- --     field
-- --       𝓣erm : Setoid ℓᵗ ℓ⁼ᵗ

-- --     open Setoid 𝓣erm public using () renaming (Carrier to 𝓣; _≈_ to _=ᵗ_)

-- --     field
-- --       𝓢ubstition : Semigroup ℓˢ ℓ⁼ˢ -- TODO Monoid?

-- --     open Semigroup 𝓢ubstition public using () renaming
-- --       (Carrier to 𝓢
-- --       ;_≈_ to _=ˢ_
-- --       ; _∙_ to _◇_)

-- --     --field
-- --     --  𝓼ubstitute : RawPApplicative (λ x x₁ → {!!})

-- --     _◃'_ : 𝓢 → 𝓣 → 𝓣
-- --     _◃'_ = {!!}

-- --     field
-- --       _◃_ : 𝓢 → 𝓣 → 𝓣
-- --       ◃-=ˢ-to-=ᵗ : ∀ {𝒮 𝒮′} → 𝒮 =ˢ 𝒮′ → (𝒯 : 𝓣) → 𝒮 ◃ 𝒯 =ᵗ 𝒮′ ◃ 𝒯
-- --       ◃-=ᵗ-to-=ˢ : ∀ {𝒮 𝒮′} → ((𝒯 : 𝓣) → 𝒮 ◃ 𝒯 =ᵗ 𝒮′ ◃ 𝒯) → 𝒮 =ˢ 𝒮′

-- --     field

-- --       --_◇_ : 𝓢 → 𝓢 → 𝓢
-- --       ◇-compositional : (𝒯 : 𝓣) (𝒮₁ 𝒮₂ : 𝓢) → (𝒮₂ ◇ 𝒮₁) ◃ 𝒯 =ᵗ 𝒮₂ ◃ 𝒮₁ ◃ 𝒯

-- --     ◇-associative : (𝒮₁ 𝒮₂ 𝒮₃ : 𝓢) → 𝒮₃ ◇ (𝒮₂ ◇ 𝒮₁) =ˢ (𝒮₃ ◇ 𝒮₂) ◇ 𝒮₁
-- --     ◇-associative 𝒮₁ 𝒮₂ 𝒮₃ = {!!}

-- --     Property : ∀ {ℓ} → Set (ℓˢ ⊔ lsuc ℓ)
-- --     Property {ℓ} = 𝓢 → Set ℓ

-- --     Nothing : ∀ {ℓ} → (P : Property {ℓ}) → Set (ℓ ⊔ ℓˢ)
-- --     Nothing P = ∀ 𝒮 → P 𝒮 → ⊥

-- --     Unifies : (𝒯₁ 𝒯₂ : 𝓣) → Property
-- --     Unifies 𝒯₁ 𝒯₂ 𝒮 = 𝒮 ◃ 𝒯₁ ≡ 𝒮 ◃ 𝒯₂

-- --     _≤_ : (σ₋ : 𝓢) (σ₊ : 𝓢) → Set (ℓˢ ⊔ ℓ⁼ˢ)
-- --     _≤_ σ₋ σ₊ = ∃ λ σ → σ ◇ σ₊ =ˢ σ₋

-- --     Max : ∀ {ℓ} (P : Property {ℓ}) → Property
-- --     Max P σ₊ = P σ₊ × ∀ σ₋ → P σ₋ → σ₋ ≤ σ₊

-- --     field
-- --       mgu : (𝒯₁ 𝒯₂ : 𝓣) → Nothing (Unifies 𝒯₁ 𝒯₂) ⊎ ∃ λ (σ : 𝓢) → Max (Unifies 𝒯₁ 𝒯₂) σ

-- -- -- module Indexed where

-- -- --   record MGU ℓⁱ ℓᵛ ℓᵗ ℓˢ : Set (lsuc (ℓⁱ ⊔ ℓᵛ ⊔ ℓᵗ ⊔ ℓˢ)) where
-- -- --     field
-- -- --       𝓲 : Set ℓⁱ
-- -- --       𝓥 : 𝓲 → Set ℓᵛ
-- -- --       𝓣 : 𝓲 → Set ℓᵗ

-- -- --     _↦_ : (s t : 𝓲) → Set (ℓᵛ ⊔ ℓᵗ)
-- -- --     _↦_ s t = 𝓥 s → 𝓣 t

-- -- --     infix 14 _≐_
-- -- --     _≐_ : {s t : 𝓲} → s ↦ t → s ↦ t → Set (ℓᵛ ⊔ ℓᵗ)
-- -- --     _≐_ σ σ′ = ∀ x → σ x ≡ σ′ x

-- -- --     field
-- -- --       _◃_ : ∀ {s t} → s ↦ t → 𝓣 s → 𝓣 t
-- -- --       ≐-◃-identity : {!!}

-- -- --     _◇_ : ∀ {r s t : 𝓲} → (σ₂ : s ↦ t) (σ₁ : r ↦ s) → r ↦ t
-- -- --     _◇_ σ₂ σ₁ = (σ₂ ◃_) ∘ σ₁

-- -- --     field
-- -- --       𝓢 : 𝓲 → 𝓲 → Set ℓˢ
-- -- --       sub : ∀ {s t} → 𝓢 s t → s ↦ t

-- -- -- --     Property : ∀ {ℓ} → 𝓲 → Set (lsuc ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- --     Property {ℓ} s = ∀ {t} → s ↦ t → Set ℓ

-- -- -- --     Nothing : ∀ {ℓ m} → (P : Property {ℓ} m) → Set (ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- --     Nothing P = ∀ {n} f → P {n} f → ⊥

-- -- -- --     Unifies : ∀ {i} (t₁ t₂ : 𝓣 i) → Property i
-- -- -- --     Unifies t₁ t₂ f = f ◃ t₁ ≡ f ◃ t₂

-- -- -- --     _≤_ : ∀ {m n n'} (f : m ↦ n) (g : m ↦ n') → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- --     _≤_ f g = ∃ λ f' → f ≐ (f' ◇ g)

-- -- -- --     Max : ∀ {ℓ m} (P : Property {ℓ} m) → Property m
-- -- -- --     Max P = (λ f → P f × (∀ {n} f' → P {n} f' → f' ≤ f))

-- -- -- --     field
-- -- -- --       mgu : ∀ {m} (t₁ t₂ : 𝓣 m) →
-- -- -- --             Nothing (Unifies t₁ t₂) ⊎ (∃ λ n → ∃ λ (σ : 𝓢 m n) → (Max (Unifies t₁ t₂)) (sub σ))

-- -- -- -- -- -- -- open import Prelude.Function
-- -- -- -- -- -- -- open import Relation.Binary.HeterogeneousEquality.Core as H using (_≅_ ; ≅-to-≡)
-- -- -- -- -- -- -- open import Prelude.Equality

-- -- -- -- -- -- -- record MGU-addIndex-to-noIndex* {ℓⁱ ℓⱽ ℓᵀ ℓˢ}
-- -- -- -- -- -- --                             (m : MGU-addIndex ℓⁱ ℓⱽ ℓᵀ ℓˢ) : Set (lsuc (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)) where
-- -- -- -- -- -- --   open MGU-addIndex m
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     𝓥ᵢ : Set (ℓⁱ ⊔ ℓⱽ)
-- -- -- -- -- -- --     𝓣ᵢ : Set (ℓⁱ ⊔ ℓᵀ)
-- -- -- -- -- -- --     𝓼ᵢ : Set (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- --     to∃𝓥 : 𝓥ᵢ → ∃ 𝓥
-- -- -- -- -- -- --     to∃𝓣 : 𝓣ᵢ → ∃ 𝓣
-- -- -- -- -- -- --     to𝓥ᵢ : ∃ 𝓥 → 𝓥ᵢ
-- -- -- -- -- -- --     to𝓣ᵢ : ∃ 𝓣 → 𝓣ᵢ
-- -- -- -- -- -- --     iso∃𝓥 : (∃𝒱 : ∃ 𝓥) → to∃𝓥 (to𝓥ᵢ ∃𝒱) ≡ ∃𝒱
-- -- -- -- -- -- --     iso𝓥ᵢ : (𝒱ᵢ : 𝓥ᵢ) → to𝓥ᵢ (to∃𝓥 𝒱ᵢ) ≡ 𝒱ᵢ
-- -- -- -- -- -- --     iso∃𝓣 : (∃𝒯 : ∃ 𝓣) → to∃𝓣 (to𝓣ᵢ ∃𝒯) ≡ ∃𝒯
-- -- -- -- -- -- --     iso𝓣ᵢ : (𝒯ᵢ : 𝓣ᵢ) → to𝓣ᵢ (to∃𝓣 𝒯ᵢ) ≡ 𝒯ᵢ
-- -- -- -- -- -- --     inj𝓥 : ∀ {a b} → 𝓥 a ≡ 𝓥 b → a ≡ b
-- -- -- -- -- -- --     inj𝓣 : ∀ {a b} → 𝓣 a ≡ 𝓣 b → a ≡ b
-- -- -- -- -- -- --     mag : (𝓥ᵢ → 𝓣ᵢ) → ∀ {s} t → 𝓥 s → 𝓣 t
-- -- -- -- -- -- --     to∃𝓣𝓣 : 𝓣ᵢ → 𝓣ᵢ → ∃ λ i → 𝓣 i × 𝓣 i
-- -- -- -- -- -- --     max𝓣ᵢ : ∀ {m} n → (tm : 𝓣 m) → (((𝓣 n → 𝓣 m) × (𝓥 n → 𝓥 m)) ⊎ 𝓣 n)
-- -- -- -- -- -- --     max𝓲 : ∀ m n → ((𝓣 n → 𝓣 m) × (𝓥 n → 𝓥 m)) ⊎ ((𝓣 m → 𝓣 n) × (𝓥 m → 𝓥 n))
-- -- -- -- -- -- --     apply𝓼 : 𝓣ᵢ → (𝓥ᵢ → 𝓣ᵢ) → ∃ λ s → ∃ λ t → (𝓥 s → 𝓣 t) × 𝓣 s
-- -- -- -- -- -- --     to𝓼 : 𝓼ᵢ → ∃ λ s → ∃ λ t → 𝓥 s → 𝓣 t
-- -- -- -- -- -- --     to𝓼' : 𝓼ᵢ → 𝓣ᵢ → ∃ λ s → ∃ λ t → (𝓥 s → 𝓣 t) × 𝓣 s
-- -- -- -- -- -- --     to◇ : 𝓼ᵢ → 𝓼ᵢ → ∃ λ r → ∃ λ s → ∃ λ t → (𝓥 s → 𝓣 t) × (𝓥 r → 𝓣 s)
-- -- -- -- -- -- --     to= : 𝓼ᵢ → 𝓼ᵢ → ∃ λ s → ∃ λ t → (𝓥 s → 𝓣 t) × (𝓥 s → 𝓣 t)
-- -- -- -- -- -- --     to𝓼ᵢ : ∀ {r t} → (𝓥 r → 𝓣 t) → 𝓼ᵢ
-- -- -- -- -- -- --     {{ eqi }} : Eq 𝓲

-- -- -- -- -- -- --   to-noIndex : MGU-noIndex* (ℓⁱ ⊔ ℓⱽ) (ℓⁱ ⊔ ℓᵀ) (ℓⁱ ⊔ ℓˢ)
-- -- -- -- -- -- --   to-noIndex = go where
-- -- -- -- -- -- --     go : MGU-noIndex* _ _ _
-- -- -- -- -- -- --     MGU-noIndex*.𝓥 go = 𝓥ᵢ
-- -- -- -- -- -- --     MGU-noIndex*.𝓣 go = 𝓣ᵢ
-- -- -- -- -- -- --     MGU-noIndex*.𝓼 go = 𝓼ᵢ -- ∃ λ s → ∃ λ t → s ↦ t
-- -- -- -- -- -- --     MGU-noIndex*._≐_ go s1 s2 with to= s1 s2
-- -- -- -- -- -- --     ... | (s , t , vstt1 , vstt2) = {!_≐_ vstt1 vstt2!}
-- -- -- -- -- -- --     MGU-noIndex*._◃_ go f x with to𝓼' f x
-- -- -- -- -- -- --     MGU-noIndex*._◃_ go _ _ | (s , t , f , term) = to𝓣ᵢ $ _ , f ◃ term
-- -- -- -- -- -- --     MGU-noIndex*._◇_ go s1 s2 with to◇ s1 s2
-- -- -- -- -- -- --     ... | (r , s , t , vstt , vrts) = to𝓼ᵢ $ vstt ◇ vrts
-- -- -- -- -- -- --     MGU-noIndex*.mgu go = {!!}
-- -- -- -- -- -- -- --     MGU-noIndex*.𝓥 go = {!𝓥ᵢ!}
-- -- -- -- -- -- -- --     MGU-noIndex*.𝓣 go = 𝓣ᵢ
-- -- -- -- -- -- -- --     MGU-noIndex*.𝓼 go = {!!} -- ∃ λ s → ∃ λ t → s ↦ t -- ∃ λ s → ∃ λ t → 𝓥 s → 𝓣 t
-- -- -- -- -- -- -- --     MGU-noIndex*._≐_ go (s₁ , t₁ , f₁) (s₂ , t₂ , f₂) = {!!} -- ∃ λ (s-refl : s₁ ≡ s₂) → ∃ λ (t-refl : t₁ ≡ t₂) → (∀ x → f₁ x ≡ (Prelude.transport (λ i → 𝓥 s₂ → 𝓣 i) (sym t-refl) f₂) (Prelude.transport _ s-refl x))
-- -- -- -- -- -- -- --     {-
-- -- -- -- -- -- -- --     MGU-noIndex*._◃_ go (s , t , f) 𝒯 = {!_◃_ f!}
-- -- -- -- -- -- -- --     ∀ s t → 𝓣ᵢ → (𝓣 s → 𝓣 t) → 𝓣 s
-- -- -- -- -- -- -- --     ∀ s t → 𝓣ᵢ → (𝓣 s → 𝓣 t) → 𝓣ᵢ
-- -- -- -- -- -- -- --     𝓣 s
-- -- -- -- -- -- -- --     -}

-- -- -- -- -- -- -- --     MGU-noIndex*._◃_ go (s , t , f) 𝒯 with to∃𝓣 𝒯
-- -- -- -- -- -- -- --     MGU-noIndex*._◃_ go (s , t , f) 𝒯 | (s2 , ttt) with s == s2
-- -- -- -- -- -- -- --     (go MGU-noIndex*.◃ (.s , t , f)) 𝒯 | s , 𝒯s | (Prelude.yes refl) = to𝓣ᵢ (_ , _◃_ {s} {t} f 𝒯s)
-- -- -- -- -- -- -- --     (go MGU-noIndex*.◃ (s , t , f)) 𝒯 | s2 , ttt | (Prelude.no x) = 𝒯


-- -- -- -- -- -- -- --     MGU-noIndex*._◇_ go (s , t , f) (p , r , g) with max𝓲 r s
-- -- -- -- -- -- -- --     MGU-noIndex*._◇_ go (s , t , f) (p , r , g) | _⊎_.left (T , V) = {!!}
-- -- -- -- -- -- -- --     MGU-noIndex*._◇_ go (s , t , f) (p , r , g) | _⊎_.right (T , V) = _ , _ , f ◇ (T ∘ g) -- f ◃_ ∘ (T ∘ g)
-- -- -- -- -- -- -- --     {-
-- -- -- -- -- -- -- --     = _ , _ , f ◃_ ∘ (λ x → {!max𝓣ᵢ s₁ (g x)!}) -- _ , _ , f ◃_ ∘ (λ x → {!g x!})
-- -- -- -- -- -- -- --     -}

-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --     MGU-noIndex*._◇_ go (s₁ , t₁ , f) (s₂ , t₂ , g) with t₂ == s₁
-- -- -- -- -- -- -- --     MGU-noIndex*._◇_ go (s₁ , t₁ , f) (s₂ , t₂ , g) | (Prelude.yes refl) = s₂ , t₁ , f ◃_ ∘ g
-- -- -- -- -- -- -- --     MGU-noIndex*._◇_ go (s₁ , t₁ , f) (s₂ , t₂ , g) | (Prelude.no x) = s₂ , t₂ , g
-- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- --     -- = s₂ , t₁ , {!(f ◃_)!}
-- -- -- -- -- -- -- --     MGU-noIndex*.mgu go t₁ t₂ with to∃𝓣𝓣 t₁ t₂
-- -- -- -- -- -- -- --     … | i , tt₁ , tt₂ with mgu tt₁ tt₂
-- -- -- -- -- -- -- --     MGU-noIndex*.mgu go t₁ t₂ | i , tt₁ , tt₂ | (_⊎_.left x) = {!!}
-- -- -- -- -- -- -- --     MGU-noIndex*.mgu go t₁ t₂ | i , tt₁ , tt₂ | (_⊎_.right (i₂ , σ , subσ-refl , ff)) with to∃𝓣 t₁ | to∃𝓣 t₂
-- -- -- -- -- -- -- --     MGU-noIndex*.mgu go t₁ t₂ | i , tt₁ , tt₂ | (_⊎_.right (i₂ , σ , subσ-refl , ff)) | (fst₁ , snd₁) | (fst₂ , snd₂) = _⊎_.right ((_ , _ , sub σ) , {!!} , {!!}) -- _⊎_.right ((i , i₂ , sub σ) , {!subσ-refl!} , {!!})

-- -- -- -- -- -- -- -- record MGU-noIndex-to-addIndex {ℓⁱ ℓⱽ ℓᵀ ℓˢ}
-- -- -- -- -- -- -- --                             (m : MGU-noIndex ℓⱽ ℓᵀ ℓˢ) : Set (lsuc (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)) where
-- -- -- -- -- -- -- --   open MGU-noIndex m
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     𝓲 : Set ℓⁱ
-- -- -- -- -- -- -- --     𝓥ᵢ : 𝓲 → Set ℓⱽ
-- -- -- -- -- -- -- --     𝓣ᵢ : 𝓲 → Set ℓᵀ
-- -- -- -- -- -- -- --     to𝓥 : ∃ 𝓥ᵢ → 𝓥
-- -- -- -- -- -- -- --     to𝓣 : ∃ 𝓣ᵢ → 𝓣
-- -- -- -- -- -- -- --     to∃𝓥ᵢ : 𝓥 → ∃ 𝓥ᵢ
-- -- -- -- -- -- -- --     to∃𝓣ᵢ : 𝓣 → ∃ 𝓣ᵢ
-- -- -- -- -- -- -- --     inj𝓥 : ∀ {a b} → 𝓥ᵢ a ≡ 𝓥ᵢ b → a ≡ b
-- -- -- -- -- -- -- --     inj𝓣 : ∀ {a b} → 𝓣ᵢ a ≡ 𝓣ᵢ b → a ≡ b
-- -- -- -- -- -- -- --     mag : ∀ {s t} → (𝓥ᵢ s → 𝓣ᵢ t) → 𝓥 → 𝓣
-- -- -- -- -- -- -- --     {-
-- -- -- -- -- -- -- --     iso∃𝓥 : (∃𝒱 : ∃ 𝓥) → to∃𝓥 (to𝓥ᵢ ∃𝒱) ≡ ∃𝒱
-- -- -- -- -- -- -- --     iso𝓥ᵢ : (𝒱ᵢ : 𝓥ᵢ) → to𝓥ᵢ (to∃𝓥 𝒱ᵢ) ≡ 𝒱ᵢ
-- -- -- -- -- -- -- --     iso∃𝓣 : (∃𝒯 : ∃ 𝓣) → to∃𝓣 (to𝓣ᵢ ∃𝒯) ≡ ∃𝒯
-- -- -- -- -- -- -- --     iso𝓣ᵢ : (𝒯ᵢ : 𝓣ᵢ) → to𝓣ᵢ (to∃𝓣 𝒯ᵢ) ≡ 𝒯ᵢ
-- -- -- -- -- -- -- --     mag : (𝓥ᵢ → 𝓣ᵢ) → ∀ {s} t → 𝓥 s → 𝓣 t
-- -- -- -- -- -- -- --     -}

-- -- -- -- -- -- -- --   to-addIndex : MGU-addIndex ℓⁱ ℓⱽ ℓᵀ ℓˢ
-- -- -- -- -- -- -- --   to-addIndex = go where
-- -- -- -- -- -- -- --     go : MGU-addIndex ℓⁱ ℓⱽ ℓᵀ ℓˢ
-- -- -- -- -- -- -- --     MGU-addIndex.𝓲 go = 𝓲
-- -- -- -- -- -- -- --     MGU-addIndex.𝓥 go = 𝓥ᵢ
-- -- -- -- -- -- -- --     MGU-addIndex.𝓣 go = 𝓣ᵢ
-- -- -- -- -- -- -- --     MGU-addIndex._◃_ go {s} {t} f x = Prelude.transport 𝓣ᵢ {!!} $ snd ∘ to∃𝓣ᵢ $ _◃_ (λ v → to𝓣 (t , f (Prelude.transport 𝓥ᵢ (inj𝓥 {_} {_} {!!}) (snd $ to∃𝓥ᵢ v)))) (to𝓣 (s , x)) -- let Ti , Tit = to∃𝓣ᵢ $ _◃_ (λ v → to𝓣 (t , f {!!})) (to𝓣 (s , x)) in {!!}
-- -- -- -- -- -- -- --     MGU-addIndex.𝓢 go = {!!}
-- -- -- -- -- -- -- --     MGU-addIndex.sub go = {!!}
-- -- -- -- -- -- -- --     MGU-addIndex.mgu go = {!!}

-- -- -- -- -- -- -- -- record MGU-addIndex-to-noIndex {ℓⁱ ℓⱽ ℓᵀ ℓˢ}
-- -- -- -- -- -- -- --                             (m : MGU-addIndex ℓⁱ ℓⱽ ℓᵀ ℓˢ) : Set (lsuc (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)) where
-- -- -- -- -- -- -- --   open MGU-addIndex m
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     𝓥ᵢ : Set (ℓⁱ ⊔ ℓⱽ)
-- -- -- -- -- -- -- --     𝓣ᵢ : Set (ℓⁱ ⊔ ℓᵀ)
-- -- -- -- -- -- -- --     to∃𝓥 : 𝓥ᵢ → ∃ 𝓥
-- -- -- -- -- -- -- --     to∃𝓣 : 𝓣ᵢ → ∃ 𝓣
-- -- -- -- -- -- -- --     to𝓥ᵢ : ∃ 𝓥 → 𝓥ᵢ
-- -- -- -- -- -- -- --     to𝓣ᵢ : ∃ 𝓣 → 𝓣ᵢ
-- -- -- -- -- -- -- --     iso∃𝓥 : (∃𝒱 : ∃ 𝓥) → to∃𝓥 (to𝓥ᵢ ∃𝒱) ≡ ∃𝒱
-- -- -- -- -- -- -- --     iso𝓥ᵢ : (𝒱ᵢ : 𝓥ᵢ) → to𝓥ᵢ (to∃𝓥 𝒱ᵢ) ≡ 𝒱ᵢ
-- -- -- -- -- -- -- --     iso∃𝓣 : (∃𝒯 : ∃ 𝓣) → to∃𝓣 (to𝓣ᵢ ∃𝒯) ≡ ∃𝒯
-- -- -- -- -- -- -- --     iso𝓣ᵢ : (𝒯ᵢ : 𝓣ᵢ) → to𝓣ᵢ (to∃𝓣 𝒯ᵢ) ≡ 𝒯ᵢ
-- -- -- -- -- -- -- --     inj𝓥 : ∀ {a b} → 𝓥 a ≡ 𝓥 b → a ≡ b
-- -- -- -- -- -- -- --     inj𝓣 : ∀ {a b} → 𝓣 a ≡ 𝓣 b → a ≡ b
-- -- -- -- -- -- -- --     mag : (𝓥ᵢ → 𝓣ᵢ) → ∀ {s} t → 𝓥 s → 𝓣 t

-- -- -- -- -- -- -- --   to-noIndex : MGU-noIndex (ℓⁱ ⊔ ℓⱽ) (ℓⁱ ⊔ ℓᵀ) ℓˢ
-- -- -- -- -- -- -- --   to-noIndex = go where
-- -- -- -- -- -- -- --     go : MGU-noIndex _ _ _
-- -- -- -- -- -- -- --     MGU-noIndex.𝓥 go = 𝓥ᵢ
-- -- -- -- -- -- -- --     MGU-noIndex.𝓣 go = 𝓣ᵢ
-- -- -- -- -- -- -- --     MGU-noIndex._◃_ go 𝓈 𝒯ᵢ with to∃𝓣 𝒯ᵢ | Prelude.graphAt to∃𝓣 𝒯ᵢ | (Prelude.curry $ snd ∘ to∃𝓣 ∘ 𝓈 ∘ to𝓥ᵢ) (fst $ to∃𝓣 𝒯ᵢ) | Prelude.graphAt (Prelude.curry $ snd ∘ to∃𝓣 ∘ 𝓈 ∘ to𝓥ᵢ) (fst $ to∃𝓣 𝒯ᵢ)
-- -- -- -- -- -- -- --     … | s , 𝒯s | Prelude.ingraph eq | 𝓈' | Prelude.ingraph refl with cong fst eq
-- -- -- -- -- -- -- --     (go MGU-noIndex.◃ 𝓈) 𝒯ᵢ | .(fst (to∃𝓣 𝒯ᵢ)) , 𝒯s | (Prelude.ingraph eq) | _ | (Prelude.ingraph refl) | refl with cong fst eq
-- -- -- -- -- -- -- --     (go MGU-noIndex.◃ 𝓈) 𝒯ᵢ | .(fst (to∃𝓣 _ 𝒯ᵢ)) , 𝒯s | (Prelude.ingraph eq) | 𝓈' | (Prelude.ingraph refl) | refl | refl rewrite Prelude.sym eq with _◃_ {_} {{!!}} (λ v → 𝓈' (Prelude.transport 𝓥 (cong fst (sym eq)) {!!})) (snd ∘ to∃𝓣 $ 𝒯ᵢ)
-- -- -- -- -- -- -- --     … | dfsf = to𝓣ᵢ (_ , dfsf)
-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --     … | s , 𝒯s | Prelude.ingraph eq | 𝓈' | Prelude.ingraph refl with _◃_ {fst (to∃𝓣 𝒯ᵢ)} {s} (λ v → Prelude.transport 𝓣 {!!} (𝓈' (Prelude.transport 𝓥 (cong fst eq) v))) (snd ∘ to∃𝓣 $ 𝒯ᵢ)
-- -- -- -- -- -- -- --     … | dd = to𝓣ᵢ (_ , dd)
-- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- --     MGU-noIndex.𝓢 go = {!!}
-- -- -- -- -- -- -- --     MGU-noIndex.sub go = {!!}
-- -- -- -- -- -- -- --     MGU-noIndex.mgu go = {!!}


-- -- -- -- -- -- -- -- -- MGU-addIndex-to-noIndex : ∀ {ℓⁱ ℓⱽ ℓᵀ ℓˢ} →
-- -- -- -- -- -- -- -- --                             (m : MGU-addIndex ℓⁱ ℓⱽ ℓᵀ ℓˢ)
-- -- -- -- -- -- -- -- --                             (open MGU-addIndex m)
-- -- -- -- -- -- -- -- --                             (𝓥ᵢ : Set (ℓⁱ ⊔ ℓⱽ))
-- -- -- -- -- -- -- -- --                             (𝓣ᵢ : Set (ℓⁱ ⊔ ℓᵀ))
-- -- -- -- -- -- -- -- --                             (to∃𝓥 : 𝓥ᵢ → ∃ 𝓥)
-- -- -- -- -- -- -- -- --                             (to∃𝓣 : 𝓣ᵢ → ∃ 𝓣)
-- -- -- -- -- -- -- -- --                             (to𝓥ᵢ : ∃ 𝓥 → 𝓥ᵢ)
-- -- -- -- -- -- -- -- --                             (to𝓣ᵢ : ∃ 𝓣 → 𝓣ᵢ)
-- -- -- -- -- -- -- -- --                             (iso∃𝓥 : (∃𝒱 : ∃ 𝓥) → to∃𝓥 (to𝓥ᵢ ∃𝒱) ≡ ∃𝒱)
-- -- -- -- -- -- -- -- --                             (iso𝓥ᵢ : (𝒱ᵢ : 𝓥ᵢ) → to𝓥ᵢ (to∃𝓥 𝒱ᵢ) ≡ 𝒱ᵢ)
-- -- -- -- -- -- -- -- --                             (iso∃𝓣 : (∃𝒯 : ∃ 𝓣) → to∃𝓣 (to𝓣ᵢ ∃𝒯) ≡ ∃𝒯)
-- -- -- -- -- -- -- -- --                             (iso𝓣ᵢ : (𝒯ᵢ : 𝓣ᵢ) → to𝓣ᵢ (to∃𝓣 𝒯ᵢ) ≡ 𝒯ᵢ)
-- -- -- -- -- -- -- -- --                             → MGU-noIndex (ℓⁱ ⊔ ℓⱽ) (ℓⁱ ⊔ ℓᵀ) ℓˢ
-- -- -- -- -- -- -- -- -- MGU-addIndex-to-noIndex {ℓⁱ} {ℓⱽ} {ℓᵀ} {ℓˢ} m = go where
-- -- -- -- -- -- -- -- --   open MGU-addIndex m
-- -- -- -- -- -- -- -- --   go : MGU-noIndex _ _ _
-- -- -- -- -- -- -- -- --   go = {!!}

-- -- -- -- -- -- -- -- -- --  open import Relation.Binary.HeterogeneousEquality.Core as H using (_≅_ ; ≅-to-≡)
-- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- --   𝓼 = ∃ 𝓥 → ∃ 𝓣

-- -- -- -- -- -- -- -- --   _∶_↦_ : 𝓼 → 𝓲 → 𝓲 → Set (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- --   _∶_↦_ 𝓈 s t = ((𝒱ₛ : 𝓥 s) → ∃ λ (𝒯ₜ : 𝓣 t) → 𝓈 (s , 𝒱ₛ) ≡ (t , 𝒯ₜ))
-- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- --   go : MGU-noIndex _ _ _
-- -- -- -- -- -- -- -- -- --   MGU-noIndex.𝓥 go = ∃ 𝓥
-- -- -- -- -- -- -- -- -- --   MGU-noIndex.𝓣 go = ∃ 𝓣
-- -- -- -- -- -- -- -- -- --   MGU-noIndex._≐_ go f g = (𝒾 : 𝓲) (𝒱 : 𝓥 𝒾) → f (𝒾 , 𝒱) ≡ g (𝒾 , 𝒱)
-- -- -- -- -- -- -- -- -- --   MGU-noIndex._◃_ go 𝓈 (𝒾 , 𝒯) = 𝒾 , _◃_ {𝒾} {𝒾} (λ v → (Prelude.transport _ (≅-to-≡ $ snd (mag (fst (𝓈 (𝒾 , v))) (( (𝒾 ))) (snd (𝓈 (𝒾 , v))))) $
-- -- -- -- -- -- -- -- -- --                                                            snd (𝓈 (𝒾 , v)))
-- -- -- -- -- -- -- -- -- --                                                           {!!}) {!!}
-- -- -- -- -- -- -- -- -- --   -- (snd ∘ (λ (𝒱 : 𝓥 𝒾) → 𝓈 (𝒾 , 𝒱)))
-- -- -- -- -- -- -- -- -- --   -- fst (𝓈 (s , {!!})) , _◃_ {s} {fst (𝓈 (s , _))} (λ v → {!𝓈 (s , v)!}) {!𝒯ₛ!}
-- -- -- -- -- -- -- -- -- --   -- Have: {s t : 𝓲} → (𝓥 s → 𝓣 t) → 𝓣 s → 𝓣 t
-- -- -- -- -- -- -- -- -- --   -- λ (𝒱 : 𝓥 𝒾) → 𝓈 (𝒾 , 𝒱)
-- -- -- -- -- -- -- -- -- --   MGU-noIndex.𝓢 go = {!!}
-- -- -- -- -- -- -- -- -- --   MGU-noIndex.sub go = {!sub {s} {t}!}
-- -- -- -- -- -- -- -- -- --   MGU-noIndex.mgu go = {!!}
-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.𝓥 (MGU-addIndex-to-noIndex m) = let open MGU-addIndex m in ∃ 𝓥
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.𝓣 (MGU-addIndex-to-noIndex m) = let open MGU-addIndex m in ∃ 𝓣
-- -- -- -- -- -- -- -- -- -- MGU-noIndex._≐_ (MGU-addIndex-to-noIndex m) f g = {!let open MGU-addIndex m in ∀ (s t : 𝓲) → (𝒯ₜ : 𝓣 fst (f (s , 𝓥 s)) ≡ t →  ≡ g → Set !} -- ∀ {s t} → (f g : s ↦ t) → f ≐ g
-- -- -- -- -- -- -- -- -- -- MGU-noIndex._◃_ (MGU-addIndex-to-noIndex m) = {!let open MGU-addIndex m in _◃_!}
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.𝓢 (MGU-addIndex-to-noIndex m) = {!!}
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.sub (MGU-addIndex-to-noIndex m) = {!!}
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.mgu (MGU-addIndex-to-noIndex m) = {!!}
-- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.𝓥 (MGU-addIndex-to-noIndex record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu }) = ∃ 𝓥
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.𝓣 (MGU-addIndex-to-noIndex record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu }) = ∃ 𝓣
-- -- -- -- -- -- -- -- -- -- MGU-noIndex._≐_ (MGU-addIndex-to-noIndex m@(record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu })) f g = {!!} -- (i : 𝓲) → MGU-addIndex._≐_ m (λ v → {!snd $ f (i , v)!}) (λ v → {!!})
-- -- -- -- -- -- -- -- -- -- MGU-noIndex._◃_ (MGU-addIndex-to-noIndex record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu }) = {!!}
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.𝓢 (MGU-addIndex-to-noIndex record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu }) = {!!}
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.sub (MGU-addIndex-to-noIndex record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu }) = {!!}
-- -- -- -- -- -- -- -- -- -- MGU-noIndex.mgu (MGU-addIndex-to-noIndex record { 𝓲 = 𝓲 ; 𝓥 = 𝓥 ; 𝓣 = 𝓣 ; _◃_ = _◃_ ; ◃ext = ◃ext ; 𝓢 = 𝓢 ; sub = sub ; mgu = mgu }) = {!!}
-- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- record MGU⋆ ℓⁱ ℓⱽ ℓᵀ ℓˢ : Set (lsuc (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ ⊔ ℓˢ)) where
-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     𝓲
-- -- -- -- -- -- -- -- -- --       : Set ℓⁱ

-- -- -- -- -- -- -- -- -- --     𝓥 -- variables
-- -- -- -- -- -- -- -- -- --       : 𝓲 → Set ℓⱽ

-- -- -- -- -- -- -- -- -- --     𝓣 -- terms
-- -- -- -- -- -- -- -- -- --       : 𝓲 → Set ℓᵀ

-- -- -- -- -- -- -- -- -- --   -- substitution
-- -- -- -- -- -- -- -- -- --   _↦_ : (s t : 𝓲) → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   _↦_ s t = 𝓥 s → 𝓣 t

-- -- -- -- -- -- -- -- -- --   infix 14 _≐_
-- -- -- -- -- -- -- -- -- --   _≐_ : {s t : 𝓲} → s ↦ t → s ↦ t → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   _≐_ f g = ∀ x → f x ≡ g x

-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     -- substitution applied to a term
-- -- -- -- -- -- -- -- -- --     _◃_ : ∀ {s t} → s ↦ t → 𝓣 s → 𝓣 t
-- -- -- -- -- -- -- -- -- --     -- applying extentionally-equal subsitutions preserves equality of terms
-- -- -- -- -- -- -- -- -- --     ◃ext : ∀ {s t} {f g : s ↦ t} → f ≐ g → ∀ t → f ◃ t ≡ g ◃ t

-- -- -- -- -- -- -- -- -- --   _◇_ : ∀ {r s t : 𝓲} → (f : s ↦ t) (g : r ↦ s) → r ↦ t
-- -- -- -- -- -- -- -- -- --   _◇_ f g = (f ◃_) ∘ g

-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     𝓢 : 𝓲 → 𝓲 → Set ℓˢ
-- -- -- -- -- -- -- -- -- --     sub : ∀ {s t} → 𝓢 s t → s ↦ t

-- -- -- -- -- -- -- -- -- --   Property : ∀ {ℓ} → 𝓲 → Set (lsuc ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   Property {ℓ} s = ∀ {t} → s ↦ t → Set ℓ

-- -- -- -- -- -- -- -- -- --   Nothing : ∀ {ℓ m} → (P : Property {ℓ} m) → Set (ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   Nothing P = ∀ {n} f → P {n} f → ⊥

-- -- -- -- -- -- -- -- -- --   Unifies : ∀ {i} (t₁ t₂ : 𝓣 i) → Property i
-- -- -- -- -- -- -- -- -- --   Unifies t₁ t₂ f = f ◃ t₁ ≡ f ◃ t₂

-- -- -- -- -- -- -- -- -- --   _≤_ : ∀ {m n n'} (f : m ↦ n) (g : m ↦ n') → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   _≤_ f g = ∃ λ f' → f ≐ (f' ◇ g)

-- -- -- -- -- -- -- -- -- --   Max : ∀ {ℓ m} (P : Property {ℓ} m) → Property m
-- -- -- -- -- -- -- -- -- --   Max P = (λ f → P f × (∀ {n} f' → P {n} f' → f' ≤ f))

-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     mgu : ∀ {m} (t₁ t₂ : 𝓣 m) →
-- -- -- -- -- -- -- -- -- --           Nothing (Unifies t₁ t₂) ⊎ (∃ λ n → ∃ λ (σ : 𝓢 m n) → (Max (Unifies t₁ t₂)) (sub σ))

-- -- -- -- -- -- -- -- -- -- record MGU ℓⁱ ℓⱽ ℓᵀ ℓˢ : Set (lsuc (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ ⊔ ℓˢ)) where
-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     𝓲
-- -- -- -- -- -- -- -- -- --       : Set ℓⁱ

-- -- -- -- -- -- -- -- -- --     𝓥 -- variables
-- -- -- -- -- -- -- -- -- --       : 𝓲 → Set ℓⱽ

-- -- -- -- -- -- -- -- -- --     𝓣 -- terms
-- -- -- -- -- -- -- -- -- --       : 𝓲 → Set ℓᵀ

-- -- -- -- -- -- -- -- -- --   -- substitution
-- -- -- -- -- -- -- -- -- --   _↦_ : (s t : 𝓲) → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   _↦_ s t = 𝓥 s → 𝓣 t

-- -- -- -- -- -- -- -- -- --   infix 14 _≐_
-- -- -- -- -- -- -- -- -- --   _≐_ : {s t : 𝓲} → s ↦ t → s ↦ t → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   _≐_ f g = ∀ x → f x ≡ g x

-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     -- substitution applied to a term
-- -- -- -- -- -- -- -- -- --     _◃_ : ∀ {s t} → s ↦ t → 𝓣 s → 𝓣 t
-- -- -- -- -- -- -- -- -- --     -- applying extentionally-equal subsitutions preserves equality of terms
-- -- -- -- -- -- -- -- -- --     ◃ext : ∀ {s t} {f g : s ↦ t} → f ≐ g → ∀ t → f ◃ t ≡ g ◃ t

-- -- -- -- -- -- -- -- -- --   _◇_ : ∀ {r s t : 𝓲} → (f : s ↦ t) (g : r ↦ s) → r ↦ t
-- -- -- -- -- -- -- -- -- --   _◇_ f g = (f ◃_) ∘ g

-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- --     𝓢 : 𝓲 → 𝓲 → Set ℓˢ
-- -- -- -- -- -- -- -- -- --     sub : ∀ {s t} → 𝓢 s t → s ↦ t
-- -- -- -- -- -- -- -- -- --     mgu : ∀ {m} → (s t : 𝓣 m) → Maybe (∃ (𝓢 m))

-- -- -- -- -- -- -- -- -- --   Property⋆ : ∀ {ℓ} → 𝓲 → Set (lsuc ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   Property⋆ {ℓ} s = ∀ {t} → s ↦ t → Set ℓ

-- -- -- -- -- -- -- -- -- --   Property : ∀ {ℓ} → 𝓲 → Set (lsuc ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   Property {ℓ} s = Σ (Property⋆ {ℓ} s) λ P → ∀ {s f g} → f ≐ g → P {s} f → P g

-- -- -- -- -- -- -- -- -- --   Nothing : ∀ {ℓ m} → (P : Property {ℓ} m) → Set (ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   Nothing P = ∀ {n} f → fst P {n} f → ⊥

-- -- -- -- -- -- -- -- -- --   Unifies : ∀ {i} (t₁ t₂ : 𝓣 i) → Property i
-- -- -- -- -- -- -- -- -- --   Unifies t₁ t₂ = (λ {_} f → f ◃ t₁ ≡ f ◃ t₂) , λ {_} {f} {g} f≐g f◃t₁=f◃t₂ →
-- -- -- -- -- -- -- -- -- --       g ◃ t₁
-- -- -- -- -- -- -- -- -- --     ≡⟨ sym (◃ext f≐g t₁) ⟩
-- -- -- -- -- -- -- -- -- --       f ◃ t₁
-- -- -- -- -- -- -- -- -- --     ≡⟨ f◃t₁=f◃t₂ ⟩
-- -- -- -- -- -- -- -- -- --       f ◃ t₂
-- -- -- -- -- -- -- -- -- --     ≡⟨ ◃ext f≐g t₂ ⟩
-- -- -- -- -- -- -- -- -- --       g ◃ t₂
-- -- -- -- -- -- -- -- -- --     ∎

-- -- -- -- -- -- -- -- -- --   _≤_ : ∀ {m n n'} (f : m ↦ n) (g : m ↦ n') → Set (ℓⱽ ⊔ ℓᵀ)
-- -- -- -- -- -- -- -- -- --   _≤_ f g = ∃ λ f' → f ≐ (f' ◇ g)

-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- --   Max : ∀ {ℓ m} (P : Property {ℓ} m) → Property m
-- -- -- -- -- -- -- -- -- --   Max P' =
-- -- -- -- -- -- -- -- -- --     let open Σ P' using () renaming (fst to P; snd to Peq) in
-- -- -- -- -- -- -- -- -- --     let lemma1 : {m : 𝓲} {f : _ ↦ m} {g : _ ↦ m} →
-- -- -- -- -- -- -- -- -- --                  f ≐ g →
-- -- -- -- -- -- -- -- -- --                  P f × ({n : 𝓲} (f' : _ ↦ n) → P f' → f' ≤ f) →
-- -- -- -- -- -- -- -- -- --                  P g × ({n : 𝓲} (f' : _ ↦ n) → P f' → f' ≤ g)
-- -- -- -- -- -- -- -- -- --         lemma1 {_} {_} {g} f≐g = λ { (Pf , MaxPf) →
-- -- -- -- -- -- -- -- -- --           Peq f≐g Pf , λ {_} →
-- -- -- -- -- -- -- -- -- --             let lemma2 : ∀ {n} f' → P {n} f' → ∃ λ f0 → f' ≐ (f0 ◇ g)
-- -- -- -- -- -- -- -- -- --                 lemma2 f' Pf' =
-- -- -- -- -- -- -- -- -- --                   let f0 = fst (MaxPf f' Pf')
-- -- -- -- -- -- -- -- -- --                       f'≐f0◇f = snd (MaxPf f' Pf') in
-- -- -- -- -- -- -- -- -- --                   f0 , λ x → trans (f'≐f0◇f x) (cong (f0 ◃_) (f≐g x)) in
-- -- -- -- -- -- -- -- -- --             lemma2 } in
-- -- -- -- -- -- -- -- -- --     --(λ {_} f → P f × (∀ {n} f' → P {n} f' → f' ≤ f)) , λ {_} {_} {_} → lemma1
-- -- -- -- -- -- -- -- -- --     (λ f → P f × (∀ {n} f' → P {n} f' → f' ≤ f)) , lemma1
-- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- --   Max : ∀ {ℓ m} (P : Property {ℓ} m) → Property⋆ m
-- -- -- -- -- -- -- -- -- --   Max P' =
-- -- -- -- -- -- -- -- -- --     let open Σ P' using () renaming (fst to P) in
-- -- -- -- -- -- -- -- -- --     (λ f → P f × (∀ {n} f' → P {n} f' → f' ≤ f))

-- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- --     mgu-c : ∀ {m} (t₁ t₂ : 𝓣 m) →
-- -- -- -- -- -- -- -- -- --             (∃ λ n → ∃ λ σ → fst (Max (Unifies t₁ t₂)) (sub σ) × mgu t₁ t₂ ≡ just (n , σ))
-- -- -- -- -- -- -- -- -- --             ⊎ (Nothing (Unifies t₁ t₂)                         × mgu t₁ t₂ ≡ nothing)

-- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- --     mgu-c : ∀ {m} (t₁ t₂ : 𝓣 m) →
-- -- -- -- -- -- -- -- -- --             (∃ λ n → ∃ λ σ → (Max (Unifies t₁ t₂)) (sub σ) × mgu t₁ t₂ ≡ just (n , σ))
-- -- -- -- -- -- -- -- -- --             ⊎ (Nothing (Unifies t₁ t₂)                     × mgu t₁ t₂ ≡ nothing)

-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- --     -- trivial substitution
-- -- -- -- -- -- -- -- -- --     -- ▹ : ∀ {s t} → (𝓥 s → 𝓥 t) → s ↦ t

-- -- -- -- -- -- -- -- -- --   ≐-cong : ∀ {m n o} {f : m ↦ n} {g} (h : _ ↦ o) → f ≐ g → (h ◇ f) ≐ (h ◇ g)
-- -- -- -- -- -- -- -- -- --   ≐-cong h f≐g t = cong (h ◃_) (f≐g t)

-- -- -- -- -- -- -- -- -- --   ≐-sym : ∀ {m n} {f : m ↦ n} {g} → f ≐ g → g ≐ f
-- -- -- -- -- -- -- -- -- --   ≐-sym f≐g = sym ∘ f≐g
-- -- -- -- -- -- -- -- -- -- -}

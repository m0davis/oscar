
open import Oscar.Prelude
open import Oscar.Class
import Oscar.Data.Constraint

module Oscar.Class.Transitivity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y z}
  (x∼y : x ∼ y)
  (y∼z : y ∼ z)
  where
  𝔱ransitivity : ℭlass $ x∼y , y∼z , _∼_
  𝔱ransitivity = ∁ (x ∼ z)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  𝓽ransitivity = ∀ {x y z} (x∼y : x ∼ y) (y∼z : y ∼ z) → ℭlass.SET-METHOD (𝔱ransitivity _∼_ x∼y y∼z)
  𝓣ransitivity = ∀ {x y z} {x∼y : x ∼ y} {y∼z : y ∼ z} → ℭlass.SET-CLASS (𝔱ransitivity _∼_ x∼y y∼z)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  ⦃ _ : 𝓣ransitivity _∼_ ⦄
  where
  transitivity[_] = λ {x y z} (x∼y : x ∼ y) (y∼z : y ∼ z) → ℭlass.GET-METHOD (𝔱ransitivity _∼_ x∼y y∼z)
  infixr 9 ∙[]-syntax
  ∙[]-syntax = transitivity[_]
  syntax ∙[]-syntax _⊸_ f g = g ∙[ _⊸_ ] f

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  transitivity = transitivity[ _∼_ ]
  infixr 9 transitivity
  syntax transitivity f g = g ∙ f

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
  where

  open import Oscar.Data.Proposequality

  ≡̇-transitivity = transitivity[ Proposextensequality⟦ 𝔓 ⟧ ]

  infixr 9 ≡̇-transitivity
  syntax ≡̇-transitivity f g = g ≡̇-∙ f

  infixr 9 ≡̇-transitivity-syntax
  ≡̇-transitivity-syntax = ≡̇-transitivity
  syntax ≡̇-transitivity-syntax f g = g ⟨≡̇⟩ f

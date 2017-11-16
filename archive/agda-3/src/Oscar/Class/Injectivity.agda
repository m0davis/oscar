
open import Oscar.Prelude

module Oscar.Class.Injectivity where

module _ where

  module _ -- Arity=1
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    where
    𝓲njection₁ = (x : 𝔒₁) → 𝔒₂ x
    record 𝓘njection₁ : Ø 𝔬₁ ∙̂ 𝔬₂ where field injection₁ : 𝓲njection₁
    open 𝓘njection₁ ⦃ … ⦄ public
    module _
      {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
      {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
      where
      record [𝓘njectivity₁] : Ø₀ where
        no-eta-equality
        constructor ∁
      module _
        ⦃ _ : 𝓘njection₁ ⦄
        where
        𝓲njectivity₁ = ∀ {x₁ x₂} → injection₁ x₁ ∼₂ injection₁ x₂ → x₁ ∼₁ x₂
        record 𝓘njectivity₁ ⦃ _ : [𝓘njectivity₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where field injectivity₁ : 𝓲njectivity₁
        open 𝓘njectivity₁ ⦃ … ⦄ public

  injectivity₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {ℓ₂} {_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    ⦃ _ : 𝓘njection₁ (λ (x : 𝔒₁) → 𝔒₂ x) ⦄
    ⦃ _ : [𝓘njectivity₁] (λ (x : 𝔒₁) → 𝔒₂ x) _∼₂_ _∼₁_ ⦄
    ⦃ _ : 𝓘njectivity₁ (λ (x : 𝔒₁) → 𝔒₂ x) _∼₂_ _∼₁_ ⦄
    → 𝓲njectivity₁ (λ (x : 𝔒₁) → 𝔒₂ x) _∼₂_ _∼₁_
  injectivity₁[ _ ] = injectivity₁

  module _ -- Arity=2
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} (𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃)
    where
    𝓲njection₂ = ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂
    record 𝓘njection₂ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
      constructor ∁
      field injection₂ : 𝓲njection₂
    open 𝓘njection₂ ⦃ … ⦄ public
    module _ -- Fixed=0
      {ℓ₃} (_∼₃_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃)
      where
      module _ -- Var=1
        {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
        where
        record [𝓘njectivity₂,₀,₁] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₂ ⦄
          where
          𝓲njectivity₂,₀,₁ = ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → injection₂ _ y₁ ∼₃ injection₂ _ y₂ → x₁ ∼₁ x₂
          record 𝓘njectivity₂,₀,₁ ⦃ _ : [𝓘njectivity₂,₀,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₁ ∙̂ ℓ₃ where field injectivity₂,₀,₁ : 𝓲njectivity₂,₀,₁
          open 𝓘njectivity₂,₀,₁ ⦃ … ⦄ public
      module _ -- Var=2
        {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
        where
        record [𝓘njectivity₂,₀,₂] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₂ ⦄
          where
          𝓲njectivity₂,₀,₂ = ∀ {x₁ x₂ : 𝔒₁} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → injection₂ _ y₁ ∼₃ injection₂ _ y₂ → y₁ ∼₂ y₂
          record 𝓘njectivity₂,₀,₂ ⦃ _ : [𝓘njectivity₂,₀,₂] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₃ where field injectivity₂,₀,₂ : 𝓲njectivity₂,₀,₂
          open 𝓘njectivity₂,₀,₂ ⦃ … ⦄ public
    module _ -- Fixed=1
      {ℓ₃} (_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂ x} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃)
      {ℓ₂} (_∼₂_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ₂)
      where
      record [𝓘njectivity₂,₁] : Ø₀ where
        no-eta-equality
        constructor ∁
      module _
        ⦃ _ : 𝓘njection₂ ⦄
        where
        𝓲njectivity₂,₁ = ∀ (x : 𝔒₁) {y₁ y₂ : 𝔒₂ x} → injection₂ _ y₁ ∼₃ injection₂ _ y₂ → y₁ ∼₂ y₂
        record 𝓘njectivity₂,₁ ⦃ _ : [𝓘njectivity₂,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₃ where field injectivity₂,₁ : 𝓲njectivity₂,₁
        open 𝓘njectivity₂,₁ ⦃ … ⦄ public

  injectivity₂,₀,₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : [𝓘njectivity₂,₀,₁] 𝔒₃ _∼₃_ _∼₁_ ⦄
    ⦃ _ : 𝓘njectivity₂,₀,₁ 𝔒₃ _∼₃_ _∼₁_ ⦄
    → 𝓲njectivity₂,₀,₁ 𝔒₃ _∼₃_ _∼₁_
  injectivity₂,₀,₁[ _ ] = injectivity₂,₀,₁

  injectivity₂,₀,₂[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃}
    {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : [𝓘njectivity₂,₀,₂] 𝔒₃ _∼₃_ _∼₂_ ⦄
    ⦃ _ : 𝓘njectivity₂,₀,₂ 𝔒₃ _∼₃_ _∼₂_ ⦄
    → 𝓲njectivity₂,₀,₂ 𝔒₃ _∼₃_ _∼₂_
  injectivity₂,₀,₂[ _ ] = injectivity₂,₀,₂

  injectivity₂,₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂ x} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃}
    {ℓ₂} (_∼₂_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ₂)
    ⦃ _ : [𝓘njectivity₂,₁] 𝔒₃ _∼₃_ _∼₂_ ⦄
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : 𝓘njectivity₂,₁ 𝔒₃ _∼₃_ _∼₂_ ⦄
    → 𝓲njectivity₂,₁ 𝔒₃ _∼₃_ _∼₂_
  injectivity₂,₁[ _ ] = injectivity₂,₁

  module _ -- Arity=3
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {𝔬₄} (𝔒₄ : ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂ → Ø 𝔬₄)
    where
    𝓲njection₃ = ∀ x₁ → (x₂ : 𝔒₂ x₁) → (x₃ : 𝔒₃ _ x₂) → 𝔒₄ _ _ x₃
    record 𝓘njection₃ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
      constructor ∁
      field injection₃ : 𝓲njection₃
    open 𝓘njection₃ ⦃ … ⦄ public
    module _ -- Fixed=0
      {ℓ₄} (_∼₄_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → 𝔒₄ _ _ z₁ → 𝔒₄ _ _ z₂ → Ø ℓ₄)
      where
      module _ -- Var=1
        {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
        where
        record [𝓘njectivity₃,₀,₁] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₃ ⦄
          where
          𝓲njectivity₃,₀,₁ = ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → injection₃ _ _ z₁ ∼₄ injection₃ _ _ z₂ → x₁ ∼₁ x₂
          record 𝓘njectivity₃,₀,₁ ⦃ _ : [𝓘njectivity₃,₀,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ ℓ₁ ∙̂ ℓ₄ where field injectivity₃,₀,₁ : 𝓲njectivity₃,₀,₁
          open 𝓘njectivity₃,₀,₁ ⦃ … ⦄ public
      module _ -- Var=2
        {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
        where
        record [𝓘njectivity₃,₀,₂] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₃ ⦄
          where
          𝓲njectivity₃,₀,₂ = ∀ {x₁ x₂ : 𝔒₁} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → injection₃ _ _ z₁ ∼₄ injection₃ _ _ z₂ → y₁ ∼₂ y₂
          record 𝓘njectivity₃,₀,₂ ⦃ _ : [𝓘njectivity₃,₀,₂] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₄ where field injectivity₃,₀,₂ : 𝓲njectivity₃,₀,₂
          open 𝓘njectivity₃,₀,₂ ⦃ … ⦄ public

  injectivity₃,₀,₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {𝔬₄} {𝔒₄ : ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂ → Ø 𝔬₄}
    {ℓ₄} {_∼₄_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → 𝔒₄ _ _ z₁ → 𝔒₄ _ _ z₂ → Ø ℓ₄}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    ⦃ _ : [𝓘njectivity₃,₀,₁] 𝔒₄ _∼₄_ _∼₁_ ⦄
    ⦃ _ : 𝓘njection₃ 𝔒₄ ⦄
    ⦃ _ : 𝓘njectivity₃,₀,₁ 𝔒₄ _∼₄_ _∼₁_ ⦄
    → 𝓲njectivity₃,₀,₁ 𝔒₄ _∼₄_ _∼₁_
  injectivity₃,₀,₁[ _ ] = injectivity₃,₀,₁

  injectivity₃,₀,₂[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {𝔬₄} {𝔒₄ : ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂ → Ø 𝔬₄}
    {ℓ₄} {_∼₄_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → 𝔒₄ _ _ z₁ → 𝔒₄ _ _ z₂ → Ø ℓ₄}
    {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
    ⦃ _ : [𝓘njectivity₃,₀,₂] 𝔒₄ _∼₄_ _∼₂_ ⦄
    ⦃ _ : 𝓘njection₃ 𝔒₄ ⦄
    ⦃ _ : 𝓘njectivity₃,₀,₂ 𝔒₄ _∼₄_ _∼₂_ ⦄
    → 𝓲njectivity₃,₀,₂ 𝔒₄ _∼₄_ _∼₂_
  injectivity₃,₀,₂[ _ ] = injectivity₃,₀,₂

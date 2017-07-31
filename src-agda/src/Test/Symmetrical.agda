
open import Oscar.Prelude
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical
import Oscar.Class.Symmetrical.Symmetry

module Test.Symmetrical where

  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  -- test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _ -- FIXME no longer works after 𝓢ymmetrical𝓢ymmetry was "rationalised"
  test-𝓢ymmetrical𝓢ymmetry {𝔒 = 𝔒} = symmetrical {𝔄 = 𝔒} _ _

  test-𝓢ymmetrical𝓢ymmetry-alternate : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry-alternate {x = x} = symmetrical x _

  lhs-test1 : ∀ {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    {_∼'_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼'_ ⦄
    → ∀ x y → _
  lhs-test1 {_∼_ = _∼_} = symmetrical {_↦_ = λ x y → x → y} {{∁ _∼_}}

  lhs-test2 : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
        {_↦'_ : 𝔅 → 𝔅 → Ø ℓ}
    {_∼1_ : 𝔄 → 𝔄 → 𝔅}
    {_∼2_ : 𝔄 → 𝔄 → 𝔅}
    (let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                  _ = ∁ _∼1_)
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦_ ⦄
    (let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                  _ = ∁ _∼1_)
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦'_ ⦄
    (let instance i2 : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                  i2 = ∁ _∼2_)
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦_ ⦃ i2 ⦄ ⦄
    (let instance i2' : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                  i2' = ∁ _∼2_)
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦'_ ⦃ i2' ⦄ ⦄
    → ∀ (x y : 𝔄) → _
  lhs-test2 {𝔄 = 𝔄} {𝔅 = 𝔅} {_↦_ = _↦_} {_↦'_ = _↦'_} {_∼1_ = _∼1_} {_∼2_ = _∼2_} =
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                 _ = ∁ _∼1_ in
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                 _ = ∁ _∼1_ in
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                 _ = ∁ _∼2_ in
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                 _ = ∁ _∼2_ in
      -- symmetrical {_↦_ = _↦_} ⦃ ∁ _∼1_ ⦄
      -- symmetrical {_↦_ = _ {-_↦_-}} ⦃ ∁ _∼1_ ⦄ -- FIXME why does this not need _↦_ ... (because it figures out that the only 𝓢ymmetrical compatibly defined with the given [𝓢ymmetrical] has {_↦_ = _ _↦_}
      explicit-symmetrical _↦_ _∼1_

  lhs-test2a : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
        {_↦'_ : 𝔅 → 𝔅 → Ø ℓ}
    {_∼1_ : 𝔄 → 𝔄 → 𝔅}
    {_∼2_ : 𝔄 → 𝔄 → 𝔅}
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦_ ⦃ ∁ _∼1_ ⦄ ⦄
    (let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                  _ = ∁ _∼1_)
    (let instance i2 : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                  i2 = ∁ _∼2_)
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦_ ⦃ i2 ⦄ ⦄
    (let instance i2' : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                  i2' = ∁ _∼2_)
    ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦'_ ⦃ i2' ⦄ ⦄
    → ∀ (x y : 𝔄) → _
  lhs-test2a {𝔄 = 𝔄} {𝔅 = 𝔅} {_↦_ = _↦_} {_↦'_ = _↦'_} {_∼1_ = _∼1_} {_∼2_ = _∼2_} =
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                 _ = ∁ _∼1_ in
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                 _ = ∁ _∼1_ in
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_
                 _ = ∁ _∼2_ in
    let instance _ : [𝓢ymmetrical] 𝔄 𝔅 _↦'_
                 _ = ∁ _∼2_ in
      explicit-symmetrical _ _∼1_

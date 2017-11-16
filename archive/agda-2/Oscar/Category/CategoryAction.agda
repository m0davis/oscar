
module Oscar.Category.CategoryAction where

open import Oscar.Category.Action
open import Oscar.Category.Category
open import Oscar.Category.SemigroupoidAction
open import Oscar.Category.Setoid
open import Oscar.Level

module _ {𝔊𝔬 𝔊𝔪 𝔊𝔮} (category : Category 𝔊𝔬 𝔊𝔪 𝔊𝔮) where
  open Category category

  module _ {𝔄𝔬 𝔄𝔮} (action : Action ⋆ 𝔄𝔬 𝔄𝔮) where
    open Action action

    record IsCategoryAction
      (_◂_ : ∀ {x y} → x ↦ y → ↥ x → ↥ y)
      : Set (𝔊𝔬 ⊔ 𝔊𝔪 ⊔ 𝔊𝔮 ⊔ 𝔄𝔬 ⊔ 𝔄𝔮) where
      field ⦃ isSemigroupoidAction ⦄ : IsSemigroupoidAction semigroupoid action _◂_
      field identity : ∀ {x} → (s : ↥ x) → ε ◂ s ≋ s

open IsCategoryAction ⦃ … ⦄ public

record CategoryAction 𝔊𝔬 𝔊𝔪 𝔊𝔮 𝔄𝔬 𝔄𝔮 : Set (lsuc (𝔊𝔬 ⊔ 𝔊𝔪 ⊔ 𝔊𝔮 ⊔ 𝔄𝔬 ⊔ 𝔄𝔮)) where
  constructor [_/_]
  field category : Category 𝔊𝔬 𝔊𝔪 𝔊𝔮
  open Category category public

  field action : Action ⋆ 𝔄𝔬 𝔄𝔮
  open Action action public

  field _◂_ : ∀ {x y} → x ↦ y → ↥ x → ↥ y
  field ⦃ isCategoryAction ⦄ : IsCategoryAction category action _◂_

  semgroupoidAction : SemigroupoidAction _ _ _ _ _
  SemigroupoidAction.semigroupoid semgroupoidAction = semigroupoid
  SemigroupoidAction.action semgroupoidAction = action
  SemigroupoidAction._◂_ semgroupoidAction = _◂_

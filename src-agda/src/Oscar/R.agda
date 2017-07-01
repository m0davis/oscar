
module Oscar.R where

open import Oscar.Prelude

module _ where
  record 𝓡₀,₀ : Ø₀ where no-eta-equality

  module _ {𝔬₀} (𝔒₀ : Ø 𝔬₀) where
    𝑹₀ = 𝔒₀
    record 𝓡₁,₀ : Ø₀ where no-eta-equality
    record 𝓡₁,₁ : Ø 𝔬₀ where
      field 𝓻₁,₁,₀ : 𝑹₀
    record 𝓡₁,₂ : Ø 𝔬₀ where
      field 𝓻₁,₂,₀ : 𝑹₀
      field 𝓻₁,₂,₁ : 𝑹₀
    record 𝓡₁,₃ : Ø 𝔬₀ where
      field 𝓻₁,₃,₀ : 𝑹₀
      field 𝓻₁,₃,₁ : 𝑹₀
      field 𝓻₁,₃,₂ : 𝑹₀
    record 𝓡₁,₄ : Ø 𝔬₀ where
      field 𝓻₁,₄,₀ : 𝑹₀
      field 𝓻₁,₄,₁ : 𝑹₀
      field 𝓻₁,₄,₂ : 𝑹₀
      field 𝓻₁,₄,₃ : 𝑹₀
    record 𝓡₁,₅ : Ø 𝔬₀ where
      field 𝓻₁,₅,₀ : 𝑹₀
      field 𝓻₁,₅,₁ : 𝑹₀
      field 𝓻₁,₅,₂ : 𝑹₀
      field 𝓻₁,₅,₃ : 𝑹₀
      field 𝓻₁,₅,₄ : 𝑹₀
    record 𝓡₁,₆ : Ø 𝔬₀ where
      field 𝓻₁,₆,₀ : 𝑹₀
      field 𝓻₁,₆,₁ : 𝑹₀
      field 𝓻₁,₆,₂ : 𝑹₀
      field 𝓻₁,₆,₃ : 𝑹₀
      field 𝓻₁,₆,₄ : 𝑹₀
      field 𝓻₁,₆,₅ : 𝑹₀
    record 𝓡₁,₇ : Ø 𝔬₀ where
      field 𝓻₁,₇,₀ : 𝑹₀
      field 𝓻₁,₇,₁ : 𝑹₀
      field 𝓻₁,₇,₂ : 𝑹₀
      field 𝓻₁,₇,₃ : 𝑹₀
      field 𝓻₁,₇,₄ : 𝑹₀
      field 𝓻₁,₇,₅ : 𝑹₀
      field 𝓻₁,₇,₆ : 𝑹₀
    record 𝓡₁,₈ : Ø 𝔬₀ where
      field 𝓻₁,₈,₀ : 𝑹₀
      field 𝓻₁,₈,₁ : 𝑹₀
      field 𝓻₁,₈,₂ : 𝑹₀
      field 𝓻₁,₈,₃ : 𝑹₀
      field 𝓻₁,₈,₄ : 𝑹₀
      field 𝓻₁,₈,₅ : 𝑹₀
      field 𝓻₁,₈,₆ : 𝑹₀
      field 𝓻₁,₈,₇ : 𝑹₀

    module _ {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁) where
      𝑹₁ = ∀ ⓪ → 𝔒₁ ⓪
      record 𝓡₂,₀ : Ø₀ where no-eta-equality
      record 𝓡₂,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₁,₀ : 𝑹₁
      record 𝓡₂,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₂,₀ : 𝑹₁
        field 𝓻₂,₂,₁ : 𝑹₁
      record 𝓡₂,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₃,₀ : 𝑹₁
        field 𝓻₂,₃,₁ : 𝑹₁
        field 𝓻₂,₃,₂ : 𝑹₁
      record 𝓡₂,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₄,₀ : 𝑹₁
        field 𝓻₂,₄,₁ : 𝑹₁
        field 𝓻₂,₄,₂ : 𝑹₁
        field 𝓻₂,₄,₃ : 𝑹₁
      record 𝓡₂,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₅,₀ : 𝑹₁
        field 𝓻₂,₅,₁ : 𝑹₁
        field 𝓻₂,₅,₂ : 𝑹₁
        field 𝓻₂,₅,₃ : 𝑹₁
        field 𝓻₂,₅,₄ : 𝑹₁
      record 𝓡₂,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₆,₀ : 𝑹₁
        field 𝓻₂,₆,₁ : 𝑹₁
        field 𝓻₂,₆,₂ : 𝑹₁
        field 𝓻₂,₆,₃ : 𝑹₁
        field 𝓻₂,₆,₄ : 𝑹₁
        field 𝓻₂,₆,₅ : 𝑹₁
      record 𝓡₂,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₇,₀ : 𝑹₁
        field 𝓻₂,₇,₁ : 𝑹₁
        field 𝓻₂,₇,₂ : 𝑹₁
        field 𝓻₂,₇,₃ : 𝑹₁
        field 𝓻₂,₇,₄ : 𝑹₁
        field 𝓻₂,₇,₅ : 𝑹₁
        field 𝓻₂,₇,₆ : 𝑹₁
      record 𝓡₂,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ where
        field 𝓻₂,₈,₀ : 𝑹₁
        field 𝓻₂,₈,₁ : 𝑹₁
        field 𝓻₂,₈,₂ : 𝑹₁
        field 𝓻₂,₈,₃ : 𝑹₁
        field 𝓻₂,₈,₄ : 𝑹₁
        field 𝓻₂,₈,₅ : 𝑹₁
        field 𝓻₂,₈,₆ : 𝑹₁
        field 𝓻₂,₈,₇ : 𝑹₁

      module _ {𝔬₂} (𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂) where
        𝑹₂ = ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴
        record 𝓡₃,₀ : Ø₀ where no-eta-equality
        record 𝓡₃,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₁,₀ : 𝑹₂
        record 𝓡₃,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₂,₀ : 𝑹₂
          field 𝓻₃,₂,₁ : 𝑹₂
        record 𝓡₃,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₃,₀ : 𝑹₂
          field 𝓻₃,₃,₁ : 𝑹₂
          field 𝓻₃,₃,₂ : 𝑹₂
        record 𝓡₃,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₄,₀ : 𝑹₂
          field 𝓻₃,₄,₁ : 𝑹₂
          field 𝓻₃,₄,₂ : 𝑹₂
          field 𝓻₃,₄,₃ : 𝑹₂
        record 𝓡₃,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₅,₀ : 𝑹₂
          field 𝓻₃,₅,₁ : 𝑹₂
          field 𝓻₃,₅,₂ : 𝑹₂
          field 𝓻₃,₅,₃ : 𝑹₂
          field 𝓻₃,₅,₄ : 𝑹₂
        record 𝓡₃,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₆,₀ : 𝑹₂
          field 𝓻₃,₆,₁ : 𝑹₂
          field 𝓻₃,₆,₂ : 𝑹₂
          field 𝓻₃,₆,₃ : 𝑹₂
          field 𝓻₃,₆,₄ : 𝑹₂
          field 𝓻₃,₆,₅ : 𝑹₂
        record 𝓡₃,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₇,₀ : 𝑹₂
          field 𝓻₃,₇,₁ : 𝑹₂
          field 𝓻₃,₇,₂ : 𝑹₂
          field 𝓻₃,₇,₃ : 𝑹₂
          field 𝓻₃,₇,₄ : 𝑹₂
          field 𝓻₃,₇,₅ : 𝑹₂
          field 𝓻₃,₇,₆ : 𝑹₂
        record 𝓡₃,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
          field 𝓻₃,₈,₀ : 𝑹₂
          field 𝓻₃,₈,₁ : 𝑹₂
          field 𝓻₃,₈,₂ : 𝑹₂
          field 𝓻₃,₈,₃ : 𝑹₂
          field 𝓻₃,₈,₄ : 𝑹₂
          field 𝓻₃,₈,₅ : 𝑹₂
          field 𝓻₃,₈,₆ : 𝑹₂
          field 𝓻₃,₈,₇ : 𝑹₂

        module _ {𝔬₃} (𝔒₃ : ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴ → Ø 𝔬₃) where
          𝑹₃ = ∀ ⓪ ⑴ ⑵ → 𝔒₃ ⓪ ⑴ ⑵
          record 𝓡₄,₀ : Ø₀ where no-eta-equality
          record 𝓡₄,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₁,₀ : 𝑹₃
          record 𝓡₄,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₂,₀ : 𝑹₃
            field 𝓻₄,₂,₁ : 𝑹₃
          record 𝓡₄,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₃,₀ : 𝑹₃
            field 𝓻₄,₃,₁ : 𝑹₃
            field 𝓻₄,₃,₂ : 𝑹₃
          record 𝓡₄,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₄,₀ : 𝑹₃
            field 𝓻₄,₄,₁ : 𝑹₃
            field 𝓻₄,₄,₂ : 𝑹₃
            field 𝓻₄,₄,₃ : 𝑹₃
          record 𝓡₄,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₅,₀ : 𝑹₃
            field 𝓻₄,₅,₁ : 𝑹₃
            field 𝓻₄,₅,₂ : 𝑹₃
            field 𝓻₄,₅,₃ : 𝑹₃
            field 𝓻₄,₅,₄ : 𝑹₃
          record 𝓡₄,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₆,₀ : 𝑹₃
            field 𝓻₄,₆,₁ : 𝑹₃
            field 𝓻₄,₆,₂ : 𝑹₃
            field 𝓻₄,₆,₃ : 𝑹₃
            field 𝓻₄,₆,₄ : 𝑹₃
            field 𝓻₄,₆,₅ : 𝑹₃
          record 𝓡₄,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₇,₀ : 𝑹₃
            field 𝓻₄,₇,₁ : 𝑹₃
            field 𝓻₄,₇,₂ : 𝑹₃
            field 𝓻₄,₇,₃ : 𝑹₃
            field 𝓻₄,₇,₄ : 𝑹₃
            field 𝓻₄,₇,₅ : 𝑹₃
            field 𝓻₄,₇,₆ : 𝑹₃
          record 𝓡₄,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
            field 𝓻₄,₈,₀ : 𝑹₃
            field 𝓻₄,₈,₁ : 𝑹₃
            field 𝓻₄,₈,₂ : 𝑹₃
            field 𝓻₄,₈,₃ : 𝑹₃
            field 𝓻₄,₈,₄ : 𝑹₃
            field 𝓻₄,₈,₅ : 𝑹₃
            field 𝓻₄,₈,₆ : 𝑹₃
            field 𝓻₄,₈,₇ : 𝑹₃

          module _ {𝔬₄} (𝔒₄ : ∀ ⓪ ⑴ ⑵ → 𝔒₃ ⓪ ⑴ ⑵ → Ø 𝔬₄) where
            𝑹₄ = ∀ ⓪ ⑴ ⑵ ⑶ → 𝔒₄ ⓪ ⑴ ⑵ ⑶
            record 𝓡₅,₀ : Ø₀ where no-eta-equality
            record 𝓡₅,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₁,₀ : 𝑹₄
            record 𝓡₅,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₂,₀ : 𝑹₄
              field 𝓻₅,₂,₁ : 𝑹₄
            record 𝓡₅,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₃,₀ : 𝑹₄
              field 𝓻₅,₃,₁ : 𝑹₄
              field 𝓻₅,₃,₂ : 𝑹₄
            record 𝓡₅,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₄,₀ : 𝑹₄
              field 𝓻₅,₄,₁ : 𝑹₄
              field 𝓻₅,₄,₂ : 𝑹₄
              field 𝓻₅,₄,₃ : 𝑹₄
            record 𝓡₅,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₅,₀ : 𝑹₄
              field 𝓻₅,₅,₁ : 𝑹₄
              field 𝓻₅,₅,₂ : 𝑹₄
              field 𝓻₅,₅,₃ : 𝑹₄
              field 𝓻₅,₅,₄ : 𝑹₄
            record 𝓡₅,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₆,₀ : 𝑹₄
              field 𝓻₅,₆,₁ : 𝑹₄
              field 𝓻₅,₆,₂ : 𝑹₄
              field 𝓻₅,₆,₃ : 𝑹₄
              field 𝓻₅,₆,₄ : 𝑹₄
              field 𝓻₅,₆,₅ : 𝑹₄
            record 𝓡₅,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₇,₀ : 𝑹₄
              field 𝓻₅,₇,₁ : 𝑹₄
              field 𝓻₅,₇,₂ : 𝑹₄
              field 𝓻₅,₇,₃ : 𝑹₄
              field 𝓻₅,₇,₄ : 𝑹₄
              field 𝓻₅,₇,₅ : 𝑹₄
              field 𝓻₅,₇,₆ : 𝑹₄
            record 𝓡₅,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
              field 𝓻₅,₈,₀ : 𝑹₄
              field 𝓻₅,₈,₁ : 𝑹₄
              field 𝓻₅,₈,₂ : 𝑹₄
              field 𝓻₅,₈,₃ : 𝑹₄
              field 𝓻₅,₈,₄ : 𝑹₄
              field 𝓻₅,₈,₅ : 𝑹₄
              field 𝓻₅,₈,₆ : 𝑹₄
              field 𝓻₅,₈,₇ : 𝑹₄

            module _ {𝔬₅} (𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶ → 𝔒₄ ⓪ ⑴ ⑵ ⑶ → Ø 𝔬₅) where
              𝑹₅ = ∀ ⓪ ⑴ ⑵ ⑶ ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
              record 𝓡₆,₀ : Ø₀ where no-eta-equality
              record 𝓡₆,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₁,₀ : 𝑹₅
              record 𝓡₆,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₂,₀ : 𝑹₅
                field 𝓻₆,₂,₁ : 𝑹₅
              record 𝓡₆,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₃,₀ : 𝑹₅
                field 𝓻₆,₃,₁ : 𝑹₅
                field 𝓻₆,₃,₂ : 𝑹₅
              record 𝓡₆,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₄,₀ : 𝑹₅
                field 𝓻₆,₄,₁ : 𝑹₅
                field 𝓻₆,₄,₂ : 𝑹₅
                field 𝓻₆,₄,₃ : 𝑹₅
              record 𝓡₆,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₅,₀ : 𝑹₅
                field 𝓻₆,₅,₁ : 𝑹₅
                field 𝓻₆,₅,₂ : 𝑹₅
                field 𝓻₆,₅,₃ : 𝑹₅
                field 𝓻₆,₅,₄ : 𝑹₅
              record 𝓡₆,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₆,₀ : 𝑹₅
                field 𝓻₆,₆,₁ : 𝑹₅
                field 𝓻₆,₆,₂ : 𝑹₅
                field 𝓻₆,₆,₃ : 𝑹₅
                field 𝓻₆,₆,₄ : 𝑹₅
                field 𝓻₆,₆,₅ : 𝑹₅
              record 𝓡₆,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₇,₀ : 𝑹₅
                field 𝓻₆,₇,₁ : 𝑹₅
                field 𝓻₆,₇,₂ : 𝑹₅
                field 𝓻₆,₇,₃ : 𝑹₅
                field 𝓻₆,₇,₄ : 𝑹₅
                field 𝓻₆,₇,₅ : 𝑹₅
                field 𝓻₆,₇,₆ : 𝑹₅
              record 𝓡₆,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ where
                field 𝓻₆,₈,₀ : 𝑹₅
                field 𝓻₆,₈,₁ : 𝑹₅
                field 𝓻₆,₈,₂ : 𝑹₅
                field 𝓻₆,₈,₃ : 𝑹₅
                field 𝓻₆,₈,₄ : 𝑹₅
                field 𝓻₆,₈,₅ : 𝑹₅
                field 𝓻₆,₈,₆ : 𝑹₅
                field 𝓻₆,₈,₇ : 𝑹₅

              module _ {𝔬₆} (𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷ → Ø 𝔬₆) where
                𝑹₆ = ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸
                record 𝓡₇,₀ : Ø₀ where no-eta-equality
                record 𝓡₇,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₁,₀ : 𝑹₆
                record 𝓡₇,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₂,₀ : 𝑹₆
                  field 𝓻₇,₂,₁ : 𝑹₆
                record 𝓡₇,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₃,₀ : 𝑹₆
                  field 𝓻₇,₃,₁ : 𝑹₆
                  field 𝓻₇,₃,₂ : 𝑹₆
                record 𝓡₇,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₄,₀ : 𝑹₆
                  field 𝓻₇,₄,₁ : 𝑹₆
                  field 𝓻₇,₄,₂ : 𝑹₆
                  field 𝓻₇,₄,₃ : 𝑹₆
                record 𝓡₇,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₅,₀ : 𝑹₆
                  field 𝓻₇,₅,₁ : 𝑹₆
                  field 𝓻₇,₅,₂ : 𝑹₆
                  field 𝓻₇,₅,₃ : 𝑹₆
                  field 𝓻₇,₅,₄ : 𝑹₆
                record 𝓡₇,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₆,₀ : 𝑹₆
                  field 𝓻₇,₆,₁ : 𝑹₆
                  field 𝓻₇,₆,₂ : 𝑹₆
                  field 𝓻₇,₆,₃ : 𝑹₆
                  field 𝓻₇,₆,₄ : 𝑹₆
                  field 𝓻₇,₆,₅ : 𝑹₆
                record 𝓡₇,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₇,₀ : 𝑹₆
                  field 𝓻₇,₇,₁ : 𝑹₆
                  field 𝓻₇,₇,₂ : 𝑹₆
                  field 𝓻₇,₇,₃ : 𝑹₆
                  field 𝓻₇,₇,₄ : 𝑹₆
                  field 𝓻₇,₇,₅ : 𝑹₆
                  field 𝓻₇,₇,₆ : 𝑹₆
                record 𝓡₇,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ where
                  field 𝓻₇,₈,₀ : 𝑹₆
                  field 𝓻₇,₈,₁ : 𝑹₆
                  field 𝓻₇,₈,₂ : 𝑹₆
                  field 𝓻₇,₈,₃ : 𝑹₆
                  field 𝓻₇,₈,₄ : 𝑹₆
                  field 𝓻₇,₈,₅ : 𝑹₆
                  field 𝓻₇,₈,₆ : 𝑹₆
                  field 𝓻₇,₈,₇ : 𝑹₆

                module _ {𝔬₇} (𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ → Ø 𝔬₇) where
                  𝑹₇ = ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹  → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹
                  record 𝓡₈,₀ : Ø₀ where no-eta-equality
                  record 𝓡₈,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₁,₀ : 𝑹₇
                  record 𝓡₈,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₂,₀ : 𝑹₇
                    field 𝓻₈,₂,₁ : 𝑹₇
                  record 𝓡₈,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₃,₀ : 𝑹₇
                    field 𝓻₈,₃,₁ : 𝑹₇
                    field 𝓻₈,₃,₂ : 𝑹₇
                  record 𝓡₈,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₄,₀ : 𝑹₇
                    field 𝓻₈,₄,₁ : 𝑹₇
                    field 𝓻₈,₄,₂ : 𝑹₇
                    field 𝓻₈,₄,₃ : 𝑹₇
                  record 𝓡₈,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₅,₀ : 𝑹₇
                    field 𝓻₈,₅,₁ : 𝑹₇
                    field 𝓻₈,₅,₂ : 𝑹₇
                    field 𝓻₈,₅,₃ : 𝑹₇
                    field 𝓻₈,₅,₄ : 𝑹₇
                  record 𝓡₈,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₆,₀ : 𝑹₇
                    field 𝓻₈,₆,₁ : 𝑹₇
                    field 𝓻₈,₆,₂ : 𝑹₇
                    field 𝓻₈,₆,₃ : 𝑹₇
                    field 𝓻₈,₆,₄ : 𝑹₇
                    field 𝓻₈,₆,₅ : 𝑹₇
                  record 𝓡₈,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₇,₀ : 𝑹₇
                    field 𝓻₈,₇,₁ : 𝑹₇
                    field 𝓻₈,₇,₂ : 𝑹₇
                    field 𝓻₈,₇,₃ : 𝑹₇
                    field 𝓻₈,₇,₄ : 𝑹₇
                    field 𝓻₈,₇,₅ : 𝑹₇
                    field 𝓻₈,₇,₆ : 𝑹₇
                  record 𝓡₈,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ where
                    field 𝓻₈,₈,₀ : 𝑹₇
                    field 𝓻₈,₈,₁ : 𝑹₇
                    field 𝓻₈,₈,₂ : 𝑹₇
                    field 𝓻₈,₈,₃ : 𝑹₇
                    field 𝓻₈,₈,₄ : 𝑹₇
                    field 𝓻₈,₈,₅ : 𝑹₇
                    field 𝓻₈,₈,₆ : 𝑹₇
                    field 𝓻₈,₈,₇ : 𝑹₇

                  module _ {𝔬₈} (𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ → Ø 𝔬₈) where
                    𝑹₈ = ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺
                    record 𝓡₉,₀ : Ø₀ where no-eta-equality
                    record 𝓡₉,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₁,₀ : 𝑹₈
                    record 𝓡₉,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₂,₀ : 𝑹₈
                      field 𝓻₉,₂,₁ : 𝑹₈
                    record 𝓡₉,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₃,₀ : 𝑹₈
                      field 𝓻₉,₃,₁ : 𝑹₈
                      field 𝓻₉,₃,₂ : 𝑹₈
                    record 𝓡₉,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₄,₀ : 𝑹₈
                      field 𝓻₉,₄,₁ : 𝑹₈
                      field 𝓻₉,₄,₂ : 𝑹₈
                      field 𝓻₉,₄,₃ : 𝑹₈
                    record 𝓡₉,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₅,₀ : 𝑹₈
                      field 𝓻₉,₅,₁ : 𝑹₈
                      field 𝓻₉,₅,₂ : 𝑹₈
                      field 𝓻₉,₅,₃ : 𝑹₈
                      field 𝓻₉,₅,₄ : 𝑹₈
                    record 𝓡₉,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₆,₀ : 𝑹₈
                      field 𝓻₉,₆,₁ : 𝑹₈
                      field 𝓻₉,₆,₂ : 𝑹₈
                      field 𝓻₉,₆,₃ : 𝑹₈
                      field 𝓻₉,₆,₄ : 𝑹₈
                      field 𝓻₉,₆,₅ : 𝑹₈
                    record 𝓡₉,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₇,₀ : 𝑹₈
                      field 𝓻₉,₇,₁ : 𝑹₈
                      field 𝓻₉,₇,₂ : 𝑹₈
                      field 𝓻₉,₇,₃ : 𝑹₈
                      field 𝓻₉,₇,₄ : 𝑹₈
                      field 𝓻₉,₇,₅ : 𝑹₈
                      field 𝓻₉,₇,₆ : 𝑹₈
                    record 𝓡₉,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ where
                      field 𝓻₉,₈,₀ : 𝑹₈
                      field 𝓻₉,₈,₁ : 𝑹₈
                      field 𝓻₉,₈,₂ : 𝑹₈
                      field 𝓻₉,₈,₃ : 𝑹₈
                      field 𝓻₉,₈,₄ : 𝑹₈
                      field 𝓻₉,₈,₅ : 𝑹₈
                      field 𝓻₉,₈,₆ : 𝑹₈
                      field 𝓻₉,₈,₇ : 𝑹₈

                    module _ {𝔬₉} (𝔒₉ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → Ø 𝔬₉) where
                      𝑹₉ = ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ ⑻ → 𝔒₉ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ ⑻
                      record 𝓡₁₀,₀ : Ø₀ where no-eta-equality
                      record 𝓡₁₀,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₁,₀ : 𝑹₉
                      record 𝓡₁₀,₂ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₂,₀ : 𝑹₉
                        field 𝓻₁₀,₂,₁ : 𝑹₉
                      record 𝓡₁₀,₃ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₃,₀ : 𝑹₉
                        field 𝓻₁₀,₃,₁ : 𝑹₉
                        field 𝓻₁₀,₃,₂ : 𝑹₉
                      record 𝓡₁₀,₄ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₄,₀ : 𝑹₉
                        field 𝓻₁₀,₄,₁ : 𝑹₉
                        field 𝓻₁₀,₄,₂ : 𝑹₉
                        field 𝓻₁₀,₄,₃ : 𝑹₉
                      record 𝓡₁₀,₅ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₅,₀ : 𝑹₉
                        field 𝓻₁₀,₅,₁ : 𝑹₉
                        field 𝓻₁₀,₅,₂ : 𝑹₉
                        field 𝓻₁₀,₅,₃ : 𝑹₉
                        field 𝓻₁₀,₅,₄ : 𝑹₉
                      record 𝓡₁₀,₆ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₆,₀ : 𝑹₉
                        field 𝓻₁₀,₆,₁ : 𝑹₉
                        field 𝓻₁₀,₆,₂ : 𝑹₉
                        field 𝓻₁₀,₆,₃ : 𝑹₉
                        field 𝓻₁₀,₆,₄ : 𝑹₉
                        field 𝓻₁₀,₆,₅ : 𝑹₉
                      record 𝓡₁₀,₇ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₇,₀ : 𝑹₉
                        field 𝓻₁₀,₇,₁ : 𝑹₉
                        field 𝓻₁₀,₇,₂ : 𝑹₉
                        field 𝓻₁₀,₇,₃ : 𝑹₉
                        field 𝓻₁₀,₇,₄ : 𝑹₉
                        field 𝓻₁₀,₇,₅ : 𝑹₉
                        field 𝓻₁₀,₇,₆ : 𝑹₉
                      record 𝓡₁₀,₈ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅ ∙̂ 𝔬₆ ∙̂ 𝔬₇ ∙̂ 𝔬₈ ∙̂ 𝔬₉ where
                        field 𝓻₁₀,₈,₀ : 𝑹₉
                        field 𝓻₁₀,₈,₁ : 𝑹₉
                        field 𝓻₁₀,₈,₂ : 𝑹₉
                        field 𝓻₁₀,₈,₃ : 𝑹₉
                        field 𝓻₁₀,₈,₄ : 𝑹₉
                        field 𝓻₁₀,₈,₅ : 𝑹₉
                        field 𝓻₁₀,₈,₆ : 𝑹₉
                        field 𝓻₁₀,₈,₇ : 𝑹₉

open 𝓡₀,₀ ⦃ … ⦄ public
open 𝓡₁,₀ ⦃ … ⦄ public
open 𝓡₁,₁ ⦃ … ⦄ public
open 𝓡₁,₂ ⦃ … ⦄ public
open 𝓡₁,₃ ⦃ … ⦄ public
open 𝓡₁,₄ ⦃ … ⦄ public
open 𝓡₁,₅ ⦃ … ⦄ public
open 𝓡₁,₆ ⦃ … ⦄ public
open 𝓡₁,₇ ⦃ … ⦄ public
open 𝓡₁,₈ ⦃ … ⦄ public
open 𝓡₂,₀ ⦃ … ⦄ public
open 𝓡₂,₁ ⦃ … ⦄ public
open 𝓡₂,₂ ⦃ … ⦄ public
open 𝓡₂,₃ ⦃ … ⦄ public
open 𝓡₂,₄ ⦃ … ⦄ public
open 𝓡₂,₅ ⦃ … ⦄ public
open 𝓡₂,₆ ⦃ … ⦄ public
open 𝓡₂,₇ ⦃ … ⦄ public
open 𝓡₂,₈ ⦃ … ⦄ public
open 𝓡₃,₀ ⦃ … ⦄ public
open 𝓡₃,₁ ⦃ … ⦄ public
open 𝓡₃,₂ ⦃ … ⦄ public
open 𝓡₃,₃ ⦃ … ⦄ public
open 𝓡₃,₄ ⦃ … ⦄ public
open 𝓡₃,₅ ⦃ … ⦄ public
open 𝓡₃,₆ ⦃ … ⦄ public
open 𝓡₃,₇ ⦃ … ⦄ public
open 𝓡₃,₈ ⦃ … ⦄ public
open 𝓡₄,₀ ⦃ … ⦄ public
open 𝓡₄,₁ ⦃ … ⦄ public
open 𝓡₄,₂ ⦃ … ⦄ public
open 𝓡₄,₃ ⦃ … ⦄ public
open 𝓡₄,₄ ⦃ … ⦄ public
open 𝓡₄,₅ ⦃ … ⦄ public
open 𝓡₄,₆ ⦃ … ⦄ public
open 𝓡₄,₇ ⦃ … ⦄ public
open 𝓡₄,₈ ⦃ … ⦄ public
open 𝓡₅,₀ ⦃ … ⦄ public
open 𝓡₅,₁ ⦃ … ⦄ public
open 𝓡₅,₂ ⦃ … ⦄ public
open 𝓡₅,₃ ⦃ … ⦄ public
open 𝓡₅,₄ ⦃ … ⦄ public
open 𝓡₅,₅ ⦃ … ⦄ public
open 𝓡₅,₆ ⦃ … ⦄ public
open 𝓡₅,₇ ⦃ … ⦄ public
open 𝓡₅,₈ ⦃ … ⦄ public
open 𝓡₆,₀ ⦃ … ⦄ public
open 𝓡₆,₁ ⦃ … ⦄ public
open 𝓡₆,₂ ⦃ … ⦄ public
open 𝓡₆,₃ ⦃ … ⦄ public
open 𝓡₆,₄ ⦃ … ⦄ public
open 𝓡₆,₅ ⦃ … ⦄ public
open 𝓡₆,₆ ⦃ … ⦄ public
open 𝓡₆,₇ ⦃ … ⦄ public
open 𝓡₆,₈ ⦃ … ⦄ public
open 𝓡₇,₀ ⦃ … ⦄ public
open 𝓡₇,₁ ⦃ … ⦄ public
open 𝓡₇,₂ ⦃ … ⦄ public
open 𝓡₇,₃ ⦃ … ⦄ public
open 𝓡₇,₄ ⦃ … ⦄ public
open 𝓡₇,₅ ⦃ … ⦄ public
open 𝓡₇,₆ ⦃ … ⦄ public
open 𝓡₇,₇ ⦃ … ⦄ public
open 𝓡₇,₈ ⦃ … ⦄ public
open 𝓡₈,₀ ⦃ … ⦄ public
open 𝓡₈,₁ ⦃ … ⦄ public
open 𝓡₈,₂ ⦃ … ⦄ public
open 𝓡₈,₃ ⦃ … ⦄ public
open 𝓡₈,₄ ⦃ … ⦄ public
open 𝓡₈,₅ ⦃ … ⦄ public
open 𝓡₈,₆ ⦃ … ⦄ public
open 𝓡₈,₇ ⦃ … ⦄ public
open 𝓡₈,₈ ⦃ … ⦄ public
open 𝓡₉,₀ ⦃ … ⦄ public
open 𝓡₉,₁ ⦃ … ⦄ public
open 𝓡₉,₂ ⦃ … ⦄ public
open 𝓡₉,₃ ⦃ … ⦄ public
open 𝓡₉,₄ ⦃ … ⦄ public
open 𝓡₉,₅ ⦃ … ⦄ public
open 𝓡₉,₆ ⦃ … ⦄ public
open 𝓡₉,₇ ⦃ … ⦄ public
open 𝓡₉,₈ ⦃ … ⦄ public
open 𝓡₁₀,₀ ⦃ … ⦄ public
open 𝓡₁₀,₁ ⦃ … ⦄ public
open 𝓡₁₀,₂ ⦃ … ⦄ public
open 𝓡₁₀,₃ ⦃ … ⦄ public
open 𝓡₁₀,₄ ⦃ … ⦄ public
open 𝓡₁₀,₅ ⦃ … ⦄ public
open 𝓡₁₀,₆ ⦃ … ⦄ public
open 𝓡₁₀,₇ ⦃ … ⦄ public
open 𝓡₁₀,₈ ⦃ … ⦄ public

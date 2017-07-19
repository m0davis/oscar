
open import Oscar.Class.Congruity
open import Oscar.Data

module Oscar.Class.Congruity.Proposextensequality where

instance

  𝓒̇ongruityProposextensequality : ∀ {a b} → 𝓒̇ongruity a b Proposextensequality
  𝓒̇ongruity.ċongruity 𝓒̇ongruityProposextensequality _ f≡̇g x rewrite f≡̇g x = ∅

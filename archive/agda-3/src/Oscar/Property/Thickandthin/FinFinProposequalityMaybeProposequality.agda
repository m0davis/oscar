open import Oscar.Prelude
open import Oscar.Class.Successor₀
open import Oscar.Class.Successor₁
open import Oscar.Class.Injectivity
open import Oscar.Class.Thickandthin
open import Oscar.Class.Congruity
open import Oscar.Class.Fmap
open import Oscar.Data.¶
open import Oscar.Data.Fin
open import Oscar.Data.Proposequality
open import Oscar.Data.Maybe
import Oscar.Property.Monad.Maybe
import Oscar.Class.Congruity.Proposequality

module Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality where

instance

  𝓢uccessor₀¶ : 𝓢uccessor₀ ¶
  𝓢uccessor₀¶ .𝓢uccessor₀.successor₀ = ↑_

  [𝓢uccessor₁]Fin : [𝓢uccessor₁] Fin
  [𝓢uccessor₁]Fin = ∁

  𝓢uccessor₁Fin : 𝓢uccessor₁ Fin
  𝓢uccessor₁Fin .𝓢uccessor₁.successor₁ = ↑_

  [𝓘njectivity₁]Fin : ∀ {m} → [𝓘njectivity₁] (λ (_ : Fin m) → Fin (⇑₀ m)) Proposequality Proposequality
  [𝓘njectivity₁]Fin = ∁

  𝓘njectivity₁Fin : ∀ {m} → 𝓘njectivity₁ (λ (_ : Fin m) → Fin (⇑₀ m)) Proposequality Proposequality
  𝓘njectivity₁Fin .𝓘njectivity₁.injectivity₁ ∅ = ∅

  [𝓣hick]Fin,Fin : [𝓣hick] Fin Fin
  [𝓣hick]Fin,Fin = ∁

  𝓣hickFin,Fin : 𝓣hick Fin Fin
  𝓣hickFin,Fin .𝓣hick.thick {∅} () ∅
  𝓣hickFin,Fin .𝓣hick.thick {↑ _} _ ∅ = ∅
  𝓣hickFin,Fin .𝓣hick.thick ∅ (↑ y) = y
  𝓣hickFin,Fin .𝓣hick.thick (↑ x) (↑ y) = ↑ thick x y

  [𝓣hin]Fin,Fin : [𝓣hin] Fin Fin
  [𝓣hin]Fin,Fin = ∁

  𝓣hinFin,Fin : 𝓣hin Fin Fin
  𝓣hinFin,Fin .𝓣hin.thin ∅ = ↑_
  𝓣hinFin,Fin .𝓣hin.thin (↑ x) ∅ = ∅
  𝓣hinFin,Fin .𝓣hin.thin (↑ x) (↑ y) = ↑ (thin x y)

  [𝓘njectivity₂,₁]ThinFinFin : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin Fin Fin m) Proposequality Proposequality
  [𝓘njectivity₂,₁]ThinFinFin = ∁

  𝓘njectivity₂,₁ThinFinFin : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin Fin Fin m) Proposequality Proposequality
  𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ ∅ ∅ = ∅
  𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {∅}    {∅} _ = ∅
  𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {∅}    {↑ _} ()
  𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {↑ _}  {∅}   ()
  𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ x) {↑ _}  {↑ _} = congruity ↑_ ∘ injectivity₂,₁ x ∘ injectivity₁[ Proposequality ]

  [𝓒heck]FinFinMaybe : [𝓒heck] Fin Fin Maybe
  [𝓒heck]FinFinMaybe = ∁

  𝓒heckFinFinMaybe : 𝓒heck Fin Fin Maybe
  𝓒heckFinFinMaybe .𝓒heck.check ∅ ∅ = ∅
  𝓒heckFinFinMaybe .𝓒heck.check ∅ (↑ y) = ↑ y
  𝓒heckFinFinMaybe .𝓒heck.check {∅} (↑ ()) _
  𝓒heckFinFinMaybe .𝓒heck.check {↑ _} (↑ x) ∅ = ↑ ∅
  𝓒heckFinFinMaybe .𝓒heck.check {↑ _} (↑ x) (↑ y) = fmap′ ¶⟨<_⟩.↑_ $ check x y

  [𝓣hick/thin=1]FinFin : [𝓣hick/thin=1] Fin Fin Proposequality
  [𝓣hick/thin=1]FinFin = ∁

  𝓣hick/thin=1FinFin : 𝓣hick/thin=1 Fin Fin Proposequality
  𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 x ∅ = ∅
  𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 ∅ (↑ y) = ∅
  𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 (↑ x) (↑ y) = congruity ↑_ (thick/thin=1 x y)

  [𝓒heck/thin=1FinFin] : [𝓒heck/thin=1] Fin Fin Maybe Proposequality
  [𝓒heck/thin=1FinFin] = ∁

  𝓒heck/thin=1FinFin : 𝓒heck/thin=1 Fin Fin Maybe Proposequality
  𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 ∅ y = ∅
  𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 (↑ x) ∅ = ∅
  𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 (↑ x) (↑ y) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y = ∅

  IsThickandthinFinFin : IsThickandthin Fin Fin Proposequality Maybe Proposequality
  IsThickandthinFinFin = ∁

ThickandthinFinFin : Thickandthin _ _ _ _ _ _
ThickandthinFinFin = ∁ Fin Fin Proposequality Maybe Proposequality

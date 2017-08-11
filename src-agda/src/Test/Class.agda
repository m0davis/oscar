
open import Oscar.Class
open import Oscar.Prelude
open import Oscar.Data.𝟙

module Test.Class where

module ℭ = ℭLASS renaming (𝒄lass to class; 𝒕ype to type; 𝒎ethod to method)

module _
  {𝔞} (𝔄 : Ø 𝔞)
  where
  𝔲nit : ℭlass $′ 𝔄 -- 𝟙
  𝔲nit = ∁ 𝔄
  module Unit = ℭ 𝔲nit

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  (x : 𝔄)
  where
  𝔭rop : ℭlass $′ 𝔅
  𝔭rop = ∁ $′ 𝔅 x
  module Prop = ℭ 𝔭rop

module AllUnitTest where
  test : ⦃ I : ∀ {𝔞} {𝔄 : Ø 𝔞} → Unit.class 𝔄 ⦄ → ∀ {𝔞} {𝔄 : Ø 𝔞} → Unit.class 𝔄
  test = {!!!}

module PropClass
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  where
  class = ∀ {x} → Prop.class 𝔅 x
  type = ∀ x → Prop.type 𝔅 x
  method = λ ⦃ _ : class ⦄ x → Prop.method 𝔅 x

module UnitPropClass
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  where
  class = ∀ {x} → Unit.class (𝔅 x)
  type = ∀ x → Unit.type (𝔅 x)
  method = λ ⦃ _ : class ⦄ x → Unit.method (𝔅 x)

module AllTest
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟}
  where
  testProp : ⦃ I : {𝔅 : 𝔄 → Ø 𝔟} → PropClass.class 𝔅 ⦄ → {𝔅 : 𝔄 → Ø 𝔟} → PropClass.class 𝔅
  testProp = {!!!}
{-
Goal: ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {.𝔅}
      (∁ (.𝔅 .x)) {{.Oscar.Data.Constraint.Constraint.∅}}
————————————————————————————————————————————————————————————
.x : 𝔄
.𝔅 : 𝔄 → Set 𝔟
.I : {𝔅 : 𝔄 → Set 𝔟} {x : 𝔄} →
     ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {𝔅} (∁ (𝔅 x))
     {{.Oscar.Data.Constraint.Constraint.∅}}
𝔟  : Ł
𝔄  : Set 𝔞
𝔞  : Ł
-}
{-
Goal: ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {.𝔅} (∁ (.𝔅 .x)) {{.Oscar.Data.Constraint.Constraint.∅}}
Have: {a : Ł} {A : Set a} {{x : A}} → A
_A = ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {.𝔅} (∁ (.𝔅 .x)) {{.Oscar.Data.Constraint.Constraint.∅}}
_x : ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {.𝔅} (∁ (.𝔅 .x)) {{.Oscar.Data.Constraint.Constraint.∅}}
candidate:
  .I : {𝔅 : 𝔄 → Set 𝔟} {x : 𝔄} →
       ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {𝔅} (∁ (𝔅 x))
       {{.Oscar.Data.Constraint.Constraint.∅}}
  ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {_𝔅1} (∁ (_𝔅1 _x1)) {{.Oscar.Data.Constraint.Constraint.∅}}
=
  ℭlass.SET-CLASS {𝔟} {(↑̂ 𝔟) ∙̂ 𝔞} {𝔄 → Set 𝔟} {.𝔅} (∁ (.𝔅 .x)) {{.Oscar.Data.Constraint.Constraint.∅}}
.𝔅 = _𝔅1
.𝔅 .x = _𝔅1 _x1
.𝔅 .x = .𝔅 _x1
.x = _x1
solution: .I {.𝔅} {.x}
-}
  testUnitProp : ⦃ I : {𝔅 : 𝔄 → Ø 𝔟} → UnitPropClass.class 𝔅 ⦄ → {𝔅 : 𝔄 → Ø 𝔟} → UnitPropClass.class 𝔅
  testUnitProp = {!!!}
{-
Goal: ℭlass.SET-CLASS {𝔟} {↑̂ ∅̂} {Set} {𝟙} (∁ (.𝔅 .x))
      {{.Oscar.Data.Constraint.Constraint.∅}}
————————————————————————————————————————————————————————————
.x : 𝔄
.𝔅 : 𝔄 → Set 𝔟
.I : {𝔅 : 𝔄 → Set 𝔟} {x : 𝔄} →
     ℭlass.SET-CLASS {𝔟} {↑̂ ∅̂} {Set} {𝟙} (∁ (𝔅 x))
     {{.Oscar.Data.Constraint.Constraint.∅}}
𝔟  : Ł
𝔄  : Set 𝔞
𝔞  : Ł
-}
{-
  ℭlass.SET-CLASS {𝔟} {↑̂ ∅̂} {Set} {𝟙} (∁ (.𝔅 .x))
      {{.Oscar.Data.Constraint.Constraint.∅}}
=
  ℭlass.SET-CLASS {𝔟} {↑̂ ∅̂} {Set} {𝟙} (∁ (_𝔅 _x))
      {{.Oscar.Data.Constraint.Constraint.∅}}
_𝔅 _x = .𝔅 .x
-}

module SinglePropTest
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  where
  testProp : ⦃ _ : PropClass.class 𝔅 ⦄ → PropClass.class 𝔅
  testProp = !
  testUnitProp : ⦃ _ : UnitPropClass.class 𝔅 ⦄ → UnitPropClass.class 𝔅
  testUnitProp = !

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → 𝔄 → Ø 𝔟)
  (x : 𝔄)
  where
  𝔯el : ℭlass $′ 𝔅
  𝔯el = ∁ $′ 𝔅 x x
  module Rel = ℭ 𝔯el

module RelClass
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → 𝔄 → Ø 𝔟)
  where
  class = ∀ {x} → Rel.class 𝔅 x
  type = ∀ x → Rel.type 𝔅 x
  method = λ ⦃ _ : class ⦄ x → Rel.method 𝔅 x

module UnitRelClass
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → 𝔄 → Ø 𝔟)
  where
  class = ∀ {x} → Unit.class (𝔅 x x)
  type = ∀ x → Unit.type (𝔅 x x)
  method = λ ⦃ _ : class ⦄ x → Unit.method (𝔅 x x)

module SingleRelTest
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → 𝔄 → Ø 𝔟)
  where
  testProp : ⦃ _ : RelClass.class 𝔅 ⦄ → RelClass.class 𝔅
  testProp = !
  testUnit : ⦃ _ : UnitRelClass.class 𝔅 ⦄ → UnitRelClass.class 𝔅
  testUnit = !

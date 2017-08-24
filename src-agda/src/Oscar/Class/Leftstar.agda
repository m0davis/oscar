
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Leftstar where

module Leftstar
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  (𝔄̇ : 𝔄 → Ø 𝔞̇)
  (𝔅̇ : 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  = ℭLASS (_◂_ , 𝔅̇) (∀ {x} f → 𝔄̇ x → 𝔅̇ (f ◂ x))

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  (𝔄̇ : 𝔄 → Ø 𝔞̇)
  (𝔅̇ : 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  where
  module LEFTSTAR = Leftstar 𝔄̇ 𝔅̇ _◂_ using () renaming (class to ∁⟦_/_/_⟧; method to F⟦_/_/_⟧)
  open Leftstar 𝔄̇ 𝔅̇ _◂_ using () renaming (class to Leftstar; method to leftstar⟦_/_/_⟧) public

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  {𝔄̇ : 𝔄 → Ø 𝔞̇}
  {𝔅̇ : 𝔅 → Ø 𝔟̇}
  {_◂_ : 𝔉 → 𝔄 → 𝔅}
  where
  open Leftstar 𝔄̇ 𝔅̇ _◂_ using () renaming (method to leftstar) public


open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data.𝟙

module Oscar.Class.Unit where

module Unit {𝔞} (𝔄 : Ø 𝔞) = ℭLASS 𝟙 𝔄

module _ {𝔞} {𝔄 : Ø 𝔞} where ‼ = Unit.method 𝔄

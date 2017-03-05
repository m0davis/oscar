
module Oscar.Data.Equality where

open import Oscar.Data.Equality.Core public
open import Relation.Binary.PropositionalEquality public using (_≢_; cong; cong₂; cong-app; subst; subst₂; sym; trans)

module Enagda01 where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Bool.Base

data ℕ⁺ : Set where
  Infinity : ℕ⁺
  [_] : ( n : ℕ ) → ℕ⁺

_<⁺_ : ℕ⁺ → ℕ⁺ → Set
_<⁺_ [ a ] [ b ] = a < b
_<⁺_ _ _ = {!!}

foo : ∀ a { b } → a <⁺ b → ℕ
foo = {!!}

no : ∀ ( a b : ℕ ) ( a<b : [ a ] <⁺ [ b ] ) → ℕ
no a b a<b = foo [ a ] { b = [ b ] } a<b

{-
foo : ∀ a { b } → a <⁺ b → ℕ
foo = {!!}

o : ∀ (a⁺ : ℕ⁺) ( b : ℕ ) ( a<b : a⁺ <⁺ [ b ] ) → ℕ
o a⁺ b a<b = foo a⁺ a<b

no : ∀ ( a b : ℕ ) ( a<b : [ a ] <⁺ [ b ] ) → ℕ
no a b a<b = foo [ a ] a<b
-}


trans⁺ : ∀ a { b c } → a <⁺ b → b <⁺ c → a <⁺ c
trans⁺ [ a ] { b = [ b ] } { c = [ c ] } a<b b<c = {!!}
trans⁺ _ _ _ = {!!}

okay : ∀ ( a b c : ℕ⁺ ) ( a<b : a <⁺ b ) ( b<c : b <⁺ c ) → a <⁺ c
okay a b c a<b b<c = trans⁺ a a<b b<c

not-okay : ∀ ( a b c : ℕ ) ( a<b : [ a ] <⁺ [ b ] ) ( b<c : [ b ] <⁺ [ c ] ) → [ a ] <⁺ [ c ]
not-okay a b c a<b b<c = trans⁺ [ a ] a<b b<c

{-
trans : 

open import Data.AVL Value isStrictTotalOrder using ( module Extended-key )
open Extended-key

okay : ∀ ( a b c : Key⁺ ) ( a<b : a <⁺ b ) ( b<c : b <⁺ c ) → a <⁺ c
okay a b c a<b b<c = trans⁺ a a<b b<c

not-okay : ∀ ( a b c : Key ) ( a<b : [ a ] <⁺ [ b ] ) ( b<c : [ b ] <⁺ [ c ] ) → [ a ] <⁺ [ c ]
not-okay a b c a<b b<c = trans⁺ [ a ] a<b b<c
-}

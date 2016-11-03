module Control.Monad.Free where

open import Level using ( _⊔_ )
open import Level using ( suc )

data Free { α φ } ( f : Set α → Set φ ) ( a : Set α ) : Set ( suc ( α ⊔ φ ) ) where
  pure : a → Free f a
  free : ∀ { x : Set α } → ( x → Free f a ) → f x → Free f a

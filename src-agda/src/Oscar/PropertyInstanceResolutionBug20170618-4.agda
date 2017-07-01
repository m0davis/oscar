{-# OPTIONS --show-implicit #-}
module Oscar.PropertyInstanceResolutionBug20170618-4 where

postulate
  Nat : Set
  Fin : Nat → Set

Finnat : Nat → Set
Finnat x = Fin x → Nat

postulate
  fortytwo : Nat
  finnatic : Finnat fortytwo
  _==_ : Finnat fortytwo → Finnat fortytwo → Set
  ==-copy : ∀ {x y : Finnat fortytwo} → x == y → x == y

record Fixer : Set where
  field fix : ∀ {x} → Finnat x → Finnat fortytwo
open Fixer ⦃ … ⦄

record Fixidentity ⦃ _ : Fixer ⦄ : Set where
  field fixidentity : ∀ {f : Finnat fortytwo} → fix f == f
open Fixidentity ⦃ … ⦄

record InstanceWrapper : Set where
  no-eta-equality
  instance
    postulate FixerInstance : Fixer

open InstanceWrapper record {}

{-
  If the above InstanceWrapper is "unwrapped" and replaced with the code below, the failing tests succeed.

instance
  postulate FixerInstance : Fixer
-}

instance
  postulate FixidentityInstance : Fixidentity

works : fix finnatic == finnatic
works = ==-copy fixidentity

fails₁ : fix finnatic == finnatic
fails₁ = ==-copy {x = fix finnatic} fixidentity

fails₂ : fix finnatic == finnatic
fails₂ = fixidentity

{-
The errors are:

Failed to solve the following constraints:
  Resolve instance argument _45 : Fixidentity {{FixerInstance}}
  Candidates FixidentityInstance : Fixidentity {{FixerInstance}}
  Resolve instance argument _38 : (Fixidentity {{FixerInstance}})
  Candidates FixidentityInstance : (Fixidentity {{FixerInstance}})
-}

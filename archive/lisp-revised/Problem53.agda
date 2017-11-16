{-
Problem #53
Given premises:
    (all x)[(F x) -> (some y)((F y) & (G x y))]    justification = 1.0

Ultimate epistemic interests:
    (all x)[(F x) -> (some y)(some z)((G x y) & (G y z))]    interest = 1.0
-}

open import Prelude

postulate
  U : Set
  F : U → Set
  G : U → U → Set

record Premise {x : U} (Fx : F x) : Set where
  field
    pY : U
    pF : F pY
    pG : G x pY

open Premise

record Conclusion {x : U} (Fx : F x) : Set where
  field
    cY : U
    cZ : U
    cGxy : G x cY
    cGyz : G cY cZ

open Conclusion

premise = ∀ x → (Fx : F x) → Premise Fx
conclusion = ∀ x → (Fx : F x) → Conclusion Fx

proof1 : premise → conclusion
proof1 p x Fx =
  record
  { cY = _
  ; cZ = _
  ; cGxy = pG p1
  ; cGyz = pG p2 }
  where
  p1 = p x Fx
  p2 = p (pY p1) (pF p1)

{-
postulate
  U : Set
  F : U → Set
  G : U → U → Set

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ = Σ _

premise = ∀ x → F x → ∃ λ y → (F y × G x y)
conclusion = ∀ x → F x → ∃ λ y → ∃ λ z → (G x y × G y z)

pY : premise → ∀ x → F x → _
pY p x Fx = fst (p x Fx)

pF : premise → ∀ x → F x → F y -- y is not in scope!
pF p x Fx = {!fst (snd (p x Fx))!}

pG : premise → ∀ x → F x → _
pG p x Fx = {!snd (snd (p x Fx))!}

proof1 : premise → conclusion
proof1 p x Fx = y , z , Gxy , Gyz
  where
    y : U
    y = {!!}

    z : U
    z = {!!}

    Gxy : G x y
    Gxy = {!!}

    Gyz : G y z
    Gyz = {!!}
-}

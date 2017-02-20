open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

infix 2 _↔_
record _↔_ {a} {b} (p : Set a) (q : Set b) : Set (a ⊔ b) where
  field
    l2r : p → q
    r2l : q → p

_&_ : Bool → Bool → Bool
true & true = true
_ & _ = false

[_] : Bool → Set
[ P ] = P ≡ true

record ∃ {A : Set} (P : A → Bool) : Set where
  field
    {witness} : A
    proof : [ P witness ]

postulate
  U : Set
  set : Set
  subset : set → set → Bool
  int : set → set → set
  mem : ∀ {A : Set} → A → set → Bool
  mapsF : set → set → Bool
  F : ∀ {A B : Set} → A → B → Bool
  same : ∀ {A B : Set} → A → B → Bool
  equal : set → set → Bool
  invF : set → set → set
  subsetMembershipLaw : ∀ {A} {B} → [ subset A B ] ↔ (∀ {M : Set} {x : M} → [ mem x A ] → [ mem x B ])
--  mapsFLaw : ∀ {A} {B} → [ mapsF A B ] ↔ ((∀ {M : Set} {x : M} → [ mem x A ] → ∃ λ (y : M) → mem y B & F x y)

{-
Problem #758
same as problem 757 but rewritten with only expressions of first-order logic
Given premises:
     (all A)(all B)((subset A B) <-> (all x)((mem x A) -> (mem x B)))    justification = 1.0
     (all A)(all B)(some intAB)(IsInt A B intAB)    justification = 1.0
     (all A)(all B)(all intAB)((IsInt A B intAB) <-> (all x)((mem x intAB) <-> ((mem x A) & (mem x B))))    justification = 1.0
     (all A)(all B)((mapsF A B) <-> ((all x)((mem x A) -> (some y)((mem y B) & (F x y))) & (all x)(all y)(all z)(((mem x A) & ((mem y A) & (mem z A))) -> (((F x y) & (F x z)) -> (same y z)))))    justification = 1.0
     (all A)(all x)(all y)((same x y) -> ((mem x A) -> (mem y A)))    justification = 1.0
     (all x)(same x x)    justification = 1.0
     (all x)(all y)((same x y) <-> (same y x))    justification = 1.0
     (all x)(all y)(all z)(((same x y) & (same y z)) -> (same x z))    justification = 1.0
     (all A)(all B)((equal A B) <-> ((subset A B) & (subset B A)))    justification = 1.0
     (all A)(all B)(some invFBA)(IsInvF B A invFBA)    justification = 1.0
     (all A)(all B)(all invFBA)((IsInvF B A invFBA) <-> (all x)((mem x invFBA) <-> ((mem x A) & (some y)((mem y B) & (F x y)))))    justification = 1.0
Ultimate epistemic interests:
     (all A)(all B)(all X)(all Y)(((mapsF A B) & ((subset X B) & (subset Y B))) -> (some intXY)((IsInt X Y intXY) & (some invFIntXYA)((IsInvF intXY A invFIntXYA) & (some invFXA)((IsInvF X A invFXA) & (some invFYA)((IsInvF Y A invFYA) & (some intInvFXAInvFYA)((IsInt invFXA invFYA intInvFXAInvFYA) & (equal invFIntXYA intInvFXAInvFYA)))))))    interest = 1.0
-}

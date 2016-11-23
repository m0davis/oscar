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

_↔_ : Set → Set → Set
p ↔ q = p → q

postulate
  U : Set
  subset : U → U → Set
--  subsetMembership : ∀ {A} {B} →

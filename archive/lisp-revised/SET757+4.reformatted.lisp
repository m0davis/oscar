
(setf *problems*
          (eval-when (:compile-toplevel :execute)
              (make-problem-list
                "
Problem #1
Given premises:
	(all A)(all B)((subset A B) <-> (all x) ((mem x A) -> (mem x
B)))    justification = 1.0
	(all A)(all B)(all x)((mem x (int A B)) <-> ((mem x A) & (mem
x B)))    justification = 1.0
	(all A)(all B)((maps F A B) <->
			((all x)((mem x A) -> (some y)((mem y B) & (F x y)))
			& (all x)(all y)(all z)(((mem x A) & ((mem y
A) & (mem z A))) -> (((F x y) & (F x z)) -> (y = z)))))
justification = 1.0
	(all A)(all x)(all y)((x = y) -> ((mem x A) -> (mem y A)))
justification = 1.0
	(all A)(all B)((equal A B) <-> ((subset A B) & (subset B A)))
justification = 1.0
	(all B)(all A)(all B)(all x)((mem x (inv F B A)) <-> ((mem x
A) & (some y)((mem y B) & (F x y))))    justification = 1.0

Ultimate epistemic interests:
	(all A)(all B)(all X)(all Y)(((maps F A B) & ((subset X B) &
(subset Y B)))
								 ->
(equal (inv F (int X Y) A) (int (inv F X A) (inv F Y A))))
interest = 1.0
")))

#|
                                  OSCAR_3.31          12/30/2005
14:58:30

*reductio-discount* = 0.23
*reductio-interest* = 0.23
*skolem-multiplier* = 10
*quantifier-discount* = 0.95

******************************************************************************************
******************************************************************************************
Problem #1

Given premises:
      (all A)(all B)((subset A B) <-> (all x)((mem x A) -> (mem x B))) justification = 1.0
      (all A)(all B)(all x)((mem x (int A B)) <-> ((mem x A) & (mem x B)))    justification = 1.0
      (all A)(all B)((maps F A B) <-> ((all x)((mem x A) -> (some y)((mem y B) & (F x y))) & (all x)(all y)(all z)(((mem x A) & ((mem y A) & (mem z A))) -> (((F x y) & (F x z)) -> (= y z))))) justification = 1.0
      (all A)(all x)(all y)((= x y) -> ((mem x A) -> (mem y A))) justification = 1.0
      (all A)(all B)((equal A B) <-> ((subset A B) & (subset B A))) justification = 1.0
      (all B)(all A)(all b1)(all x)((mem x (inv F b1 A)) <-> ((mem x A) & (some y)((mem y b1) & (F x y))))    justification = 1.0
Ultimate epistemic interests:
      (all A)(all B)(all X)(all Y)(((maps F A B) & ((subset X B) & (subset Y B))) -> (equal (inv F (int X Y) A) (int (inv F X A) (inv F Y A))))    interest = 1.0



================== ULTIMATE EPISTEMIC INTERESTS ===================
   Interest in (all A)(all B)(all X)(all Y)(((maps F A B) & ((subset X
B) & (subset Y B))) -> (equal (inv F (int X Y) A) (int (inv F X A)
(inv F Y A))))
   is answered affirmatively by node 2010
---------------------------------------------------

Elapsed time = 3.428 sec

===========================================================================
ARGUMENT #1
This is an undefeated argument of strength 1.0 for:
       (all A)(all B)(all X)(all Y)(((maps F A B) & ((subset X B) &
(subset Y B))) -> (equal (inv F (int X Y) A) (int (inv F X A) (inv F
Y A))))
  which is of ultimate interest.

5.  (all A)(all B)((equal A B) <-> ((subset A B) & (subset B A)))     given
5.    GIVEN                               ∀ A B (A ≡ B ↔ A ⊂ B ∧ B ⊂ A
10.  (all B)((equal x4 B) <-> ((subset x4 B) & (subset B x4)))     UI from { 5 }
10.   UI 5                                ∀ B (x4 ≡ B ↔ (x4 ⊂ B ∧ B ⊂ x4))
12.  ((equal x4 x6) <-> ((subset x4 x6) & (subset x6 x4)))     UI from { 10 }
12.   UI 10                               x4 ≡ x6 ↔ (x4 ⊂ x6 ∧ x6 ⊂ x4)
19.  (((subset x4 x6) & (subset x6 x4)) -> (equal x4 x6)) bicondit-simp from { 12 }
19.   bicondit-simp 12                    x4 ⊂ x6 ∧ x6 ⊂ x4 → x4 ≡ x6
18.  ((equal x4 x6) -> ((subset x4 x6) & (subset x6 x4))) bicondit-simp from { 12 }
18.   bicondit-simp 12                    x4 ≡ x6 → (x4 ⊂ x6 ∧ x6 ⊂ x4)
20.  ((subset x4 x6) -> ((subset x6 x4) -> (equal x4 x6))) exportation from { 19 }
20.   exportation 19                      x4 ⊂ x6 → (x6 ⊂ x4 → x4 ≡ x6)
1.  (all A)(all B)((subset A B) <-> (all x)((mem x A) -> (mem x B)))     given
1.    GIVEN                               ∀ A B (A ⊂ B ↔ ∀ x (x ∈ A → x ∈ B))
8.  (all B)((subset x2 B) <-> (all x)((mem x x2) -> (mem x B))) UI from { 1 }
8.    UI 1                                ∀ B (x2 ⊂ B ↔ ∀ x (x ∈ x2 → x ∈ B))
11.  ((subset x2 x5) <-> (all x)((mem x x2) -> (mem x x5)))     UI from { 8 }
11.   UI 8                                x2 ⊂ x5 ↔ ∀ x (x ∈ x2 → x ∈ x5)
14.  ((subset x2 x5) -> (all x)((mem x x2) -> (mem x x5))) bicondit-simp from { 11 }
14.   bicondit-simp 11                    x2 ⊂ x5 → ∀ x (x ∈ x2 → x ∈ x5)
15.  ((all x)((mem x x2) -> (mem x x5)) -> (subset x2 x5)) bicondit-simp from { 11 }
16.  (some z8)(((mem z8 x2) -> (mem z8 x5)) -> (subset x2 x5)) A-removal from { 15 }
17.  (((mem (@y9 x2 x5) x2) -> (mem (@y9 x2 x5) x5)) -> (subset x2 x5))     EI from { 16 }
46.  (~(mem (@y9 x2 x5) x2) -> (subset x2 x5)) cond-antecedent-simp from { 17 }
47.  ((mem (@y9 x2 x5) x5) -> (subset x2 x5)) cond-antecedent-simp from { 17 }
531.  ~(equal x596 ^x18) supposing { ~(equal x596 ^x18) } reductio-supposition
45.  ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     reductio-supposition
75.  ~((subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) & (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     modus-tollens2 from { 19 , 45 }
76.  (~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) v ~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     DM from { 75 }
77.  ((subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> ~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     disj-simp from { 76 }
81.  (~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) v ~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     disj-cond-2 from { 77 }
84.  ((subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) -> ~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     disj-simp from { 81 }
79.  (mem x86 x85) supposing { (mem x86 x85) }     reductio-supposition
80.  (subset x90 x89) supposing { (subset x90 x89) }     reductio-supposition
89.  ((subset x6 x4) -> (equal x4 x6)) supposing { (subset x4 x6) } modus-ponens2 from { 20 , 80 }
94.  (equal x4 x6) supposing { (subset x4 x6) , (subset x6 x4) } modus-ponens1 from { 89 , 80 }
532.  ~(subset ^x18 ^@y39) supposing { (subset ^@y39 ^x18) , ~(equal ^@y39 ^x18) }     reductio from { 94 , 531 }
535.  ((subset ^x18 ^@y39) -> ~(subset ^@y39 ^x18)) supposing { ~(equal ^@y39 ^x18) }     contra-conditionalization from { 532 }
540.  (~(subset ^x18 ^@y38) v ~(subset ^@y38 ^x18)) supposing { ~(equal ^@y39 ^x18) }     disj-cond from { 535 }
541.  ~((subset ^x18 ^@y38) & (subset ^@y38 ^x18)) supposing { ~(equal ^@y39 ^x18) }     i-DM from { 540 }
641.  ~(equal ^x18 x6) supposing { ~(equal ^@y39 ^x18) } modus-tollens2 from { 18 , 541 }
668.  ~(subset ^x18 ^@y106) supposing { ~(equal ^@y39 ^x18) , (subset ^@y106 ^x18) }     reductio from { 641 , 94 }
671.  ((subset ^@y38 ^x18) -> ~(subset ^x18 ^@y38)) supposing { ~(equal ^@y39 ^x18) }     conditionalization from { 668 }
740.  ~(subset ^x18 ^x18) supposing { ~(equal ^@y39 ^x18) } cond-simp1 from { 671 }
741.  (mem (@y9 ^x18 ^x18) ^x18) supposing { ~(equal ^@y39 ^x18) } modus-tollens2 from { 46 , 740 }
1396.  (subset ^x18 ^x18) supposing { ~(equal ^@y39 ^x18) } modus-ponens2 from { 47 , 741 }
751.  ~(mem (@y9 ^x18 ^x18) ^x18) supposing { ~(equal ^@y39 ^x18) } modus-tollens2 from { 47 , 740 }
752.  ~((mem (@y9 ^x18 ^x18) ^x18) -> (mem (@y9 ^x18 ^x18) ^x18)) supposing { ~(equal ^@y39 ^x18) }     i-neg-condit from { 751 , 741 }
753.  (some x)~((mem x ^x18) -> (mem x ^x18)) supposing { ~(equal ^@y39 ^x18) }     EG from { 752 }
754.  ~(all x)((mem x ^x18) -> (mem x ^x18)) supposing { ~(equal ^@y39 ^x18) }     i-neg-ug from { 753 }
1404.  ~((subset ^x18 ^x18) -> (all x)((mem x ^x18) -> (mem x ^x18))) supposing { ~(equal ^@y39 ^x18) }     i-neg-condit from { 754 , 1396 }
1405.  (equal ^@y39 ^x18)     reductio from { 1404 , 14 }
1423.  ((subset x4 ^x18) & (subset ^x18 x4))     modus-ponens2 from { 18 , 1405 }
1424.  (subset x4 ^x18)     simp from { 1423 }
1460.  (subset ^x18 x4)     simp from { 1423 }
1516.  (all x)((mem x x2) -> (mem x ^x18))     modus-ponens2 from { 14 , 1424 }
1528.  ((mem x1354 x2) -> (mem x1354 ^x18))     UI from { 1516 }
1522.  (all x)((mem x ^x18) -> (mem x x5))     modus-ponens2 from { 14 , 1460 }
1527.  ((mem x1346 ^x18) -> (mem x1346 x5))     UI from { 1522 }
86.  ~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-ponens2 from { 84 , 80 }
115.  (mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) (inv F (int ^x18 ^x19) ^x0)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-tollens2 from { 46 , 86 }
117.  ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-tollens2 from { 47 , 86 }
90.  (all x)((mem x x2) -> (mem x x5)) supposing { (subset x2 x5) } modus-ponens2 from { 14 , 80 }
93.  ((mem x95 x2) -> (mem x95 x5)) supposing { (subset x2 x5) } UI from { 90 }
128.  (mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) x5) supposing { (subset (inv F (int ^x18 ^x19) ^x0) x5) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-ponens2 from { 93 , 115 }
129.  ~((mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) ^@y42) -> (mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))) supposing { (subset (inv F (int ^x18 ^x19) ^x0) ^@y42) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     i-neg-condit from { 117 , 128 }
130.  (some x)~((mem x ^@y42) -> (mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))) supposing { (subset (inv F (int ^x18 ^x19) ^x0) ^@y42) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     EG from { 129 }
131.  ~(all x)((mem x ^@y42) -> (mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))) supposing { (subset (inv F (int ^x18 ^x19) ^x0) ^@y42) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     i-neg-ug from { 130 }
137.  ~(subset x2 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) supposing { (subset (inv F (int ^x18 ^x19) ^x0) x2) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) } modus-tollens2 from { 14 , 131 }
1491.  ~(subset (inv F (int ^x18 ^x19) ^x0) ^x18) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     reductio from { 1460 , 137 }
1753.  (mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) (inv F (int ^x18 ^x19) ^x0)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-tollens2 from { 46 , 1491 }
166.  ~(subset (inv F (int ^x18 ^x19) ^x0) ^@y41) supposing { (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset ^@y41 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     reductio from { 137 , 80 }
229.  ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) x5) x5) supposing { (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset x5 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     modus-tollens2 from { 47 , 166 }
311.  ~(subset ^@y43 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) , (mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^@y43) ^@y43) }     reductio from { 229 , 79 }
1479.  ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) ^x18) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     reductio from { 1460 , 311 }
1806.  ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) x2) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-tollens2 from { 1528 , 1479 }
1813.  ~((mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) (inv F (int ^x18 ^x19) ^x0)) -> (mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) ^@y43)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     i-neg-condit from { 1806 , 1753 }
1814.  (some x)~((mem x (inv F (int ^x18 ^x19) ^x0)) -> (mem x ^@y43)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     EG from { 1813 }
1815.  ~(all x)((mem x (inv F (int ^x18 ^x19) ^x0)) -> (mem x ^@y43)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     i-neg-ug from { 1814 }
1924.  ~(subset (inv F (int ^x18 ^x19) ^x0) x5) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }     modus-tollens2 from { 14 , 1815 }
1963.  ~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     reductio from { 1924 , 1424 }
1975.  ~(mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) (inv F (int ^x18 ^x19) ^x0)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     modus-tollens2 from { 47 , 1963 }
1995.  ~(mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) ^x18) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     modus-tollens2 from { 1527 , 1975 }
1968.  (mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     modus-tollens2 from { 46 , 1963 }
2000.  ~((mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) ^x18)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     i-neg-condit from { 1995 , 1968 }
2001.  (some x)~((mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem x ^x18)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     EG from { 2000 }
2002.  ~(all x)((mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem x ^x18)) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     i-neg-ug from { 2001 }
2003.  ~((subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) ^x18) -> (all x)((mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem x ^x18))) supposing { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }     i-neg-condit from { 2002 , 1424 }
2004.  (equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))     reductio from { 2003 , 14 }
2006.  (((maps F ^x0 ^x17) & ((subset ^x18 ^x17) & (subset ^x19 ^x17))) -> (equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))))     conditionalization from { 2004 }
2007.  (all Y)(((maps F ^x0 ^x17) & ((subset ^x18 ^x17) & (subset Y ^x17))) -> (equal (inv F (int ^x18 Y) ^x0) (int (inv F ^x18 ^x0) (inv F Y ^x0))))     UG from { 2006 }
2008.  (all X)(all Y)(((maps F ^x0 ^x17) & ((subset X ^x17) & (subset Y ^x17))) -> (equal (inv F (int X Y) ^x0) (int (inv F X ^x0) (inv F Y ^x0))))     UG from { 2007 }
2009.  (all B)(all X)(all Y)(((maps F ^x0 B) & ((subset X B) & (subset Y B))) -> (equal (inv F (int X Y) ^x0) (int (inv F X ^x0) (inv F Y ^x0))))     UG from { 2008 }
2010.  (all A)(all B)(all X)(all Y)(((maps F A B) & ((subset X B) & (subset Y B))) -> (equal (inv F (int X Y) A) (int (inv F X A) (inv F Y A))))     UG from { 2009 }

===========================================================================


Cumulative size of arguments = 84
Size of inference-graph = 2010 of which 5 were unused suppositions.
4% of the inference-graph was used in the argument.
259 interests were adopted.
8 suppositions were made.

===========================================================================
THE FOLLOWING IS THE REASONING INVOLVED IN THE SOLUTION
Nodes marked DEFEATED have that status at the end of the reasoning.

   # 1
   (all A)(all B)((subset A B) <-> (all x)((mem x A) -> (mem x B)))
   given
   # 5
   (all A)(all B)((equal A B) <-> ((subset A B) & (subset B A)))
   given
                                         # 1
                                         interest: (all A)(all B)(all
X)(all Y)(((maps F A B) & ((subset X B) & (subset Y B))) -> (equal
(inv F (int X Y) A) (int (inv F X A) (inv F Y A))))
                                         This is of ultimate interest
                                         # 2
                                         interest: (all B)(all X)(all
Y)(((maps F ^x0 B) & ((subset X B) & (subset Y B))) -> (equal (inv F
(int X Y) ^x0) (int (inv F X ^x0) (inv F Y ^x0))))
                                         For interest 1 by UG
                                         This interest is discharged
by node 2009
   # 8
   (all B)((subset x2 B) <-> (all x)((mem x x2) -> (mem x B)))
   Inferred by:
                 support-link #8 from { 1 } by UI
   # 10
   (all B)((equal x4 B) <-> ((subset x4 B) & (subset B x4)))
   Inferred by:
                 support-link #10 from { 5 } by UI
   # 11
   ((subset x2 x5) <-> (all x)((mem x x2) -> (mem x x5)))
   Inferred by:
                 support-link #11 from { 8 } by UI
   # 12
   ((equal x4 x6) <-> ((subset x4 x6) & (subset x6 x4)))
   Inferred by:
                 support-link #12 from { 10 } by UI
   # 14
   ((subset x2 x5) -> (all x)((mem x x2) -> (mem x x5)))
   Inferred by:
                 support-link #14 from { 11 } by bicondit-simp
   # 15
   ((all x)((mem x x2) -> (mem x x5)) -> (subset x2 x5))
   Inferred by:
                 support-link #15 from { 11 } by bicondit-simp
   # 16
   (some z8)(((mem z8 x2) -> (mem z8 x5)) -> (subset x2 x5))
   Inferred by:
                 support-link #16 from { 15 } by A-removal
   # 17
   (((mem (@y9 x2 x5) x2) -> (mem (@y9 x2 x5) x5)) -> (subset x2 x5))
   Inferred by:
                 support-link #17 from { 16 } by EI
   # 18
   ((equal x4 x6) -> ((subset x4 x6) & (subset x6 x4)))
   Inferred by:
                 support-link #18 from { 12 } by bicondit-simp
   # 19
   (((subset x4 x6) & (subset x6 x4)) -> (equal x4 x6))
   Inferred by:
                 support-link #19 from { 12 } by bicondit-simp
   # 20
   ((subset x4 x6) -> ((subset x6 x4) -> (equal x4 x6)))
   Inferred by:
                 support-link #20 from { 19 } by exportation
                                         # 3
                                         interest: (all X)(all
Y)(((maps F ^x0 ^x17) & ((subset X ^x17) & (subset Y ^x17))) ->
(equal (inv F (int X Y) ^x0) (int (inv FX ^x0) (inv F Y ^x0))))
                                         For interest 2 by UG
                                         This interest is discharged
by node 2008
                                         # 4
                                         interest: (all Y)(((maps F
^x0 ^x17) & ((subset ^x18 ^x17) & (subset Y ^x17))) -> (equal (inv F
(int ^x18 Y) ^x0) (int (inv F ^x18 ^x0) (inv F Y ^x0))))
                                         For interest 3 by UG
                                         This interest is discharged
by node 2007
                                         # 5
                                         interest: (((maps F ^x0 ^x17)
& ((subset ^x18 ^x17) & (subset ^x19 ^x17))) -> (equal (inv F (int
^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))))
                                         For interest 4 by UG
                                         This interest is discharged
by node 2006
                                         # 6
                                         interest: (equal (inv F (int
^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
supposition: { ((maps F ^x0 ^x17) & ((subset ^x18 ^x17) & (subset
^x19 ^x17))) }
                                         For interest 5 by conditionalization
                                         This interest is discharged
by node 2004
   # 45
   ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0)))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0)
(int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   reductio-supposition
   generated by interest 6
                                         # 21
                                         reductio interest: ~((subset
^@y42 ^@y43) -> (all x)((mem x ^@y42) -> (mem x ^@y43)))
                                         Reductio interest generated by node 14
                                         This interest is discharged
by nodes (1404 2003)
   # 46
   (~(mem (@y9 x2 x5) x2) -> (subset x2 x5))
   Inferred by:
                 support-link #44 from { 17 } by cond-antecedent-simp
   # 47
   ((mem (@y9 x2 x5) x5) -> (subset x2 x5))
   Inferred by:
                 support-link #45 from { 17 } by cond-antecedent-simp
   # 75
   ~((subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) & (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)))    supposition: { ~(equal (inv F (int ^x18
^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #73 from { 19 , 45 } by modus-tollens2
   This discharges interest 43 but no inference made by discharging
this interest is used in the solution.
   # 76
   (~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) v ~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)))    supposition: { ~(equal (inv F (int ^x18
^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #74 from { 75 } by DM
   # 77
   ((subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) -> ~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv
F (int ^x18 ^x19) ^x0)))    supposition: { ~(equal (inv F (int ^x18
^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #75 from { 76 } by disj-simp
   This discharges interest 45
                                         # 37
                                         reductio interest: ~(all
x)((mem x ^@y42) -> (mem x ^@y43))
                                         For reductio interest 21 by
i-neg-condit
                                         This interest is discharged
by nodes (754 2002)
                                         # 38
                                         reductio interest: (some
x)~((mem x ^@y42) -> (mem x ^@y43))
                                         For reductio interest 37 by i-neg-ug
                                         This interest is discharged
by nodes (130 753 1814 2001)
                                         # 39
                                         reductio interest: ~((mem
^@y82 ^@y42) -> (mem ^@y82 ^@y43))
                                         For reductio interest 38 by EG
                                         Reductio interest generated by node 93
                                         This interest is discharged
by nodes (129 752 1813 2000)
                                         # 40
                                         reductio interest: ~(mem ^@y82 ^@y43)
                                         For reductio interest 39 by
i-neg-condit
                                         Reductio interest generated by node 79
                                         This interest is discharged
by nodes (117 229 751 1806 1995)
   # 79
   (mem x86 x85)    supposition: { (mem x86 x85) }
   reductio-supposition
   generated by interest 40
   # 80
   (subset x90 x89)    supposition: { (subset x90 x89) }
   reductio-supposition
  generated by interests (45 45)
                                         # 43
                                         reductio interest: ~((subset
^@y39 ^@y38) & (subset ^@y38 ^@y39))
                                         This interest is discharged
by nodes (75 541)
                                         but no inference made by
discharging this interest is used in the solution.
                                         # 44
                                         reductio interest: (~(subset
^@y39 ^@y38) v ~(subset ^@y38 ^@y39))
                                         For reductio interest 43 by i-DM
                                         This interest is discharged by node 540
                                         # 45
                                         reductio interest: ((subset
^@y38 ^@y39) -> ~(subset ^@y39 ^@y38))
                                         For reductio interest 44 by disj-cond-2
                                         For reductio interest 44 by disj-cond
                                         This interest is discharged
by nodes (77 535)
   # 81
   (~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) v ~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))))    supposition: { ~(equal (inv F (int ^x18
^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #76 from { 77 } by disj-cond-2
   This node is inferred by discharging a link to interest #44
   # 84
   ((subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) -> ~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))))    supposition: { ~(equal (inv F (int ^x18
^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #79 from { 81 } by disj-simp
                                         # 48
                                         reductio interest: ~(subset
^@y38 ^@y39)    supposition: { (subset ^@y39 ^@y38) }
                                         For reductio interest 45 by
contra-conditionalization
                                         For reductio interest 45 by
conditionalization
                                         This interest is discharged
by nodes (532 668)
   # 86
   ~(subset (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0)))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0)
(int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18
^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #81 from { 84 , 80 } by modus-ponens2
   # 89
   ((subset x6 x4) -> (equal x4 x6))    supposition: { (subset x4 x6) }
   Inferred by:
                 support-link #84 from { 20 , 80 } by modus-ponens2
   # 90
   (all x)((mem x x2) -> (mem x x5))    supposition: { (subset x2 x5) }
   Inferred by:
                 support-link #85 from { 14 , 80 } by modus-ponens2
   # 93
   ((mem x95 x2) -> (mem x95 x5))    supposition: { (subset x2 x5) }
   Inferred by:
                 support-link #88 from { 90 } by UI
   # 94
   (equal x4 x6)    supposition: { (subset x4 x6) , (subset x6 x4) }
   Inferred by:
                 support-link #89 from { 89 , 80 } by modus-ponens1
                                         # 57
                                         reductio interest: (mem (@y9
(int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0))
^@y42)
                                         For reductio interest 39 by
i-neg-condit using node 105
                                         For reductio interest 39 by
i-neg-condit using node 214
                                         For reductio interest 39 by
i-neg-condit using node 396
                                         For reductio interest 39 by
i-neg-condit using node 507
                                         For reductio interest 39 by
i-neg-condit using node 1770
                                         For reductio interest 39 by
i-neg-condit using node 1795
                                         For reductio interest 39 by
i-neg-condit using node 1850
                                         For reductio interest 39 by
i-neg-condit using node 1890
                                         For reductio interest 39 by
i-neg-condit using node 1975
                                         For reductio interest 39 by
i-neg-condit using node 1995
                                         This interest is discharged
by node 1968
   # 115
   (mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) (inv F (int ^x18 ^x19) ^x0))    supposition: { ~(equal
(inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
, (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) }
   Inferred by:
                 support-link #110 from { 46 , 86 } by modus-tollens2
   # 117
   ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))    supposition:
{ ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #112 from { 47 , 86 } by modus-tollens2
   This discharges interest 40
                                         # 64
                                         reductio interest: (mem (@y9
(inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
^@y42)
                                         For reductio interest 39 by
i-neg-condit using node 117
                                         This interest is discharged by node 128
   # 128
   (mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) x5)    supposition: { (subset (inv F (int ^x18 ^x19) ^x0)
x5) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv
F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv
F (int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #123 from { 93 , 115 } by modus-ponens2
   This discharges interest 64
   # 129
   ~((mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv
F ^x19 ^x0))) ^@y42) -> (mem (@y9 (inv F (int ^x18 ^x19) ^x0) (int
(inv F ^x18 ^x0) (inv F ^x19 ^x0))) (int (inv F ^x18 ^x0) (inv F ^x19
^x0))))    supposition: { (subset (inv F (int ^x18 ^x19) ^x0) ^@y42)
, ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #124 from { 117 , 128 } by i-neg-condit
   This node is inferred by discharging a link to interest #39
   # 130
   (some x)~((mem x ^@y42) -> (mem x (int (inv F ^x18 ^x0) (inv F ^x19
^x0))))    supposition: { (subset (inv F (int ^x18 ^x19) ^x0) ^@y42)
, ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #125 from { 129 } by EG
   This node is inferred by discharging a link to interest #38
   # 131
   ~(all x)((mem x ^@y42) -> (mem x (int (inv F ^x18 ^x0) (inv F ^x19
^x0))))    supposition: { (subset (inv F (int ^x18 ^x19) ^x0) ^@y42)
, ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #126 from { 130 } by i-neg-ug
   This node is inferred by discharging a link to interest #37
   # 137
   ~(subset x2 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
supposition: { (subset (inv F (int ^x18 ^x19) ^x0) x2) , ~(equal (inv
F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) ,
(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) }
   Inferred by:
                 support-link #132 from { 14 , 131 } by modus-tollens2
   # 166
   ~(subset (inv F (int ^x18 ^x19) ^x0) ^@y41)    supposition: {
(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) , (subset ^@y41 (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) }
   Inferred by:
                 support-link #161 from { 137 , 80 } by reductio
   # 229
   ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) x5) x5)    supposition: {
(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) , ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) , (subset x5 (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) }
   Inferred by:
                 support-link #224 from { 47 , 166 } by modus-tollens2
   This discharges interest 40
   # 311
   ~(subset ^@y43 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19
^x0)) (inv F (int ^x18 ^x19) ^x0)) , (mem (@y9 (inv F (int ^x18 ^x19)
^x0) ^@y43) ^@y43) }
   Inferred by:
                 support-link #306 from { 229 , 79 } by reductio
                                         # 134
                                         reductio interest: (mem (@y9
(inv F (int ^x18 ^x19) ^x0) ^x18) ^@y42)
                                         For reductio interest 39 by
i-neg-condit using node 522
                                         For reductio interest 39 by
i-neg-condit using node 942
                                         For reductio interest 39 by
i-neg-condit using node 1088
                                         For reductio interest 39 by
i-neg-condit using node 1479
                                         For reductio interest 39 by
i-neg-condit using node 1589
                                         For reductio interest 39 by
i-neg-condit using node 1806
                                         Reductio interest generated
by node 1806
                                         This interest is discharged
by node 1753
   # 531
   ~(equal x596 ^x18)    supposition: { ~(equal x596 ^x18) }
   reductio-supposition
   # 532
   ~(subset ^x18 ^@y39)    supposition: { (subset ^@y39 ^x18) ,
~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #524 from { 94 , 531 } by reductio
   This discharges interest 48
   # 535
   ((subset ^x18 ^@y39) -> ~(subset ^@y39 ^x18))    supposition: {
~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #527 from { 532 } by contra-conditionalization
   This node is inferred by discharging a link to interest #45
cycle = 143
   # 540
   (~(subset ^x18 ^@y38) v ~(subset ^@y38 ^x18))    supposition: {
~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #532 from { 535 } by disj-cond
   This node is inferred by discharging a link to interest #44
                                         # 44  reductio interest:
                                            (~(subset ^@y39 ^@y38) v
~(subset ^@y38 ^@y39))
                                         For reductio interest 43 by i-DM
   # 541
   ~((subset ^x18 ^@y38) & (subset ^@y38 ^x18))    supposition: {
~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #533 from { 540 } by i-DM
   This node is inferred by discharging a link to interest #43
                                         # 175
                                         reductio interest: (mem (@y9
^x18 ^x18) ^@y42)
                                         For reductio interest 39 by
i-neg-condit using node 625
                                         For reductio interest 39 by
i-neg-condit using node 751
                                         This interest is discharged by node 741
                                         # 176
                                         reductio interest: (subset ^x18 ^x18)
                                         For reductio interest 21 by
i-neg-condit using node 628
                                         For reductio interest 21 by
i-neg-condit using node 754
                                         For reductio interest 21 by
i-neg-condit using node 1243
                                         For reductio interest 21 by
i-neg-condit using node 1248
                                         For reductio interest 21 by
i-neg-condit using node 1253
                                         This interest is discharged
by nodes (1396 1424)
   # 641
   ~(equal ^x18 x6)    supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #633 from { 18 , 541 } by modus-tollens2
   # 668
   ~(subset ^x18 ^@y106)    supposition: { ~(equal ^@y39 ^x18) ,
(subset ^@y106 ^x18) }
   Inferred by:
                 support-link #660 from { 641 , 94 } by reductio
   This discharges interest 48
cycle = 150
   # 671
   ((subset ^@y38 ^x18) -> ~(subset ^x18 ^@y38))    supposition: {
~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #663 from { 668 } by conditionalization
   This node is inferred by discharging a link to interest #45
   # 740
   ~(subset ^x18 ^x18)    supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #732 from { 671 } by cond-simp1
---------------------------------------------------------------------------
155:    Retrieving #<Node 671> from the inference-queue.  Preference = 0.0833

REASON-FORWARDS-FROM: #<Node 671>
. REASON-FROM-CURRENT-INTEREST-SCHEME: #<Node 671> and #<d-node: 906>
. REASON-FROM-CURRENT-INTEREST-SCHEME: #<Node 671> and #<d-node: 905>
. REASON-FROM-CURRENT-INTEREST-SCHEME: #<Node 671> and #<d-node: 124>
. REASON-FROM-CURRENT-INTEREST-SCHEME: #<Node 671> and #<d-node: 2>
. REASON-FROM-CURRENT-INTEREST-SCHEME: #<Node 671> and #<d-node: 1>

   Constructing instantiated-premise #99
   next premise:  (subset ^@y38 ^x18)
   by modus-ponens2,  basis = (671) with clues ()


   Constructing instantiated-premise #100
   next premise:  ~~(subset ^x18 ^@y38)
   by modus-tollens2,  basis = (671) with clues ()

ADJUST-SUPPORT-FOR-CONSEQUENCES for #<Node 740>
DRAW CONCLUSION: #<Node 740>
   # 740   ~(subset ^x18 ^x18)    supposition: { ~(equal ^@y39 ^x18) }
   Inferred by support-link #732 from { 671 } by cond-simp1



   # 741
   (mem (@y9 ^x18 ^x18) ^x18)    supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #733 from { 46 , 740 } by modus-tollens2
   This discharges interest 175
   # 751
   ~(mem (@y9 ^x18 ^x18) ^x18)    supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #743 from { 47 , 740 } by modus-tollens2
   This discharges interest 40
   # 752
   ~((mem (@y9 ^x18 ^x18) ^x18) -> (mem (@y9 ^x18 ^x18) ^x18))
supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #744 from { 751 , 741 } by i-neg-condit
   This node is inferred by discharging a link to interest #39
   # 753
   (some x)~((mem x ^x18) -> (mem x ^x18))    supposition: { ~(equal
^@y39 ^x18) }
   Inferred by:
                 support-link #745 from { 752 } by EG
   This node is inferred by discharging a link to interest #38
   # 754
   ~(all x)((mem x ^x18) -> (mem x ^x18))    supposition: { ~(equal
^@y39 ^x18) }
   Inferred by:
                 support-link #746 from { 753 } by i-neg-ug
   This node is inferred by discharging a link to interest #37
   # 1396
   (subset ^x18 ^x18)    supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #1388 from { 47 , 741 } by modus-ponens2
   This discharges interest 176
   # 1404
   ~((subset ^x18 ^x18) -> (all x)((mem x ^x18) -> (mem x ^x18)))
supposition: { ~(equal ^@y39 ^x18) }
   Inferred by:
                 support-link #1396 from { 754 , 1396 } by i-neg-condit
   This node is inferred by discharging a link to interest #21
   # 1405
   (equal ^@y39 ^x18)
   Inferred by:
                 support-link #1397 from { 1404 , 14 } by reductio
   # 1423
   ((subset x4 ^x18) & (subset ^x18 x4))
   Inferred by:
                 support-link #1415 from { 18 , 1405 } by modus-ponens2
   # 1424
   (subset x4 ^x18)
   Inferred by:
                 support-link #1416 from { 1423 } by simp
   This discharges interests (176 259)
   # 1460
   (subset ^x18 x4)
   Inferred by:
                 support-link #1452 from { 1423 } by simp
   # 1479
   ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) ^x18)    supposition:
{ ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F
(int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1471 from { 1460 , 311 } by reductio
   # 1491
   ~(subset (inv F (int ^x18 ^x19) ^x0) ^x18)    supposition: {
~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19
^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int
^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1483 from { 1460 , 137 } by reductio
   # 1516
   (all x)((mem x x2) -> (mem x ^x18))
   Inferred by:
                 support-link #1508 from { 14 , 1424 } by modus-ponens2
   # 1522
   (all x)((mem x ^x18) -> (mem x x5))
   Inferred by:
                 support-link #1514 from { 14 , 1460 } by modus-ponens2
   # 1527
   ((mem x1346 ^x18) -> (mem x1346 x5))
   Inferred by:
                 support-link #1519 from { 1522 } by UI
   # 1528
   ((mem x1354 x2) -> (mem x1354 ^x18))
   Inferred by:
                 support-link #1520 from { 1516 } by UI
   # 1753
   (mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) (inv F (int ^x18 ^x19)
^x0))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv
F ^x18 ^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F
^x19 ^x0)) (inv F (int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1745 from { 46 , 1491 } by modus-tollens2
   This discharges interest 134
   # 1806
   ~(mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) x2)    supposition: {
~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19
^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int
^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1798 from { 1528 , 1479 } by modus-tollens2
   This discharges interest 40
   # 1813
   ~((mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) (inv F (int ^x18
^x19) ^x0)) -> (mem (@y9 (inv F (int ^x18 ^x19) ^x0) ^x18) ^@y43))
supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19
^x0)) (inv F (int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1805 from { 1806 , 1753 } by i-neg-condit
   This node is inferred by discharging a link to interest #39
   # 1814
   (some x)~((mem x (inv F (int ^x18 ^x19) ^x0)) -> (mem x ^@y43))
supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19
^x0)) (inv F (int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1806 from { 1813 } by EG
   This node is inferred by discharging a link to interest #38
   # 1815
   ~(all x)((mem x (inv F (int ^x18 ^x19) ^x0)) -> (mem x ^@y43))
supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) , (subset (int (inv F ^x18 ^x0) (inv F ^x19
^x0)) (inv F (int ^x18 ^x19) ^x0)) }
   Inferred by:
                 support-link #1807 from { 1814 } by i-neg-ug
   This node is inferred by discharging a link to interest #37
   # 1924
   ~(subset (inv F (int ^x18 ^x19) ^x0) x5)    supposition: { ~(equal
(inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
, (subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) }
   Inferred by:
                 support-link #1916 from { 14 , 1815 } by modus-tollens2
   # 1963
   ~(subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0)
(int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1955 from { 1924 , 1424 } by reductio
   # 1968
   (mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))    supposition:
{ ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F
^x19 ^x0))) }
   Inferred by:
                 support-link #1960 from { 46 , 1963 } by modus-tollens2
   This discharges interest 57
   # 1975
   ~(mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) (inv F (int ^x18 ^x19) ^x0))    supposition: { ~(equal
(inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1967 from { 47 , 1963 } by modus-tollens2
   # 1995
   ~(mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18
^x19) ^x0)) ^x18)    supposition: { ~(equal (inv F (int ^x18 ^x19)
^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1987 from { 1527 , 1975 } by modus-tollens2
   This discharges interest 40
   # 2000
   ~((mem (@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int
^x18 ^x19) ^x0)) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem
(@y9 (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) (inv F (int ^x18 ^x19)
^x0)) ^x18))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0)
(int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1992 from { 1995 , 1968 } by i-neg-condit
   This node is inferred by discharging a link to interest #39
   # 2001
   (some x)~((mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem x
^x18))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int
(inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1993 from { 2000 } by EG
   This node is inferred by discharging a link to interest #38
   # 2002
   ~(all x)((mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem x
^x18))    supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int
(inv F ^x18 ^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1994 from { 2001 } by i-neg-ug
   This node is inferred by discharging a link to interest #37
                                         # 259
                                         reductio interest: (subset
(int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) ^x18)
                                         For reductio interest 21 by
i-neg-condit using node 2002
                                         This interest is discharged
by node 1424
   # 2003
   ~((subset (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)) ^x18) -> (all
x)((mem x (int (inv F ^x18 ^x0) (inv F ^x19 ^x0))) -> (mem x ^x18)))
supposition: { ~(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18
^x0) (inv F ^x19 ^x0))) }
   Inferred by:
                 support-link #1995 from { 2002 , 1424 } by i-neg-condit
   This node is inferred by discharging a link to interest #21
   # 2004
   (equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19 ^x0)))
   Inferred by:
                 support-link #1996 from { 2003 , 14 } by reductio
   This discharges interest 6
   # 2006
   (((maps F ^x0 ^x17) & ((subset ^x18 ^x17) & (subset ^x19 ^x17))) ->
(equal (inv F (int ^x18 ^x19) ^x0) (int (inv F ^x18 ^x0) (inv F ^x19
^x0))))
   Inferred by:
                 support-link #1998 from { 2004 } by conditionalization
   This node is inferred by discharging a link to interest #5
   # 2007
   (all Y)(((maps F ^x0 ^x17) & ((subset ^x18 ^x17) & (subset Y
^x17))) -> (equal (inv F (int ^x18 Y) ^x0) (int (inv F ^x18 ^x0) (inv
F Y ^x0))))
   Inferred by:
                 support-link #1999 from { 2006 } by UG
   This node is inferred by discharging a link to interest #4
   # 2008
   (all X)(all Y)(((maps F ^x0 ^x17) & ((subset X ^x17) & (subset Y
^x17))) -> (equal (inv F (int X Y) ^x0) (int (inv F X ^x0) (inv F Y
^x0))))
   Inferred by:
                 support-link #2000 from { 2007 } by UG
   This node is inferred by discharging a link to interest #3
   # 2009
   (all B)(all X)(all Y)(((maps F ^x0 B) & ((subset X B) & (subset Y
B))) -> (equal (inv F (int X Y) ^x0) (int (inv F X ^x0) (inv F Y
^x0))))
   Inferred by:
                 support-link #2001 from { 2008 } by UG
   This node is inferred by discharging a link to interest #2
   # 2010
   (all A)(all B)(all X)(all Y)(((maps F A B) & ((subset X B) &
(subset Y B))) -> (equal (inv F (int X Y) A) (int (inv F X A) (inv F
Y A))))
   Inferred by:
                 support-link #2002 from { 2009 } by UG
   This node is inferred by discharging a link to interest #1
============================================================


|#

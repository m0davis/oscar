(analyze-probability-structure
 :name "ps-2-working"
 :constants '(r s)
 :subsets '(H F A) ; weirdly not-so-sensitive to ordering bug
 :probability-constraints '((prob(H / (F & A)) = r)
                            (prob(H / (F & ~A)) = s))
 )

(find-expectable-values
 :ps ps-2-working
 :args '((r = 0.5) (s = 0.9))
 :probability-queries '(prob(H / F))
 )

(analyze-probability-structure
 :name "ps-2"
 :constants '(r s)
 :subsets '(H F P) ; highly-sensitive to ordering bug
 :probability-constraints '((prob(H / (X & F)) = r)
                            (prob(H / (X & ~F)) = s))
 )

(find-expectable-values
 :ps ps-2 
 :args '((r = 0.5) (s = 0.9))
 :probability-queries '(prob(P / H))
 )

(analyze-probability-structure
 :name "ps-2"
 :constants '(a b)
 :subsets '(U F P) ; highly-sensitive to ordering bug
 :probability-constraints '((prob(P / (U & F)) = a)
                            (prob(P / (U & ~F)) = b))
 )

(find-expectable-values
 :ps ps-2 
 :args '((a = 0.5) (b = 0.9))
 :probability-queries '(prob(P / U))
 )

(analyze-probability-structure
 :name "ps-3"
 :constants '(a b c)
 :subsets '(U F P G)
 :probability-constraints '((prob(P / (U & F & G)) = a)
                            (prob(P / (U & ~F & G)) = b)
                            (prob(P / (U & F & ~G)) = c))
 )

(find-expectable-values
 :args '((a = 0.5) (b = 0.1) (c = 0.9))
 :ps ps-3 
 :probability-queries '(prob(P / U)
                            prob(P / (U & (F v G))))
 )

; coin flipping
 (find-expectable-values
  :args '((a = .9) (b = .7))
  :subsets '(P R S H)
  :probability-constraints '((prob(H / (R & S)) = a)
                             (prob(H / (P & S)) = b))
  :probability-queries '(prob(H / S))
  )

 (find-expectable-values
  :args '((r = .9) (s = .7))
  :subsets '(A B F G Z)
  :probability-constraints '((prob(F / (A & Z)) = r)
                             (prob(G / (B & Z)) = r)
                             (prob(~F / (A & ~Z)) = s)
                             (prob(~G / (B & ~Z)) = s))
  :probability-queries '(prob(Z / (F & ~G & A & B)))
  )


 (find-expectable-values
  :args '((r = .9) (s = .7))
  :subsets '(A B F G Z)
  :probability-constraints '((prob(F / (A & Z)) = r)
                             (prob(G / (B & Z)) = r)
                             (prob(~F / (A & ~Z)) = s)
                             (prob(~G / (B & ~Z)) = s))
  :probability-queries '(prob(Z / (F & ~G & A & B)))
  )



 (find-expectable-values
  :args '((r = .9) (s = .7))
  :subsets '(A B F G Z)
  :probability-constraints '((prob(F / (A & Z)) = r)
                             (prob(G / (B & Z)) = r)
                             (prob(~F / (A & ~Z)) = s)
                             (prob(~G / (B & ~Z)) = s))
  :probability-queries '(prob(Z / (F & ~G & A & B)))
  )

 :independence-queries '((A B F G)
                         ((F & G) (A & B) Z))

 (find-expectable-values
  :ps my-ps
  :args '((r = .9) (s = .9) (u = .8))
  :subsets '(A B F G Z U)
  :constants '(r s u)
  :probability-constraints '((prob(Z / U) = t)
                             (prob(F / (A & Z & U)) = r)
                             (prob(G / (B & Z & U)) = r)
                             (prob(~F / (A & ~Z & U)) = s)
                             (prob(~G / (B & ~Z & U)) = s))
  :probability-queries '(prob(Z / (F & ~G & A & B & U)))
  )

 (analyze-probability-structure
  :name "my-ps"
  :subsets '(A B F G Z U)
  :constants '(r s u)
  :probability-constraints '((prob(Z / U) = u)
                             (prob(F / (A & Z & U)) = r)
                             (prob(G / (B & Z & U)) = r)
                             (prob(~F / (A & ~Z & U)) = s)
                             (prob(~G / (B & ~Z & U)) = s))
  :probability-queries '(prob(Z / (F & ~G & A & B & U)))
  )



 THEIST VS AGNOSTIC


 (analyze-probability-structure
  :name "theist-vs-agnostic"
  (find-expectable-values
   :args '((r = .9) (s = .9))
   :subsets '(A B C D E F G H I J K L U V W)
   :constants '(r s)
   :probability-constraints '((prob(E / A) = r)
                              (prob(I / A) = r)
                              (prob(F / B) = r)
                              (prob(J / B) = r)
                              (prob(G / C) = r)
                              (prob(K / C) = r)
                              (prob(H / D) = r)
                              (prob(L / D) = r)
                              (prob(~E / ~A) = s)
                              (prob(~I / ~A) = s)
                              (prob(~F / ~B) = s)
                              (prob(~J / ~B) = s)
                              (prob(~G / ~C) = s)
                              (prob(~K / ~C) = s)
                              (prob(~H / ~D) = s)
                              (prob(~L / ~D) = s))
   :subset-constraints '((B subset (A intersection (- C)))
                         (F subset (E intersection (- G)))
                         (J subset (I intersection (- K)))
                         (D subset (C intersection (- A)))
                         (H subset (G intersection (- E)))
                         (L subset (K intersection (- I)))
                         (A subset U)
                         (C subset U)
                         (E subset V)
                         (G subset V)
                         (I subset W)
                         (K subset W))
   :probability-queries '(prob(B / ((E & G & ~F & ~H) & J & U)) ; really theist / me agnostic & peer theist
                              prob((A & C) / ((E & G & ~F & ~H) & J & U)) ; really agnostic / me agnostic & peer theist
                              )
   :display t
   )
  )



;doesn't work
 (find-expectable-values
  :args '((r = .9) (s = .9))
  :subsets '(A B C X Y Z U V W) 
  :constants '(r s)
  :probability-constraints '((prob(B / A) = r)
                             (prob(C / A) = r)
                             (prob(Y / X) = r)
                             (prob(Z / X) = r)
                             (prob(~B / ~A) = s)
                             (prob(~C / ~A) = s)
                             (prob(~Y / ~X) = s)
                             (prob(~Z / ~X) = s))
  :probability-queries '(prob((A & ~X) / ((B & ~Y) & (~C & Z) & U)) 
                             prob((A & ~X) / ((B & ~Y) & (C & Z) & U)))
  :subset-constraints '((A subset U)
                        (X subset U)
                        (B subset V)
                        (Y subset V)
                        (C subset W)
                        (Z subset W))
  :display t
  )

 (find-expectable-values
  :args '((r = .9) (s = .9))
  :subsets '(A B C F G X Y Z) 
  :constants '(r s)
  :probability-constraints '((prob(B / (F & A)) = r)
                             (prob(C / (G & A)) = r)
                             (prob(Y / (F & X)) = r)
                             (prob(Z / (G & X)) = r)
                             (prob(~B / (F & ~A)) = s)
                             (prob(~C / (G & ~A)) = s)
                             (prob(~Y / (F & ~X)) = s)
                             (prob(~Z / (G & ~X)) = s))
  :probability-queries '(prob((A & ~X) / (F & G & (B & ~Y) & (~C & Z))) 
                             prob((A & ~X) / (F & G & (B & ~Y) & (C & Z))))
; :subset-constraints '((B subset F)
;                       (Y subset F)
;                       (C subset G)
;                       (Z subset G))
  )

;works -- theist vs atheist
 (find-expectable-values
  :args '((r = .9) (s = .7))
  :subsets '(A B F G Z)
  :probability-constraints '((prob(F / (A & Z)) = r)
                             (prob(G / (B & Z)) = r)
                             (prob(~F / (A & ~Z)) = s)
                             (prob(~G / (B & ~Z)) = s))
  :probability-queries '(prob(Z / (F & ~G & A & B)))
  )


;sleeping beauty
 (find-expectable-values
  :args '((r = .5) (d = .002) (e = .001))
  :subsets '(H B S W)
 ; doesn't work with '(H S B W)
; :constants '(r d e) SOMEHOW DOESN'T WORK IF UNCOMMENTED!
  :probability-constraints '((prob(H / (B & S)) = r)
                             (prob(W / (~H & B & S)) = d)
                             (prob(W / (H & B & S)) = e))
  :probability-queries '(prob(H / (W & B & S)))
  )

;almost working beauty
 (find-expectable-values
  :args '((r = 0.5) (x = .9)) ; doesn't work if x = 1
  :subsets '(H S W D)
 ; H=Heads, S=Scenario, W=remembers having been Woken and told it's monday, D=tuesDay
  :constants '(r x)
  :probability-constraints '((prob(((W & H) v (~W & ~H)) / (D & S)) = x)
                             (prob(~W / (~D & S)) = x)
                             (prob(H / S) = r))
  :probability-queries '(prob(H / (~W & S)))
  )

;differently-not-working beauty
 (find-expectable-values
  :args '((r = 0.5))
  :constants '(r)
  :subsets '(H S M D)
  :probability-constraints '((prob(H / S) = r))
  :subset-constraints '((((M intersection (- H)) union ((- M) intersection H)) subset (D intersection S))
                        ((- M) subset ((- D) intersection S)))
  :probability-queries '(prob(H / (~M & S)))
  )

;wtf, why doesn't this work??
 (find-expectable-values
  :args '((r = 0.5))
  :subsets '(H M S)
  :probability-constraints '((prob(H / S) = r)
                             (prob(M / S) = 1)) ; change 1 to r and it works
  :probability-queries '(prob(H / S))
  )

;works but useless
 (find-expectable-values
  :args '((r = 0.5))
  :subsets '(H M S)
  :probability-constraints '((prob(H / S) = r)) ; change 1 to r and it works
  :subset-constraints '((M subset S))
  :probability-queries '(prob(H / S))
  )


;redish, bluish
 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A B C X Y Z)
  :probability-constraints '((prob(B / A) = r)
                             (prob(C / A) = r)
                             (prob(Y / X) = r)
                             (prob(Z / X) = r)
                             (prob(~B / ~A) = r)
                             (prob(~C / ~A) = r)
                             (prob(~Y / ~X) = r)
                             (prob(~Z / ~X) = r))
  :probability-queries '(prob((A & X) / (B & Y & C & ~Z)))
  )

;doesn't work without adding "D" (see below)
 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A B C)
  :probability-constraints '((prob(B / A) = r)
                             (prob(C / A) = r)
                             (prob(~B / ~A) = r)
                             (prob(~C / ~A) = r))
  :probability-queries '(prob(A / (B & ~C)))
  )

; added "D"
 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A B C)
  :probability-constraints '((prob(B / (A & D)) = r)
                             (prob(C / (A & D)) = r)
                             (prob(~B / (~A & D)) = r)
                             (prob(~C / (~A & D)) = r))
  :probability-queries '(prob(A / (B & ~C & D)))
  )

;redish, bluish, adding "D" (tried adding "E" also, nothing worked)
 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A B C X Y Z D E)
  :probability-constraints '((prob(B / (A & D)) = r)
                             (prob(C / (A & D)) = r)
                             (prob(Y / (X & D)) = r)
                             (prob(Z / (X & D)) = r)
                             (prob(~B / (~A & E)) = r)
                             (prob(~C / (~A & E)) = r)
                             (prob(~Y / (~X & E)) = r)
                             (prob(~Z / (~X & E)) = r))
  :probability-queries '(prob((A & X) / (B & Y & C & ~Z)))
  )

;redish, bluish, different strategy
 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A P B H)
 ; A(prop) I (dis)believe [proposition]
 ; B(prop) Peer (dis)believes [proposition]
 ; P(prop) [proposition] is bound to "God exists."
 ; H(prop) [proposition] is (not) the TRUTH
 
  :probability-constraints '((prob(A / (P & H)) = r)
                             (prob(~A / (P & ~H)) = r)
                             (prob(B / (P & H)) = r)
                             (prob(~B / (P & ~H)) = r))
  :probability-queries '(prob(H / (P & A & ~B)))
  )

 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A P B H)
 ; A(prop) I (dis)believe [proposition]
 ; B(prop) Peer (dis)believes [proposition]
 ; P(prop) [proposition] is bound to "God exists."
 ; H(prop) [proposition] is (not) the TRUTH
 
  :constraints '((prob(A / (P & H)) = r)
                 (prob(~A / (P & ~H)) = r)
                 (prob(B / (P & H)) = r)
                 (prob(~B / (P & ~H)) = r))
  :probability-queries '(prob(H / (P & A & ~B)))
  )

 (find-expectable-values
  :args '((r = .9))
  :constants '(r)
  :subsets '(A P B H)
 ; A(prop1) I (dis)believe [proposition]
 ; B(prop1) Peer (dis)believes [proposition]
 ; C(prop2) I (dis)believe [proposition]
 ; D(prop2) Peer (dis)believes [proposition]
 ; E(prop1,prop2) = A(prop1)&B(prop2)
 ; P(prop1) [proposition] is bound to "God exists."
 ; P(prop2) [proposition] is bound to "God exists."
 ; H(prop1) [proposition] is (not) the TRUTH
 ; H(prop2) [proposition] is (not) the TRUTH
 
  :constraints '((e = ab))
  (prob(A / (P & H)) = r)
  (prob(~A / (P & ~H)) = r)
  (prob(B / (P & H)) = r)
  (prob(~B / (P & ~H)) = r))
 :probability-queries '(prob(H / (P & A & ~B)))
 )






;
;        BP = (- (+ (* R HP) (/ (- (+ AP HP) (+ (* R HP) (* R HP))) (- 1 R)) (* R HP))
;                (+ HP (/ (* (- (+ HP AP) (+ (* R HP) (* R HP))) R) (- 1 R))))
;        BHP = (* R HP)
;        P = (/ (- (+ AP HP) (+ (* R HP) (* R HP))) (- 1 R))
;        AHP = (* R HP)
;
;
;        BP = (((2RHP) + ((P(A + H) - P(2RH)) / (1 - R))) - 
;                (HP + ((((HP + AP) - (2RHP)) * R) / (1 - R))))
;        BHP = (* R HP)
;        P = (/ (- (+ AP HP) (+ (* R HP) (* R HP))) (- 1 R))
;        AHP = (* R HP)




(find-expectable-values
 :args '((r = .9))
 :constants '(r)
 :subsets '(P F B Z) 
; somehow doesn't work if it's (P F Z B) ??!!
; somehow doesn't work if it's (B F P Z) ??!!
 ;'(P B F Z) also works
 ;'(B P F Z) also works
 :probability-constraints '((prob(F / (P & Z)) = r)
                            (prob(~F / (P & ~Z)) = r)
                            (prob(B / (P & Z)) = r)
                            (prob(~B / (P & ~Z)) = r))
 :probability-queries '(prob(Z / (F & ~B & P)))
 )

(find-expectable-values
 :args '((r = .9))
 :constants '(r)
 :subsets '(A F G Z)
 :probability-constraints '((prob(F / (A & Z)) = r)
                            (prob(~F / (A & ~Z)) = r)
                            (prob(G / (A & Z)) = r)
                            (prob(~G / (A & ~Z)) = r))
 :probability-queries '(prob(Z / (F & ~G & A)))
 )

(find-expectable-values
 :args '((r = .9))
 :subsets '(A B F G Z)
 :probability-constraints '((prob(F / (A & Z)) = r)
                            (prob(~F / (A & ~Z)) = r)
                            (prob(G / (B & Z)) = r)
                            (prob(~G / (B & ~Z)) = r))
 :probability-queries '(prob(Z / (F & ~G & A & B)))
 )

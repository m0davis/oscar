
;(trace-on)
;(display-on)
;(proof-on)
;(logic-on)
;(reductio-on)
;(log-on)
;(IQ-on)
;(graph-log-on)
;(test 757)

(test)

(so 1)
(so 2)
(so 3)
(so 4)
(so 5)
(so 6)
(so 7)
(so 8)
(so 9)
(so 10)
(so 11)
(so 12)
(so 13)
(so 14)

(p-test)

(find-expectable-values
 :args '((a = .5) (b = .5) (c = .5) (d = .5) (bc = .25) (bd = .25) (r = .9) (v = .9) (s = .9))
 :subsets '(A B C D)
 :probability-constraints '((prob(A / B) = r)
			    (prob(A / (B & C)) = s)
			    (prob(A / (B & D)) = v))
 :probability-queries '(prob(A / C)
			    prob(A / (B & (C & D))))
 :independence-queries '(((B & C) (B & D) (A & B)) ((B & C) (B & D) (~A & B))))

(find-expectable-values
 :args '((a = 0.37) (b = 0.42) (ab = 0.16) (c = 0.55) (d = 0.53) (r1 = 0.6) (r2 = 0.55) (s1 = 0.45) (s2 = 0.48))
 :subsets '(A B C D)
 :constants '(a b c d ab r1 s1 r2 s2)
 :probability-constraints '((prob(A / C) = r1)
			    (prob(A / D) = s1)
			    (prob(B / C) = r2)
			    (prob(B / D) = s2))
 :probability-queries '(prob(A / (C & D))
			    prob(B / (C & D)))
 :independence-queries '((C D A) (C D (U & ~A)) (C D B) (C D (U & ~B))))

(analyze-probability-structure
 :name "my-ps"
 :subsets '(A B C D)
 :constants '(a b c d ab r1 s1 r2 s2)
 :probability-constraints '((prob(A / C) = r1)
			    (prob(A / D) = s1)
			    (prob(B / C) = r2)
			    (prob(B / D) = s2))
 :probability-queries '(prob(A / (C & D))
			    prob(B / (C & D)))
 :independence-queries '((C D A) (C D (U & ~A)) (C D B) (C D (U & ~B))))

;;FAILING (does not halt)
#|
(find-expectable-values
 :ps my-ps
 :args '((a = 0.37) (b = 0.42) (ab = 0.16) (c = 0.55) (d = 0.53) (r1 = 0.6) (r2 = 0.55) (s1 = 0.45) (s2 = 0.48))
 :subsets '(A B C D)
 :constants '(a b c d ab r1 s1 r2 s2)
 :probability-constraints '((prob(A / C) = r1)
			    (prob(A / D) = s1)
			    (prob(B / C) = r2)
			    (prob(B / D) = s2))
 :probability-queries '(prob(A / (C & D))
			    prob(B / (C & D)))
 :independence-queries '((C D A) (C D (U & ~A)) (C D B) (C D (U & ~B))))
|#

(proclaim '(special Y-ps autoY-ps))

(build-probability-structure
 :name "Y-ps"
 :subsets '(A B P)
 :constants '(r s)
 :probability-constraints '((prob(P / A) = r)
			    (prob(P / B) = s))
 :term-definitions '((abp / (* r a s b) p)
		     (ab / (* (- (+ p (* r s)) (+ (* s p) (* r p))) a b) (* p (- 1 p)))
		     (ap * r a)
		     (bp * s b))
 :term-characterizations '((a (* (expt (- 1 r) (- 1 r)) (expt r r) a
				 (expt (- (+ (* r a) 1) (+ a p)) (- r 1)) (expt (- p (* r a)) (- r))))
			   (b (* (expt (- 1 s) (- 1 s)) (expt s s) b
				 (expt (- (+ (* s b) 1) (+ b p)) (- s 1)) (expt (- p (* s b)) (- s))))
			   (p (/ (* (- p (* s b)) (- p (* r a)) (- 1 p))
				 (* (- (+ 1 (* r a)) (+ a p)) (- (+ 1 (* s b)) (+ b p)) p))))
 :sample-args '((r = .5) (s = .5) (a .5) (b .5) (p .5)))

;;FAILING (does not halt)
#|
(find-expectable-values
 :args '((r = .95) (s = .85) (a .250) (b .250) (p .9))
 :ps Y-ps
 :probability-queries '(prob(P / (A & B))
			    prob(P / U)
			    prob(A / U)
			    prob(B / U)
			    prob(B / P)
			    prob(A / P)
			    prob((A & B) / P)
			    prob(A / (U & ~P))
			    prob(B / (U & ~P))
			    prob((A & B) / (U & ~P)))
 :display t)
|#

(build-probability-structure-automatically
 :name "autoY-ps"
 :subsets '(A B P)
 :constants '(r s)
 :probability-constraints '((prob(P / A) = r)
			    (prob(P / B) = s))
 :sample-args '((r = .5) (s = .5) (a .5) (b .5) (p .5) (ab .25) (ap .25) (bp .25) (abp .125)))

;;FAILING (ABS NIL)
#|
(find-expectable-values
 :args '((r = .95) (s = .85) (a .5) (b .5) (p .5) (ab .25) (ap .25) (bp .25) (abp .125))
 :ps autoY-ps
 :probability-queries '(prob(P / (A & B))
			    prob(P / U)
			    prob(A / U)
			    prob(B / U)
			    prob(B / P)
			    prob(A / P)
			    prob((A & B) / P)
			    prob(A / (U & ~P))
			    prob(B / (U & ~P))
			    prob((A & B) / (U & ~P)))
 :display nil)
|#

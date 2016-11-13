
(def-backwards-reason VACUOUS-CONDITION
  :conclusions "(p -> q)"
  :reason-forwards-premises
  "(define -p (neg p))"
  "-p"
  :variables  p q -p)

					; Suppositional rules

(def-backwards-reason contra-conditionalization
  :conclusions "(p -> q)"
  :condition (or (and (not (u-genp p))
		      (not (conjunctionp (quantifiers-matrix p)))
		      (e-genp q))
		 (and (literal p)
		      (literal q)
		      (or (negationp p) (negationp q))))
  :reason-backwards-premises "~p"
  :discharge "~q"
  :variables  p q)

(def-backwards-reason conditionalization
  :conclusions "(p -> q)"
  :condition (or (u-genp p)
		 (and (literal p) (not (e-genp q)))
		 (conjunctionp (quantifiers-matrix p))
		 (not (e-genp q)))
  :reason-backwards-premises "q"
  :discharge "p"
  :variables  p q)

(setf *backwards-logical-reasons*
      (list adjunction neg-intro i-neg-disj i-neg-condit i-neg-bicondit
	    bicondit-intro disj-cond i-DM conditionalization
	    i-neg-ug i-neg-eg EG UG
	    disj-cond-2
	    contra-conditionalization
					; vacuous-condition
	    ))

;; ======================================================================

#| This forms conclusions of the form (P at t). |#

(def-forwards-reason *PERCEPTION*
  :reason-forwards-premises "(p at time)" (:kind :percept)
  :conclusions "(p at time)"
  :variables p time
  :defeasible? t
  :strength .98
  :description "When information is input, it is defeasibly reasonable to believe it.")

(def-backwards-undercutter *PERCEPTUAL-RELIABILITY*
  :defeatee *perception*
  :reason-forwards-premises
  "((the probability of p given ((I have a percept with content p) & R)) <= s)"
  (:condition (s < 0.99))
  :reason-backwards-premises "(R at time)"
  :variables p time R time0 s
  :defeasible? t
  :description "When perception is unreliable, it is not reasonable to accept its representations.")

(def-forwards-reason *DISCOUNTED-PERCEPTION*
  :reason-forwards-premises
  "((the probability of p given ((I have a percept with content p) & R)) <= s)"
  (:condition (and (projectible R) (0.5 < s) (s < 0.99)))
  "(p at time)"
  (:kind :percept)
  :reason-backwards-premises "(R at time)"
  :conclusions "(p at time)"
  :variables p time R time0 s
  :strength  (2 * (s - 0.5))
  :defeasible? t
  :description "When information is input, it is defeasibly reasonable to believe it.")

(def-backwards-undercutter *PERCEPTUAL-UNRELIABILITY*
  :defeatee *discounted-perception*
  :reason-forwards-premises
  "((the probability of p given ((I have a percept with content p) & A)) <= s*)"
  (:condition (and (projectible A) (s* < s)))
  :reason-backwards-premises "(A at time)"
  :variables p time R A time0 time1 s s*
  :defeasible? t
  :description "When perception is unreliable, it is not reasonable to accept its representations.")

(def-backwards-reason *TEMPORAL-PROJECTION*
  :conclusions	"(p throughout (op time* time))"
  :condition  (and (temporally-projectible p) (numberp time*) (numberp time) (<= time* time)
		   (or (eq op 'open) (eq op 'closed) (eq op 'clopen)))
  :reason-forwards-premises
  "(p at time0)"
  (:condition (time0 < time))
  :variables p time0 time* time op
  :defeasible? T
  :strength  (expt *temporal-reason-decay* (- time time0))
  :description
  "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")

#|
;; The condition does not work, because there could be a later argument proving such a support-link,
;; and the inference would not then be redone.
(def-backwards-reason *TEMPORAL-PROJECTION*
  :conclusions	"(p throughout (op time* time))"
  :reason-forwards-premises
  "(p at time0)"
  (:condition (some #'(lambda (L) (not (eq (support-link-rule L) *temporal-projection*)))
		    (support-links c)))
  :condition  (and (temporally-projectible p) (numberp time*) (numberp time) (<= time* time)
		   (or (eq op 'open) (eq op 'closed) (eq op 'clopen)))
  :variables p time0 time* time op
  :defeasible? T
  :strength  (expt *temporal-reason-decay* (max (abs (- time* time0)) (abs (- time time0))))
  :description
  "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")

(def-backwards-reason *TEMPORAL-PROJECTION*
  :conclusions	"(p throughout (op time* time))"
  :reason-forwards-premises
  "(p at time0)"
  :condition  (and (temporally-projectible p) (numberp time*) (numberp time) (<= time* time)
		   (or (eq op 'open) (eq op 'closed) (eq op 'clopen)))
  :variables p time0 time* time op
  :defeasible? T
  :strength  (expt *temporal-reason-decay* (max (abs (- time* time0)) (abs (- time time0))))
  :description
  "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")

(def-backwards-reason *TEMPORAL-PROJECTION*
  :conclusions	"(p throughout (op time* time))"
  :reason-forwards-premises
  "(p at time0)"
  (:condition (and  (numberp time*) (time0 <= time*)
		    (some #'(lambda (L) (not (eq (support-link-rule L) *temporal-projection*)))
			  (support-links c))))
  :condition  (and (temporally-projectible p) (numberp time*) (numberp time) (<= time* time)
		   (or (eq op 'open) (eq op 'closed) (eq op 'clopen)))
  :variables p time0 time* time op
  :defeasible? T
  :strength  (expt *temporal-reason-decay* (- time time0))
  :description
  "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")
|#

(def-backwards-undercutter *PROBABILISTIC-DEFEAT-FOR-TEMPORAL-PROJECTION*
  :defeatee  *temporal-projection*
  :reason-forwards-premises
  "((the probability of (p at (t + 1)) given (p at t)) = s)"
  (:condition (s < *temporal-decay*))
  :variables  p s time0 time)

(def-backwards-reason *INCOMPATIBLE-COLORS*
  :conclusions "~((the color of x is y) at time)"
  :reason-forwards-premises
  "((the color of x is z) at time)"
  (:condition (not (eq z y)))
  :variables  x y z time)

(def-backwards-reason *INDEXICAL-INCOMPATIBLE-COLORS*
  :conclusions "~(the color of x is y)"
  :reason-forwards-premises
  "(the color of x is z)"
  (:condition (not (eq z y)))
  :variables  x y z time)

(def-forwards-reason *INDEXICAL-PERCEPTION*
  :reason-forwards-premises "(p at time)"
  (:kind :percept)
  :conclusions "p"
  :variables p time
  :strength  (min .98 (expt *temporal-reason-decay* (- *cycle* time)))
  :defeasible? t
  :reason-temporal? t
  :description	"When information is input, it is defeasibly reasonable to believe it.")

(def-backwards-undercutter *PROBABILISTIC-DEFEAT-FOR-INDEXICAL-PERCEPTION*
  :defeatee  *indexical-perception*
  :reason-forwards-premises
  "((the probability of (p at (t + 1)) given (p at t)) = s)"
  (:condition (s < *temporal-decay*))
  :variables  p s time0 time)

(def-backwards-undercutter *INDEXICAL-PERCEPTUAL-RELIABILITY*
  :defeatee *indexical-perception*
  :reason-forwards-premises
  "((the probability of p given ((I have a percept with content p) & R)) <= s)"
  (:condition (and (projectible R) (s < 0.99)))
  :reason-backwards-premises "(R at time)"
  :variables p time R time0 s
  :description "When perception is unreliable, it is not reasonable to accept its representations.")

(def-forwards-reason *DISCOUNTED-INDEXICAL-PERCEPTION*
  :reason-forwards-premises
  "((the probability of p given ((I have a percept with content p) & R)) <= s)"
  (:condition (and (projectible R) (0.5 < s) (s < 0.99)))
  "(p at time)"
  (:kind :percept)
  :reason-backwards-premises "(R at time)"
  :conclusions "p"
  :variables p R time0 time s
  :strength (min (* 2 (s - 0.5)) (expt *temporal-reason-decay* (- *cycle* time)))
  :defeasible? t
  :reason-temporal? t
  :description "When information is input, it is defeasibly reasonable to believe it.")

(def-backwards-undercutter *INDEXICAL-PERCEPTUAL-UNRELIABILITY*
  :defeatee *discounted-indexical-perception*
  :reason-forwards-premises
  "((the probability of p given ((I have a percept with content p) & A)) <= s*)"
  (:condition (and (projectible A) (s* < s)))
  :reason-backwards-premises "(A at time)"
  :variables p time R A time0 time1 s s*
  :description "When perception is unreliable, it is not reasonable to accept its representations.")

(def-backwards-reason *INDEXICAL-INCOMPATIBLE-COLORS*
  :conclusions "~(the color of x is y)"
  :reason-forwards-premises
  "(the color of x is z)"
  (:condition (not (eq z y)))
  :variables  x y z)

(def-backwards-reason *INDEXICAL-TEMPORAL-PROJECTION*
  :conclusions	"p"
  :reason-forwards-premises
  "(p at time0)"
  (:condition (time0 < now))
  :condition  (and (temporally-projectible p) (not (occur 'at p)))
  :variables p time0
  :defeasible? T
  :reason-temporal? T
  :strength  (expt *temporal-reason-decay* (- now time0))
  :description
  "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")

(def-backwards-undercutter *PROBABILISTIC-DEFEAT-FOR-INDEXICAL-TEMPORAL-PROJECTION*
  :defeatee  *indexical-temporal-projection*
  :reason-forwards-premises
  "((the probability of (p at (t + 1)) given (p at t)) = s)"
  (:condition (s < *temporal-decay*))
  :variables  p s time0 time)

(def-forwards-reason *RELIABLE-INFORMANT*
  :reason-forwards-premises
  "(x is a reliable informant)"
  "((x reports that P) at time)"
  :conclusions "(P at time)"
  :variables x P time
  :strength 0.99
  :defeasible? T
  :description "it is reasonable to accept the reports of reliable informants.")

#|  No time reference in the conclusion.
(def-forwards-reason *RELIABLE-INFORMANT*
  :reason-forwards-premises
  "(x is a reliable informant)"
  "((x reports that P) at time)"
  :conclusions "P"
  :variables x P time
  :strength 0.99
  :defeasible? T
  :description "it is reasonable to accept the reports of reliable informants.")
|#

;; ======================================================================
;; UTILITIES USED FOR REASONING ABOUT TIME COMPARISONS

;(def-backwards-reason *INDEXICAL-INCOMPATIBLE-COLORS*
;   :conclusions  "~((the color of x is y) now)"
;    :reason-forwards-premises
;    "((the color of x is w) now)"
;	(:condition (and (is-inference c) (not (equal w y))))
;    :variables x y w
;    :defeasible? nil)

#| Given an interest in (x < y) where x and y are numbers, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason strict-arithmetical-inequality
  :conclusions	"(x < y)"
  :condition  (x < y)
  :variables  x y)

#| Given an interest in (x <= y) where x and y are numbers, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason arithmetical-inequality
  :conclusions	"(x <= y)"
  :condition  (x <= y)
  :variables  x y)

#|
(def-backwards-reason arithmetical-equality
  :conclusions	"(x = y)"
  :condition   (catch 'numbers
		 (cond
		  ((interest-variable x)
		   (let ((p* (list '= (arithmetical-value y) y)))
		     (draw-conclusion
		      p* nil arithmetical-equality nil 1 0 nil)))
		  ((interest-variable y)
		   (let ((p* (list '= (arithmetical-value x) x)))
		     (draw-conclusion
		      p* nil arithmetical-equality nil 1 0 nil)))
		  (t
		   (let ((val1 (arithmetical-value x))
			 (val2 (arithmetical-value y)))
		     (when (and val1 val2 (= val1 val2))
		       (let ((p (list '= x y)))
			 (draw-conclusion
			  p nil arithmetical-equality nil 1 0 nil)))))))
  :variables  x y)

(def-backwards-reason arithmetical-nonequality
  :conclusions	"~(x = y)"
  :condition   (catch 'numbers
		 (let ((val1 (arithmetical-value x))
		       (val2 (arithmetical-value y)))
		   (when (and val1 val2 (not (= val1 val2)))
		     (let ((p `(~ (= ,x ,y))))
		       (draw-conclusion
			p nil arithmetical-nonequality nil 1 0 nil))))
		 nil)
  :variables  x y)
|#

(def-backwards-reason arithmetical-equality
  :conclusions	"(x = y)"
  :condition   (x = y)
  :variables  x y)

(def-backwards-reason arithmetical-nonequality
  :conclusions	"~(x = y)"
  :condition   (not (x = y))
  :variables  x y)

#| Given an interest in (x <= now) where x is a number, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason is-past-or-present
  :conclusions	"(x <= now)"
  :condition  (<= x *cycle*)
  :variables  x)

#| Given an interest in (x < now) where x is a number, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason is-past
  :conclusions	"(x < now)"
  :condition  (< x *cycle*)
  :variables  x)

(def-backwards-reason *CAUSAL-IMPLICATION*
  :conclusions	"(Q throughout (op time* time**))"
  :condition (and (numberp time*) (<= time* time**))
  :reason-forwards-premises
  "(A when P is causally sufficient for Q after an interval interval)"
  (:condition (every #'temporally-projectible (conjuncts Q)))
  "(A at time)"
  (:condition
   (or (and (eq op 'clopen) ((time + interval) <= time*) (time* < time**))
       (and (eq op 'closed) ((time + interval) < time*) (time* <= time**))
       (and (eq op 'open) ((time + interval) <= time*) (time* < time**))))
  :reason-backwards-premises
  "(P at time)"
  :variables  A P Q interval time time* time** op
  :strength  (expt *temporal-reason-decay* (- time** time))
  :defeasible?	T)

(def-backwards-reason *CAUSAL-IMPLICATION2*
  :conclusions	"(Q throughout (op time* time**))"
  :condition (and (numberp time*) (<= time* time**))
  :reason-forwards-premises
  "(A when P is causally sufficient for Q after an interval interval)"
  (:condition (every #'temporally-projectible (conjuncts Q)))
  "(P at time-)"
  (:clue? t)
  :reason-backwards-premises
  "(A at time)"
  (:condition
   (and (time- <= time)
	(or (and (eq op 'clopen) ((time + interval) <= time*) (time* < time**))
	    (and (eq op 'closed) ((time + interval) < time*) (time* <= time**))
	    (and (eq op 'open) ((time + interval) <= time*) (time* < time**)))))
  "(P at time)"
  :variables  A P Q interval time time* time** time- op
  :strength  (expt *temporal-reason-decay* (- time** time))
  :defeasible?	T)

(def-backwards-reason *CAUSAL-IMPLICATION+*
  :conclusions	"(Q throughout (op time* time**))"
  :condition (and (numberp time*) (<= time* time**))
  :reason-forwards-premises
  "((R at time*) -> (Q at time*))"
  "(A when P is causally sufficient for R after an interval interval)"
  (:condition (every #'temporally-projectible (conjuncts Q)))
  "(A at time)"
  (:condition
   (or (and (eq op 'clopen) ((time + interval) <= time*) (time* < time**))
       (and (eq op 'closed) ((time + interval) < time*) (time* <= time**))
       (and (eq op 'open) ((time + interval) <= time*) (time* < time**))))
  :reason-backwards-premises
  "(P at time)"
  :variables  A P Q R interval time time* time** op
  :strength  (expt *temporal-reason-decay* (- time** time))
  :defeasible?	T)

(def-backwards-reason *INDEXICAL-CAUSAL-IMPLICATION*
  :conclusions	"Q"
  :reason-forwards-premises
  "(A when P is causally sufficient for Q after an interval interval)"
  (:condition (every #'temporally-projectible (conjuncts Q)))
  "(A at time)"
  (:condition ((time + interval) < now))
  :reason-backwards-premises
  "(P at time)"
  :variables  A P Q interval time
  :defeasible?	T
  :strength  (expt *temporal-reason-decay* (- now time))
  :reason-temporal? T)

(def-backwards-undercutter *CAUSAL-UNDERCUTTER*
  :defeatee *temporal-projection*
  :reason-forwards-premises
					;"(define -p (neg p))" TODO?
					;"(A when Q is causally sufficient for -p after an interval interval)"
  "(A when Q is causally sufficient for (neg p) after an interval interval)"
  "(A at time1)"
  (:condition (and (time0 <= (time1 + interval)) ((time1 + interval) < time)))
  :reason-backwards-premises
  "(Q at time00)"
  (:condition (time00 <= time1))
  :variables  A Q p -p time0 time00 time time* time1 interval op
  :defeasible?	T)

(def-backwards-undercutter *CAUSAL-UNDERCUTTER+*
  :defeatee *temporal-projection*
  :reason-forwards-premises
  "((R at time1) -> ~(p at time1))"
  "(A when Q is causally sufficient for R after an interval interval)"
  "(A at time1)"
  (:condition (and (time0 <= (time1 + interval)) ((time1 + interval) < time)))
  :reason-backwards-premises
  "(Q at time00)"
  (:condition (time00 <= time1))
  :variables  A Q p  R time0 time00 time time* time1 interval op
  :defeasible?	T)

(def-backwards-undercutter *INDEXICAL-CAUSAL-UNDERCUTTER*
  :defeatee *indexical-temporal-projection*
  :reason-forwards-premises
					;"(define -p (neg p))"
					;"(A when Q is causally sufficient for -p after an interval interval)"
  "(A when Q is causally sufficient for (neg p) after an interval interval)"
  "(A at time1)"
  (:condition (and (time0 <= (time1 + interval)) ((time1 + interval) < time)))
  :reason-backwards-premises
  "(Q at time00)"
  (:condition (time00 <= time1))
  :variables  A Q p -p time0 time00 time time* time1 interval op
  :defeasible?	T)

(def-backwards-undercutter *INDEXICAL-CAUSAL-UNDERCUTTER+*
  :defeatee *indexical-temporal-projection*
  :reason-forwards-premises
  "(R -> ~p)"
  "(A when Q is causally sufficient for R after an interval interval)"
  "(A at time1)"
  (:condition (and (time0 <= (time1 + interval)) ((time1 + interval) < now)))
  :reason-backwards-premises
  "(Q at time00)"
  (:condition (time00 <= time1))
  :variables  A Q p R time0 time00 time1 interval
  :defeasible?	T
  :reason-temporal? T)

(def-backwards-undercutter *CAUSAL-UNDERCUTTER-FOR-CAUSAL-IMPLICATION*
  :defeatee *causal-implication*
  :reason-forwards-premises
					;"(define -q (neg q))"
					;"(A* when R is causally sufficient for -q after an interval interval*)"
  "(A* when R is causally sufficient for (neg q) after an interval interval*)"
  "(A* at time1)"
  (:condition (and ((time + interval) <= (time1 + interval*)) ((time1 + interval*) < time**)))
  :reason-backwards-premises
  "(R at time00)"
  (:condition (time00 <= time1))
  :variables  A P Q interval time time* time** op A* R -q interval* time1 time00
  :defeasible?	T)

(def-backwards-undercutter *INDEXICAL-CAUSAL-UNDERCUTTER-FOR-CAUSAL-IMPLICATION*
  :defeatee *indexical-causal-implication*
  :reason-forwards-premises
					;"(define -q (neg q))"
					;"(A* when R is causally sufficient for -q after an interval interval*)"
  "(A* when R is causally sufficient for (neg q) after an interval interval*)"
  "(A* at time1)"
  (:condition (and ((time + interval) <= (time1 + interval*)) ((time1 + interval*) < now)))
  :reason-backwards-premises
  "(R at time00)"
  (:condition (time00 <= time1))
  :variables  A P Q interval time time* op A* R -q interval* time1 time00
  :defeasible?	T)

(def-backwards-reason neg-at-intro
  :conclusions	"~(P at time)"
  :condition (not (negationp P))
  :reason-backwards-premises   "(~P at time)"
  :variables  P time)
#|
(def-backwards-reason neg-at-intro
  :conclusions	"~(P at time)"
  :reason-backwards-premises   "(~P at time)"
  :variables  P time)
|#
(def-backwards-reason neg-at-intro2
  :conclusions	"~(~P at time)"
  :reason-backwards-premises   "(P at time)"
  :variables  P time)

(def-forwards-reason neg-at-elimination
  :reason-forwards-premises   "~(P at time)"
  (:condition (not (negationp P)))
  :conclusions	"(~P at time)"
  :variables  P time)

(def-backwards-reason &-at-intro
  :conclusions	"((P & Q) at time)"
  :reason-backwards-premises   "((P at time) & (Q at time))"
  :variables  P Q time)

(def-forwards-reason &-at-elimination
  :reason-forwards-premises   "((P & Q) at time)"
  :conclusions	"((P at time) & (Q at time))"
  :variables  P Q time)

(def-backwards-reason ETERNAL-TRUTHS
  :conclusions	"(P at time)"
  :reason-backwards-premises  "P"
  :variables   P time)

(def-backwards-reason *COLLISION*
  :conclusions	"((b1 and b2 collide) at time)"
  :reason-backwards-premises
  "(some x)(some y)(((the position of b1 is (x y)) at time) & ((the position of b2 is (x y)) at time))"
  :variables   b1 b2 time)

#| Should this be a degenerate backwards-reason? |#
(def-forwards-reason COLLISION-SYMMETRY
  :reason-forwards-premises   "((B1 and B2 collide) at time)"
  :conclusions	"((B2 and B1 collide) at time)"
  :variables  B1 B2 time)

(def-backwards-reason *NEW-POSITION*
  :conclusions	"((the position of b is (x y)) at time1)"
  :reason-forwards-premises
  "((the position of b is (x0 y0)) at time0)"
  (:condition (time0 < time1))
  :reason-backwards-premises
  "(some vx)(some vy)
		      (& ((the velocity of b is (vx vy)) throughout (clopen time0 time1))
			 (x = (x0 + (vx * (time1 - time0))))
			 (y = (y0 + (vy * (time1 - time0)))))"
  :variables  b time1 x y x0 y0 time0)

(def-forwards-reason *POSITION-INCOMPATIBILITY*
  :conclusions	"~((the position of b is (z w)) at time)"
  :reason-forwards-premises
  "((the position of b is (x y)) at time)"
  "((the position of b is (z w)) at time)"
  (:condition (or (not (x = z)) (not (y = w))))
  (:clue? t)
  :variables  b time x y z w)

#|
(def-backwards-reason *POSITION-INCOMPATIBILITY*
  :conclusions	"~((the position of b is (z w)) at time)"
  :reason-forwards-premises
  "((the position of b is (x y)) at time)"
  (:condition (or (not (x = z)) (not (y = w))))
  :variables  b time x y z w)
|#

(def-backwards-reason *POSITION-INCOMPATIBILITY-1*
  :conclusions	"~((the position of b is (z w)) at time)"
  :reason-forwards-premises
  "((the position of b is (x y)) at time)"
  (:condition (not (x = z)))
  :variables  b time x y z w)

(def-backwards-reason *POSITION-INCOMPATIBILITY-2*
  :conclusions	"~((the position of b is (z w)) at time)"
  :reason-forwards-premises
  "((the position of b is (x y)) at time)"
  (:condition  (not (y = w)))
  :variables  b time x y z w)

(def-backwards-reason *VELOCITY-INCOMPATIBILITY-1*
  :conclusions	"~((the velocity of b is (z w)) at time)"
  :reason-forwards-premises   "((the velocity of b is (x y)) at time)"
  :reason-backwards-premises  "~(x = z)"
  :variables  b time x y z w)

(def-backwards-reason *VELOCITY-INCOMPATIBILITY-2*
  :conclusions	"~((the velocity of b is (z w)) at time)"
  :reason-forwards-premises   "((the velocity of b is (x y)) at time)"
  :reason-backwards-premises  "~(y = w)"
  :variables  b time x y z w)

(def-backwards-reason inequality-transitivity
  :conclusions	"(x < y)"
  :reason-forwards-premises  "(z < y)"
  :reason-backwards-premises  "(x <= z)"
  :variables  x y z)

(def-backwards-reason inequality-transitivity2
  :conclusions	"(x < y)"
  :reason-forwards-premises  "(x < z)"
  :reason-backwards-premises  "(z <= y)"
  :variables  x y z)

(def-backwards-reason PAIR-NONIDENTITY-AT-TIME
  :conclusions	"(~((x y) = (z w)) at time)"
  :reason-backwards-premises  "~((x y) = (z w))"
  :condition  (and (numberp x) (numberp y) (numberp z) (numberp w))
  :variables  b time x y z w )

(def-backwards-reason PAIR-NONIDENTITY
  :conclusions	"~((x y) = (z w))"
  :condition  (and (numberp x) (numberp y) (numberp z) (numberp w)
		   (or (not (eql x z)) (not (eql y w))))
  :variables  x y z w)

(def-forwards-reason not-alive-elimination
  :reason-forwards-premises  "(~(x is alive) at time)"
  :conclusions "((x is dead) at time)"
  :variables   x time
  :description "A person is dead iff he is not alive.")

(def-forwards-reason not-dead-elimination
  :reason-forwards-premises  "(~(x is dead) at time)"
  :conclusions "((x is alive) at time)"
  :variables   x time
  :description "A person is alive iff he is not dead.")

(def-backwards-reason not-alive-introduction
  :conclusions	"(~(x is alive) at time)"
  :reason-backwards-premises  "((x is dead) at time)"
  :variables   x time
  :description "A person is dead iff he is not alive.")

(def-backwards-reason not-dead-introduction
  :conclusions	"(~(x is dead) at time)"
  :reason-backwards-premises  "((x is alive) at time)"
  :variables   x time
  :description "A person is alive iff he is not dead.")

(def-forwards-reason dead-elimination
  :reason-forwards-premises  "((x is dead) at time)"
  :conclusions	"(~(x is alive) at time)"
  :variables   x time
  :description "A person is dead iff he is not alive")

(def-backwards-reason dead-introduction
  :conclusions	"((x is dead) at time)"
  :reason-backwards-premises  "(~(x is alive) at time)"
  :variables   x time
  :description "A person is dead iff he is not alive")

(def-backwards-reason *NEW-POSITION-*
  :conclusions	"((the position of b is (x y)) at time1)"
  :reason-forwards-premises
  "((the position of b is (x0 y0)) at time0)"
  (:condition (time0 < time1))
  :reason-backwards-premises
  "(some vx)(some vy)
		      (& ((the velocity of b is (vx vy)) throughout- (time0 time1))
			 (x = (x0 + (vx * (time1 - time0))))
			 (y = (y0 + (vy * (time1 - time0)))))"
  :variables  b time1 x y x0 y0 time0)

(def-backwards-reason *CAUSAL-IMPLICATION-*
  :conclusions	"(Q throughout- (time* time**))"
  :reason-forwards-premises
  "(A when P is causally sufficient for Q after an interval interval)"
  (:condition (every #'temporally-projectible (conjuncts Q)))
  "(A at time)"
  (:condition ((time + interval) <= time*))
  :reason-backwards-premises
  "(P at time)"
  :condition (<= time* time**)
  :variables  A P Q interval time time* time**
  :strength  (expt *temporal-reason-decay* (- time** time)))

(def-backwards-reason *TEMPORAL-PROJECTION-*
  :conclusions	"(p throughout- (time* time))"
  :reason-forwards-premises
  "(p at time0)"
  (:condition (time0 < time*))
  :condition  (and (temporally-projectible p) (numberp time*) (numberp time) (<= time* time))
  :variables p time0 time* time
  :defeasible? T
  :strength  (- (* 2 (expt *temporal-reason-decay* (- now time0))) 1)
  :description
  "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")

;;============================ relativized quantifiers=================================

(def-forwards-reason RELATIVIZED-UI
  :conclusions P*
  :reason-forwards-premises
  "(all x :type type) P)"
  "(:type object type)"
  "(define P* (subst object x P))"
  :variables  x type object P P*)

;;========================= reason-schemas for planning =================================

(def-backwards-reason PROTOPLAN
  :conclusions "(plan-for plan goal)"
  :condition (interest-variable plan)
  :reason-backwards-premises
  "(protoplan-for plan goal nil nil nil nil nil)"
  :defeasible? t
  :strength .99
  :variables goal plan)

(def-backwards-reason NULL-PLAN
  :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
  :condition (and (interest-variable plan)
		  (not (equal goal 'true))
		  (not (conjunctionp goal))
		  (temporally-projectible goal)
					; (or (null bad-link) (not (eq (causal-link-root bad-link) *start*))
					;       (not (equal goal (causal-link-goal bad-link))))
		  (or nodes nodes-used (not (mem goal goals))))
  :reason-backwards-premises
  "goal"
  (:condition (not (contains-duplicates goals goal)))
  "(define plan (null-plan goal))"
  :variables goal plan goals nodes nodes-used links bad-link)

(def-backwards-reason THE-TRUE
  :conclusions "(protoplan-for plan true goals nodes nodes-used links bad-link)"
  :condition (interest-variable plan)
  :reason-backwards-premises
  "(define plan (null-plan 'true))"
  :variables plan goals nodes nodes-used links bad-link)

(def-backwards-reason SPLIT-CONJUNCTIVE-GOAL
  :conclusions
  "(protoplan-for plan& (goal1 & goal2) goals nodes nodes-used links bad-link)"
  :condition  (and (interest-variable plan&)
		   (temporally-projectible goal1)
		   (temporally-projectible goal2)
		   (or (null bad-link)
		       (and
			(or (equal (causal-link-goal bad-link) goal1)
			    (not (mem goal1 goals)))
			(or (equal (causal-link-goal bad-link) goal2)
			    (not (mem goal2 goals))))))
  :reason-backwards-premises
  "(protoplan-for plan1 goal1 goals nodes nodes-used links bad-link)"
  "(protoplan-for plan2 goal2 goals nodes nodes-used links bad-link)"
  (:condition
   (not (some #'(lambda (L1)
		  (some #'(lambda (L2)
			    (and (eq (causal-link-target L1) (causal-link-target L2))
				 (equal (causal-link-goal L1) (causal-link-goal L2))
				 (not (eq (causal-link-root L1) (causal-link-root L2)))))
			(causal-links plan2)))
	      (causal-links plan1))))
  "(define plan& (merge-plans plan1 plan2 goal1 goal2))"
  (:condition (not (null plan&)))
  :variables  goal1 goal2 plan1 plan2 goals plan& nodes nodes-used links bad-link)

(def-backwards-reason GOAL-REGRESSION
  :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
  :condition (and (not (eq goal 'true))
		  (interest-variable plan) (null nodes-used)
		  (not (conjunctionp goal))
		  (not (mem goal goals))
		  (or (null bad-link)
		      (equal (causal-link-goal bad-link) goal)
		      (not (some
			    #'(lambda (L) (equal (causal-link-goal L) goal))
			    links))))
  :reason-backwards-premises
  "(define new-goals (cons goal goals))"
  "((precondition & action) => goal)"
  (:condition (and (temporally-projectible precondition)
		   (not (mem precondition goals))
		   (not (some #'(lambda (c) (mem c goals)) (conjuncts precondition)))
		   (not (contains-duplicates goals))))
  "(protoplan-for subplan precondition new-goals nodes nodes-used links bad-link)"
  (:condition (not (mem goal goals)))
  "(define plan (extend-plan action goal subplan bad-link))"
  (:condition (not (null plan)))
  :variables precondition action goal plan subplan goals new-goals nodes nodes-used links bad-link)

(def-backwards-reason PROTOPLAN-FOR-GOAL
  :conclusions
  (protoplan-for plan goal goals nil nil nil nil)
  :condition (interest-variable plan)
  :reason-forwards-premises
  "(protoplan-for plan goal goals0 nil nil nil nil)"
  (:condition
   (and  (not (contains-duplicates goals))
	 (every #'(lambda (L) (not (mem (causal-link-goal L) goals))) (causal-links plan))))
  :variables plan goal goals goals0)

#|
(def-backwards-undercutter UNDERMINE-CAUSAL-LINKS
  :defeatee  protoplan
  :reason-backwards-premises
  "(define links
                           (order (if (live-links? plan) (live-causal-links plan) (causal-links plan))
                                  #'(lambda (x y) (> (causal-link-length x plan) (causal-link-length y plan)))))"
  "(plan-undermines-causal-links plan links)"
  :variables plan links)
|#

(def-backwards-undercutter UNDERMINE-CAUSAL-LINKS
  :defeatee  protoplan
  :reason-backwards-premises
  "(define links (if (live-links? plan) (live-causal-links plan) (reverse (causal-links plan))))"
  "(plan-undermines-causal-links plan links)"
  :variables plan links)

(def-backwards-reason PLAN-UNDERMINES-FIRST-CAUSAL-LINK
  :conclusions  "(plan-undermines-causal-links plan links)"
  :condition  (car links)
  :reason-backwards-premises
  "(define first-link (car links))"
  "(plan-undermines-causal-link plan R node first-link e-plan)"
  :variables  plan node links first-link R e-plan)

(def-backwards-reason PLAN-UNDERMINES-ANOTHER-CAUSAL-LINK
  :conclusions  "(plan-undermines-causal-links plan links)"
  :condition  (cdr links)
  :reason-backwards-premises
  "(define rest-of-links (cdr links))"
  "(plan-undermines-causal-links plan rest-of-links)"
  :variables  plan links rest-of-links)

(def-backwards-reason PLAN-UNDERMINES-CAUSAL-LINK
  :conclusions  "(plan-undermines-causal-link plan+ R node link plan)"
  :reason-backwards-premises
  "(define -goal (neg (causal-link-goal link)))"
  "(define node1 (if (not (eq *start* (causal-link-root link))) (causal-link-root link)))"
  "(define node2 (causal-link-target link))"
  "(define before (before-nodes plan+))"
  "(define not-between (not-between plan+))"
  "(embellished-plan-for plan plan+ -goal node1 node2 before not-between)"
  (:condition
   (or (null (fixed-links plan+))
       (some #'(lambda (L) (not (member L (fixed-links plan+)))) (causal-links plan))))
  "(define node (penultimate-node plan))"
  "(define R
                         (let ((u-links (u-links-for-undermining-causal-link node plan plan+)))
                           (when u-links (gen-conjunction (mapcar #'causal-link-goal u-links)))))"
  ;; R is used for CONFRONTATION
  :variables  plan plan+ link -goal node node1 node2 R before not-between)

(def-backwards-reason EMBELLISHED-PROTOPLAN
  :conclusions "(embellished-plan-for plan plan+ -goal node1 node2 before not-between)"
  :condition (interest-variable plan)
  :reason-backwards-premises
  "(embellished-protoplan-for plan plan+ -goal node1 node2 before not-between)"
  :defeasible? t
  :strength .99
  :variables plan plan+ -goal node1 node2 before not-between)

(def-backwards-undercutter UNDERMINE-EMBEDDED-CAUSAL-LINKS
  :defeatee  embellished-protoplan
  :reason-backwards-premises
  "(define links (set-difference (causal-links plan) (causal-links plan+)))"
  "(plan-undermines-causal-links plan links)"
  :variables plan plan+ links)

(def-backwards-reason EMBELLISHED-PROTOPLAN-for-GOAL
  :conclusions  "(embellished-protoplan-for plan plan+ -goal node1 node2 before not-between)"
  :condition  (interest-variable plan)
  :reason-forwards-premises
  "(protoplan-for plan0 -goal goals nil nil nil)"
  (:condition (subplan plan0 plan+))
  "(define p-nodes (penultimate-nodes plan0))"
  (:condition
   (if node1 (subsetp p-nodes
		      (possibly-intermediate-nodes node1 node2 plan+ (plan-steps plan+) before not-between))
     (subsetp p-nodes
	      (possibly-preceding-nodes node2 plan+ (plan-steps plan+) before))))
  "(define new-order
                         (let ((before0 (remove-finish before))
                               (not-between0 (remove-not-between-finish before not-between)))
                           (dolist (L (causal-links plan0))
                             (when (eq (causal-link-target L) *finish*) (push (cons (causal-link-root L) *finish*) before0)))
                           (dolist (penultimate-node p-nodes)
                             (dolist (n (possibly-succeeding-nodes penultimate-node plan+ (plan-steps plan+) before0))
                               (multiple-value-bind
                                 (before-nodes* not-between*)
                                 (add-before *finish* n plan+ before0 not-between0)
                                 (setf before0 before-nodes* not-between0 not-between*))))
                           (list before0 not-between0)))"
  (:condition (not (null new-order)))
  "(define plan
                      (build-plan
                        (plan-steps plan+) -goal (causal-links plan0) (car new-order) (cadr new-order)))"
  :variables  plan plan0 plan+ -goal node node1 node2 p-nodes goals before not-between new-order)

#| order will have *finish* in it.  node2 can be *finish* if node1 is not nil.  As we regress backsards, we
add constraints to before and not-between.  When we get to a null-plan, we have all the constraints.
We move *finish* to the right place at that time.  Then as we walk back up the regression (using extend-
embellished-plan) we move *finish* just as we do using extend-plan, but we also place *finish* as early as
possible, i.e., before all possibly-succeeding-nodes of new-node. |#
(def-backwards-reason EMBEDDED-GOAL-REGRESSION
  :conclusions "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
  :condition (and (not (eq goal 'true)) (interest-variable plan))
  :reason-forwards-premises
  "((& precondition action) => goal)"
  (:condition (temporally-projectible precondition))
  "(define possible-nodes
                      (if node1
                        (possibly-intermediate-nodes node1 node2 plan+ (plan-steps plan+) before not-between)
                        (possibly-preceding-nodes node2 plan+ (plan-steps plan+) before)))"
  (:condition (not (null possible-nodes)))
  "(plan-node new-node action)"
  (:condition (member new-node possible-nodes))
  "(define new-order
(multiple-value-bind
 (before* not-between*)
 (catch 'merge-plans
   (add-befores (if node1 (list (cons node1 new-node) (cons new-node node2))
		  (list (cons new-node node2)))
		before not-between plan+))
 (list before* not-between*)))"
                      (:condition (car new-order))
                      "(define new-before (mem1 new-order))"
                      "(define new-between (mem2 new-order))"
                      :reason-backwards-premises
                      "(embellished-protoplan-for subplan plan+ precondition nil new-node new-before new-between)"
                      "(define plan
(extend-embellished-plan new-node goal subplan plan+))"
                      (:condition (not (null plan)))
                      :variables plan plan+ subplan goal node1 node2 new-node precondition before not-between
                      new-order new-before new-between possible-nodes action)

(def-backwards-reason EMBEDDED-NULL-PLAN
  :conclusions
  "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
  :condition (and (interest-variable plan) (null node1) (not (equal goal 'true)) (not (conjunctionp goal)))
  :reason-backwards-premises
  "goal"
  "(define plan (embedded-null-plan goal plan+ before not-between))"
  (:condition (not (null plan)))
  :variables plan+ goal plan node node1 node2 before not-between)

(def-backwards-reason EMBEDDED-THE-TRUE
  :conclusions "(embellished-protoplan-for plan plan+ true node1 node2 before not-between)"
  :condition (interest-variable plan)
  :reason-backwards-premises
  "(define plan (embedded-null-plan 'true plan+ before not-between))"
  :variables plan+ plan node node1 node2 before not-between)

(def-backwards-reason SPLIT-EMBEDDED-CONJUNCTIVE-GOAL
  :conclusions
  "(embellished-protoplan-for plan& plan+ (goal1 & goal2) node1 node2 before not-between)"
  :condition
  (and (interest-variable plan&) (null node1) (temporally-projectible goal1) (temporally-projectible goal2))
  :reason-backwards-premises
  "(embellished-protoplan-for plan1 plan+ goal1 node1 node2 before not-between)"
  "(define before1 (before-nodes plan1))"
  "(define not-between1 (not-between plan1))"
  "(embellished-protoplan-for plan2 plan+ goal2 node1 node2 before1 not-between1)"
  "(define plan& (merge-embellished-plans plan1 plan2 goal1 goal2))"
  (:condition (not (null plan&)))
  :variables
  plan+ plan& plan1 plan2 nodes goal1 goal2 node1 node2 before not-between before1 not-between1)

					;(def-backwards-undercutter UNDERMINE-EMBEDDED-CAUSAL-LINKS
					;    :defeatee   embellished-proto-plan
					;    :reason-backwards-premises
					;    "(define links (set-difference (causal-links plan) (causal-links subplan)))"
					;    "(plan-undermines-causal-links plan links)"
					;    :variables plan subplan links)

;TODO
;(def-backwards-reason PLAN-NODE-RESULT
;  :conclusions  "(node-result node R Q)"
;  :condition	(interest-variable node)
;  :reason-conclusions-function
;  (let ((conclusions nil))
;    (let ((m (match+ action (plan-node-action node*))))
;      (when m (push (cons `(node-result ,node* ,(match-sublis m R) ,Q) nil) conclusions)))
;    conclusions)
;  :reason-backwards-premises
;  "(=> (& R action) Q)"
;  "(plan-node node*)"
;  :variables	action node node* R Q)

(def-backwards-reason  =>-neg1
  :conclusions  "(P => ~(Q & R))"
  :condition (and (not (interest-variable Q)) (not (interest-variable R)))
  :reason-backwards-premises
  "(define -Q (neg Q))"
  "(P => -Q)"
  :variables  P Q -Q R)

(def-backwards-reason  =>-neg2
  :conclusions  "(P => ~(Q & R))"
  :condition (and (not (interest-variable Q)) (not (interest-variable R)))
  :reason-backwards-premises
  "(define -R (neg R))"
  "(P => -R)"
  :variables  P Q R -R)

(def-backwards-reason  =>-disj1
  :conclusions  "(P => (Q v R))"
  :condition (and (not (interest-variable Q)) (not (interest-variable R)))
  :reason-backwards-premises
  "(P => Q)"
  :variables  P Q R)

(def-backwards-reason  =>-disj2
  :conclusions  "(P => (Q v R))"
  :condition (and (not (interest-variable Q)) (not (interest-variable R)))
  :reason-backwards-premises
  "(P => R)"
  :variables  P Q R)

(def-forwards-reason SIMPLIFY-=>
  :reason-forwards-premises "(P => (Q & R))"
  :conclusions  "(P => Q)" "(P => R)"
  :variables P Q R)

(def-backwards-reason =>-ADJUNCTION
  :conclusions "(P => (Q & R))"
  :reason-backwards-premises  "(P => Q)" "(P => R)"
  :variables P Q R)

(def-backwards-reason =>-TRANSITIVITY
  :conclusions "(P => Q)"
  :reason-forwards-premises  "(R => Q)"
  :reason-backwards-premises  "(P => R)"
  :variables P Q R)

(def-forwards-reason ADD-ORDERING-CONSTRAINTS
  :conclusions
  "(protoplan-for plan goal goals nil nil nil nil)"
  :reason-forwards-premises
  "(plan-undermines-causal-link plan- R node link e-plan)"
  (:clue? t)
  "(protoplan-for plan- goal goals nil nil nil nil)"
  "(define plan (add-not-between node link plan- t))"
  (:condition (not (null plan)))
  :variables  plan plan- node link goal goals R e-plan)

;;================ defeating the defeaters ========================

(def-forwards-reason ADD-EMBEDDED-ORDERING-CONSTRAINTS
  :conclusions "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
  :condition (interest-variable plan)
  :reason-forwards-premises
  "(plan-undermines-causal-link plan- R node link e-plan)"
  (:clue? t)
  "(embellished-protoplan-for plan- plan+ goal node1 node2 before not-between)"
  "(define plan (add-not-between node link plan- nil))"
  (:condition (not (null plan)))
  :variables  plan- plan+ plan goal node1 node2 before not-between R node link e-plan)

(def-forwards-reason REUSE-NODES
  :conclusions
  "(protoplan-for plan goal nil nil nil nil nil)"
  :reason-forwards-premises
  "(plan-undermines-causal-link plan+ R node bad-link e-plan)"
  (:clue? t)
  "(protoplan-for plan+ goal nil nil nil nil nil)"
  (:node node1)
  "(define goal0 (causal-link-goal bad-link))"
  "(protoplan-for plan0 goal0 goals nodes nil links0 link0)"
  (:node node2)
  (:condition (and (subplan plan0 plan+)
		   (member node2 (hypernode-ancestors node1))
		   (some #'(lambda (L)
			     (and (eq (causal-link-target L) *finish*)
				  (eq (causal-link-root L) (causal-link-root bad-link))
				  (equal (causal-link-goal L) goal0)))
			 (causal-links plan0))
					; (goals-used (cons goal0 goals) plan+ bad-link)
		   ))
  (:clue? t)
  "(define new-nodes
                     (cons node (possibly-preceding-nodes node plan+ (plan-steps plan+) (before-nodes plan+))))"
  "(define links (remove bad-link (causal-links plan+)))"
  :reason-backwards-premises
  "(protoplan-for new-plan0 goal0 goals new-nodes nil links bad-link)"
  (:condition
   (and (not (some
              #'(lambda (L) (and (eq (causal-link-target L) *finish*)
                                 (eq (causal-link-root L) (causal-link-root bad-link))))
              (causal-links new-plan0)))
	(some #'(lambda (n) (member n new-nodes)) (plan-steps new-plan0))))
  "(define plan (replace-subplan new-plan0 plan+ bad-link))"
  (:condition (not (null plan)))
  :variables
  plan goal goal0 goals nodes plan+ R node new-nodes
  links bad-link plan0 new-plan0 links0 link0 node1 node2  e-plan)

(def-backwards-reason REUSE-PLANS
  :conclusions
  (protoplan-for plan goal goals nodes nodes-used links bad-link)
  :condition (and (interest-variable plan) (not (null nodes)))
  :reason-forwards-premises
  "(protoplan-for plan goal goals0 nodes0 nodes-used0 links0 bad-link0)"
  (:condition (and (subsetp (plan-steps plan) nodes)
		   (not (member bad-link (causal-links plan)))
		   (not (some
			 #'(lambda (L)
			     (let ((g (causal-link-goal L)))
			       (or (equal g goal) (not (mem g goals)))))
			 (causal-links plan)))
		   (or (not (equal goal (causal-link-goal bad-link)))
		       (mem goal goals)
		       (not (some
			     #'(lambda (L) (and (equal goal (causal-link-goal bad-link))
						(eq (causal-link-root L) (causal-link-root bad-link))
						(eq (causal-link-target L) *finish*)))
			     (causal-links plan))))
		   (or (plan-steps plan)
		       (null bad-link)
		       (not (eq (causal-link-target bad-link) *start*))
		       (not (equal goal (causal-link-goal bad-link))))
		   ))
  :variables plan goal goals nodes nodes-used links bad-link goals0 nodes0 nodes-used0 links0 bad-link0)

#|
(def-backwards-reason REUSE-NODE
  :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
  :condition (and (interest-variable plan) (not (null nodes)) (not (conjunctionp goal)))
  :reason-forwards-premises
  "(=> (& R action) goal)"
  "(plan-node node action)"
  (:condition
   (and (member node nodes)
	(or (null bad-link)
	    (not (equal goal (causal-link-goal bad-link)))
	    (mem goal goals)
	    (not (equal (plan-node-action (causal-link-root bad-link)) action)))
	))
  "(define precondition
                         (let ((m (match+ action (plan-node-action node))))
                           (when m (match-sublis m R))))"
  (:condition (not (null precondition)))
  "(define new-nodes (remove node nodes))"
  "(define new-nodes-used (cons node nodes-used))"
  :reason-backwards-premises
  "(protoplan-for subplan precondition goals new-nodes new-nodes-used links bad-link)"
  "(define plan (extend-plan-with-node node goal subplan bad-link))"
  (:condition (not (null plan)))
  :variables R action precondition plan goal goals nodes node new-nodes
  subplan nodes-used new-nodes-used links bad-link)
|#

(def-backwards-reason REUSE-NODE
  :conclusions "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
  :condition (and (interest-variable plan) (not (null nodes)) (not (conjunctionp goal)))
  :reason-forwards-premises
  "(=> (& R action) goal)"
  "(plan-node node action)"
  (:condition
   (and (member node nodes)
	(or (null bad-link)
	    (not (equal goal (causal-link-goal bad-link)))
	    (mem goal goals)
	    (not (equal (plan-node-action (causal-link-root bad-link)) action)))
	))
  "(define new-nodes (remove node nodes))"
  "(define new-nodes-used (cons node nodes-used))"
  :reason-backwards-premises
  "(protoplan-for subplan R goals new-nodes new-nodes-used links bad-link)"
  "(define plan (extend-plan-with-node node goal subplan bad-link))"
  (:condition (not (null plan)))
  :variables R action plan goal goals nodes node new-nodes
  subplan nodes-used new-nodes-used links bad-link)

(def-forwards-reason CONFRONTATION
  :conclusions
  "(protoplan-for plan goal goals nodes nodes-used links bad-link)"
  :reason-forwards-premises
  "(plan-undermines-causal-link plan- R node link e-plan)"
  (:condition (not (null R)))
  (:clue? t)
  "(protoplan-for plan- goal goals nodes nodes-used links bad-link)"
  :reason-backwards-premises
  "(define -R (neg R))"
  "(protoplan-for repair-plan -R nil nodes nodes-used links bad-link)"
  "(define plan (make-confrontation-plan repair-plan plan- -R node links e-plan))"
  (:condition (not (null plan)))
  :variables  plan plan- R -R repair-plan node link goal goals nodes nodes-used links bad-link e-plan)

(def-forwards-reason EMBEDDED-CONFRONTATION
  :conclusions "(embellished-protoplan-for plan plan+ goal node1 node2 before not-between)"
  :reason-forwards-premises
  "(plan-undermines-causal-link plan+ R node link   e-plan)"
  (:condition (not (null R)))
  (:clue? t)
  "(embellished-protoplan-for subplan plan+ goal node1 node2 before not-between)"
  :reason-backwards-premises
  "(define -R (neg R))"
  "(embellished-plan-for repair-plan plan+ -R node1* node2* new-before new-not-between)"
  "(define plan (make-confrontation-plan repair-plan subplan -R node (list link)  e-plan))"
  (:condition (not (null plan)))
  :variables  plan plan+ goal node1 node2 before not-between R node link subplan precondition
  new-node new-before new-not-between -R node1* node2* repair-plan  e-plan)

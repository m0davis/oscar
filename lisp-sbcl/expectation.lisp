
#|						FIND-EXPECTABLE-VALUES

version of 8/7/07

This file defines the LISP function FIND-EXPECTABLE-VALUES, which attempts to find the numerical values for
the expectable values of probabilities. You must first load the files "oscar-tools.lisp", "algebraic-simplification.lisp",
and "analyze-probability-structure.lisp". This will be done automatically upon loading the present file, but you must edit
the pathnames (above) to indicate where the files are on your computer.

Here is an example of the use of FIND-EXPECTABLE-VALUES:

(find-expectable-values
  :args '((a = .5) (b = .5) (c = .5) (d = .5) (bc = .25) (bd = .25) (r = .9) (v = .9) (s = .9))
  :subsets '(A B C D)
  :probability-constraints '((prob(A / B) = r)
                                               (prob(A / (B & C)) = s)
                                               (prob(A / (B & D)) = v))
  :probability-queries '(prob(A / C)
                                        prob(A / (B & (C & D))))
  :independence-queries '(((B & C) (B & D) (A & B)) ((B & C) (B & D) (~A & B)))
  )

The general form of a function call is:

(FIND-EXPECTABLE-VALUES
  :args a list of assignments of values to variables
  :ps a probability structure
  :constraints a list of linear equations in prefix notation
  :probability-constraints a list of probability specifications
  :subset-constraints a list of subset relations
  :probability-queries a list of probability formulas
  :independence-queries a list of triples of formulas
  :sample-args a list of assignments to variables used as the starting point for the search
  :display-results? t or nil (t by default)
  :display t or nil (nil by default)
  :shallow-display t or nil (nil by default)
  ;; the following arguments are usually left unspecified by the user:
  :ps a probability structure (usually left blank, to be computed by the function)
  :name a string naming the probability structure constructed
  :iterations an integer (default value 2)
  :dif a number less than 1
  :dif2 a number less than 1
  :split-dif a number less than 1
  :truncate an integer (default value is 4)
  :depth an integer set by the program
  :top-level t or nil (set by the program)

Note that all the displays work best if you set your LISP to display S-expressions in lower case.

The first six arguments are analogous to the fist six arguments used by ANALYZE-PROBABILITY-STRUCTURE:

subsets is a list of atoms (best typed in upper case) which symbolize the subsets of U that
are under considerations. Throughout, if for example, the atoms are A, B, C, D, then a is the cardinality
of A, b is the cardinality of B, ab is the cardinality of the intersection of A and B, abc is the cardinality
of A interesection B intersection C, and so forth. These lower-case expressions make up the list of
variables. FIND-EXPECTABLE-VALUES attempts to characterize the expectable values for
all the variables. The constraints (below) may add variables like r, s, and v used in the constraints.

args is a list variables that are held constant and their constant values. An example
is '((a = .5) (b = .5) (c = .5) (d = .5) (bc = .25) (bd = .25) (r = .9) (v = .9) (s = .9)).

ps is an optional argument. If supplied, FIND-EXPECTABLE-VALUES uses ps. Specifically, it only looks for
the expectable values of the terms that do not have definitions in ps. Those that do have definitions are
evaluated using those definitions. If ps is not supplied, a new probability structure is constructed just
as it would be constructed by ANALYZE-PROBABILITY-STRUCTURE except that it has no term-definitions.
*ps* is bound to the probability-structure, whether it is supplied or newly constructed.

constraints is a list of linear equations (in prefix form) like '((ab = (* r b)) (abc = (* s bc))).
FIND-EXPECTABLE-VALUES is trying to find the expectable values relative to the set
of constraints.

subset-constraints is a list of constraints like '((D subset C) (A = (B union C)) (E = (U - A))), and so forth.
"union", "intersection", and "-" (in the form "(- P)") can be used in these constraints. A preprocessor translates
these into normal constraints which are hten used in finding the expectable values.

probability-constraints is a list of specifications of probabilities like '((prob((F & H) / (G v ~H)) = r) (prob(A / B) = s)).
Note that there must be white space around "/" and the logical connectives other than "~".A preprocessor translates these into
normal constraints which are hten used in finding the expectable values.

Note that if the subset-constraints and probability-constraints create simultaneous equations regarding some of
the variables, the preprocessor may not correctly translate them into ordinary constraints. In that case it is best
to do the translation by hand and enter all the constraints as ordinary constraints.

probability-queries is a list of probability formulas like '(prob(A / (B & C)) prob(A / B) prob(A / (B & (C & D)))) for which
FIND-EXPECTABLE-VALUES will attempt to find analytic characterizations.

independence-queries is a list of triples of formulas like '((A B C) (A C B) (A C U) (A D (B & C))). For each triple,
FIND-EXPECTABLE-VALUES will attempt to determine whether the first two formulas are statistically
independent relative to the third.

sample-args is a list of assignment of values to the variables that are not held constant. The function works by
employing a hill-climbing algorithm, and this tells it where to start the search. If no value is specified, a default
value is used, and that usually works. However, the search will be faster if you can use a starting point that is closer
to the final result. One way to do this is to solve related problems with stipulated values only a little different from
the current problem, and use the values found in that problem as the starting point for the new search. This is
fascillitated by the fact that the constant *args* is bound to the list of values found when FIND-EXPECTABLE-VALUES
is run. For the next problem, you can then list *args* as the value of sample-args.
    The numerical problems being solved here are difficult. Generally, neither Mathematica nor Maple can solve them.
The difficulty is that if the values are perturbed very much, the functions we are using for hill-climbing may return
complex values. FIND-EXPECTABLE-VALUES does a pretty good job of solving these problems, but sometimes it
fails. When it fails, one can often solve another problem with values closer to the stipulated values, and then use *args*
as the starting point for a new search.

display-results? is t or nil (the default value is t). If it is t then FIND-EXPECTABLE-VALUES prints out its results in a readable form. If
it is nil, FIND-EXPECTABLE-VALUES merely returns the results in a list like:
   ((a = 0.5) (b = 0.5) (c = 0.5) (d = 0.5) (bc = 0.25) (bd = 0.25) (r = 0.9) (s = 0.9) (v = 0.9) (ac 0.2500000209315223)
     (abcd 0.11250195271056596) (cd 0.2500021760119019) (acd 0.12500195635419192) (bcd 0.12500197828431903)
     (ad 0.2499999544567576))

display is t or nil (the default value is nil). If it is t, FIND-EXPECTABLE-VALUES displays the progress of the search.

shallow-display is to or nil (the default value is nil). If it is t, FIND-EXPECTABLE-VALUES displays the approximations
found during the search.

ps The first six arguments are used to compute the system of simultaneous equations to be solved. These define
a probability structure. If the same probability structure is to be used repeatedly, one can use BUILD-PROBABILITY-
STRUCTURE to define it, naming it with name, and then call that in FIND-EXPECTABLE-VALUES. This will sometimes
save a little time, but not a lot.

name is a string naming ps. The default value is "*ps*". If one is using the same probability structure repeatedly, one
can let FIND-EXPECTABLE-VALUES define it the first time, naming it *ps*, and then call it subsequently by that name.
Or one can stipulate a different name, if that is convenient.

dif  is a number less than 1 (the default value is .0000001) that specifies the desired accuracy of the search.
FIND-EXPECTABLE-VALUES is solving a set of equations each having the form "x = 1". dif determines how close
to 1 we must get before the search terminates. If display-results? is t, FIND-EXPECTABLE-VALUES displays the
accuracy of the results at the end by printing something like:
The accuracy of the results is:(0.9999950420010103 0.9999991703500247 0.9999974817445123
      1.0000061718480118 1.00006684644602 1.0000009508648084)

dif2 is another number less than 1 (the default value is .0001). This determines the accuracy of intermediate calculations
used during the hilll-climbing. There is rarely any reason to change the default value.

split-dif is a number less than 1 (the default value is .00001). This determines when an approximation is so close
to the given values that FIND-EXPECTABLE-VALUES aborts the search for closer approximations.

iterations is an integer (the default value is 2). The search is accelerated significantly by first solving the problem
setting dif to 1/100 of the specified value of dif, using that result as the start of a new search with dif set at 1/10
the specified value, and finally using that result as the start of a new search with dif given its specified value. If one
increases the value of dif, it may be desirable to increase iterations.

truncate is an integer (default value is 4) specifying how many decimal places are used ti displaying the results.

Here is an example of FIND-EXPECTABLE-VALUES:

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
  :independence-queries '((C D A) (C D (U & ~A)) (C D B) (C D (U & ~B)))
  )

Find expectable values:
   :args ((a = 0.37) (b = 0.42) (ab = 0.16) (c = 0.55) (d = 0.53) (r1 = 0.6) (r2 = 0.55) (s1 = 0.45) (s2 = 0.48))
   :probability-structure *ps*
   :subsets (A B C D)
   :constants (s2 s1 r2 r1 d c ab b a)
   :constraints
        bd = (* s2 d)
        bc = (* r2 c)
        ad = (* s1 d)
        ac = (* r1 c)
   :probability-constraints
        prob(A / C) = r1
        prob(A / D) = s1
        prob(B / C) = r2
        prob(B / D) = s2
----------
The following expectable values were found:
     prob(A / (C & D)) = 0.662
     prob(B / (C & D)) = 0.5874
 ----------
C and D are INDEPENDENT relative to A within 0.01
C and D are not independent relative to (U & ~A) within 0.01
C and D are not independent relative to B within 0.01
C and D are not independent relative to (U & ~B) within 0.01
========================================================
The accuracy of the results is:(0.9999932626119115 0.9999245324699282 0.9999850997494993 0.9999942224298255 1.0000060784819058 1.0001144424566626)
Starting from
   :sample-args ((s2 = 0.5) (s1 = 0.5) (r2 = 0.5) (r1 = 0.5) (d = 0.5) (c = 0.5) (ab = 0.25) (b = 0.5) (a = 0.5) (abcd 0.0625) (cd 0.25) (abc 0.125)
                 (acd 0.125) (bcd 0.125) (abd 0.125))
the computation took 8.368 sec

((s2 = 0.48) (s1 = 0.45) (r2 = 0.55) (r1 = 0.6) (d = 0.53) (c = 0.55) (ab = 0.16) (b = 0.42) (a = 0.37) (abcd 0.11004629743878928)
 (cd 0.3234535975519361) (abc 0.15446231039854152) (acd 0.21412211626960684) (bcd 0.18999149561164613) (abd 0.11399149766412064))

The computation can be accelerated by first running:

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
  :independence-queries '((C D A) (C D (U & ~A)) (C D B) (C D (U & ~B)))
  )

This finds definitions for the expectable values of all but abc and abd, and records them in the probability structure my-ps.
We can then execute:

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
  :independence-queries '((C D A) (C D (U & ~A)) (C D B) (C D (U & ~B)))
  )

which returns values for just abc and abd, and evaluates the queried probabilities more quickly:

Find expectable values:
   :args ((a = 0.37) (b = 0.42) (ab = 0.16) (c = 0.55) (d = 0.53) (r1 = 0.6) (r2 = 0.55) (s1 = 0.45) (s2 = 0.48))
   :probability-structure ps7565
   :subsets (A B C D)
   :constants (a b c d ab r1 s1 r2 s2)
   :constraints
        bd = (* s2 d)
        bc = (* r2 c)
        ad = (* s1 d)
        ac = (* r1 c)
   :probability-constraints
        prob(A / C) = r1
        prob(A / D) = s1
        prob(B / C) = r2
        prob(B / D) = s2
----------
The following expectable values were found:
     prob(A / (C & D)) = 0.662
     prob(B / (C & D)) = 0.5874
 ----------
C and D are INDEPENDENT relative to A within 0.01
C and D are not independent relative to (U & ~A) within 0.01
C and D are not independent relative to B within 0.01
C and D are not independent relative to (U & ~B) within 0.01
========================================================
The accuracy of the results is:(1.0000000341589592 1.000001245009345)
Starting from
   :sample-args ((a = 0.5) (b = 0.5) (c = 0.5) (d = 0.5) (ab = 0.25) (r1 = 0.5) (s1 = 0.5) (r2 = 0.5) (s2 = 0.5) (abc 0.125) (abd 0.125))
the computation took 1.974 sec

((a = 0.37) (b = 0.42) (c = 0.55) (d = 0.53) (ab = 0.16) (r1 = 0.6) (s1 = 0.45) (r2 = 0.55) (s2 = 0.48) (abc 0.15446230269559796)
 (abd 0.11399022346424961))

|#

;; This tests the consistency (feasibility) of an assignment of values to the arguments
(defun coherent-probability-assignment (args &optional (terms (ps-terms *ps*)))
  (let* ((vals (mapcar #'(lambda (v) (cons (car v) (variable-value v args))) args))
	 (terms (sublis vals terms)))
    (every #'(lambda (term)
	       (let ((val (ignore-errors (eval term))))
		 (and val (>= val 0)))) terms)))

(defun atom-value (atom args)
  (let ((arg (assoc atom args)))
    (or (mem3 arg) (mem2 arg))))

(defun numerical-probability-value (X args ps)
  (let* ((P (mem1 X))
	 (Q (mem3 X))
	 (p* (dnf-cardinality (dnf (reform-prob-formula (list P '& Q))) (ps-constraints ps) (ps-partition ps)))
	 (q* (dnf-cardinality (dnf (reform-prob-formula Q)) (ps-constraints ps) (ps-partition ps))))
    (dolist (td (ps-term-definitions ps)) (setf p* (subst (mem2 td) (mem1 td) p*)))
    (dolist (td (ps-term-definitions ps)) (setf q* (subst (mem2 td) (mem1 td) q*)))
    (let* ((atoms (union (term-atoms p*) (term-atoms q*)))
	   (values (cons '(u . 1) (mapcar #'(lambda (atom) (cons atom (atom-value atom args))) atoms))))
      (eval (list '/ (sublis values p*) (sublis values q*))))))

(defun display-independence (independence-queries args ps dif)
  (terpri) (princ " ----------")
  (dolist (q independence-queries)
    (let* ((A (mem1 q))
	   (B (mem2 q))
	   (C (mem3 q))
	   (ac (numerical-probability-value (list A '/ C) args ps))
	   (bc (numerical-probability-value (list B '/ C) args ps))
	   (abc (numerical-probability-value (list (list A '& B) '/ C) args ps))
	   (ind (/ (* ac bc) abc)))
      (cond ((< (abs (- 1.0 ind)) dif)
	     (terpri) (print-probability A) (princ " and ") (print-probability B) (princ " are INDEPENDENT relative to ")
	     (print-probability C) (princ " within ") (princ dif))
	    (t
	     (terpri) (print-probability A) (princ " and ") (print-probability B) (princ " are not independent relative to ")
	     (print-probability C) (princ " within ") (princ dif))))))

;; This changes vars2 the same amount it was changed from sample, holding the stipulated members of vars constant
(defun merge-guesses-predictively (vars vars2 sample)
					;(setf v1 vars v2 vars2 v3 sample)
  (mapcar #'(lambda (x y z)
	      (cond ((mem3 x) x)
		    ((equal x y) x)
		    (t (list (mem1 x) (- (* 2 (mem2 y)) (mem2 z))))))
	  vars vars2 sample))

;; This finds a new set of guesses half way between args and args2.
(defun split-arg-difference (args args2 dif)
  (let ((split nil)
	(changed nil))
    (dolist (x args)
      (let* ((y (assoc (car x) args2))
	     (z
	      (if (equal x y) x
		(let ((m3 (mem3 x)))
		  (if m3 (cond ((numberp m3)
				(let* ((z (or (mem3 y) (mem2 y)))
				       (new-z (/ (+ z m3) 2)))
				  (if (> (abs (- z new-z)) dif) (setf changed T))
				  (list (mem1 x) '= new-z)))
			       (t x))
		    (let* ((z (or (mem3 y) (mem2 y)))
			   (new-z (/ (+ z (mem2 x)) 2)))
		      (if (> (abs (- z new-z)) dif) (setf changed T))
		      (list (mem1 x) new-z)))))))
	(push z split)))
    (if changed (reverse split) args)))

#|
(defun  split-arg-difference (args args2 dif)
    ;(setf aa args aa2 args2 dd dif)	; ;
  (let ((split nil))
    (dolist (x args)
      (let* ((y (assoc (car x) args2))
	     (z
	      (if (equal x y) x
		(let ((m3 (mem3 x)))
		  (if m3 (cond ((numberp m3)
				(let* ((z (or (mem3 y) (mem2 y)))
				       (new-z (/ (+ z m3) 2)))
				  (if (> (abs (- z new-z)) dif)
				      (list (mem1 x) '= new-z)
				    x)))
			       (t x))
		    (let* ((z (or (mem3 y) (mem2 y)))
			   (new-z (/ (+ z (mem2 x)) 2)))
		      (if (> (abs (- z new-z)) dif) (list (mem1 x) new-z) x)))))))
	(push z split)))
    (reverse split)))
|#

(defun collapse-numerically (x exceptions)
  (cond ((numberp x) x)
	((null x) nil)
	((atom x)
	 (cond ((member x exceptions) x)
	       (t (let ((x* (ignore-errors (eval x))))
		    (or x* x)))))
	((listp x)
	 (cond ((eq (car x) '+)
		(let ((y (mapcar #'(lambda (w) (collapse-numerically w exceptions)) (cdr x)))
		      (yn nil)
		      (ya nil))
		  (dolist (z y)
		    (cond ((numberp z) (push z yn))
			  (t (push z ya))))
		  (cond (ya
			 (cond (yn (cons '+ (cons (apply '+ yn) ya)))
			       (t (cons '+ ya))))
			(t (apply '+ yn)))))
	       ((eq (car x) '-)
		(let ((y (collapse-numerically (mem2 x) exceptions))
		      (z (collapse-numerically (mem3 x) exceptions)))
		  (cond ((numberp z)
			 (cond ((numberp y) (- y z))
			       ((and (listp y) (eq (car y) '+))
				(let ((yn (find-if #'numberp (cdr y))))
				  (cond (yn
					 (let ((y* (- yn z)))
					   (cond ((eq y* 0) (as-sum (remove yn (cdr y))))
						 ((< y* 0) (list '- (as-sum (remove yn (cdr y))) (- y*)))
						 (t (cons '+ (cons y* (remove yn (cdr y))))))))
					(t (list '- y z)))))
			       (t (list '- y z))))
			((null z)
			 (cond ((numberp y) (- y))
			       (t (list '- y))))
			((listp z)
			 (cond
			  ((eq (car z) '+)
			   (cond
			    ((numberp y)
			     (let ((zn (find-if #'numberp (cdr z))))
			       (cond (zn (let ((z* (- zn y)))
					   (cond ((eq z* 0) (list '- (as-sum (remove zn (cdr z)))))
						 ((< z* 0) (list '- (- z*) (as-sum (remove zn (cdr z)))))
						 (t (cons '- (cons z* (remove zn (cdr z))))))))
				     (t (list '- y z)))))
			    ((listp y)
			     (cond
			      ((eq (car y) '+)
			       (let ((yn (find-if #'numberp (cdr y)))
				     (zn (find-if #'numberp (cdr z))))
				 (cond
				  ((and yn zn)
				   (let ((y* (- yn zn)))
				     (cond
				      ((eq y* 0)
				       (list '- (as-sum (remove yn (cdr y))) (as-sum (remove zn (cdr z)))))
				      ((< y* 0)
				       (list '- (as-sum (remove yn (cdr y))) (cons '+ (cons (- y*) (remove zn (cdr z))))))
				      (t (list '- (as-sum (cons y* (remove yn (cdr y)))) (as-sum (remove zn (cdr z))))))))
				  (t (list '- y z)))))
			      (t (list '- y z))))
			    (t (list '- y z))))
			  (t (list '- y z))))
			(t (list '- y z)))))
	       ((eq (car x) '*)
		(let ((y (mapcar #'(lambda (w) (collapse-numerically w exceptions)) (cdr x)))
		      (yn nil)
		      (ya nil))
		  (dolist (z y)
		    (cond ((numberp z) (push z yn))
			  (t (push z ya))))
		  (cond (ya
			 (cond (yn (cons '* (cons (apply '* yn) ya)))
			       (t (cons '* ya))))
			(t (apply '* yn)))))
	       ((eq (car x) '/)
		(let ((y (collapse-numerically (mem2 x) exceptions))
		      (z (collapse-numerically (mem3 x) exceptions)))
		  (cond ((numberp z)
			 (cond ((numberp y) (/ y z))
			       (t (list '/ y z))))
			(t (list '/ y z)))))
	       ((eq (car x) 'expt)
		(let ((y (collapse-numerically (mem2 x) exceptions))
		      (z (collapse-numerically (mem3 x) exceptions)))
		  (cond ((numberp z)
			 (cond ((numberp y) (expt y z))
			       (t (list 'expt y z))))
			(t (list 'expt y z)))))
	       ((eq (car x) 'log)
		(let ((y (collapse-numerically (mem2 x) exceptions)))
		  (cond ((numberp y) (log y))
			(t (list 'log y)))))
	       ))))

(defun truncate-decimal (x n)
  (float (/ (round (* x (expt 10 n))) (expt 10 n))))

;; X is a list of two strings.
(defun display-probability-value (X args ps truncate)
					;(setf xx x aa args pp ps)
  (let ((val (numerical-probability-value X args ps)))
    (terpri) (princ "     ") (print-complete-probability X) (princ " = ") (princ (truncate-decimal val truncate))))

(defun apply-tc (v arg* tc)
  (set v arg*) (eval tc))

(defun find-expectable-value (v tc args dif display)
  (let* ((arg (cadr (assoc v args)))
	 (arg+ 1)
	 (arg- 0)
	 (bad-value nil)  ;; was the previous value complex or incoherent?
	 (arg* arg)
	 (val (apply-tc v arg tc)))  ;; val is real because args is coherent.
    (when display (progn (terpri) (terpri) (princ "for ") (princ v) (princ " the starting value is ") (princ arg)))
    (when display (progn (print arg-) (princ "	") (princ arg*) (princ "	") (princ arg+) (princ "	") (princ val)))
    (cond
     ((< (abs val) dif) arg)
     ;; If val < 0 we are on the left side of the minimum, so the optimal value lies between arg and arg+. Try the midpoint.
     ((< val 0) (setf arg- arg) (setf arg* (/ (+ arg arg+) 2)))
     ;; If val > 0 we are on the right side of the minimum, so the optimal value lies between arg- and arg. Try the midpoint.
     ((> val 0) (setf arg+ arg) (setf arg* (/ (+ arg- arg) 2))))
    ;; In the following arg is always the old value and arg* the new value, so that we know which way we went.
    ;; arg- and arg+ are the limits within which we know the optimal value to lie
    (loop
     ;; Let val be the value for the new arg*. If it is complex but the imaginary part is small, assume it results from
     ;; a rounding error and drop the imaginary part.
     (let ((v0 (ignore-errors (apply-tc v arg* tc))))
       (cond ((null v0) (setf val nil))
	     ((< (abs (imagpart v0)) .0001) (setf val (realpart v0)))
	     (t (setf val v0))))
     (when display (progn (print arg-) (princ "	") (princ arg*) (princ "	") (princ arg+) (princ "	") (princ val))
	   (princ "	bad-value = ") (princ bad-value))
     (cond
      ;; If val is nil,  imaginary, or real and incoherent, we went too far
      ((or (null val) (not (realp val))
	   (not (coherent-probability-assignment (subst (list v arg*) (assoc v args) args :test 'equal))))
       (cond
	;; if we moved left, then if the previous value was complex or incoherent, move left again.
	;; Otherwise, move back right half way
	((< arg* arg)
	 (cond
	  (bad-value (setf arg+ arg*) (setf arg arg*) (setf arg* (/ (+ arg- arg*) 2)))
	  (t (setf arg- arg*) (setf arg arg*) (setf arg* (/ (+ arg* arg+) 2)))))
	;; if we moved right, then if the previous value was complex or incoherent, move right again.
	;; Otherwise, move back left half way
	((> arg* arg)
	 (cond
	  (bad-value (setf arg- arg*) (setf arg arg*) (setf arg* (/ (+ arg* arg+) 2)))
	  (t (setf arg+ arg*) (setf arg arg*) (setf arg* (/ (+ arg- arg*) 2))))))
       (setf bad-value t))
      ;; otherwise, if either termination condition is satisfied, return arg*
      ((< (abs val) dif) (return arg*))
      ((< (abs (- 1 (/ arg arg*))) dif) (return arg*))
      ;; otherwise, if val < 0, we move further right:
      ((< val 0) (setf bad-value nil) (setf arg- arg*) (setf arg arg*) (setf arg* (/ (+ arg arg+) 2)))
      ;; otherwise, if val > 0, we move further left:
      (t (setf arg+ arg*) (setf bad-value nil) (setf arg arg*) (setf arg* (/ (+ arg- arg) 2))))
     )))

(labels
 ()

 (defun solve-for-expectable-values (TCS args dif)
					; (setf tc tcs aa args dd dif)
   (dolist (x args) (set (car x) (or (mem3 x) (mem2 x))))
   (let ((variables (mapcar #'car (subset #'(lambda (x) (not (mem3 x))) args))))
     (catch 'min
       (loop
	(let ((changed nil))
	  (dolist (arg variables)
	    (let* ((tc (collapse-numerically (mem2 (assoc arg TCS)) (list arg)))
		   (arg* (find-expectable-value arg tc args dif  nil )))
	      (when (>= (abs (- (cadr (assoc arg args)) arg*)) dif) (setf changed t))
	      (setf args (subst (list arg arg*) (assoc arg args) args :test 'equal))
	      (setf *args* args)))
	  (when (null changed) (return args)))))))

 (defun find-expectable-values (&key args ps  (dif .0000001) (display nil) (display-results? t) (depth 0) (iterations 2)
				     probability-queries (top-level t) (dif2 .0001) (name "*ps*") subsets constraints
				     probability-constraints (shallow-display nil) (split-dif .00001)
				     subset-constraints constants sample-args independence-queries (truncate 4))
   (when top-level (setf *args* nil *ps* ps))
   (when (> depth 1000) (terpri) (princ "Exceeded depth of 1000.") (break))
   (when top-level
     (setf constants nil)
     (dolist (x args) (when (mem3 x) (push (car x) constants))))
   (cond (ps
	  (when top-level
	    (when (not (== constants (ps-constants ps)))
	      (terpri) (princ "The list of assigned values does not agree with the list of constants for ")
	      (princ (ps-name ps)) (return-from find-expectable-values))))
	 (t
	  (setf ps (build-probability-structure-automatically
		    :name name :constraints constraints :constants constants :subsets subsets
		    :probability-constraints probability-constraints :sample-args sample-args :subset-constraints subset-constraints))))
   (dolist (x (ps-atoms ps)) (makunbound x))
   (when (null sample-args)
     (cond ((ps-sample-args ps) (setf sample-args (ps-sample-args ps)))
	   (t
	    (setf sample-args
		  (append
		   (mapcar #'(lambda (x) (default-constant-value x (ps-constraints ps))) (ps-constants ps))
		   (mapcar
		    #'(lambda (x)
			(list x (expt .5 (length (remove-if #'numberp (mapcar #'read-from-string (explode (string x))))))))
		    (ps-atoms ps)))))))
   (when (null args) (setf args sample-args))
   (when display
     (progn (terpri) (bar-indent depth) (princ "(") (terpri) (bar-indent depth)
	    (princ "Finding expectable values for probability structure ")
	    (princ (ps-name ps)) (princ " with") (terpri) (bar-indent depth) (princ "args = ") (princ args)
	    (terpri) (bar-indent depth) (princ "and sample-args = ") (princ sample-args)
	    ))
   (when (and display-results? (not display))
     (terpri) (princ "Find expectable values:")
     (terpri) (princ "   :args ") (princ args)
     (terpri) (princ "   :probability-structure ") (princ (ps-name ps))
     (terpri) (princ "   :subsets ") (princ (mapcar #'string (ps-subsets ps)))
     (terpri) (princ "   :constants ") (princ (ps-constants ps))
     (when (ps-constraints ps)
       (terpri) (princ "   :constraints ")
       (dolist (x (ps-constraints ps)) (terpri) (princ "        ") (princ (car x)) (princ " = ") (princ (cdr x))))
     (when (ps-subset-constraints ps)
       (terpri) (princ "   :subset-constraints ")
       (dolist (x (ps-subset-constraints ps)) (terpri) (princ "        ") (princ x)))
     (when (ps-probability-constraints ps)
       (terpri) (princ "   :probability-constraints ")
       (dolist (x (ps-probability-constraints ps)) (terpri) (princ "        ")
	       (print-complete-probability (mem2 x)) (princ " = ") (princ (mem4 x)))))
   (let ((terms (ps-terms ps))
	 (TCS (ps-log-term-characterizations ps))
	 (time (when top-level (get-internal-run-time)))
	 (args0 args)
	 (sa0 sample-args))
     (when (and top-level (< (length args) (length sample-args)))
       (setf args (mapcar #'(lambda (v) (or (assoc (car v) args) v)) sample-args)))
     (when (and top-level (not (coherent-probability-assignment sample-args)) (not (coherent-probability-assignment args)))
       (terpri) (princ "Neither the assigned values nor the sample-args constitute a coherent probability assignment,")
       (terpri) (princ "so the search cannot proceed.") (return-from find-expectable-values nil))
     (cond ((coherent-probability-assignment args terms)
	    (let* ((n iterations) (print-iteration (> iterations 0)))
	      (loop
	       (setf args (solve-for-expectable-values TCS args (* dif (expt 10 n))))
	       (when (and display print-iteration) (terpri) (princ "dif = ") (princ (* dif (expt 10 n))) (princ ":  ") (princ args))
					; (when (null args) (break))
	       (when (eq n 0) (return))
	       (decf n)))
	    (when shallow-display (terpri) (princ " approximation: ") (princ args))
	    args)
	   (t
	    (when display (terpri) (bar-indent depth) (princ "Finding new guesses using sample args ") (princ sample-args))
	    (let ((args2 (split-arg-difference args sample-args split-dif)))
	      (cond
	       ((not (eq args2 args))
		(let* ((new-args
			(find-expectable-values
			 :args args2 :ps ps :display display :top-level nil :depth (+ 4 depth)  :iterations 0 :split-dif split-dif
			 :display-results? nil :sample-args sample-args :dif dif2 :dif2 dif2 :shallow-display shallow-display)))
		  (cond
		   (new-args
		    (let ((predicted-args (merge-guesses-predictively args new-args sample-args)))
		      (when display
			(terpri) (bar-indent depth) (princ "args = ") (princ args)
			(terpri) (bar-indent depth) (princ "new-args = ") (princ new-args)
			(terpri) (bar-indent depth) (princ "sample-args = ") (princ sample-args)
			(terpri) (bar-indent depth) (princ "predicted-args = ") (princ predicted-args)
			(when (not (coherent-probability-assignment predicted-args (ps-terms ps)))
			  (terpri) (bar-indent depth) (princ "The predicted-args are not coherent.")))
		      (setf args
			    (find-expectable-values
			     :args predicted-args :ps ps :display display :display-results? nil :top-level nil
			     :depth depth :split-dif split-dif :probability-queries probability-queries
			     :sample-args new-args :iterations (if (eq depth 0) iterations 0) :dif dif :dif2 dif2
			     :independence-queries independence-queries :shallow-display shallow-display))))
		   (t (setf args nil)))))
	       (t (setf args nil))))))
     (when top-level (setf time (- (get-internal-run-time) time)))
     (cond
      ((and (null args) top-level)
       (when display-results?
	 (terpri) (terpri) (princ "No value found. The statement of the problem may be incoherent (inconsistent with the probability")
	 (terpri) (princ "calculus), or it may lie at the edge of the set of coherent probability assignments.")
	 (when (and (null shallow-display) (null display))
	   (terpri) (princ "For more information on the search, add \":shallow-display t\" or \":display t\" to the instruction."))
	 (when *args*
	   (terpri) (princ "The closest coherent approximation found was the following:")
	   (terpri) (terpri) (princ *args*)
	   (let ((d (find-if
		     #'(lambda (d) (every #'(lambda (x) (< (abs (- (mem3 x) (mem3 (assoc (mem1 x) *args*)))) d)) args0))
		     '(.0000001 .000001 .00001 .001 .01))))
	     (when d
	       (terpri) (terpri) (princ "This is within ") (princ d)
	       (princ " of the queried variable values, which may be close enough. It might also be possible to improve the")
	       (terpri) (princ "approximation by decreasing the value of split-dif from its default value of .00001")
					;(terpri) (princ "However, setting split-dif too low may prevent the search from terminating.")
	       (terpri) (princ "For this approximation, the expectable values are as follows:")
	       (let ((o-args
		      (find-expectable-values
		       :args (subset #'(lambda (x) (mem3 x)) *args*)
		       :ps *ps*
		       :dif dif
		       :display nil
		       :display-results? nil
		       :iterations iterations
		       :dif2 dif2
		       :subsets subsets
		       :constraints constraints
		       :probability-constraints probability-constraints
		       :split-dif split-dif
		       :subset-constraints subset-constraints
		       :sample-args sample-args
		       :independence-queries independence-queries
		       :truncate truncate
		       :probability-queries probability-queries)))
		 (terpri) (terpri) (princ o-args)
		 (when probability-queries
		   (terpri) (princ "----------") (terpri)
		   (princ "For this approximation, the following expectable values were found for the queried probabilities:")
		   (dolist (p (remove 'prob probability-queries))
		     (display-probability-value p o-args ps truncate))
		   (when independence-queries (display-independence independence-queries o-args ps .01))
		   (terpri) (princ "========================================================"))
		 (when display-results?
		   (terpri)  (princ "The accuracy of the results is:")
		   (princ (mapcar #'(lambda (x) (eval (mem2 x))) (ps-term-characterizations ps)))
		   (terpri) (princ "the computation took ") (display-run-time-in-seconds time) (terpri) (terpri))
		 (when display (princ "  )"))))))
	 (terpri) (terpri))
       nil)
      (t
       (when (and display-results? probability-queries)
	 (terpri) (princ "----------")
	 (terpri) (princ "The following expectable values were found:")
	 (dolist (p (remove 'prob probability-queries))
	   (display-probability-value p args ps truncate))
	 (when independence-queries (display-independence independence-queries args ps .01))
	 (terpri) (princ "========================================================"))
       (when display (terpri) (bar-indent depth) (princ args))
       (when display-results?
	 (terpri)  (princ "The accuracy of the results is:")
	 (princ (mapcar #'(lambda (x) (eval (mem2 x))) (ps-term-characterizations ps)))
	 (terpri) (princ "Starting from")
	 (terpri) (princ "   :sample-args ") (princ sa0)
	 (terpri) (princ "the computation took ") (display-run-time-in-seconds time) (terpri) (terpri))
       (when display (princ "  )"))
       args)))))

(defun apply-term-characterization (tc v arg args)
  (setf tc (subst arg v tc))
  (dolist (x args)
    (when (not (eq (car x) v))
      (let ((val (or (mem3 x) (mem2 x)))) (setf tc (subst val (car x) tc)))))
  (eval tc))

(defun tabulate-expectable-values (fnc ps var1 var2)
  (let* ((s-args (ps-sample-args ps))
	 (args00 (remove (assoc var1 s-args) (remove (assoc var2 s-args) s-args :test 'equal) :test 'equal)))
    (princ var1)
    (princ "	0.1	0.2	0.3	0.4	0.5	0.6	0.7	0.8	0.9")
    (dolist (x '(0.01 0.025 0.05 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 0.95 0.975 0.99))
      (terpri)
      (princ x)
      (dolist (y '(0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 0.99))
        (let* ((new-args (cons (list var1 '= x) (cons (list var2 '= y) args00)))
	       (args (find-expectable-values new-args ps :display-results? nil :count? nil)))
	  (princ "	") (princ (funcall fnc args)))))))

#|
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

(time
(tabulate-expectable-values #'(lambda (x) (let ((y (assoc 'p x))) (or (mem3 y) (mem2 y)))) Y-ps 'r 's)
)

(build-probability-structure-automatically
  :name "autoY-ps"
  :subsets '(A B P)
  :constants '(r s)
  :probability-constraints '((prob(P / A) = r)
                                               (prob(P / B) = s))
  :sample-args '((r = .5) (s = .5) (a .5) (b .5) (p .5) (ab .25) (ap .25) (bp .25) (abp .125)))

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

(time
(tabulate-expectable-values #'(lambda (x) (let ((y (assoc 'p x))) (or (mem3 y) (mem2 y)))) autoY-ps 'r 's)
)

|#

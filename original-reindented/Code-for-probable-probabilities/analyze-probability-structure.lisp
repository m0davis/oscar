
(proclaim '(special *default-line-length* *definitions* *term-characterizations* *TC* *loaded* *args* *ps*))

(setf *default-line-length* 500)

(when (not (boundp '*loaded*))
     (progn
         (load "PB12:documents:oscar:oscar folder:oscar-tools.lisp")
         (load "PB12:documents:writings:papers:probability:the y-function:sampling:LISP Ä:algebraic simplification.lisp")
         (setf *loaded* t)
         ))


#|							ANALYZE-PROBABILITY-STRUCTURES

version of 8/7/07

This file defines the LISP function ANALYZE-PROBABILITY-STRUCTURE, which attempts to find analytic
characterizations for the expectable values of probabilities. You must first load the files "oscar-tools.lisp" and 
"algebraic-simplification.lisp". This will be done automatically upon loading the present file, but you must edit
the pathnames (above) to indicate where the files are on your computer.

Here is an example of the use of ANALYZE-PROBABILITY-STRUCTURE:

(analyze-probability-structure
  :subsets '(A B C D)
  :constants '(a b c d r s)
  :constraints '((abc = (* s bc)))
  :probability-constraints '((prob(A / B) = r))
  :subset-constraints '((D subset C))
  :probability-queries '(prob(A / (B & C))
                                            prob(A / B)
                                            prob(A / (B & (C & D))))
  :independence-queries '((A B C) (A C B) (A C U) (A D (B & C)))
  :display-infix t)

The general form of a function call is:

(ANALYZE-PROBABILITY-STRUCTURE
  :subsets a list of atoms
  :constants a list of atoms
  :constraints a list of linear equations in prefix notation
  :probability-constraints a list of probability specifications
  :subset-constraints a list of subset relations
  :higher-order t or nil
  :probability-queries a list of probability formulas
  :independence-queries a list of triples of formulas
  :display-infix t or nil
  :display t or nil
  :display-details t or nil
  :display-results t or nil
  :expand-defs t or nil
  :display-terms t or nil
  :remove-u t or nil
  :parallel-term-characterizations t or nil
  :name a string)

Note that all the displays work best if you set your LISP to display S-expressions in lower case.

subsets is a list of atoms (best typed in upper case) which symbolize the subsets of U that
are under considerations. Throughout, if for example, the atoms are A, B, C, D, then a is the cardinality
of A, b is the cardinality of B, ab is the cardinality of the intersection of A and B, abc is the cardinality
of A interesection B intersection C, and so forth. These lower-case expressions make up the list of
variables. ANALYZE-PROBABILITY-STRUCTURE attempts to characterize the expectable values for
all the variables.  The constraints (below) may add variables like r and s used in the constraints.

constants is a list variables that are held constant.

constraints is a list of linear equations (in prefix form) like '((ab = (* r b)) (abc = (* s bc))).
ANALYZE-PROBABILITY-STRUCTURE is trying to find the expectable values relative to the set
of constraints.

subset-constraints is a list of constraints like '((D subset C) (A = (B union C)) (E = (- A))), and so forth.
"union", "intersection", and "-" (in the form "(- P)") can be used in these constraints. A preprocessor translates
these into normal constraints which are hten used in finding the expectable values.

probability-constraints is a list of specifications of probabilities like '((prob((F & H) / (G v ~H)) = r) (prob(A / B) = s)).
Note that there must be white space around "/" and the logical connectives other than "~".A preprocessor translates these into
normal constraints which are hten used in finding the expectable values.

Note that if the subset-constraints and probability-constraints create simultaneous equations regarding some of
the variables, the preprocessor may not correctly translate them into ordinary constraints. In that case it is best
to do the translation by hand and enter all the constraints as ordinary constraints.

higher-order determines whether ANALYZE-PROBABILITY-STRUCTURE attempts to solve quadratic and ternary
equations. The default is nil, because that can severely complicate the solution process and result in the program
running out of memory or taking inordinately long.

probability-queries is a list of probability formulas like '(prob(A / (B & C)) prob(A / B) prob(A / (B & (C & D)))) for which
ANALYZE-PROBABILITY-STRUCTURE will attempt to find analytic characterizations.

independence-queries is a list of triples of formulas like '((A B C) (A C B) (A C U) (A D (B & C))). For each triple,
ANALYZE-PROBABILITY-STRUCTURE will attempt to determine whether the first two formulas are statistically
independent relative to the third.

display-infix specifies whether the results are to be printed in prefix or infix notation. The default is nil (for prefix).
Note that there is a function (convert-to-infix x) for converting prefix formulas to infix notation, and a function
(convert-to-prefix x) to going the other way.

display  If this is t, ANALYZE-PROBABILITY-STRUCTURES prints a partial display of its progress. By default, this is nil.

display-details If this is t, ANALYZE-PROBABILITY-STRUCTURES prints out a complete proof of its results. By
default, this is nil.

display-results If this is nil, all that is displayed at the end is the results of the probability-queries and independence-
queries. If it is t, characterizations of all the variables are displayed. By default, this is t.

expand-defs ANALYZE-PROBABILITY-STRUCTURE computes a list of definitions each of which may contain
terms defined later in the list. If expand-defs  is t, the defined terms are replaced by their definitions throughout
the list, and the resulting definitions simplified. However, my computer algebra routines are not very good at this.
It may be quicker to set expand-defs to nil, in which case the unexpanded definitions are returned. They can then
be pasted into Mathematica or Maple and expanded and simplified there. That is often much faster. Executing
(print-defs-for-Mathematica) prints a Mathematica instruction that can be copied and pasted into Mathematica.
Then evaluating any of the variables in Mathematica will return its simplified definition.

display-terms If this is t, term-sets are displayed when display-results is also t. By default it is t.

remove-u If this is t, u is set to 1 in the simplification of formulas. This is to treat the values of lower-case variables
as probabilities rather than cardinalities. By default, this is t.

parallel-term-characterizations If this is nil, ANALYZE-PROBABILITY-STRUCTURES tries a different search strategy
that is sometimes faster in its attempt to find expectable values. This is nil by default.

name Sometimes ANALYZE-PROBABILITY-STRUCTURE is unable to find definitions for all the variables. In that 
case, one can still solve the problems numerically using FIND-EXPECTABLE-VALUES (defined in a separate
file). To make the use of FIND-EXPECTABLE-VALUES more efficient, ANALYZE-PROBABILITY-STRUCTURE
saves its results in a structure called a probability-structure, which can be used by FIND-EXPECTABLE-VALUES.
If no name is supplied, a name is generated for the probability structure, and the probability structure is bound
to the name. If a name is supplied, it should be a string consisting of a single atom (e.g., "my-ps"). The atom is taken as the
name of the probability-structure. One can then use the name when calling the structure in FIND-EXPECTABLE-
VALUES. A probability structure is generated even if definitions are found for all the variables. There is no use
for FIND-EXPECTABLE-VALUES in that case, but it can still be used for finding the values of probabilities and
not originally queried, or for checking independenced in cases not originally queried.

Here is an example of ANALYZE-PROBABILITY-STRUCTURE with display-details = nil:

(analyze-probability-structure
  :subsets '(A B C)
  :name "my-ps"
  :constants '(a b c r s)
  :probability-constraints '((prob(A / C) = r)
                                               (prob(B / C) = s))
  :probability-queries '(prob((A & B) / C))
  :independence-queries '((A B C)
                                                (A B U))
  :display-infix t)

(
========================================================
Dividing U into 3 subsets A,B,C whose probabilities relative to U are a, b, c,
if the following constraints are satisfied:
     prob(A / C) = r
     prob(B / C) = s
and the values of a, b, c, r, s are held constant,
grounded definitions of the expectable values were found for all the variables.
----------------------------------------------------------------------------------------------
The following definitions of expectable values were found that appeal only to the constants:
----------
abc = (s * r * c)
----------
ab = ((((s * r * c) + (a * b)) - ((r * c * b) + (a * s * c))) / (1 - c))
========================================================
The following characterizations were found for the expectable values of the probabilities wanted:
----------
prob((A & B) / C) = (s * r)
----------
========================================================
A and B are STATISTICALLY INDEPENDENT  relative to C

A and B are NOT statistically independent  relative to U
     (prob(A / U) * prob(B / U)) Ö prob((A & B) / U) = 
          (((1 - c) * a * b) / (((a * b) + (s * r * c)) - ((r * c * b) + (a * s * c))))
========================================================
These results are encoded in the probability structure my-ps
)

Setting display-details = t produces a proof of the results (but to see that it is a proof, you must
be familiar with some of the theorems in the paper "Probable probabilities":

(analyze-probability-structure
  :subsets '(A B C)
  :constants '(a b c r s)
  :probability-constraints '((prob(A / C) = r)
                                               (prob(B / C) = s))
  :probability-queries '(prob((A & B) / C))
  :independence-queries '((A B C)
                                                (A B U))
  :display-infix t
  :display-details t)

(
========================================================
Dividing U into 3 subsets A,B,C whose probabilities relative to U are a, b, c,
if the following constraints are satisfied:
     prob(A / C) = r
     prob(B / C) = s
and the values of a, b, c, r, s are held constant,
then the term-set consisting of the cardinalities of the partition of U is:
    {
     (ab - abc)
     abc
     ((a + abc) - (ab + (r * c)))
     ((r * c) - abc)
     ((b + abc) - (ab + (s * c)))
     ((s * c) - abc)
     ((ab + u + (r * c) + (s * c)) - (a + b + abc + c))
     ((c + abc) - ((r * c) + (s * c)))
    }
The subset of terms in the term-set that contain abc is:
          {
          (ab - abc)
          abc
          ((a + abc) - (ab + (r * c)))
          ((r * c) - abc)
          ((b + abc) - (ab + (s * c)))
          ((s * c) - abc)
          ((ab + u + (r * c) + (s * c)) - (a + b + abc + c))
          ((c + abc) - ((r * c) + (s * c)))
          }
The expectable-value of abc is then the real-valued solution to the following equation:
1 = (((ab - abc) ^ ((ab - (abc + 1)) - (ab - abc)))
         * (abc ^ ((abc + 1) - abc))
         * (((a + abc) - (ab + (r * c))) ^ (((a + (abc + 1)) - (ab + (r * c))) - ((a + abc) - (ab + (r * c)))))
         * (((r * c) - abc) ^ (((r * c) - (abc + 1)) - ((r * c) - abc)))
         * (((b + abc) - (ab + (s * c))) ^ (((b + (abc + 1)) - (ab + (s * c))) - ((b + abc) - (ab + (s * c)))))
         * (((s * c) - abc) ^ (((s * c) - (abc + 1)) - ((s * c) - abc)))
         * (((ab + u + (r * c) + (s * c)) - (a + b + abc + c)) ^
            (((ab + u + (r * c) + (s * c)) - (a + b + (abc + 1) + c)) - ((ab + u + (r * c) + (s * c)) - (a + b + abc + c))))
         * (((c + abc) - ((r * c) + (s * c))) ^ (((c + (abc + 1)) - ((r * c) + (s * c))) - ((c + abc) - ((r * c) + (s * c))))))
   = (((ab - abc) ^ (- 1))
         * (abc ^ 1)
         * (((a + abc) - (ab + (r * c))) ^ 1)
         * (((r * c) - abc) ^ (- 1))
         * (((b + abc) - (ab + (s * c))) ^ 1)
         * (((s * c) - abc) ^ (- 1))
         * (((ab + u + (r * c) + (s * c)) - (a + b + abc + c)) ^ (- 1))
         * (((c + abc) - ((r * c) + (s * c))) ^ 1))
   = ((1 / (ab - abc))
         * abc
         * ((abc + a) - (ab + (r * c)))
         * (1 / ((r * c) - abc))
         * ((abc + b) - (ab + (s * c)))
         * (1 / ((s * c) - abc))
         * (1 / (((s * c) + (r * c) + u + ab) - (a + b + abc + c)))
         * ((abc + c) - ((r * c) + (s * c))))
   = (abc * ((abc + a) - (ab + (r * c))) * ((abc + b) - (ab + (s * c))) * ((abc + c) - ((r * c) + (s * c)))
            * (1 / (((s * c) + (r * c) + u + ab) - (a + b + abc + c))) * (1 / ((s * c) - abc))
            * (1 / ((r * c) - abc)) * (1 / (ab - abc)))
   = ((((c + abc) - ((r * c) + (s * c))) * ((b + abc) - (ab + (s * c))) * ((a + abc) - (ab + (r * c))) * abc)
         / ((ab - abc) * ((r * c) - abc) * ((s * c) - abc) * ((ab + u + (r * c) + (s * c)) - (a + b + abc + c))))
The subset of terms in the term-set that contain ab is:
          {
          (ab - abc)
          ((a + abc) - (ab + (r * c)))
          ((b + abc) - (ab + (s * c)))
          ((ab + u + (r * c) + (s * c)) - (a + b + abc + c))
          }
The expectable-value of ab is then the real-valued solution to the following equation:
1 = (((ab - abc) ^ (((ab + 1) - abc) - (ab - abc)))
         *
         (((a + abc) - (ab + (r * c))) ^ (((a + abc) - ((ab + 1) + (r * c))) - ((a + abc) - (ab + (r * c)))))
         * (((b + abc) - (ab + (s * c))) ^ (((b + abc) - ((ab + 1) + (s * c))) - ((b + abc) - (ab + (s * c)))))
         * (((ab + u + (r * c) + (s * c)) - (a + b + abc + c)) ^
            ((((ab + 1) + u + (r * c) + (s * c)) - (a + b + abc + c)) - ((ab + u + (r * c) + (s * c)) - (a + b + abc + c)))))
   = (((ab - abc) ^ 1) * (((a + abc) - (ab + (r * c))) ^ (- 1)) * (((b + abc) - (ab + (s * c))) ^ (- 1))
         * (((ab + u + (r * c) + (s * c)) - (a + b + abc + c)) ^ 1))
   = ((ab - abc) * (1 / ((abc + a) - (ab + (r * c)))) * (1 / ((abc + b) - (ab + (s * c)))) *
            (((s * c) + (r * c) + u + ab) - (a + b + abc + c)))
   = ((ab - abc) * (((s * c) + (r * c) + u + ab) - (a + b + abc + c)) *
            (1 / ((abc + b) - (ab + (s * c)))) * (1 / ((abc + a) - (ab + (r * c)))))
   = ((((ab + u + (r * c) + (s * c)) - (a + b + abc + c)) * (ab - abc))
         / (((a + abc) - (ab + (r * c))) * ((b + abc) - (ab + (s * c)))))
The preceding term-characterization for ab simplifies to:
. . ((((c * ab) + (u * abc) + (a * b) + (r * s * (c ^ 2))) - ((c * abc) + (u * ab) + (a * s * c) + (r * c * b)))
      = 0)
Solving for ab:
. . ab = ((((u * abc) + (a * b) + (r * s * (c ^ 2))) - ((r * c * b) + (a * s * c) + (c * abc))) / (u - c))
Substituting the preceding definition for ab into the previous term-characterizations
produces the new term-characterizations:
. . . . . abc: 1 = ((((c + abc) - ((r * c) + (s * c))) *
                            ((b + abc)
                              - (((((u * abc) + (a * b) + (r * s * (c ^ 2))) - ((r * c * b) + (a * s * c) + (c * abc))) / (u - c))
                                  + (s * c)))
                            * ((a + abc)
                              -
                              (((((u * abc) + (a * b) + (r * s * (c ^ 2))) - ((r * c * b) + (a * s * c) + (c * abc))) / (u - c))
                                + (r * c)))
                            * abc)
                           / ((((((u * abc) + (a * b) + (r * s * (c ^ 2))) - ((r * c * b) + (a * s * c) + (c * abc)))
                                 / (u - c))
                               - abc)
                             * ((r * c) - abc)
                             * ((s * c) - abc)
                             * ((((((u * abc) + (a * b) + (r * s * (c ^ 2))) - ((r * c * b) + (a * s * c) + (c * abc)))
                                   / (u - c))
                                 + u + (r * c) + (s * c))
                               - (a + b + abc + c))))
These term-characterizations simplify to yield the following term-characterizations:
. . . . . abc: 1 = ((abc * ((c + abc) - ((r * c) + (s * c)))) / (((s * c) - abc) * ((r * c) - abc)))
. The preceding term-characterization for abc simplifies to:
. . . (((s * r * (c ^ 2)) - (abc * c)) = 0)
. Solving for abc:
. . . abc = (s * r * c)
. . . Substituting the new definition for abc into the previous definition for ab produces:
. . . ab = ((((u * (s * r * c)) + (a * b) + (r * s * (c ^ 2))) - ((r * c * b) + (a * s * c) + (c * (s * r * c))))
                 / (u - c))
. . . which simplifies to:
. . . ab = ((((a * b) + (u * s * r * c)) - ((r * c * b) + (a * s * c))) / (u - c))

Grounded definitions of the expectable values were found for all the variables.
----------------------------------------------------------------------------------------------
The following definitions of expectable values were found that appeal only to the constants:
----------
abc = (s * r * c)
----------
ab = ((((s * r * c) + (a * b)) - ((r * c * b) + (a * s * c))) / (1 - c))
========================================================
The following characterizations were found for the expectable values of the probabilities wanted:
----------
prob((A & B) / C) = (s * r)
----------
========================================================
A and B are STATISTICALLY INDEPENDENT  relative to C

A and B are NOT statistically independent  relative to U
     (prob(A / U) * prob(B / U)) Ö prob((A & B) / U) = 
          (((1 - c) * a * b) / (((a * b) + (s * r * c)) - ((r * c * b) + (a * s * c))))
========================================================
These results are encoded in the probability structure ps7562
)


ANALYZE-PROBABILITY-STRUCTURE finds the expectable values of probabilities by converting
the problem into one of solving a system of simultaneous equations. Occasionally, 
ANALYZE-PROBABILITY-STRUCTURE can construct the system of equations but cannot solve
them. It may be possible to solve them in a comptuer algebra program instead. Thus we also
have a function ANALYZE-PROBABILITY-STRUCTURE-in-MAPLE that constructs the system of
equations and then prints out a Maple instruction which can be pasted into Maple for solving the
equations. For example,

(analyze-probability-structure-in-Maple
  :subsets '(A B C D)
  :constants '(a b c d bc bd r s v)
  :probability-constraints '((prob(A / B) = r)
                                               (prob(A / (B & C)) = s)
                                               (prob(A / (B & D)) = v)))

produces the Maple instruction

solve({((((ac + abcd) - ((s * bc) + acd)) * ((bc + ac + 1 + (r * b) + ad + bd + abcd + cd) - (a + b + (s * bc) + c + bcd + acd + d + (v * bd)))) /
        ((((s * bc) + c + acd + bcd) - (ac + bc + abcd + cd)) * (((s * bc) + a + (v * bd) + acd) - ((r * b) + ac + abcd + ad)))) = 1, 
(((((r * b) + abcd) - ((s * bc) + (v * bd))) * abcd * ((ad + abcd) - ((v * bd) + acd)) * ((ac + abcd) - ((s * bc) + acd)) *
  ((bd + abcd) - ((v * bd) + bcd)) * ((bc + abcd) - ((s * bc) + bcd)) *
  ((bc + ac + 1 + (r * b) + ad + bd + abcd + cd) - (a + b + (s * bc) + c + bcd + acd + d + (v * bd))) * ((cd + abcd) - (acd + bcd)))
 /
 ((((s * bc) + c + acd + bcd) - (ac + bc + abcd + cd)) * (((v * bd) + d + acd + bcd) - (ad + bd + abcd + cd)) * (bcd - abcd) *
  (((s * bc) + b + (v * bd) + bcd) - ((r * b) + bc + abcd + bd)) * (acd - abcd) * (((s * bc) + a + (v * bd) + acd) - ((r * b) + ac + abcd + ad)) *
  ((s * bc) - abcd) * ((v * bd) - abcd))) = 1, 
((((bc + ac + 1 + (r * b) + ad + bd + abcd + cd) - (a + b + (s * bc) + c + bcd + acd + d + (v * bd))) * ((cd + abcd) - (acd + bcd))) /
 ((((s * bc) + c + acd + bcd) - (ac + bc + abcd + cd)) * (((v * bd) + d + acd + bcd) - (ad + bd + abcd + cd)))) = 1, 
(((((s * bc) + a + (v * bd) + acd) - ((r * b) + ac + abcd + ad)) * (acd - abcd) * (((v * bd) + d + acd + bcd) - (ad + bd + abcd + cd)) *
  (((s * bc) + c + acd + bcd) - (ac + bc + abcd + cd)))
 /
 (((cd + abcd) - (acd + bcd)) * ((bc + ac + 1 + (r * b) + ad + bd + abcd + cd) - (a + b + (s * bc) + c + bcd + acd + d + (v * bd))) *
  ((ac + abcd) - ((s * bc) + acd)) * ((ad + abcd) - ((v * bd) + acd)))) = 1, 
(((((s * bc) + b + (v * bd) + bcd) - ((r * b) + bc + abcd + bd)) * (bcd - abcd) * (((v * bd) + d + acd + bcd) - (ad + bd + abcd + cd)) *
  (((s * bc) + c + acd + bcd) - (ac + bc + abcd + cd)))
 /
 (((cd + abcd) - (acd + bcd)) * ((bc + ac + 1 + (r * b) + ad + bd + abcd + cd) - (a + b + (s * bc) + c + bcd + acd + d + (v * bd))) *
  ((bc + abcd) - ((s * bc) + bcd)) * ((bd + abcd) - ((v * bd) + bcd)))) = 1, 
((((ad + abcd) - ((v * bd) + acd)) * ((bc + ac + 1 + (r * b) + ad + bd + abcd + cd) - (a + b + (s * bc) + c + bcd + acd + d + (v * bd)))) /
 ((((v * bd) + d + acd + bcd) - (ad + bd + abcd + cd)) * (((s * bc) + a + (v * bd) + acd) - ((r * b) + ac + abcd + ad)))) = 1},
[ac, abcd, cd, acd, bcd, ad])

When this is pasted into Maple and executed, it produces the same solution as ANALYZE-PROBABILITY-STRUCTURE. Usually,
Maple is somewhat slower than ANALYZE-PROBABILITY-STRUCTURE, but occasionally it can solve problems that ANALYZE-
PROBABILITY-STRUCTURE cannot solve.

One can also try to solve the problems in Mathematica, but my experience is that Mathematica is rarely able to solve the
systems of equations. ANALYZE-PROBABILITY-STRUCTURE does much better.

In complex cases there may be no analytic characterization of the expectable values of the probabilities. This happens
when the set of simultaneous equations has no analytic solution. But it is still possible to generate that set of
equations and then solve them numerically. This is done by FIND-EXPECTABLE-VALUES in the file "Probability
structures.lisp".
|#


;; term-definitions is an a-list, not a list.
(defstruct (probability-structure (:print-function print-probability-structure) (:conc-name ps-))
    (name nil)
    (subsets nil)
    (constants nil)
    (constraints nil)  ;; a list of equalities, with the left term one of the terms
    (subset-constraints nil)
    (probability-constraints nil)
    (terms nil)
    (atoms nil)
    (term-characterizations nil)
    (log-term-characterizations nil)
    (term-definitions nil)   ;; this is an a-list
    (partition nil)
    (sample-args nil))

(defun print-probability-structure (x stream depth)
    (declare (ignore depth))
    (princ "#<probability-structure " stream) (princ (ps-name x) stream) (princ ">" stream))

(defun analyze-probability-structure
    (&key subsets name constraints probability-constraints constants subset-constraints display-infix display display-details
               (display-results t) display-terms (remove-u t) higher-order probability-queries independence-queries
               (parallel-term-characterizations t) (expand-defs t))
    (setf constraints
             (mapcar #'(lambda (x) (cond ((and (listp x) (eq (mem2 x) '=)) (cons (mem1 x) (mem3 x))) (t x)))
                              constraints))
    (let* ((partition (partition subsets))
              (terms (mapcar #'simplify (sublis constraints (mapcar #'card partition))))
              (variables0 (set-difference (term-atoms terms) (cons 'u constants)))
              (p-constraints 
                (mapcar #'(lambda (x) (compute-probability-constraint x constraints partition)) probability-constraints))
              (derivative-p-constraints (derivative-probability-constraints p-constraints variables0))
              (constraints0 constraints)
              (constraints00 (append constraints derivative-p-constraints))
              (variables00 (subset  #'(lambda (x) (not (assoc x constraints00))) variables0))
              (derivative-constraints
                (derivative-constraints
                  (derivative-subset-constraints (interpret-subset-constraints subset-constraints) partition)
                  variables00 constraints00)))
       (dolist (x (term-atoms terms)) (makunbound x))
       (dolist (x constants) (makunbound x))
       (setf constraints (append constraints0 derivative-p-constraints derivative-constraints))
       (setf terms (remove 0 (mapcar #'simplify (sublis derivative-constraints (sublis derivative-p-constraints terms)))))
       (let* ((atoms (term-atoms terms))
                 (F (set-difference atoms (mapcar #'partition-intersection (remove nil (powerset subsets)))))
                 (variables (set-difference atoms (cons 'u constants)))
                 (ps (make-probability-structure
                          :name (or (and name (read-from-string name)) (read-from-string (string (gensym "ps"))))
                          :subsets subsets
                          :constraints constraints
                          :probability-constraints probability-constraints
                          :subset-constraints subset-constraints
                          :terms (subst 1 'u terms)
                          :atoms (remove 'u (set-difference (term-atoms terms) constants))
                          :partition partition
                          :constants constants
                          )))
          (set (ps-name ps) ps)
          (setf *default-atom-values* (default-atom-values subsets F derivative-constraints))
          (setf *definitions* nil)
          (setf *term-characterizations* nil)
          (progn
              (terpri) (princ "(") (terpri)
              (princ "========================================================") (terpri)
              (princ "Dividing U into ") (princ (length subsets)) (princ " subsets ")
              (princ (concatenate 'string (list (coerce (car subsets) 'character))))
              (when (cdr subsets)
                   (dolist (x (cdr subsets)) (princ ",") (princ (concatenate 'string (list (coerce x 'character))))))
              (princ " whose cardinalities relative to U are ")
              (princ-list subsets) (princ ",")
              (when (or constraints constants) (terpri) (princ "if "))
              (when constraints (princ "the following constraints are satisfied:")
                           (dolist (x probability-constraints)
                               (terpri) (princ "     ") (print-probability-constraint x))
                           (dolist (x constraints0)
                               (terpri) (princ "     ") (princ (car x)) (princ " = ") (princ (if display-infix (convert-to-infix (cdr x)) (cdr x))))
                           (dolist (x subset-constraints)
                               (terpri) (princ "     ") (print-subset-constraint x subsets))
                           (when (or probability-constraints subset-constraints) (terpri) (princ "and hence")
                                        (dolist (x constraints)
                                            (terpri) (princ "     ") (princ (car x)) (princ " = ") (princ (cdr x))))
                           (terpri) (when constants (princ "and ")))
              (when constants
                   (princ "the values of ") (princ-list constants) (princ " are held constant,")
                   (when (or display display-details)
                        (terpri) (princ "then the term-set consisting of the cardinalities of the partition of U is:")
                        (terpri) (princ "    ") (if display-infix (princ "{") (princ "("))
                        (dolist (x terms)
                            (let ((xx (list '* (subst 1 'u x) 'u)))
                               (terpri) (princ "     ") (princ (if display-infix (convert-to-infix xx) xx))))
                        (terpri) (princ "    ") (if display-infix (princ "}") (princ ")"))
                        (when (not display-details) (terpri)
                                     (cond
                                       (parallel-term-characterizations
                                         (princ "and the following characterizations of the expectable values were found:"))
                                       (t (princ "and the following definitions of the expectable values were found:")))
                                     (terpri)))))
          (catch 'grounded
              (cond
                (parallel-term-characterizations
                  (let ((term-characterizations
                            (mapcar #'(lambda (x) (list x (term-characterization x terms display-details 0 display-infix))) variables)))
                     (setf *TC* term-characterizations)
                     (catch 'find-defs
                         (let ((defs (mapcar #'(lambda (x) (list (car x) (cdr x))) derivative-constraints)))
                            (find-defs-from-term-characterizations 
                              variables variables0 term-characterizations :display-infix display-infix :display-terms display-terms
                              :display display :display-details display-details :defs defs :higher-order higher-order :expand-defs expand-defs)))))
                (t
                  (let ((defs (mapcar #'(lambda (x) (list (car x) (cdr x))) derivative-constraints)))
                     (find-defs variables terms :display-infix display-infix :display-terms display-terms
                                        :display display :display-details display-details :defs defs :higher-order higher-order))))
              (when display-results
                   (display-definitions :variables variables0 :complexity nil :remove-u remove-u :display-infix display-infix)
                   (display-term-characterizations :variables variables0 :complexity nil :remove-u remove-u :display-infix display-infix)
                   (when (some #'(lambda (x) (> (tree-complexity x) 300)) *definitions*)
                        (display-definitions :variables variables0 :complexity 300 :remove-u remove-u :display-infix display-infix))
                   (when (some #'(lambda (x) (> (tree-complexity x) 300)) *term-characterizations*)
                        (display-term-characterizations :variables variables0 :complexity 300 :remove-u remove-u :display-infix display-infix))
                   (display-grounded-term-characterizations :variables variables0 :remove-u remove-u :display-infix display-infix)))
          (when display-results
               (display-grounded-definitions :variables variables0 :remove-u remove-u :display-infix display-infix))
          (terpri) (princ "========================================================")
          (when probability-queries
               (terpri) (princ "Reconstruing ") (princ-list subsets) (princ ", etc., as probabilities relative to U rather than as cardinalities, the")
               (terpri) (princ "following characterizations were found for the expectable values of the probabilities wanted:")
               (terpri) (princ "----------")
               (dolist (p (remove 'prob probability-queries))
                   (display-probability-definitions p ps display-infix))
               (terpri) (princ "========================================================"))
          (when independence-queries
               (display-independence-results independence-queries ps display-infix)
               (terpri) (princ "========================================================"))
          (setf (ps-term-characterizations ps) (subst 1 'u *term-characterizations*))
          (setf (ps-log-term-characterizations ps) 
                   (mapcar #'(lambda (x) (list (car x) (simple-log (mem2 x)))) (subst 1 'u *term-characterizations*)))
          (setf (ps-term-definitions ps) (subst 1 'u *definitions*))
          (dolist (td (ps-term-definitions ps))
              (setf (ps-atoms ps) (remove (car td) (ps-atoms ps)))
              (setf (ps-terms ps) (subst (mem2 td) (mem1 td) (ps-terms ps))))
          (when (ps-term-definitions ps)
               (setf (ps-terms ps) (mapcar #'(lambda (x) (simplify (expand-quotients x))) (ps-terms ps))))
          (terpri) (princ "These results are encoded in the probability structure ") (princ (ps-name ps))
          (terpri) (princ ")")          
          nil)))

;; This prints a list that can be pasted into Mathematica and evaluated
(defun print-defs-for-Mathematica (&optional (defs *definitions*))
    (terpri) (terpri)
    (princ "Clear[") (dolist (d defs) (princ (car d)) (princ ",")) (princ "u") (princ "];")
    (terpri)
    (dolist (d defs)
        (terpri) (princ (car d)) (princ " = ") (prin1 (convert-to-infix (mem2 d))) (princ ";"))
    (terpri) (princ "u = 1;")
    (terpri)
    (dolist (d defs)
        (terpri) (princ (car d)) (princ " = ") (princ "Simplify[") (princ (car d)) (princ "];"))
    (terpri) (terpri))

;; a prod1-function has the form (expt base ex)
(defun simplify-prod1-function (base ex)
    (setf base (factor base))
    (cond ((eq ex 1) base)
                ((eq ex 0) 1)
                ((eq ex -1)
                  (cond ((and (listp base) (eq (car base) '*))
                               (cons '* (mapcar #'(lambda (b) (list '/ 1 b)) (cdr base))))
                              (t (list '/ 1 base))))
                ((and (listp base) (eq (car base) '*))
                  (cons '* (mapcar #'(lambda (b) (list 'expt b ex)) (cdr base))))
                (t (list 'expt base ex))))

;; prod-functions have the form (expt x n) where x can
;; be a quotient.
(defun simplify-prod-function (x)
    (cond
      ((and (listp x) (eq (car x) 'expt))
        (let ((ex (mem3 x)) ;; we have already expanded quotients and simplified
                (base (mem2 x)))
           (cond
             ((and (listp base) (eq (car base) '/))
               (let ((prod1 (simplify-prod1-function (mem2 base) ex))
                       (prod2 (simplify-prod1-function (mem3 base) ex)))
                  (cond
                    ((eq (car prod1) '*)
                      (cond
                        ((eq (car prod2) '*)
                          (cons
                            '* (append
                                 (cdr prod1)
                                 (mapcar
                                   #'(lambda (y) 
                                         (cond
                                           ((listp y) (if (and (eq (car y) '/) (eq (mem2 y) 1))
                                                             (mem3 y)
                                                             (list '/ 1 y)))
                                           (t (list '/ 1 y))))
                                   (cdr prod2)))))
                        (t (cons '/ (cons prod2 (cdr prod1))))))
                    ((eq (car prod2) '*)
                      (cons
                        '* (cons
                             prod1
                             (mapcar
                               #'(lambda (y) 
                                     (cond
                                       ((listp y)
                                         (if (and (eq (car y) '/) (eq (mem2 y) 1))
                                            (mem3 y)
                                            (list '/ 1 y)))
                                       (t (list '/ 1 y))))
                               (cdr prod2)))))
                    (t (list '/ prod1 prod2)))))
             (t (simplify-prod1-function base ex)))))
      (t x)))

;; prod is a product of prod-functions
(defun simplify-prod (x)
    ; (progn (terpri) (princ "simplify-prod ") (setf xx x))
    (cond ((productp x)
                 (let ((product
                           (write-as-product
                             (combine-exponents0
                               (collect-multipliers
                                 (cdr (flatten-product (cons '* (mapcar #'simplify-prod-function (cdr x))))))))))
                    (cond ((productp product)
                                 (write-as-quotient
                                   (simplify
                                     (as-product 
                                       (mapcar
                                         #'(lambda (y)
                                               (cond ((and (listp y) (eq (car y) 'expt))
                                                            (list 'expt (mem2 y)
                                                                    (simplify 
                                                                      (expand-quotients (mem3 y)))))
                                                           (t y)))
                                         (cdr product))))))
                                (t product))))
                (t (simplify-prod-function x))))

(defun write-as-product (x)
    (cond ((and (listp x) (eq (car x) '/))
                 (as-product 
                   (append
                     (cond ((productp (mem2 x)) (cdr (mem2 x)))
                                 (t (list (mem2 x))))
                     (cond ((productp (mem3 x)) (mapcar #'invert (cdr (mem3 x))))
                                 (t (list (invert (mem3 x))))))))
                (t x)))

(defun invert (x)
    (cond ((and (listp x) (eq (car x) 'expt)) (list 'expt (mem2 x) (negate (mem3 x))))
                (t (list '/ 1 x))))

(defun write-as-quotient (x)
    (cond ((and (listp x) (eq (car x) '*))
                 (let ((num nil) (den nil))
                    (dolist (y (cdr x)) 
                        (cond ((and (listp y) (eq (car y) '/) (eq (mem2 y) 1)) (push (mem3 y) den))
                                    ((and (listp y) (eq (car y) 'expt) (integerp (mem3 y)) (< (mem3 y) 0))
                                      (push (list 'expt (mem2 y) (* (mem3 y) -1)) den))
                                    (t (push y num))))
                    (cond (den (list '/ (as-product num) (as-product den)))
                                (t x))))
                (t x)))

;; x is an atom occurring in terms. The term-function is the log of this.
(defun term-characterization (x terms &optional display-details (depth 0) display-infix)
    ; (progn (setf xx x tt terms))
    ;(when (eq x 'c) (setf tt terms) (break))
    (setf *repeated-exponents* nil)
    (let ((x-terms (subset #'(lambda (y) (occur* x y)) terms)))
       (cond
         (display-details
           (display-computation-of-term-characterization x x-terms depth display-infix))
         (t
           (simplify-prod
             (conditionally-flatten-product 
               (as-product
                 (mapcar 
                   #'(lambda (y)
                         (simplify-exponentiation
                           (list 'expt y 
                                   (factor-atoms
                                     (expand-quotients 
                                       (simplify-difference (list '- (subst (list '+ x '1) x y) y)))))))
                   x-terms))))))))

(defun display-computation-of-term-characterization (x x-terms depth display-infix)
    (terpri) (indent depth) (princ "The subset of terms in the term-set that contain ") (princ x) (princ " is:")
    (terpri) (blank-indent (+ depth 5)) (if display-infix (princ "{") (princ "("))
    (dolist (term x-terms)
        (let ((xx (list '* (subst 1 'u term) 'u)))
           (terpri) (blank-indent (+ depth 5)) (print-tree xx (+ depth 2) *default-line-length* nil display-infix)))
    (terpri) (blank-indent (+ depth 5)) (if display-infix (princ "}") (princ ")"))
    (terpri) (indent depth) (princ "The expectable-value of ") (princ x)
    (princ " is then the real-valued solution to the following equation:")
    (terpri) (indent depth) (princ "1 = ") 
    (let ((eq1 (cons '* (mapcar #'(lambda (y) (list 'expt y (list '- (subst (list '+ x '1) x y) y))) x-terms))))
       (print-tree (remove-u eq1) (+ depth 2) *default-line-length* nil display-infix)
       (let ((eq2
                 (cons '* (mapcar 
                                 #'(lambda (y)
                                       (list 'expt (mem2 y) (factor-atoms (expand-quotients (simplify-difference (mem3 y))))))
                                 (cdr eq1)))))
          (terpri) (indent depth) (princ "   = ")
          (print-tree (remove-u eq2) (+ depth 2) *default-line-length* nil display-infix)
          (let ((eq3 (conditionally-flatten-product (as-product (mapcar #'simplify-exponentiation (cdr eq2))))))
             (when (not (equal eq3 eq2))
                  (terpri) (indent depth) (princ "   = ")
                  (print-tree (remove-u eq3) (+ depth 2) *default-line-length* nil display-infix))
             (cond
               ((productp eq3)
                 (let ((eq4 (flatten-product (cons '* (mapcar #'simplify-prod-function (cdr eq3))))))
                    (when (not (equal eq3 eq4))
                         (terpri) (indent depth) (princ "   = ")
                         (print-tree (remove-u eq4) (+ depth 2) *default-line-length* nil display-infix))
                    (let ((eq5 (write-as-product (combine-exponents0 (collect-multipliers (cdr eq4))))))
                       (when (not (equal eq5 eq4))
                            (terpri) (indent depth) (princ "   = ")
                            (print-tree (remove-u eq5) (+ depth 2) *default-line-length* nil display-infix))
                       (cond
                         ((productp eq5)
                           (let ((eq6 (as-product 
                                              (mapcar
                                                #'(lambda (y)
                                                      (cond ((and (listp y) (eq (car y) 'expt))
                                                                   (list 'expt (mem2 y)
                                                                           (simplify 
                                                                             (expand-quotients (mem3 y)))))
                                                                  (t y)))
                                                (cdr eq5)))))
                              (when (not (equal eq5 eq6))
                                   (terpri) (indent depth) (princ "   = ")
                                   (print-tree (remove-u eq6) (+ depth 2) *default-line-length* nil display-infix))
                              (let ((eq7 (write-as-quotient (simplify eq6))))
                                 (when (not (equal eq7 eq6))
                                      (terpri) (indent depth) (princ "   = ")
                                      (print-tree (remove-u eq7) (+ depth 2) *default-line-length* nil display-infix))
                                 eq7)))
                         (t eq5)))))
               (t 
                 (let ((eq8 (simplify-prod-function eq3)))
                    (when (not (equal eq8 eq3))
                         (terpri) (indent depth) (princ "   = ")
                         (print-tree (remove-u eq8) (+ depth 2) *default-line-length* nil display-infix))
                    eq8)))))))

(defun conditionally-flatten-product (x)
    (if (productp x) (flatten-product x) x))

(defun order-quotient (x)
    (cond ((and (listp x) (eq (car x) '/))
                 (let ((num (mem2 x)) (den (mem3 x)))
                    (cond ((< (default-term-value num) 0) (list '/ (negate num) (negate den)))
                                (t (list '/ num den)))))
                (t x)))

#| Where def is produced by TERM-CHARACTERIZATION, this solves the equation
"def = 1" for term if that can be done by simple factorization. |#
(defun solve-for-term (term def &optional higher-order display-details depth display-infix)
    (when (and (listp def) (eq (car def) '/)
                          (or (atom (mem2 def))
                                (and (listp (mem2 def))
                                          (or (eq (car (mem2 def)) '+)
                                                (eq (car (mem2 def)) '-)
                                                (and (eq (car (mem2 def)) 'expt) (eq (mem3 (mem2 def)) 2)
                                                          (or (atom (mem2 (mem2 def)))
                                                                (and (listp (mem2 (mem2 def)))
                                                                          (or (eq (car (mem2 (mem2 def))) '+)
                                                                                (eq (car (mem2 (mem2 def))) '-)))))
                                                (and (eq (car (mem2 def)) '*) (<= (product-length (cdr (mem2 def)) term) 3)))))
                          (or (atom (mem3 def))
                                (and (listp (mem3 def))
                                          (or (eq (car (mem3 def)) '+)
                                                (eq (car (mem3 def)) '-)
                                                (and (eq (car (mem3 def)) 'expt) (eq (mem3 (mem3 def)) 2)
                                                          (or (atom (mem2 (mem3 def)))
                                                                (and (listp (mem2 (mem3 def)))
                                                                          (or (eq (car (mem2 (mem3 def))) '+)
                                                                                (eq (car (mem2 (mem3 def))) '-)))))
                                                (and (eq (car (mem3 def)) '*) (<= (product-length (cdr (mem3 def)) term) 3))))))
         (let ((equation (recover-equation term def)))
            (when equation
                 (multiple-value-bind
                      (solution higher-order-soln)
                      (solve-equation-for-term term equation higher-order)
                    (when display-details
                         (cond
                           (solution
                             (terpri) (indent depth) (princ "The preceding term-characterization for ") (princ term) (princ " simplifies to:")
                             (terpri) (indent (+ depth 2)) (print-tree (list equation '= 0) (+ depth 5) *default-line-length* nil display-infix)
                             (terpri) (indent depth) (princ "Solving for ") (princ term) (princ ":")
                             (terpri) (indent (+ depth 2)) (princ term) (princ " = ")
                             (print-tree solution (+ depth 7 (round (/ (length (explode (string term))) 1.5)))
                                                *default-line-length* nil display-infix))
                           (t (terpri) (indent depth) 
                               (princ "No solution was found for ") (princ term) (princ " in the preceding equation."))))
                    (values solution higher-order-soln))))))

#|
(defun solve-for-term (term def &optional higher-order display-details depth display-infix)
    (when (and (listp def) (eq (car def) '/)
                          (or (atom (mem2 def))
                                (and (listp (mem2 def))
                                          (or (eq (car (mem2 def)) '+)
                                                (eq (car (mem2 def)) '-)
                                                (and (eq (car (mem2 def)) 'expt) (eq (mem3 (mem2 def)) 2)
                                                          (or (atom (mem2 (mem2 def)))
                                                                (and (listp (mem2 (mem2 def)))
                                                                          (or (eq (car (mem2 (mem2 def))) '+)
                                                                                (eq (car (mem2 (mem2 def))) '-)))))
                                                (and (eq (car (mem2 def)) '*) (<= (product-length (cdr (mem2 def))) 3)))))
                          (or (atom (mem3 def))
                                (and (listp (mem3 def))
                                          (or (eq (car (mem3 def)) '+)
                                                (eq (car (mem3 def)) '-)
                                                (and (eq (car (mem3 def)) 'expt) (eq (mem3 (mem3 def)) 2)
                                                          (or (atom (mem2 (mem3 def)))
                                                                (and (listp (mem2 (mem3 def)))
                                                                          (or (eq (car (mem2 (mem3 def))) '+)
                                                                                (eq (car (mem2 (mem3 def))) '-)))))
                                                (and (eq (car (mem3 def)) '*) (<= (product-length (cdr (mem3 def))) 3))))))
         (let ((equation (recover-equation term def)))
            (when equation
                 (multiple-value-bind
                      (solution higher-order-soln)
                      (solve-equation-for-term term equation higher-order)
                    (when display-details
                         (cond
                           (solution
                             (terpri) (indent depth) (princ "The preceding term-characterization for ") (princ term) (princ " simplifies to:")
                             (terpri) (indent (+ depth 2)) (print-tree (list equation '= 0) (+ depth 5) *default-line-length* nil display-infix)
                             (terpri) (indent depth) (princ "Solving for ") (princ term) (princ ":")
                             (terpri) (indent (+ depth 2)) (princ term) (princ " = ")
                             (print-tree solution (+ depth 7 (round (/ (length (explode (string term))) 1.5)))
                                                *default-line-length* nil display-infix))
                           (t (terpri) (indent depth) 
                               (princ "No solution was found for ") (princ term) (princ " in the preceding equation."))))
                    (values solution higher-order-soln))))))

(defun product-length (x)
    (when (and (listp x) (eq (car x) '*)) (setf x (cdr x)))
    (cond ((atom x) 1)
                ((eq (car x) '+) 1)
                ((eq (car x) '-) 1)
                ((eq (car x) 'expt)
                  (cond ((and (integerp (mem3 x)) (> (mem3 x) 0)) (mem3 x))
                              (t 1)))
                (t (apply '+ (mapcar #'product-length x)))))
|#

#|
(defun solve-for-term (term def &optional higher-order display-details depth display-infix)
    (when (and (listp def) (eq (car def) '/)
                          (or (atom (mem2 def))
                                (and (listp (mem2 def))
                                          (or (eq (car (mem2 def)) '+)
                                                (eq (car (mem2 def)) '-)
                                                (and (eq (car (mem2 def)) 'expt) (eq (mem3 (mem2 def)) 2)
                                                          (or (atom (mem2 (mem2 def)))
                                                                (and (listp (mem2 (mem2 def)))
                                                                          (or (eq (car (mem2 (mem2 def))) '+)
                                                                                (eq (car (mem2 (mem2 def))) '-)))))
                                                (and (eq (car (mem2 def)) '*) (<= (product-length (cdr (mem2 def))) 3)))))
                          (or (atom (mem3 def))
                                (and (listp (mem3 def))
                                          (or (eq (car (mem3 def)) '+)
                                                (eq (car (mem3 def)) '-)
                                                (and (eq (car (mem3 def)) 'expt) (eq (mem3 (mem3 def)) 2)
                                                          (or (atom (mem2 (mem3 def)))
                                                                (and (listp (mem2 (mem3 def)))
                                                                          (or (eq (car (mem2 (mem3 def))) '+)
                                                                                (eq (car (mem2 (mem3 def))) '-)))))
                                                (and (eq (car (mem3 def)) '*) (<= (product-length (cdr (mem3 def))) 3))))))
         (let ((equation (recover-equation term def)))
            (when equation
                 (let ((solution (solve-equation-for-term term equation higher-order)))
                    (when display-details
                         (cond
                           (solution
                             (terpri) (indent depth) (princ "The preceding term-characterization for ") (princ term) (princ " simplifies to:")
                             (terpri) (indent (+ depth 2)) (print-tree (list equation '= 0) (+ depth 5) *default-line-length* nil display-infix)
                             (terpri) (indent depth) (princ "Solving for ") (princ term) (princ ":")
                             (terpri) (indent (+ depth 2)) (princ term) (princ " = ")
                             (print-tree solution (+ depth 7 (round (/ (length (explode (string term))) 1.5)))
                                                *default-line-length* nil display-infix))
                           (t (terpri) (indent depth) 
                               (princ "No solution was found for ") (princ term) (princ " in the preceding equation."))))
                    solution)))))
|#

(defun product-length (x term)
    (when (and (listp x) (eq (car x) '*)) (setf x (cdr x)))
    (cond ((and (not (eq term x)) (not (occur term x))) 0)
                ((atom x) 1)
                ((eq (car x) '+) 1)
                ((eq (car x) '-) 1)
                ((eq (car x) 'expt)
                  (cond ((and (integerp (mem3 x)) (> (mem3 x) 0)) (mem3 x))
                              (t 1)))
                (t (apply '+ (mapcar #'(lambda (y) (product-length y term)) x)))))

(defun recover-equation (term def)
    (let ((def* (expand-quotients def)) (left nil) (right nil))
       (cond ((eq (car def*) '/)
                    (setf right 
                             (cond
                               ((productp (mem3 def*)) (expand-product (mem3 def*)))
                               ((and (exponentiationp (mem3 def*)) (eq (mem3 (mem3 def*)) 2))
                                 (expand-product (list '* (mem2 (mem3 def*)) (mem2 (mem3 def*)))))
                               (t (d-simplify (mem3 def*)))))
                    (setf left
                             (cond
                               ((productp (mem2 def*)) (expand-product (mem2 def*)))
                               ((and (exponentiationp (mem2 def*)) (eq (mem3 (mem2 def*)) 2))
                                 (expand-product (list '* (mem2 (mem2 def*)) (mem2 (mem2 def*)))))
                               (t (d-simplify (mem2 def*))))))
                   ((eq (car def*) '*)
                     (dolist (x (cdr def*))
                         (cond ((and (listp x) (eq (car x) '/)) (push (mem3 x) right))
                                     (t (push x left))))
                     (setf right (remove-common-terms (expand-product right)))
                     (when (some #'(lambda (x) (and (listp x) (eq (car x) 'expt) (eq (mem2 x) term))) (mem2 right))
                          (return-from recover-equation nil))
                     (setf left (remove-common-terms (expand-product left)))
                     (when (some #'(lambda (x) (and (listp x) (eq (car x) 'expt) (eq (mem2 x) term))) (mem2 left))
                          (return-from recover-equation nil))
                     ))
       (let ((exp1 (remove-common-terms (list (mem1 left) (mem1 right)))))
          (when (some #'(lambda (x)
                                         (and (listp x)
                                                   (some #'(lambda (z) (and (listp z) (eq (car z) 'expt) (eq (mem2 z) term)
                                                                                                  (or (not (integerp (mem3 z))) (> (mem3 z) 2)))) x)))
                                    (mem2 exp1))
               (return-from recover-equation nil))
          (let ((exp2 (remove-common-terms (list (mem2 left) (mem2 right)))))
             (when (some #'(lambda (x)
                                            (and (listp x)
                                                      (some #'(lambda (z) (and (listp z) (eq (car z) 'expt) (eq (mem2 z) term)
                                                                                                     (or (not (integerp (mem2 z))) (> (mem2 z) 2)))) x)))
                                       (mem2 exp2))
                  (return-from recover-equation nil))
             (list '- (as-sum (append (mem1 exp2) (mem2 exp1)))
                     (as-sum (append (mem1 exp1) (mem2 exp2))))))))

;; equation is a term, and the equation we are solving is (equation = 0).
(defun solve-equation-for-term (term equation higher-order)
    (let ((a1 (subterm-for term equation)))
       (when a1
            (let* ((a1- (decrement-term-count term a1))
                      (a2 (subterm-for term a1-)))
               (cond
                 (a2
                   (when higher-order
                        (let* ((a2- (decrement-term-count term a2))
                                  (a3 (subterm-for term a2-)))
                           (cond
                             (a3
                               (let ((a3- (decrement-term-count term a3)))
                                  (when (not (occur* term a3-))
                                       (values
                                         (solve-cubic-equation
                                           a3-
                                           (subtract-terms a2- a3)
                                           (subtract-terms a1- a2)
                                           (subtract-terms equation a1)) t))))
                             (t
                               (when (not (occur* term a2-))
                                    (values
                                      (solve-quadratic-equation
                                        a2-
                                        (subtract-terms a1- a2)
                                        (subtract-terms equation a1)) t)))))))
                   (t (values
                        (solve-linear-equation
                          a1- (subtract-terms equation a1)) nil)))))))

(defun solve-linear-equation (a2 a1)
    (order-quotient (f-simplify-quotient (list '/ (negate a1) a2))))

(defun solve-quadratic-equation (a b c)
    (let* ((s1(list '/ (list '- (list '+ b (list 'expt (list '- (list 'expt b 2) (as-product (list 4 a c))) (list '/ 1 2))))
                          (simplify (as-product  (list 2 a)))))
              (val (default-term-value s1)))
       (cond ((and (realp s1) (<= 0 val) (<= val 1)) s1)
                   (t (list '/ (list '- (list 'expt (list '- (list 'expt b 2) (as-product (list 4 a c))) (list '/ 1 2)) b)
                              (simplify (as-product (list 2 a))))))))

#|
(defun solve-quadratic-equation (a b c)
    (list '/ (list '+/- (list '- b) (list 'expt (list '- (list 'expt b 2) (as-product (list 4 a c))) (list '/ 1 2)))
            (simplify (as-product  (list 2 a)))))
|#

(defun solve-cubic-equation (a b c d)
    `(-
       (+ (/ (* (expt 2 1/3) (- (* 3 ,a ,c) (expt ,b 2)))
               (* 3 ,a 
                   (expt (- (+ (* 9 ,a ,b ,c)
                                     (expt (+ (* 4 (expt (- (* 3 ,a ,c) (expt ,b 2)) 3))
                                                    (expt (- (* 9 ,a ,b ,c) (+ (* 2 (expt ,b 3)) (* 27 (expt ,a 2) ,d))) 2)
                                                    ) 1/2))
                                 (* 27 (expt ,a 2) ,d)
                                 (* 2 (expt ,b 3))
                                 ) 1/3)))
            (/ (expt
                 (- (+ (* 9 ,a ,b ,c)
                          (expt
                            (+ (* 4 (expt
                                          (- (* 3 ,a ,c) (expt ,b 2))
                                          3))
                                 (expt
                                   (- (* 9 ,a ,b ,c) (+ (* 2 (expt ,b 3)) (* 27 (expt ,a 2) ,d)))
                                   2))
                            1/2)
                          )
                     (+ (* 2 (expt ,b 3)) (* 27 ,d (expt ,a 2))))
                 1/3)
                (* 3 ,a (expt 2 1/3))))
       (/ ,b (* 3 ,a))))

(defun find-defs (variables terms &key display-infix (depth 0) defs display-terms
                                                          display display-details higher-order)
    ; (setf vv variables tt terms)
    ; (print terms) (break)
    (let ((more-defs-found nil)
            (term-characterizations nil))
       (dolist (x variables)
           (let ((term-characterization (term-characterization x terms display-details depth display-infix)))
              (multiple-value-bind
                   (def higher-order-soln)
                   (solve-for-term x term-characterization higher-order display-details depth display-infix)
                   (push (list x term-characterization) term-characterizations)
                   (when def
                        (when (and display (not display-details))
                             (terpri) (indent depth) (princ x) (princ " = ")
                             (print-tree def  (+ depth 4 (round (/ (length (explode (string x))) 1.5))) *default-line-length* nil display-infix))
                        (when higher-order-soln
                             (setf variables (remove x variables))
                             (push (list x def) defs)
                             (pushnew (list x def) *definitions* 
                                                        :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
                        (when (null higher-order-soln)
                             (setf more-defs-found t)
                             (let* ((variables* (remove x variables))
                                       (new-terms (subst def x terms))
                                       (terms* (mapcar #'(lambda (y) (simplify (factor-atoms (expand-quotients y))))
                                                                      new-terms)))
                                (when (and variables* display-details)
                                     (terpri) (indent depth)
                                     (princ "Substituting the preceding definition into the previous term-set produces the new term-set:")
                                     (terpri) (indent (+ depth 5)) (print-tree new-terms (+ depth 2) *default-line-length* nil display-infix)
                                     (terpri) (indent depth) (princ "This term-set simplifies to produce the following term-set:")
                                     (terpri) (indent (+ depth 5)) (print-tree terms* (+ depth 2) *default-line-length* nil display-infix))                                     
                                (when (and variables* (not display-details) display-terms display)
                                     (terpri) (indent depth)
                                     (princ "Substituting the preceding definition into the previous term-set produces the new term-set:")
                                     (terpri) (indent (+ depth 5)) (print-tree terms* (+ depth 2) *default-line-length* nil display-infix))
                                (find-defs variables* terms* :display-infix display-infix :depth (1+ depth) :higher-order higher-order
                                                   :defs (cons (list x def) defs) :display-terms display-terms :display display
                                                   :display-details display-details))
                             )))))
       (when (null more-defs-found)
            (when defs (pushnew (list (caar defs)
                                                             (factor-numbers (simplify-arithmetically (factor (mem2 (car defs)))))) *definitions* 
                                                     :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
            (setf *term-characterizations* 
                     (union term-characterizations *term-characterizations*
                                  :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
            (when (cdr defs)
                 (expand-defs defs (1+ depth) display-infix display display-details))
            (when (null variables) 
                 (cond (display-details
                             (terpri) (terpri) (princ "Grounded definitions of the expectable values were found for all the variables."))
                             (t (terpri) (princ "grounded definitions of the expectable values were found for all the variables.")))
                 (throw 'grounded nil))
            (when (or display display-details)
                 (dolist (x variables)
                     (terpri) (indent depth) (princ "No definition was found for ") (princ x)
                     (princ ", but the most probable value for ") (princ x)
                     (princ " is the real-valued solution to the following equation:")
                     (terpri) (indent (+ depth 5)) (princ "1 = ")
                     (print-tree (mem2 (assoc x term-characterizations)) (+ depth 5) *default-line-length* nil display-infix))))
       more-defs-found))

(defun find-defs-from-term-characterizations
    (variables variables0 term-characterizations &key display-infix (depth 0) defs display-terms
                       display display-details higher-order expand-defs)
   ; (when (equal variables '(bc)) (setf vv variables tt term-characterizations dd defs) (break))
    ;(setf vv variables tt term-characterizations dd defs)
    ;; (stepper (find-defs-from-term-characterizations vv tt :defs dd))
    (let ((more-defs-found nil))
       (dolist (x variables)
           (let ((term-characterization (cadr (assoc x term-characterizations))))
              ;(terpri )(princ (assoc x term-characterizations)) (break)
              (multiple-value-bind
                   (def higher-order-soln)
                   (solve-for-term x term-characterization higher-order display-details depth display-infix)
                   (when def
                        (when (and display (not display-details))
                             (terpri) (indent depth) (princ x) (princ " = ")
                             (print-tree def  (+ depth 4 (round (/ (length (explode (string x))) 1.5))) *default-line-length* nil display-infix))
                        (when higher-order-soln
                             (setf variables (remove x variables))
                             (push (list x def) defs)
                             (pushnew (list x def) *definitions* 
                                                        :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
                        (when (null higher-order-soln)
                             (setf more-defs-found t)
                             (let ((variables* (remove x variables)))
                                (when (and variables* display-details)
                                     (terpri) (indent depth)
                                     (princ "Substituting the preceding definition for ") (princ x)
                                     (princ " into the previous term-characterizations")
                                     (terpri) (indent depth) (princ "produces the new term-characterizations:")
                                     (dolist (tc term-characterizations)
                                         (when (not (eq (car tc) x))
                                              (terpri) (indent (+ depth 5)) (princ (car tc)) (princ ": 1 = ")
                                              (print-tree (subst def x (cadr tc)) (+ depth 10) *default-line-length* nil display-infix)))
                                     (terpri) (indent depth) 
                                     (princ "These term-characterizations simplify to yield the following term-characterizations:"))
                                (let ((new-term-characterizations
                                          (mapcar
                                            #'(lambda (tc) 
                                                  (let ((z (simplify (factor-atoms (expand-quotients (subst def x (cadr tc)))))))
                                                     (when display-details
                                                          (terpri) (indent (+ depth 5)) (princ (car tc)) (princ ": 1 = ")
                                                          (print-tree z (+ depth 10) *default-line-length* nil display-infix))
                                                     (list (car tc) z)))
                                            (remove (assoc x term-characterizations) term-characterizations))))
                                   (when (and variables* (not display-details) display-terms display)
                                        (terpri) (indent depth)
                                        (princ "Substituting the preceding definition for ") (princ x)
                                        (princ " into the previous term-characterizations produces the new term-characterizations:")
                                        (dolist (tc new-term-characterizations)
                                            (terpri) (indent (+ depth 5)) (princ (car tc)) (princ ": ")
                                            (print-tree (subst def x (cadr tc)) (+ depth 10) *default-line-length* nil display-infix)))
                                   (find-defs-from-term-characterizations variables* variables0 new-term-characterizations :display-infix display-infix 
                                                                                                         :depth (1+ depth) :higher-order higher-order :expand-defs expand-defs
                                                                                                         :defs (cons (list x def) defs) :display-terms display-terms
                                                                                                         :display display :display-details display-details))
                                ))))))
       (when (null more-defs-found)
           ; (break)
           ; (when defs (pushnew (factor (car defs)) *definitions* 
           ;                                          :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
            (setf *term-characterizations* 
                     (union term-characterizations *term-characterizations*
                                  :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
            (cond (expand-defs
                         (cond ((cdr defs) (expand-defs defs variables0 display-infix display display-details))
                                     (t (setf *definitions* defs))))
                        (t (setf *definitions* defs)))
            (when (null variables) 
                 (cond (display-details
                             (terpri) (terpri) (princ "Grounded definitions of the expectable values were found for all the variables."))
                             (t (terpri) (princ "grounded definitions of the expectable values were found for all the variables.")))
                 (throw 'grounded nil))
            (when (or display display-details)
                 (dolist (x variables)
                     (terpri) (indent depth) (princ "No definition was found for ") (princ x)
                     (princ ", but the most probable value for ") (princ x)
                     (princ " is the real-valued solution to the following equation:")
                     (terpri) (indent (+ depth 5)) (princ "1 = ")
                     (print-tree (cdr (assoc x term-characterizations)) (+ depth 5) *default-line-length* nil display-infix)))
            (throw 'find-defs nil))
       more-defs-found))

#|
(defun expand-defs (defs depth display-infix display display-details)
    ; (when (occur nil defs) (setf dd defs dp depth di display-infix) (break))
    ; (setf *defs* defs) (break)
    ;; (stepper (expand-defs dd dp di t t))
    (when (cdr defs)
         (let* ((def (car defs))
                   (atom (car def))
                   (def1 (mem2 defs))
                   (new-def0 (when (occur* atom (mem2 def1)) (subst* (cadr def) atom (mem2 def1))))
                   (new-def1 (when new-def0 
                                           (cond ((quotientp new-def0)
                                                        (f-simplify-quotient (expand-quotients new-def0)))
                                                       ((productp new-def0) (flatten-product new-def0))
                                                       (t (simplify new-def0))))))
            (cond (new-def1
                         (pushnew (list (car def1) (factor-numbers (simplify-arithmetically (factor new-def1)))) *definitions*
                                             :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y))))))
                        (t
                          (pushnew def1 *definitions*
                                              :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y)))))))
            (when new-def1
                 (when display-details
                      (terpri) (indent depth) (princ "Substituting the new definition for ") (princ atom)
                      (princ " into the previous definition for ") (princ (car def1)) (princ " produces:")
                      (terpri) (indent depth) (princ (car def1)) (princ " = ")
                      (print-tree (remove-u new-def0) (+ depth 4 (round (/ (length (explode (string atom))) 1.5)))
                                         *default-line-length* nil display-infix)
                      (when (not (term-equal new-def0 new-def1))
                           (terpri) (indent depth) (princ "which simplifies to:")
                           (terpri) (indent depth) (princ (car def1)) (princ " = ")
                           (print-tree (remove-u new-def1) (+ depth 4 (round (/ (length (explode (string atom))) 1.5)))
                                              *default-line-length* nil display-infix)))
                 (when (and display (not display-details))
                      (terpri) (indent depth) (princ (car def1)) (princ " = ")
                      (print-tree new-def1 (+ depth 4 (round (/ (length (explode (string atom))) 1.5)))
                                         *default-line-length* nil display-infix)))
            (let ((new-defs
                      (cons
                        (list (car def1) (or new-def1 (mem2 def1)))
                        (mapcar
                          #'(lambda (x) 
                                (let ((new-def0 (subst (cadr def) atom (mem2 x))))
                                   (list (car x) (cond ((quotientp new-def0)
                                                                    (f-simplify-quotient (expand-quotients new-def0)))
                                                                  ((productp new-def0) (flatten-product new-def0))
                                                                  (t (simplify new-def0))))))
                          (cddr defs)))))
               (when display-details
                    (let ((changed
                              (remove nil (mapcar #'(lambda (x y)
                                                                         (when (not (term-equal (mem2 x) (mem2 y))) (list x y)))
                                                                    (cddr defs) (cdr new-defs)))))
                       (when changed
                            (terpri) (indent depth)
                            (if (> (length changed) 1) (princ "The preceding definitions for ") (princ "The preceding definition for "))
                            (princ-list (mapcar #'caar changed))
                            (if (> (length changed) 1) (princ " then expand as follows:"))
                            (dolist (x changed)
                                (terpri) (indent depth) (princ (caar x)) (princ " = ")
                                (print-tree (remove-u (subst (cadr def) atom (mem2 (car x))))
                                                   (+ depth 4 (round (/ (length (explode (string atom))) 1.5)))
                                                   *default-line-length* nil display-infix))
                            (terpri) (indent depth)
                            (if (> (length changed) 1) (princ "and these simplify to:") (princ "and this simplifies to:"))
                            (dolist (x changed)
                                (terpri) (indent depth) (princ (car (mem2 x))) (princ " = ")
                                (print-tree (remove-u (mem2 (mem2 x)))
                                                   (+ depth 4 (round (/ (length (explode (string atom))) 1.5)))
                                                   *default-line-length* nil display-infix)))))
               (expand-defs new-defs depth display-infix display display-details)))))
|#

#| We were not taking advantage of what we know about the structure of the definitions that are 
being expanded and simplified. They are quotients whose denominators are factored, and 
whose numerators are sums or differences of products of atoms. We substitute for a particular 
atom another definition of this same form. So first we simplify the products, which are now 
products of atoms together with some power of such a definition. That is easy to simplify. 
We just check to see whether any of the atoms occur as terms in the product of the denominator 
of the definition being substituted in. We do this with expand-quotients-in-product-simply. 

Next we simplify the sum or difference comprising the numerator. We can do that in one 
operation. First we collect all the denominators resulting from expand-quotients-in-product-simply. 
For each term in the sum or product, we multiply by all denominators they do not have, expand 
the products, and simplify the sum or difference. The latter is simple as we just have a sum or 
difference of products of atoms.

The denominator is a product of sums or differences like the numerator, so we do the same 
thing to each term in the product. So we get a product of ratios of sums or differences and 
products of sums or differences. We see whether we can cancel denominators in the numerator 
and denominators in the denominator. Factor the numerators in the denominator, and cancel 
with the denominators in the denominator if possible. See if the numerator can be divided by 
any of the remaining numerators in the denominator, and eliminate those numerators that 
divide into the numerator. Add into the product of the numerators in the denominator the 
denominators we have accumulated from the numerator. Remaining denominators in the 
denominator must then be multiplied by the numerator, and the result simplified. 
|#

(defun expand-quotients-in-product-simply (x)
    (cond ((atom x) x)
                ((quotientp x) x)
                ((productp x)
                  (let ((simple nil)
                          (quotients nil)
                          (difs nil))
                     (dolist (y (cdr x))
                         (cond ((atom y) (push y simple))
                                     ((quotientp y) (push y quotients))
                                     ((and (exponentiationp y) (integerp (mem3 y)))
                                       (cond
                                         ((atom (mem2 y)) (dotimes (i (mem3 y)) (push (mem2 y) simple)))
                                         ((quotientp (mem2 y)) (dotimes (i (mem3 y)) (push (mem2 y) quotients)))
                                         (t (dotimes (i (mem3 y)) (push (mem2 y) difs)))))
                                     (t (push y difs))))  ;; sums or differences
                     (cond ((null quotients)
                                  (cond ((null difs) x)
                                              (t (let ((p (as-product (append simple difs))))
                                                    (cond ((productp p) (simplify (format-difference (expand-product p))))
                                                                (t p))))))
                                 (t (let ((den nil) (num nil))
                                       (dolist (y quotients)
                                           (push (mem2 y) num)
                                           (cond ((productp (mem3 y))
                                                        (dolist (z (cdr (mem3 y))) (push z den)))
                                                       (t (push (mem3 y) den))))
                                       (dolist (y simple)
                                           (dolist (z den)
                                               (when (eq y z)
                                                    (setf simple (remove y simple :count 1))
                                                    (setf den (remove z den :count 1)))))
                                       (let ((p (as-product (append simple difs num))))
                                          (when (productp p) (setf p (format-difference (expand-product p))))
                                          (as-quotient (simplify p) (as-product den))))))))
                ((and (exponentiationp x) (integerp (mem3 x)))
                  (let ((simple nil)
                          (quotients nil)
                          (difs nil))
                     (cond
                       ((atom (mem2 x)) (dotimes (i (mem3 x)) (push (mem2 x) simple)))
                       ((quotientp (mem2 x)) (dotimes (i (mem3 x)) (push (mem2 x) quotients)))
                       (t (dotimes (i (mem3 x)) (push (mem2 x) difs))))
                     (cond ((null quotients)
                                  (cond ((null difs) x)
                                              (t (let ((p (as-product (append simple difs))))
                                                    (cond ((productp p) (simplify (format-difference (expand-product p))))
                                                                (t p))))))
                                 (t (let ((den nil) (num nil))
                                       (dolist (y quotients)
                                           (push (mem2 y) num)
                                           (cond ((productp (mem3 y))
                                                        (dolist (z (cdr (mem3 y))) (push z den)))
                                                       (t (push (mem3 y) den))))
                                       (dolist (y simple)
                                           (dolist (z den)
                                               (when (eq y z)
                                                    (setf simple (remove y simple :count 1))
                                                    (setf den (remove z den :count 1)))))
                                       (let ((p (as-product (append simple difs num))))
                                          (when (productp p) (setf p (format-difference (expand-product p))))
                                          (as-quotient (simplify p) (as-product den))))))))
                ))

;; This is like set-difference, but repetitions get counted separately
(defun list-difference (X Y)
    (let ((Xdif nil) (Y* Y))
       (dolist (z X)
           (cond ((mem z Y*) (setf Y* (remove z Y* :count 1 :test 'equal)))
                       (t (push z Xdif))))
       Xdif))

(defun quotient-denominators (x)
    (when (quotientp x)
         (let ((den (mem3 x)))
            (cond ((productp den) (cdr den))
                        (t (list den))))))

(defun collect-denominators (x)
    (cond ((productp x) (quotient-denominators (expand-quotients-in-product-simply x)))
                ((sump x)
                  (let ((x* (mapcar #'(lambda (y) (quotient-denominators (expand-quotients-in-product-simply y))) (cdr x)))
                          (dens nil))
                     (dolist (y x*)
                         (when y (setf dens (append dens (list-difference y dens)))))
                     dens))
                ((differencep x)
                  (let ((den1 (collect-denominators (mem2 x)))
                          (den2 (collect-denominators (mem3 x))))
                  (append (list-difference den1 den2) den2)))))

;; x can be either a sum or difference of sums
(defun expand-quotients-in-difference-simply (x)
    (cond ((atom x) x)
                ((productp x) (expand-quotients-in-product-simply x))
                ((exponentiationp x)
                  (cond ((integerp (mem3 x))
                               (let ((prod nil))
                                  (dotimes (i (mem3 x)) (push (mem2 x) prod))
                                  (expand-quotients-in-product-simply (cons '* prod))))
                              (t x)))
                ((sump x)
                  (let* ((prods (mapcar #'(lambda (y) (expand-quotients-in-product-simply y)) (if (sump x) (cdr x) (list x))))
                            (x* (mapcar #'quotient-denominators prods))
                            (dens nil))
                     (dolist (y x*)
                         (when y (setf dens (append dens (list-difference y dens)))))
                     (cond (dens
                                  (let ((new-prods nil))
                                     (dolist (z prods)
                                         (cond ((quotientp z)
                                                      (cond ((productp (mem3 z))
                                                                   (let ((den (list-difference dens (cdr (expand-exponents (mem3 z))))))
                                                                      (cond (den (push (format-difference (expand-product (cons (mem2 z) den))) new-prods))
                                                                                  (t (push (mem2 z) new-prods)))))
                                                                  (t (let ((den (remove (mem3 z) dens :count 1 :test 'equal)))
                                                                      (cond (den (push (format-difference (expand-product (cons (mem3 z) den))) new-prods))
                                                                                  (t (push (mem2 z) new-prods)))))))
                                                     (t (push (format-difference (expand-product (cons z dens))) new-prods))))
                                     (list '/
                                             (simplify (cons '+ new-prods))
                                             (as-product dens))))
                                 (t x))))
                ((differencep x)
                  (let* ((prods1 (mapcar #'(lambda (y) (expand-quotients-in-product-simply y)) (if (sump (mem2 x)) (cdr (mem2 x)) (list (mem2 x)))))
                            (x1 (mapcar #'quotient-denominators prods1))
                            (prods2 (mapcar #'(lambda (y) (expand-quotients-in-product-simply y)) (if (sump (mem3 x)) (cdr (mem3 x)) (list (mem3 x)))))
                            (x2 (mapcar #'quotient-denominators prods2))
                            (dens nil))
                     (dolist (y x1)
                         (when y (setf dens (append dens (list-difference y dens)))))
                     (dolist (y x2)
                         (when y (setf dens (append dens (list-difference y dens)))))
                     (cond (dens
                                  (let ((new-prods1 nil) (new-prods2 nil))
                                     (dolist (z prods1)
                                         (cond ((quotientp z)
                                                      (cond ((productp (mem3 z))
                                                                   (let ((den (list-difference dens (cdr (expand-exponents (mem3 z))))))
                                                                      (cond (den (push (format-difference (expand-product (cons (mem2 z) den))) new-prods1))
                                                                                  (t (push (mem2 z) new-prods1)))))
                                                                  (t (let ((den (remove (mem3 z) dens :count 1 :test 'equal)))
                                                                      (cond (den (push (format-difference (expand-product (cons (mem2 z) den))) new-prods1))
                                                                                  (t (push (mem2 z) new-prods1)))))))
                                                     (t (push (format-difference (expand-product (cons z dens))) new-prods1))))
                                     (when prods2
                                          (dolist (z prods2)
                                              (cond ((quotientp z)
                                                           (cond ((productp (mem3 z))
                                                                   (let ((den (list-difference dens (cdr (expand-exponents (mem3 z))))))
                                                                      (cond (den (push (format-difference (expand-product (cons (mem2 z) den))) new-prods2))
                                                                                  (t (push (mem2 z) new-prods2)))))
                                                                  (t (let ((den (remove (mem3 z) dens :count 1 :test 'equal)))
                                                                      (cond (den (push (format-difference (expand-product (cons (mem2 z) den))) new-prods2))
                                                                                  (t (push (mem2 z) new-prods2)))))))
                                                          (t (push (format-difference (expand-product (cons z dens))) new-prods2)))))
                                     (list '/
                                             (simplify 
                                               (cond (new-prods2
                                                            (list '-
                                                                    (as-sum new-prods1)
                                                                    (as-sum new-prods2)))
                                                           (t (list '- (as-sum new-prods1)))))
                                             (as-product dens))))
                                 (t x))))))

;; x is a product of atoms and exponentiations of atoms
(defun expand-exponents (x)
    (let ((terms nil))
       (dolist (y (cdr x))
           (cond ((and (exponentiationp y) (integerp (mem3 y))) (dotimes (i (mem3 y)) (push (mem2 y) terms)))
                       (t (push y terms))))
       (cons '* terms)))

(defun expand-quotients-simply (x)
    (cond ((quotientp x)
                 (let ((nums nil) (dens nil)
                         (num (expand-quotients-in-difference-simply (mem2 x)))
                         (x-dens nil))
                    (cond ((quotientp num)
                                 (setf nums (list (mem2 num)))
                                 (cond ((productp (mem3 num)) (setf dens (cdr (mem3 num))))
                                             (t (setf dens (list (mem3 num))))))
                                (t (setf nums (list num))))
                    (cond ((productp (mem3 x))
                                 (setf x-dens (mapcar #'expand-quotients-in-difference-simply (cdr (mem3 x)))))
                                (t (setf x-dens (list (expand-quotients-in-difference-simply (mem3 x))))))
                    (dolist (y x-dens)
                        (cond ((quotientp y)
                                     (cond ((productp (mem2 y)) (setf dens (append dens (cdr (mem2 y)))))
                                                 (t (push (mem2 y) dens)))
                                     (cond ((productp (mem3 y)) (setf nums (append nums (cdr (mem3 y)))))
                                                 (t (push (mem3 y) nums))))
                                    ((productp y) (setf dens (append dens (cdr y))))
                                    (t (push y dens))))
                    (let ((new-num nil))
                       (dolist (z nums)
                           (cond ((member z dens) (setf dens (remove z nums :count 1 :test 'equal)))
                                       (t (push z new-num))))
                       (setf nums new-num))
                    (let ((new-den nil))
                       (dolist (y dens)
                           (let ((y* (factor y)))
                              (cond ((productp y*) (setf new-den (append new-den (cdr y*))))
                                          (t (push y new-den)))))
                       (setf dens new-den))
                    (divide-nums-by-dens nums dens)))
                (t (expand-quotients-in-difference-simply x))))

;; We have two lists. For each member y of the first list, we consider each member z of the second list and try 
;; to divide y by z. If that yields a non-nil d, replace y by d in the first list and delete z from the second list.  
;; Then go to the next member of the first list and repeat, until we have exhausted the first list.
(defun divide-nums-by-dens (nums dens) 
    (let ((new-nums nil))
       (loop
          (let ((y (car nums))
                  (new-dens dens)
                  (d nil))
             (loop
                (let ((z (car new-dens)))
                   (cond ((term-equal y z) (setf dens (remove z dens :count 1 :test 'equal)) (return))
                               ((setf d (divide-difference y z)) (setf y d) (setf dens (remove z dens :count 1 :test 'equal))))
                   (setf new-dens (cdr new-dens))
                   (when (null new-dens) (push y new-nums) (return))))
             (setf nums (cdr nums))
             (when (null nums) (return))))
       (when new-nums (setf new-nums (simplify (format-difference (expand-product new-nums)))))
       (cond (dens (as-quotient new-nums (as-product dens)))
                   (new-nums new-nums)
                   (t 1))))

(defun expand-defs (defs variables0 display-infix display display-details)
    (when display-details
         (terpri) (terpri) (princ"========================= EXPAND-DEFS ============================")
         (terpri) (princ "Thus far we have found the following definitions:")
         (dolist (def defs)
             (when (mem (car def) variables0)
                  (terpri) (princ (car def)) (princ " = ") (print-tree (mem2 def) 0 nil t display-infix))))
    (let ((new-defs nil))
       (dolist (d defs)
           (when (mem (car d) variables0) (push d new-defs)))
       (let ((expandees (list (car new-defs)))
               (expanders (cdr new-defs)))
          (loop
             (let ((expander (car expanders))
                     (new-expandees nil))
                (dolist (expandee expandees)
                    (cond ((occur* (car expander) (mem2 expandee))
                                 (when display-details
                                      (terpri) (terpri) (princ "Substituting the definition for ") (princ (car expander)) (princ " into the definition for ")
                                      (princ (car expandee)) (princ " and simplifying, produces:"))
                                 (let* ((new-def0 (subst* (mem2 expander) (car expander) (mem2 expandee)))
                                           (new-def1 
                                             (cond ((quotientp (mem2 expander))
                                                          ;(f-simplify-quotient (expand-quotients new-def0)))
                                                          (expand-quotients-simply new-def0))
                                                         (t (simplify new-def0)))))
                                    (when (or display display-details)
                                         (terpri) (princ (car expandee)) (princ " = ") (print-tree new-def1 0 nil t display-infix))
                                    (push (list (car expandee) new-def1) new-expandees)))
                                (t (push expandee new-expandees))))
                (push expander new-expandees)
                (setf expandees new-expandees)
                (setf expanders (cdr expanders))
                (when (null expanders) (return))))
          (setf *definitions*
                   (mapcar #'(lambda (expandee)
                                         (list (car expandee) (factor-numbers (simplify-arithmetically (factor (mem2 expandee))))))
                                    expandees)))))

(defun affected-defs (x defs)
    (let ((affected (subset #'(lambda (df) (occur* x (mem2 df))) defs)))
       (dolist (y affected)
           (setf affected (union affected (affected-defs (car y) defs))))
       affected))

(defun tree-length (tree)
    (let ((length
              (cond ((numberp tree) 1)
                          ((atom tree) (length (explode (string tree))))
                          ((listp tree) (+ 2 (apply '+ (mapcar #'tree-length tree)))))))
       (round (* 1.5 length))))

(defun print-tree (tree &optional (depth 0) (length *default-line-length*) (indent? t) display-infix)
    (declare (ignore length))
    (when display-infix (setf tree (convert-to-infix tree)))
    (cond (indent? (clear-indent depth) (prin1 tree))
                (t (prin1 tree)))
    nil)

(defun clear-indent (depth &optional stream)
    (dotimes (i depth) (princ "   " stream)))

#|
display-details: give full details of mathematical proof
display-terms: display term-sets as they are produced (mainly for debugging)
remove-u: replace the variable u with 1 (on by default)
higher-order: try to solve quadratic and cubic equations
parallel-term-characterizations: solve the term-characterizations in parallel rather than substituting solutions into
        the term-set and finding new term-characterizations from that. This makes the logic clearer, but it is slower.
|#

#| Maple is much better at solving systems of equations than is my LISP code. This writes an instruction
to be pasted into Maple for the purpose of solving for term-definitions. |#
(defun analyze-probability-structure-in-Maple (&key subsets constants constraints probability-constraints subset-constraints)
    (setf constraints
             (mapcar #'(lambda (x) (cond ((and (listp x) (eq (mem2 x) '=)) (cons (mem1 x) (mem3 x))) (t x)))
                              constraints))
    (let* ((partition (partition subsets))
              (terms (mapcar #'simplify (sublis constraints (mapcar #'card partition))))
              (variables0 (set-difference (term-atoms terms) (cons 'u constants)))
              (p-constraints 
                (mapcar #'(lambda (x) (compute-probability-constraint x constraints partition)) probability-constraints))
              (derivative-p-constraints (derivative-probability-constraints p-constraints variables0))
              (constraints0 constraints)
              (constraints00 (append constraints derivative-p-constraints))
              (variables00 (subset  #'(lambda (x) (not (assoc x constraints00))) variables0))
              (derivative-constraints
                (derivative-constraints
                  (derivative-subset-constraints (interpret-subset-constraints subset-constraints) partition)
                  variables00 constraints00)))
       (setf constraints (append constraints0 derivative-p-constraints derivative-constraints))
       (setf terms (remove 0 (mapcar #'simplify (sublis derivative-constraints (sublis derivative-p-constraints terms)))))
       (let* ((atoms (term-atoms terms))
                 (F (set-difference atoms (mapcar #'partition-intersection (remove nil (powerset subsets)))))
                 (variables (set-difference atoms (cons 'u constants))))
          (setf *default-atom-values* (default-atom-values subsets F derivative-constraints))
          (setf *definitions* nil)
          (setf *term-characterizations* (mapcar #'(lambda (x) (list x (remove-u (term-characterization x terms nil 0 t)))) variables))
          (progn
              (terpri) (princ "Analyze probability structure in Maple:")
              (terpri) (princ "   :subsets ") (princ (mapcar #'string subsets))
              (terpri) (princ "   :constants ") (princ constants)
              (when constraints
                   (terpri) (princ "   :constraints ")
                   (dolist (x constraints) (terpri) (princ "        ") (princ (car x)) (princ " = ") (princ (cdr x))))
              (when subset-constraints
                   (terpri) (princ "   :subset-constraints ")
                   (dolist (x subset-constraints) (terpri) (princ "        ") (princ x)))
              (when probability-constraints
                   (terpri) (princ "   :probability-constraints ") 
                   (dolist (x probability-constraints) (terpri) (princ "        ")
                                (print-complete-probability (mem2 x)) (princ " = ") (princ (mem4 x))))
              (terpri) (princ "The resulting term-characterizations are:")
              (dolist (x *term-characterizations*)
                  (terpri) (princ "     ") (princ (car x)) (princ ":  ")
                  (print-tree (mem2 x) (round (/ (length (explode (string (car x)))) 1.5)) *default-line-length* nil t)))
          (terpri) (princ "To find the term-definitions, execute the following instruction in Maple:")
          (terpri) (terpri)
          (princ "solve({")
          (princ (convert-to-infix (mem2 (mem1 *term-characterizations*)))) (princ " = 1")
          (dolist (x (cdr *term-characterizations*))
              (princ ", ") (terpri) (princ (convert-to-infix (mem2 x))) (princ " = 1"))
          (princ "},") (terpri) (princ "[")
          (princ-list (domain *term-characterizations*))
          (princ "])")
          (terpri) (terpri) nil)))

;; X is the set of atoms designating the starting subsets of U, and F is the set of atoms (f1, f2, etc) for probs.
(defun default-atom-values (X F derivative-constraints)
    (let ((default-values
                (cons (cons 'u 1)
                            (append
                              (mapcar #'(lambda (y) (cons y .4)) (remove 'u F))
                              (mapcar #'(lambda (y) (cons (partition-intersection y) (expt .5 (length y))))
                                               (remove nil (powerset X)))))))
       (dolist (dc derivative-constraints)
           (when (and (atom (cdr dc)) (not (numberp (cdr dc))))
                (let ((a (assoc (cdr dc) default-values))
                        (b (assoc (car dc) default-values)))
                   (when (< (cdr b) (cdr a)) (setf (cdr a) (cdr b))))))
       default-values))

;; X has the form (prob(P / Q) = r)
(defun compute-probability-constraint (X constraints partition)
    (let* ((P (mem1 (mem2 X))) (Q (mem3 (mem2 X))) (r (mem4 x))
              (p* (dnf-cardinality (dnf (reform-prob-formula (list P '& Q))) constraints partition))
              (q* (dnf-simple-cardinality (dnf (reform-prob-formula Q)) constraints partition)))
       (list p* '= (list '* r q*))))

(defun dnf-simple-cardinality (X constraints partition)
    (cond
      ((equal X '((u))) 'u)
      (t
        (simplify
          (as-sum
            (sublis constraints
                          (mapcar
                            #'card
                            (unionmapcar= #'(lambda (z) (subset #'(lambda (y) (subsetp z y :test '==)) partition)) X))))))))

;; p-constraints have the form (p = q).
(defun derivative-probability-constraints (p-constraints variables)
    (let ((PC p-constraints)
            (vars variables)
            (d-constraints nil))
       (loop
          (when (null PC) (return d-constraints))
          (let* ((x (car PC))
                    (var (find-if #'(lambda (y) (occur y x)) vars))
                    (d-constraint (cons var (simplify (solve-equation-for-term var (simplify (list '- (car x) (mem3 x))) nil)))))
             (setf d-constraints (cons d-constraint (mapcar #'(lambda (y) (cons (car y) (simplify (subst (cdr d-constraint) (car d-constraint) (cdr y)))))
                                                                                                  d-constraints)))
             (setf PC (cdr PC))
             (setf vars (remove (car d-constraint) vars))
             (setf PC (mapcar #'(lambda (y) (subst (cdr d-constraint) (car d-constraint) y)) PC))))))

#|
(defun derivative-probability-constraints (p-constraints variables)
    (mapcar
      #'(lambda (x) (solve-difference (simplify (list '- (mem1 x) (mem3 x))) variables))
      p-constraints))
|#

#| I will allow constraints of the form (X subset Y) where X and Y can involve unions, intersections, and
complements of the subsets. I will also allow constraints of the form (X = Y), where X and Y are as
above. The latter expands to the two constraints (X subset Y) and (Y subset X). (X subset Y) expands to
(DNF (X intersection (complement Y))) = nil, where DNF expands things into disjunctive normal form
(using union and intersection rather than disjunction and conjunction). |#

;; x is in infix notation
(defun drive-in-complement (x)
    (cond
      ((atom x) x)
      ((or (eq (car x) '-) (eq (car x) '~))
        (cond
          ((atom (mem2 x)) x)
          ((or (eq (car (mem2 x)) '-) (eq (car (mem2 x)) '~)) (mem2 (mem2 x)))
          ((or (eq (mem2 (mem2 x)) 'union) (eq (mem2 (mem2 x)) 'v))
            (list (drive-in-complement (list '- (car (mem2 x))))
                    'intersection (drive-in-complement (list '- (mem3 (mem2 x))))))
          ((or (eq (mem2 (mem2 x)) 'intersection) (eq (mem2 (mem2 x)) '&))
            (list (drive-in-complement (list '- (car (mem2 x))))
                    'union (drive-in-complement (list '- (mem3 (mem2 x))))))))
      ((or (eq (mem2 x) 'union) (eq (mem2 x) 'v))
        (list (drive-in-complement (car x)) 'union (drive-in-complement (mem3 x))))
      ((or (eq (mem2 x) 'intersection) (eq (mem2 x) '&))
        (list (drive-in-complement (car x)) 'intersection (drive-in-complement (mem3 x))))))

;; This assumes the complements have been driven in. This returns a list of lists of atoms and their complements.
(defun distribute-union (x)
    (cond ((atom x) (list (list x)))
                ((or (eq (car x) '-) (eq (car x) '~)) (list (list (list (mem2 x)))))
                ((or (eq (mem2 x) 'union) (eq (mem2 x) 'v))
                  (union (distribute-union (car x)) (distribute-union (mem3 x)) :test '==))
                ((or (eq (mem2 x) 'intersection) (eq (mem2 x) '&))
                  (cond
                    ((eq (mem1 x) 'u) (distribute-union (mem3 x)))
                    ((eq (mem3 x) 'u) (distribute-union (mem1 x)))
                    (t (mapcar #'(lambda (x) (union (mem1 x) (mem2 x) :test 'equal))
                                        (crossproduct (distribute-union (car x)) (distribute-union (mem3 x)))))))))

(defun DNF (x) (distribute-union (drive-in-complement x)))

;; partition is the partition produced by a list of atoms, and constraints is in dnf.
;; This returns a partition with any elements containing a constraint removed.
(defun impose-subset-constraints (constraints partition)
    (subset #'(lambda (x) (not (some #'(lambda (y) (subsetp y x :test 'equal)) constraints))) partition))

(defun interpret-subset-constraints (subset-constraints)
    (let ((dnf-constraints nil))
       (dolist (x subset-constraints)
           (cond ((or (eq (mem2 x) 'subset) (eq (mem2 x) 'subproperty))
                        (setf dnf-constraints (append dnf-constraints (DNF (list (car x) 'intersection (list '- (mem3 x)))))))
                       ((eq (mem2 x) '=)
                         (setf dnf-constraints
                                  (append dnf-constraints
                                                   (DNF (list (car x) 'intersection (list '- (mem3 x))))
                                                   (DNF (list (mem3 x) 'intersection (list '- (car x)))))))))
       dnf-constraints))

(defun derivative-subset-constraints (dnf-constraints partition)
    (subset #'(lambda (x) (some #'(lambda (y) (subsetp y x :test 'equal)) dnf-constraints)) partition))

;; This prints atoms in uppercase
(defun print-subset-constraint (x subsets)
    (princ (sublis
                 (mapcar #'(lambda (x) (cons x (concatenate 'string (list (coerce x 'character))))) subsets)
                 x)))

;; dif is a difference of two sums of atoms
(defun solve-difference (dif variables)
    (cond
      ((and dif (atom dif)) (cons dif 0))
      ((and (listp dif) (eq (car dif) '-))
         (let* ((dif* (simplified-form dif)) 
                   (var (find-if #'(lambda (x) (member x variables)) (mem1 dif*))))
            (cond
              (var (cons var (simplify (format-difference (list (mem2 dif*) (remove var (mem1 dif*)))))))
              (t (setf var (find-if #'(lambda (x) (member x variables)) (mem2 dif*)))
                  (when var
                       (cons var (simplify (format-difference (list (mem1 dif*) (remove var (mem2 dif*)))))))))))))

#|
;; dif is a difference of two sums of atoms
(defun solve-difference (dif variables)
    (when (and (listp dif) (eq (car dif) '-))
         (let* ((dif* (simplified-form dif)) 
                   (var (find-if #'(lambda (x) (member x variables)) (mem1 dif*))))
            (cond
              (var (cons var (simplify (format-difference (list (mem2 dif*) (remove var (mem1 dif*)))))))
              (t (setf var (find-if #'(lambda (x) (member x variables)) (mem2 dif*)))
                  (when var
                       (cons var (simplify (format-difference (list (mem1 dif*) (remove var (mem2 dif*))))))))))))
|#

;; This turns the subset constraints into ordinary constraints. Constraints0 is a list of ordinary constraints.
(defun derivative-constraints (constraints variables constraints0)
    (let* ((difs (mapcar #'card constraints))
              (dif (mem1 difs))
              (d-constraints nil)
              (extra-constraints nil))
       (loop
          (let ((dc (solve-difference (simplify dif) variables)))
             (cond
               (dc
                  (setf d-constraints 
                           (mapcar #'(lambda (x) 
                                                 (cons (car x) (sublis constraints0 (simplify (subst (cdr dc) (car dc) (cdr x))))))
                                            d-constraints))
                  (push (cons (car dc) (sublis constraints0 (cdr dc))) d-constraints)
                  (setf difs (cdr difs))
                  (when (null difs) (return (values d-constraints extra-constraints)))
                  (setf difs (subst (cdr dc) (car dc) difs))
                  (setf dif (car difs))
                  (setf variables (remove (car dc) variables)))
               (t 
                  (push (cons (car dc) (sublis constraints0 (cdr dc))) extra-constraints)
                  (setf difs (cdr difs))
                  (when (null difs) (return (values d-constraints extra-constraints)))
                  (setf dif (car difs))))))))

(defun simplify-arithmetically (x)
    (let ((val (ignore-errors (eval x))))
       (or val
             (cond
               ;((eq x 'u) 1)
               ((atom x) x)
               ((eq (car x) '+) 
                 (let* ((num (subset #'numberp (cdr x)))
                           (x* (mapcar #'simplify-arithmetically (set-difference (cdr x) num)))
                           (terms (remove-duplicates x* :test 'term-equal))
                           (collection (mapcar #'(lambda (y) (as-product (list (count y x* :test 'term-equal) y))) terms)))
                    (if num (as-sum (cons (apply '+ num) collection)) (as-sum collection))))
                 ;          (atoms (subset #'atom (cdr x)))
                 ;          (remainder (mapcar #'simplify-arithmetically (set-difference (set-difference (cdr x) atoms) num)))
                 ;          (collection (mapcar #'(lambda (y) (as-product (list (count y (cdr x))  y))) atoms)))
                 ;   (if num (as-sum (cons (apply '+ num) (append collection remainder))) (append collection remainder))))
                 ;;(as-sum (mapcar #'simplify-arithmetically (cdr x))))
               ((eq (car x) '-)
                 (cond ((mem3 x) (list '- (simplify-arithmetically (mem2 x)) (simplify-arithmetically (mem3 x))))
                             (t (list '- (simplify-arithmetically (mem2 x))))))
               ((eq (car x) '*)
                 (let* ((vals (mapcar #'simplify-arithmetically (cdr x)))
                           (nums (subset #'numberp vals)))
                    (cond
                      (nums
                        (let* ((non-nums (setdifference vals nums))
                                  (num (apply '* nums)))
                           (cond ((zerop num) 0)
                                       (non-nums
                                         (cond
                                           ((< num 0)
                                             (let ((z (find-if #'(lambda (y) (and (listp y) (eq (car y) '-) (null (mem3 y)))) non-nums)))
                                                (cond (z (as-product (cons (- num) (cons (mem2 z) (remove z non-nums)))))
                                                            (t (list '- (as-product (cons (- num) non-nums)))))))
                                           (t (as-product (cons num non-nums)))))
                                       (t num))))
                      (t (as-product vals)))))
               ((eq (car x) '/)
                 (let ((s1 (simplify-arithmetically (mem2 x)))
                         (s2 (simplify-arithmetically (mem3 x))))
                    (cond ((eq s2 1) s1)
                                ((and (numberp s2) (< s2 0)) (factor-numbers (list '/ (negate s1) (- s2))))
                                ((and (numberp s1) (< s1 0)) (factor-numbers (list '/ (- s1) (negate s2))))
                                ((and (listp s2) (eq (car s2) '-) (null (mem3 s2))) (factor-numbers (list '/ (negate s1) (mem2 s2))))
                                ((and (listp s1) (eq (car s1) '-) (null (mem3 s1))) (factor-numbers (list '/ (mem2 s1) (negate s2))))
                                (t (factor-numbers (list '/ s1 s2))))))
               ((eq (car x) 'expt)
                 (list 'expt (simplify-arithmetically (mem2 x)) (simplify-arithmetically (mem3 x))))))))

;; dif is a sum or difference of products or atoms, and the products may start with
;; a number, and the atom may be a number.
(defun divide-by-number (dif n)
    (cond
      ((atom dif)
        (when (numberp dif)
             (let ((div (/ dif n)))
                (when (integerp div) div))))
      ((eq (car dif) '*)
        (when (integerp (mem2 dif))
             (let ((div (/ (mem2 dif) n)))
                (when (integerp div)
                     (as-product (cons div (cddr dif)))))))
      ((eq (car dif) '+)
        (let ((div (mapcar #'(lambda (x) (divide-by-number x n)) (cdr dif))))
           (when (not (member nil div)) (as-sum div))))
      ((eq (car dif) '-)
        (cond
          ((mem3 dif)
            (let ((d1 (divide-by-number (mem2 dif) n))
                    (d2 (divide-by-number (mem3 dif) n)))
               (when (and d1 d2) (list '- d1 d2))))
          (t (let ((d (divide-by-number (mem2 dif) n)))
                (when d (list '- d))))))))

(defun factor-numbers (p)
    (cond
      ((atom p) p)
      ((eq (car p) '*)
        (let* ((p* (flatten-product+ (cons '* (mapcar #'factor-numbers (cdr p)))))
                  (numbers (subset #'integerp (cdr p*))))
           (cond
             (numbers (as-product
                                  (cons (eval (cons '* numbers)) (set-difference (cdr p*) numbers))))
             (t p))))
      ((eq (car p) '+)
        (let ((s1 (factor-numbers (mem2 p))))
           (cond
             ((and (productp s1) (integerp (mem2 s1)))
               (let ((n (mem2 s1))
                       (s p)
                       (coefficient nil))
                  (loop
                     (let* ((numbers (cdr (nseq n)))
                               (k (find-if
                                     #'(lambda (x)
                                           (and (integerp (/ n x))
                                                     (let ((s* (divide-by-number s x)))
                                                        (and s* (setf s s*))))) numbers)))
                        (cond (k (push k coefficient) (setf n (/ n k)))
                                    (t (return (as-product (list (eval (as-product coefficient)) s)))))))))
             (t p))))
      ((eq (car p) '-)
        (cond
          ((mem3 p)
            (let ((p1 (factor-numbers (mem2 p)))
                    (p2 (factor-numbers (mem3 p))))
           (cond
             ((and (productp p1) (integerp (mem2 p1))
                        (productp p2) (integerp (mem2 p2)))
               (let ((n (mem2 p1)) (m (mem2 p2))
                       (coefficient nil))
                  (loop
                     (let* ((numbers (cdr (nseq n)))
                               (k (find-if
                                     #'(lambda (x)
                                           (and (integerp (/ n x)) (integerp (/ m x)))) numbers)))
                        (cond (k (push k coefficient) (setf n (/ n k)) (setf m (/ m k)))
                                    (t (return
                                         (as-product
                                           (list (eval (as-product coefficient))
                                                       (list '- (as-product (cons n (cddr p1)))
                                                               (as-product (cons m (cddr p2)))))))))))))
             (t p))))
          (t (let ((p* (factor-numbers (mem2 p))))
                (cond ((and (productp p*) (integerp (mem2 p*)))
                             (list '* (mem2 p*) (list '- (as-product (cddr p*)))))
                            (t p))))))
      ((eq (car p) '/)
        (let ((den (factor-numbers (mem3 p))))
            (cond
              ((and (productp den) (integerp (mem2 den)))
                 (let ((n (mem2 den))
                         (num (mem2 p)))
                    (loop
                       (let* ((numbers (cdr (nseq n)))
                                 (k (find-if 
                                       #'(lambda (x)
                                             (and (integerp (/ n x))
                                                       (let ((num* (divide-by-number num x)))
                                                          (and num* (setf num num*))))) numbers)))
                          (cond (k (setf n k))
                                      (t (return (list '/ num (as-product (cons n (cddr den)))))))))))
              (t p))))))

(defun display-definitions (&key variable variables remove-u (complexity 300) display-infix)
    (when *definitions*
         (when (> (tree-complexity *definitions*) 500) (terpri) (princ "("))
         (terpri) (princ "----------------------------------------------------------------------------------------------")
         (terpri) 
         (cond (complexity (princ "The following short definitions of expectable values were found:"))
                     (t (princ "The following definitions of expectable values were found:")))
         (cond
           (variable
             (dolist (x *definitions*)
                 (when
                      (and (eq variable (car x)) (or (null complexity) (<= (tree-complexity x) complexity)))
                      (terpri) (princ (car x)) (princ " = ")
                      (print-tree (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))
                                         (round (/ (length (explode (string (car x)))) 1.5)) *default-line-length* nil display-infix))))
           (t (dolist (v variables)
                  (let ((defs (order
                                      (remove-duplicates
                                        (mapcar
                                          #'(lambda (x)
                                                (list (car x) (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))))
                                          (subset 
                                            #'(lambda (x)
                                                  (and (eq v (car x)) (or (null complexity) (<= (tree-complexity x) complexity))))
                                            *definitions*))
                                        :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y)))))
                                      #'(lambda (z w) (< (tree-complexity z) (tree-complexity w))))))
                     (when defs
                          (terpri) (princ "----------")
                          (dolist (x defs)
                              (terpri) (princ (car x)) (princ " = ")
                              (print-tree (mem2 x) (round (/ (length (explode (string (car x)))) 1.5))
                                                 *default-line-length* nil display-infix)))))))
         (when (> (tree-complexity *definitions*) 500) (terpri) (princ ")"))
         nil))

(defun display-grounded-definitions (&key variable variables remove-u display-infix)
   ; (setf vv variables)
    (when (some #'(lambda (x) (every #'(lambda (y) (not (occur* y (mem2 x)))) variables)) *definitions*)
         (when (> (tree-complexity *definitions*) 500) (terpri) (princ "("))
         (terpri) (princ "----------------------------------------------------------------------------------------------")
         (terpri) 
         (princ "The following definitions of expectable values were found that appeal only to the constants:")
         (cond
           (variable
             (dolist (x *definitions*)
                 (when
                      (and (eq variable (car x)) (every #'(lambda (y) (not (occur* y (mem2 x)))) variables))
                      (terpri) (princ (car x)) (princ " = ")
                      (print-tree (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))
                                         (round (/ (length (explode (string (car x)))) 1.5)) *default-line-length* nil display-infix))))
           (t (dolist (v variables)
                  (let ((defs (order
                                      (remove-duplicates
                                        (mapcar
                                          #'(lambda (x)
                                                (list (car x) (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))))
                                          (subset 
                                            #'(lambda (x)
                                                  (and (eq v (car x)) (every #'(lambda (y) (not (occur* y (mem2 x)))) variables)))
                                            *definitions*))
                                        :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y)))))
                                      #'(lambda (z w) (< (tree-complexity z) (tree-complexity w))))))
                     (when defs
                          (terpri) (princ "----------")
                          (dolist (x defs)
                              (terpri) (princ (car x)) (princ " = ")
                              (print-tree (mem2 x) (round (/ (length (explode (string (car x)))) 1.5))
                                                 *default-line-length* nil display-infix)))))))
         (when (> (tree-complexity *definitions*) 500) (terpri) (princ ")"))
         nil))

(defun list-definitions (variable &optional (infix nil))
    (let ((defs nil))
       (dolist (x *definitions*)
           (when (eq variable (car x))
                (if infix (push (convert-to-infix (mem2 x)) defs) (push x defs))))
       (when infix ;; this produces an instruction to be pasted into Mathematica
            (setf *print-pretty* nil)
            (setf *print-right-margin* nil)
            (unwind-protect 
                (progn (terpri) (princ "(Simplify[{") (princ (car defs))
                             (dolist (x (cdr defs)) (princ ",") (princ x)) (princ "}])") (terpri))
                (setf *print-right-margin* 250)
                (setf *print-pretty* t)))
       (when (null infix) defs)))

(defun display-term-characterizations (&key variable variables remove-u (complexity 300) display-infix)
    (when *term-characterizations*
         (when (> (tree-complexity *term-characterizations*) 500) (terpri) (princ "("))
         (terpri) (princ "----------------------------------------------------------------------------------------------")
         (terpri) 
         (cond (complexity (princ "The following short term-characterizations of expectable values were found:"))
                     (t (princ "The following term-characterizations were found:")))
         (cond
           (variable
             (dolist (x *term-characterizations*)
                 (when
                      (and (eq variable (car x)) (or (null complexity) (<= (tree-complexity x) complexity)))
                      (let ((indent (round (/ (length (explode (string (car x)))) 1.5))))
                         (terpri) (princ (car x)) (princ ": ")
                         (print-tree (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))
                                            indent *default-line-length* nil display-infix)
                         (terpri) (clear-indent (* 2 indent)) (princ "= 1")))))
           (t (dolist (v variables)
                  (let ((defs (order
                                      (remove-duplicates
                                        (mapcar
                                          #'(lambda (x)
                                                (list (car x) (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))))
                                          (subset 
                                            #'(lambda (x)
                                                  (and (eq v (car x)) (or (null complexity) (<= (tree-complexity x) complexity))))
                                            *term-characterizations*))
                                        :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y)))))
                                      #'(lambda (z w) (< (tree-complexity z) (tree-complexity w))))))
                     (when defs
                          (terpri) (princ "---------------------------------------------")
                          (dolist (x defs)
                              (let ((indent (round (/ (length (explode (string (car x)))) 1.5))))
                                 (terpri) (princ (car x)) (princ ": ")
                                 (print-tree (mem2 x) indent *default-line-length* nil display-infix)
                                 (terpri) (clear-indent (* 2 indent)) (princ "= 1"))))))))
         (when (> (tree-complexity *term-characterizations*) 500) (terpri) (princ ")"))
         nil))

(defun display-grounded-term-characterizations (&key variable variables remove-u (complexity 300) display-infix)
    (when (some #'(lambda (x) (every #'(lambda (y) (not (occur* y (mem2 x)))) variables)) *term-characterizations*)
         (when (> (tree-complexity *term-characterizations*) 500) (terpri) (princ "("))
         (terpri) (princ "----------------------------------------------------------------------------------------------")
         (terpri) 
         (cond (complexity
                      (princ "The following short term-characterizations of expectable values were found that appeal only to the constants:"))
                     (t (princ "The following term-characterizations of expectable values were found that appeal only to the constants:")))
         (cond
           (variable
             (dolist (x *term-characterizations*)
                 (when
                      (and (eq variable (car x)) (every #'(lambda (y) (not (occur* y (mem2 x)))) variables)
                                (or (null complexity) (<= (tree-complexity x) complexity)))
                      (let ((indent (round (/ (length (explode (string (car x)))) 1.5))))
                         (terpri) (princ (car x)) (princ ": ")
                         (print-tree (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))
                                            indent *default-line-length* nil display-infix)
                         (terpri) (clear-indent (* 2 indent)) (princ "= 1")))))
           (t (dolist (v variables)
                  (let ((defs (order
                                      (remove-duplicates
                                        (mapcar
                                          #'(lambda (x)
                                                (list (car x) (simplify (simplify-arithmetically (if remove-u (remove-u (mem2 x)) (mem2 x))))))
                                      (subset 
                                        #'(lambda (x)
                                              (and (eq v (car x)) (every #'(lambda (y) (not (occur* y (mem2 x)))) variables)
                                                        (or (null complexity) (<= (tree-complexity x) complexity))))
                                        *term-characterizations*))
                                        :test #'(lambda (x y) (and (eq (car x) (car y)) (term-equal (mem2 x) (mem2 y)))))
                                      #'(lambda (z w) (< (tree-complexity z) (tree-complexity w))))))
                     (when defs
                          (terpri) (princ "---------------------------------------------")
                          (dolist (x defs)
                              (let ((indent (round (/ (length (explode (string (car x)))) 1.5))))
                                 (terpri) (princ (car x)) (princ ": ")
                                 (print-tree (mem2 x) indent *default-line-length* nil display-infix)
                                 (terpri) (clear-indent (* 2 indent)) (princ "= 1"))))))))
         (when (> (tree-complexity *term-characterizations*) 500) (terpri) (princ ")"))
         nil))

(defun remove-u (x)
    (cond
      ((atom x) (if (eq x 'u) 1 x))
      ((eq (car x) '*) (as-product (mapcar #'remove-u (cdr x))))
      ((eq (car x) '/) (as-quotient (remove-u (mem2 x)) (remove-u (mem3 x))))
      ((eq (car x) '+) (as-sum (mapcar #'remove-u (cdr x))))
      ((eq (car x) '-)
        (cond ((mem3 x) (list '- (remove-u (mem2 x)) (remove-u (mem3 x))))
                    (t (list '- (remove-u (mem2 x))))))
      ((eq (car x) 'expt)
        (let ((x2 (remove-u (mem2 x))))
           (cond ((eq x2 1) 1)
                       (t (list 'expt x2 (remove-u (mem3 x)))))))))

(defun list-term-characterizations (variable &optional (infix nil))
    (let ((defs nil))
       (dolist (x *term-characterizations*)
           (when (eq variable (car x))
                (if infix (push (convert-to-infix (mem2 x)) defs) (push x defs))))
       (when infix ;; this produces an instruction to be pasted into Mathematica
            (setf *print-pretty* nil)
            (setf *print-right-margin* nil)
            (unwind-protect 
                (progn (terpri) (princ "(Simplify[{") (princ (car defs))
                             (dolist (x (cdr defs)) (princ ",") (princ x)) (princ "}])") (terpri))
                (setf *print-right-margin* 250)
                (setf *print-pretty* t)))
       (when (null infix) defs)))

(defun print-compactly (x)
    (setf *print-pretty* nil)
    (setf *print-right-margin* nil)
    (unwind-protect 
        (progn (terpri) (princ x) (terpri))
        (setf *print-right-margin* 250)
        (setf *print-pretty* t)))

(defun tree-complexity (tree)
    (cond ((null tree) 0)
                ((atom tree) 1)
                (t (+ (tree-complexity (car tree)) (tree-complexity (cdr tree))))))

(defun dnf-cardinality (X constraints partition)
    (cond
      ((equal X '((u))) 1)
      (t
        (simplify
          (as-sum
            (sublis constraints
                          (mapcar
                            #'card
                            (unionmapcar= #'(lambda (z) (subset #'(lambda (y) (subsetp z y :test '==)) partition)) X))))))))

#|
(defun probability-values (X constraints partition)
    (let* ((P (mem1 X)) (Q (mem3 X))
              (p* (dnf-cardinality (dnf (reform-prob-formula (list P '& Q))) constraints partition))
              (q* (dnf-cardinality (dnf (reform-prob-formula Q)) constraints partition))
              (vals nil)
              (atoms (union (term-atoms p*) (term-atoms q*)))
              (definitions
                  (gencrossproduct
                    (mapcar
                      #'(lambda (x) (let ((y (subset #'(lambda (d) (eq (car d) x)) *definitions*)))
                                                 (cond (y (mapcar #'(lambda (d) (cons (car d) (mem2 d))) y))
                                                             (t (list (list (cons x x)))))))
                      atoms))))
       (dolist (d definitions)
           (pushnew 
             (factor-numbers
               (simplify
                 (simplify-arithmetically
                   (factor (expand-quotients (simplify (remove-u (list '/ (sublis d p*) (sublis d q*)))))))))
             vals :test 'term-equal))
       (order vals #'(lambda (z w) (< (tree-complexity z) (tree-complexity w))))))
|#

(defun probability-values (X constraints partition)
    (let* ((P (mem1 X)) (Q (mem3 X))
              (p* (dnf-cardinality (dnf (reform-prob-formula (list P '& Q))) constraints partition))
              (q* (dnf-cardinality (dnf (reform-prob-formula Q)) constraints partition))
              (vals nil)
              (atoms (union (term-atoms p*) (term-atoms q*)))
              (definitions
                  (gencrossproduct
                    (mapcar
                      #'(lambda (x) (let ((y (subset #'(lambda (d) (eq (car d) x)) *definitions*)))
                                                ; (cond (y (cons (list (cons x x)) (mapcar #'(lambda (d) (cons (car d) (mem2 d))) y)))
                                                 (cond (y (mapcar #'(lambda (d) (cons (car d) (mem2 d))) y))
                                                             (t (list (list (cons x x)))))))
                      atoms))))
       (dolist (d definitions)
           (pushnew 
             (factor-numbers
               (simplify
                 (simplify-arithmetically
                   (factor (expand-quotients (simplify (remove-u (list '/ (sublis d p*) (sublis d q*)))))))))
             vals :test 'term-equal))
       (order vals #'(lambda (z w) (< (tree-complexity z) (tree-complexity w))))))

(defun statistically-independent (X constraints partition)
    (let ((A (mem1 X)) (B (mem2 X)) (C (mem3 X)) (ratios nil))
       (values
         (some
           #'(lambda (x)
                 (some
                   #'(lambda (y)
                         (some
                           #'(lambda (z) (let ((ratio (simplify (list '/ (list '* y z) x))))
                                                      (push ratio ratios)
                                                      (eq ratio 1)))
                           (probability-values (list B '/ C) constraints partition)))
                   (probability-values (list A '/ C) constraints partition)))
           (probability-values (list (list A '& B) '/ C) constraints partition))
         ratios)))

(defun display-independence-results (queries ps display-infix)
    (let* ((constraints (ps-constraints ps))
              (partition (ps-partition ps))
              (variables (ps-atoms ps))
              (results (mapcar #'(lambda (x) 
                                                 (multiple-value-bind
                                                      (independent ratios)
                                                      (statistically-independent x constraints partition)
                                                      (list x independent ratios)))
                                            queries)))
       (dolist (x results)
           (when (mem2 x)
                (terpri) (print-probability (mem1 (mem1 x))) (princ " and ") (print-probability (mem2 (mem1 x)))
                (princ " are STATISTICALLY INDEPENDENT  relative to ") (print-probability (mem3 (mem1 x)))))
       (dolist (x results)
           (when (null (mem2 x))
                (let ((ratios (mem3 x)))
                   (terpri) (terpri) (print-probability (mem1 (mem1 x))) (princ " and ") (print-probability (mem2 (mem1 x)))
                   (princ " were NOT proven to be statistically independent  relative to ") (print-probability (mem3 (mem1 x)))
                   (let ((g-ratio (find-if #'(lambda (x) (every #'(lambda (y) (not (occur* y x))) variables)) ratios)))
                      (cond (g-ratio
                                   (terpri) (princ "     ") (princ "(") (print-complete-probability (list (mem1 (mem1 x)) '/ (mem3 (mem1 x))))
                                   (princ " * ") (print-complete-probability (list (mem2 (mem1 x)) '/ (mem3 (mem1 x)))) (princ ") Ö ")
                                   (print-complete-probability (list (list (mem1 (mem1 x)) '& (mem2 (mem1 x))) '/ (mem3 (mem1 x))))
                                   (princ " = ") (terpri) (princ "          ")
                                   (print-tree g-ratio 2 *default-line-length* nil display-infix))
                                  (t
                                    (dolist (ratio ratios)
                                        (terpri) (princ "     ") (princ "(") (print-complete-probability (list (mem1 (mem1 x)) '/ (mem3 (mem1 x))))
                                        (princ " * ") (print-complete-probability (list (mem2 (mem1 x)) '/ (mem3 (mem1 x)))) (princ ") Ö ")
                                        (print-complete-probability (list (list (mem1 (mem1 x)) '& (mem2 (mem1 x))) '/ (mem3 (mem1 x))))
                                        (princ " = ") (terpri) (princ "          ")
                                        (print-tree ratio 2 *default-line-length* nil display-infix))))))))))

;; X is a list of two strings.

(defun display-probability-definitions (X ps display-infix)
    (let* ((constraints (ps-constraints ps))
              (partition (ps-partition ps))
              (variables (ps-atoms ps))
              (vals (probability-values X constraints partition))
              (g-val (find-if #'(lambda (x) (every #'(lambda (y) (not (occur* y x))) variables)) vals)))
       (cond (g-val
                    (terpri) (print-complete-probability X) (princ " = ")
                    (print-tree g-val (+ (tree-complexity X) 4) *default-line-length* nil display-infix))
                   (t
                     (dolist (v vals)
                         (terpri) (print-complete-probability X) (princ " = ")
                         (print-tree v (+ (tree-complexity X) 4) *default-line-length* nil display-infix))))
       (terpri) (princ "----------")))

;(defun print-probability (P)
;    (cond ((eq P '&) (princ " & "))
;                ((eq P 'v) (princ " v "))
;                ((eq P '/) (princ " / "))
;                ((eq P '~) (princ "~"))
;                ((atom P)
;                  (let ((P* (explode (string P))))
;                     (cond ((eq (car P*) "~") (princ "~") (dolist (x (cdr P*)) (princ (coerce x 'string))))
;                                 (t (dolist (x P*) (princ (coerce x 'string)))))))
;                ((listp P) (princ "(") (dolist (x P) (print-probability x)) (princ ")"))))

(defun print-probability (P)
    (cond ((eq P '&) (princ " & "))
                ((eq P 'v) (princ " v "))
                ((eq P '/) (princ " / "))
                ((eq P '~) (princ "~"))
                ((atom P)
                  (let ((P* (explode (string P))))
                     (cond ((eq (car P*) "~") (princ "~") (dolist (x (cdr P*)) (princ x)))
                                 (t (dolist (x P*) (princ x))))))
                ((listp P) (princ "(") (dolist (x P) (print-probability x)) (princ ")"))))

(defun print-complete-probability (P)
    (princ "prob") (print-probability P))

(defun reform-prob-formula (P)
    (cond ((eq P '&) 'intersection)
                ((eq P 'v) 'union)
                ((eq P '~) '-)
                ((atom P)
                  (let ((P* (explode (string P))))
                     (cond ((equal (car P*) "~") (list '- (read-from-string (cat-list (cdr P*)))))
                                 (t P))))
                ((eq (car P) '~) (list '- (reform-prob-formula (mem2 P)) (reform-prob-formula (mem3 P))
                                                   (cond ((eq (mem4 P) '~) (list '- (reform-prob-formula (mem5 P))))
                                                               (t (reform-prob-formula (mem4 P))))))
                (t (list (reform-prob-formula (mem1 P)) (reform-prob-formula (mem2 P))
                           (cond ((eq (mem3 P) '~) (list '- (reform-prob-formula (mem4 P))))
                                       (t (reform-prob-formula (mem3 P))))))))

(defun print-probability-constraint (x)
    (princ "prob") (print-probability (mem2 x))
    (princ " = ")
    (cond ((eq (mem4 x) 'prob) (princ "prob") (print-probability (mem5 x)))
                (t (princ (mem4 x)))))

;; ========================================================================
#|Given a set U, and n subsets, we can construct 2^n partitions. |#

;; Where X is a list of subsets of U, representing the complement of A as (A):
(defun partition (X)
    (let* ((A (car X))
              (partition (list (list A) (list (list A))))
              (atoms (cdr X)))
       (loop
          (when (null atoms) (return partition))
          (setf A (car atoms))
          (setf partition (unionmapcar= #'(lambda (p) (list (cons A p) (cons (list A) p))) partition))
          (setf atoms (cdr atoms)))))

#| Next we want an expression whose evaluation computes the cardinality of a partition in
terms of the cardinalities of intersections of atoms. Let (card p) be a function producing that expression. 
The basic idea is that (card '(A B C)) = abc, and (card '(A (B) C)) = (- (card '(A C)) (card '(A B C))). |#

(defun partition-intersection (p)
    (setf p (order p #'(lambda (x y) (char> (coerce x 'character) (coerce y 'character)))))
    (let ((int nil))
       (dolist (A p) (setf int (concatenate 'string (string A) int)))
       (read-from-string int)))

;; (partition-intersection '(c b a)) = 'abc.

(defun card (p)
    (cond ((null p) 'u)
                ((every #'atom p) (partition-intersection p))
                (t (let* ((A (find-if #'(lambda (x) (not (atom x))) p))
                             (p-A (remove-if-equal A p)))
                      (list '- (card p-A) (card (cons (car A) p-A)))))))

;; Where X is a list of atoms:
(defun prod-terms (X)
    (mapcar #'card (partition X)))

;; The value of var in vars, which is either (mem2 var) or (mem3 var), or the value of (mem3 var).
(defun variable-value (var vars)
    (cond ((numberp (mem3 var)) (mem3 var))
              ((mem3 var)
                (let ((var* (find-if #'(lambda (x) (eq (mem3 var) (car x))) vars)))
                  (variable-value var* vars)))
              (t (mem2 var))))

;; This adds the constraints built-into vars to var2.
(defun merge-guesses (vars vars2)
    (mapcar #'(lambda (x y)
                       (if (equal x y) x
                           (let ((m3 (mem3 x)))
                             (if m3 x y))))
                     vars vars2))

(defun princ-prob (r)
    (if (>= r .1)
      (princ (float (/ (round (* 10000 r)) 10000)))
      (princ (float (/ (round (* 100000 r)) 100000)))))

(defun Y (r s a) (/ (* r s (- 1 a)) (+ (* r s) (* a (- 1 r s)))))

(defun display-probability-structure (ps)
    (terpri) (princ "(") (princ "probability-structure ")
    (princ (ps-name ps))
    (terpri) (princ "	:subsets ") (princ (ps-subsets ps))
    (terpri) (princ "	:constants ") (princ (ps-constants ps))
    (terpri) (princ "	:constraints ") (p-print (ps-constraints ps) 10)
    (terpri) (princ "	:subset-constraints ") (p-print (ps-subset-constraints ps) 10)
    (terpri) (princ "	:probability-constraints ") (p-print (ps-probability-constraints ps) 10)
    (terpri) (princ "	:atoms ") (princ (ps-atoms ps))
    (terpri) (princ "	:terms ") (p-print (ps-terms ps) 10)
    (terpri) (princ "	:log-term-characterizations ") (p-print (ps-log-term-characterizations ps) 10)
    (terpri) (princ "	:term-definitions ") (p-print (ps-term-definitions ps) 10)
    (terpri) (princ "	:sample-args ") (princ (ps-sample-args ps))
    (princ ")") nil)

;; term-definitions is a list.
(defun build-probability-structure (&key name subsets constraints probability-constraints subset-constraints
                                                                                   constants term-characterizations term-definitions sample-args)
    (let* ((partition (partition subsets))
              (terms (mapcar #'simplify (subst 1 'u (sublis term-definitions (sublis constraints (mapcar #'card partition))))))
              ; (atoms (remove 'u (set-difference (term-atoms terms) constants)))
              (atoms (remove 'u (set-difference (term-atoms terms) constants)))
              (p-constraints 
                (mapcar #'(lambda (x) (compute-probability-constraint x constraints partition)) probability-constraints))
              (derivative-p-constraints (derivative-probability-constraints p-constraints atoms))
              (constraints00 (append constraints derivative-p-constraints)))
       (dolist (td term-definitions) (setf atoms (remove (car td) atoms)))
       (let ((ps (make-probability-structure
                        :name name
                        :subsets subsets
                        :constants constants
                        :constraints constraints00
                        :subset-constraints subset-constraints
                        :probability-constraints probability-constraints
                        :terms terms
                        :atoms atoms
                        :term-characterizations term-characterizations
                        :log-term-characterizations 
                        (mapcar #'(lambda (x) (list (car x) (simple-log (mem2 x)))) (subst 1 'u term-characterizations))
                        :term-definitions (mapcar #'(lambda (x) (cons (car x) (cadr x))) (subst 1 'u term-definitions))
                        :partition partition
                        :sample-args sample-args
                        ))
               (simple-name (read-from-string name)))
          (eval `(setf ,simple-name ,ps))
          (eval `(proclaim '(special ,simple-name))))))

(proclaim '(special *tc*))

;; This builds the probability-structure automatically, without trying to find term-definitions
(defun build-probability-structure-automatically (&key name subsets constraints probability-constraints 
                                                                                                             subset-constraints constants sample-args)
    (setf constraints
             (mapcar #'(lambda (x) (cond ((and (listp x) (eq (mem2 x) '=)) (cons (mem1 x) (mem3 x))) (t x)))
                              constraints))
    (let* ((partition (partition subsets))
              (terms (mapcar #'simplify (subst 1 'u (sublis constraints (mapcar #'card partition)))))
              (atoms (remove 'u (set-difference (term-atoms terms) constants)))
              (p-constraints 
                (mapcar #'(lambda (x) (compute-probability-constraint x constraints partition)) probability-constraints))
              (derivative-p-constraints (derivative-probability-constraints p-constraints atoms))
              (constraints0 constraints)
              (constraints00 (append constraints derivative-p-constraints))
              (variables00 (subset  #'(lambda (x) (not (assoc x constraints00))) atoms))
              (derivative-constraints
                (derivative-constraints
                  (derivative-subset-constraints (interpret-subset-constraints subset-constraints) partition)
                  variables00 constraints00)))
       (setf constraints (append constraints0 derivative-p-constraints derivative-constraints))
       (setf terms (remove 0 (mapcar #'simplify (sublis derivative-constraints (sublis derivative-p-constraints terms)))))
       (when (null sample-args)
            (setf sample-args
                     (append 
                       (mapcar #'(lambda (x) (default-constant-value x constraints00)) constants)
                       (mapcar
                         #'(lambda (x)
                               (list x (expt .5 (length (remove-if #'numberp (mapcar #'read-from-string (explode (string x))))))))
                         (setdifference (term-atoms terms) constants)))))
       (setf *default-atom-values*
                (default-atom-values subsets 
                    (set-difference (append constants atoms) (mapcar #'partition-intersection (remove nil (powerset subsets))))
                    derivative-constraints))
       (let* ((variables (subset #'(lambda (x) (not (assoc x constraints))) (set-difference atoms (cons 'u constants))))
                 (term-characterizations
                   (mapcar #'(lambda (x) (list x (term-characterization x terms nil 0 nil))) variables))
                 (ps (make-probability-structure
                          :name name
                          :subsets subsets
                          :constants constants
                          :constraints constraints00
                          :subset-constraints subset-constraints
                          :probability-constraints probability-constraints
                          :terms terms
                          :atoms atoms
                          :term-characterizations term-characterizations
                          :log-term-characterizations
                          (mapcar #'(lambda (x) (list (car x) (simple-log (mem2 x)))) (subst 1 'u term-characterizations))
                          :partition partition
                          :sample-args sample-args
                          ))
                 (simple-name (if name (read-from-string name))))
          (setf *tc* term-characterizations)
          (when name (eval `(setf ,simple-name ,ps)))
          ps)))

(defun default-constant-value (x constraints)
    (let ((c (find-if #'(lambda (y) (and (atom (mem1 y)) (eq (mem2 y) '*) (eq (mem3 y) x) (atom (mem4 y))))
                             constraints)))
       (cond (c (list x '= (expt .5 (- (length (explode (string (mem1 c)))) (length (explode (string (mem4 c))))))))
                   (t
                     (let ((c (find-if #'(lambda (y) (and (atom (mem1 y)) (eq (mem2 y) '/) (eq (mem4 y) x) (atom (mem3 y))))
                                           constraints)))
                        (cond (c (list x '= (expt .5 (- (length (explode (string (mem3 c)))) (length (explode (string (mem1 c))))))))
                                    (t (list x '= (expt .5 (length (remove-if #'numberp (mapcar #'read-from-string (explode (string x))))))))))))))

(defun simple-log (x)
    (cond ((atom x) (list 'log x))
                ((eq (car x) 'expt) (list '* (mem3 x) (simple-log (mem2 x))))
                ((eq (car x) '*) (cons '+ (mapcar #'simple-log (cdr x))))
                ((eq (car x) '/) (list '- (simple-log (mem2 x)) (simple-log (mem3 x))))
                (t (list 'log x))))

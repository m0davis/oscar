#| This is the syntax of a first-order language with function
symbols.  It uses '@ for undercutting defeaters. |#

(proclaim '(special *logical-constants* *pretty-list* *string-symbols* *constant-transformation*
                    *bracket-transformation* *reform-list*))

(defvar *string-symbols* nil)
(defvar *operators* nil)
(defvar *reform-list* nil)

;                 **********************   FORMULAS  ************************

(setq *logical-constants* (list '~ '& 'v '-> '<-> '@ 'all 'some '=))

(defun negationp (p)
  (and (listp p) (eq (mem1 p) '~)))

(defmacro negand (p)
  "When p is a negation, this returns the negated body"
  `(mem2 ,p))

(defun conjunctionp (p)
  (and (listp p) (eq (mem1 p) '&)))

(defmacro conjunct1 (p)
  "The first conjunct"
  `(mem2 ,p))

(defmacro conjunct2 (p)
  `(mem3 ,p))

(defun disjunctionp (p)
  (and (listp p) (eq (mem1 p) 'v)))

(defmacro disjunct1 (p)
  "The first disjunct"
  `(mem2 ,p))

(defmacro disjunct2 (p)
  `(mem3 ,p))

(defun conditionalp (p)
  (and (listp p) (eq (mem1 p) '->)))

(defmacro antecedent (p)
  `(mem2 ,p))

(defmacro consequent (p)
  `(mem3 ,p))

(defun biconditionalp (p)
  (and (listp p) (eq (mem1 p) '<->)))

(defmacro bicond1 (p)
  `(mem2 ,p))

(defmacro bicond2 (p)
  `(mem3 ,p))

(defun undercutterp (p)
  (and (listp p) (eq (mem1 p) '@)))

(defmacro undercut1 (p)
  `(mem2 ,p))

(defmacro undercut2 (p)
  `(mem3 ,p))

(defun identityp (p)
  (and (listp p)
       (eq (car p) '=)))

(defun iden1 (p)
  (mem2 p))

(defun iden2 (p)
  (mem3 p))

(defun subformula1 (p) (mem2 p))

(defun subformula2 (p) (mem3 p))

(defun predicationp (p)
  (and (listp p)
       (not (null (cdr p)))
       (symbolp (car p))
       (not (member (mem1 p) *logical-constants*))))

(defun arg-list (p) (cdr p))

(defun atomic-formula (p)
  (or
    (not (listp p))
    (not (member (mem1 p) (list '~ '& 'v '-> '<-> '@ 'all 'some)))))

(defun literal (p)
  (or (atomic-formula p)
      (and (negationp p) (atomic-formula (negand p)))))

(defun tilde (p) (list '~ p))

(defun neg (p)
  (cond ((negationp p) (mem2 p))
        (t (tilde p))))

(defun disj (p q) (list 'v p q))

(defun condit (p q) (list '-> p q))

(defun bicondit (p q) (list '<-> p q))

(defun conj (p q) (list '& p q))

(defun make-@ (p q) (list '@ p q))

(defun u-genp (p)
  (and (listp p) (eq (mem1 p) 'all)))

(defun e-genp (p)
  (and (listp p) (eq (mem1 p) 'some)))

(defun q-matrix (p) (mem3 p))

(defun quantifiers-matrix (p)
  (cond ((or (e-genp p) (u-genp p)) (quantifiers-matrix (mem3 p)))
        (t p)))

(defun q-variable (p) (mem2 p))

(defun u-gen (x p) (list 'all x p))

(defun e-gen (x p) (list 'some x p))

(defun iden (x y) (list '= x y))

(defun ?-genp (p)
  (and (listp p) (eq (mem1 p) '?) (cddr p)))

(defun whether-formula (P)
  (and (listp p) (eq (mem1 p) '?) (null (cddr p))))

;;*****************  SEQUENTS  *****************

(defun sequent-supposition (sequent)
  (mem1 sequent))

(defun sequent-formula (sequent)
  (mem2 sequent))

;;*****************  PRETTY FORMULAS  *****************

#|
(let ((P (gensym)) (Q (gensym)) (x (gensym)) (y (gensym)) (A (gensym)) (z (gensym)))
  (setf *reform-list*
        (list
          `((,P now) (at ,P now) (,P))
          `((,P at ,x) (at ,P ,x) (,P ,x))
          `((The probability of ,P given ,Q) (the-probability-of ,P ,Q) (,P ,Q))
          `((I  have a percept with content ,Q) (I-have-a-percept-with-content ,Q) (,Q))
          `((It appears to me that ,Q at ,x) (it-appears-to-me-that ,Q ,x) (,Q ,x))
          `((,x < ,y) (< ,x ,y) (,x ,y))
          `((,x <= ,y) (<= ,x ,y) (,x ,y))
          `((,x = ,y) (= ,x ,y) (,x ,y))
          `((,x is a reliable informant) (reliable-informant ,x) (,x))
          `((,x reports that ,P) (reports-that ,x ,P) (,x ,P))
          `((the color of ,x is ,y) (color-of ,x ,y) (,x ,y))
          `((,P when ,A is causally sufficient for ,Q after an interval ,x) (causally-sufficient ,P ,A ,Q ,x) (,P ,A ,Q ,x))
          `((,x and ,y collide) (collide ,x ,y) (,x ,y))
          `((the position of ,x is (,y ,z)) (position-of ,x ,y ,z) (,x ,y ,z))
          `((the velocity of ,x is (,y ,z)) (velocity-of ,x ,y ,z) (,x ,y ,z))
          `((,x is dead) (dead ,x) (,x))
          `((,x is alive) (alive ,x) (,x)))))
|#

(defun pretty-cons (x)
  (when x
    (cond ((listp x)
           (cond ((cdr x) (cons (pretty (car x)) (cons " " (pretty-cons (cdr x)))))
                 (t (list (pretty (car x))))))
          (t (list ". " (pretty x))))))


#| I want to use structures and conses as singular terms. |#
(defun pretty (p)
  (let ((p* nil))
    (cond ((stringp p) p)
          ((symbolp p) (convert-to-string p))
          ; ((identityp p) (imp (list "(" (pretty (iden1 p)) " = " (pretty (iden2 p)) ")")))
          ((negationp p) (imp (list "~" (pretty (negand p)))))
          ((u-genp p)
           (implode
             (list "(all" " " (convert-to-string (mem2 p))
                   ")" (pretty (mem3 p)))))
          ((e-genp p)
           (implode
             (list "(some" " " (convert-to-string (mem2 p))
                   ")" (pretty (mem3 p)))))
          ((?-genp p)
           (implode
             (list "(?" " " (convert-to-string (mem2 p))
                   ")" (pretty (mem3 p)))))
          ; ((and (listp p) (not (listp (cadr p)))) (write-to-string p))
          ((listp p)
           (let ((mem1 (mem1 p)))
             (cond
               ((eq mem1 'v)
                (imp (list "(" (pretty (mem2 P)) " " "v" " " (pretty (mem3 P)) ")")))
               ((eq mem1 '&)
                (imp (list "(" (pretty (mem2 P)) " " "&" " " (pretty (mem3 P)) ")")))
               ((eq mem1 '->)
                (imp (list "(" (pretty (mem2 P)) " " "->" " " (pretty (mem3 P)) ")")))
               ((eq mem1 '<->)
                (imp (list "(" (pretty (mem2 P)) " " "<->" " " (pretty (mem3 P)) ")")))
               ((eq mem1 '@)
                (imp (list "(" (pretty (mem2 P)) " " "@" " " (pretty (mem3 P)) ")")))
               ((eq mem1 '?) (imp (list "(? " (pretty (mem2 P)) ")")))
               ((eq mem1 'open) (imp (list "(" (pretty (mem2 P)) " " (pretty (mem3 P)) ")")))
               ((eq mem1 'closed) (imp (list "[" (pretty (mem2 P)) " " (pretty (mem3 P)) "]")))
               ((eq mem1 'clopen) (imp (list "(" (pretty (mem2 P)) " " (pretty (mem3 P)) "]")))
               ;;========================================================
               ((some #'(lambda (rf)
                          (let ((m (match (mem2 rf) P (mem3 rf))))
                            (when m
                              (when (listp m)
                                (setf m
                                      (mapcar
                                        #'(lambda (x) (if (consp x) (cons (car x) (pretty (cdr x))) (cdr x))) m)))
                              (setf P* (match-sublis m (mem1 rf))))))
                      *reform-list*)
                (remove-if-equal #\" (pretty P*)))
               ;;========================================================
               (t
                 (imp (cons "(" (append (pretty-cons p) (list ")"))))))))
          (t (write-to-string p))
          )))

(defun convert-to-string (s)
  (let ((string (get s 'pretty-form)))
    (or string (princ-to-string s))))

#| find-match, when applied to a list with "(" and ")", should return
a list of the initial segment up to the first unmatched ")" and the
remainder following the matching ")". |#

(defun find-match (s)
  (let ((number 1)
        (match nil)
        (rest s))
    (loop
      (cond ((null rest) (return nil))
            ((equal (car rest) "(") (incf number))
            ((equal (car rest) ")")
             (decf number)
             (cond ((equal number 0)
                    (return (list (reverse match) (cdr rest)))))))
      (setq match (cons (car rest) match))
      (setq rest (cdr rest)))))

#| This should convert a string of characters with " ", "(", and ")" in it
into a tree of words: |#
(defun parse (s variables)
  (let ((parse-list nil)
        (word-list nil)
        (rest s))
    (loop
      (cond ((or (equal (car rest) " ")
                 (equal (car rest) "
")
                 (equal (car rest) "	"))
                        (if word-list
                          (setq parse-list 
                                (cons (convert-to-symbol (implode (reverse word-list)) variables) parse-list)))
                        (setq rest (cdr rest))
                        (setq word-list nil))
                 ((equal (car rest) "(")
                  (let ((match (find-match (cdr rest))))
                    (setq parse-list (cons (parse (car match) variables) parse-list))
                    (setq rest (cadr match))))
                 ((equal (car rest) "~")
                  (setq parse-list (cons (car rest) parse-list))
                  (setq rest (cdr rest)))
                 (t (setq word-list (cons (car rest) word-list))
                    (setq rest (cdr rest))))
      (cond ((null rest)
             (if (null word-list) (return (reverse parse-list))
               (return (reverse (cons (convert-to-symbol (implode (reverse word-list)) variables)
                                      parse-list)))))))))

#| Uncommenting the following yields case-sensitivity.  However, that does not work with
def-backwards-reason and def-forwards-reason, because they read the premises and variables
as S-expressions rather than strings. The members of variables are not gensymed. |#
(defun convert-to-symbol (form variables)
  (cond ((mem form '("v" "&" "~" "->" "<->" "@" "all" "some" "?")) form)
        ((equal form "nil") nil)
        (t
          (let ((symbol* (read-from-string form)))
            (cond ((or (member symbol* variables) (not (symbolp symbol*))) symbol*)
                  (t
                    (let ((symbol (e-assoc form *string-symbols*)))
                      (when (null symbol)
                        (setf symbol symbol*)
                        (when (rassoc symbol *string-symbols*)
                          (setf symbol (gensym form)))
                        (when (symbolp symbol)
                          (setf (get symbol 'pretty-form) form))
                        (push (cons form symbol) *string-symbols*))
                      symbol)))))))

;This fixes the nesting of tildes and quantifiers (they are listed by rs):
(defun fix-nest (s)
  (cond ((or (symbolp s) (stringp s) (numberp s)) s)
        ((equal (length s) 1) (list (fix-nest (car s))))
        ((or (equal (car s) "~")
             (and (listp (car s))
                  (or (equal (caar s) "all")
                      (equal (caar s) "some")
                      (equal (caar s) "?"))))
         (cons (list (car s) (car (fix-nest (cdr s))))
               (cdr (fix-nest (cdr s)))))
        (t (cons (fix-nest (car s)) (fix-nest (cdr s))))))

(defun resolve-variable-conflicts (p &optional variables (reset-counter? t))
  (when reset-counter? (setf *gensym-counter* 1))
  (cond ((or (u-genp p) (e-genp p))
         (let ((var (q-variable p)))
           (cond ((mem var variables)
                  (let ((var* (gensym (string var))))
                    (list (mem1 p) var*
                          (=subst var* var
                                  (resolve-variable-conflicts (mem3 p) variables nil)))))
                 (t 
                   (list (mem1 p) var
                         (resolve-variable-conflicts (mem3 p) (cons var variables) nil))))))


        ((negationp p) (tilde (resolve-variable-conflicts (negand p) variables nil)))
        ((conjunctionp p)
         (conj (resolve-variable-conflicts (conjunct1 p) variables nil)
               (resolve-variable-conflicts (conjunct2 p) variables nil)))
        ((disjunctionp p)
         (disj (resolve-variable-conflicts (disjunct1 p) variables nil)
               (resolve-variable-conflicts (disjunct2 p) variables nil)))
        ((conditionalp p)
         (condit (resolve-variable-conflicts (antecedent p) variables nil)
                 (resolve-variable-conflicts (consequent p) variables nil)))
        ((biconditionalp p)
         (bicondit (resolve-variable-conflicts (bicond1 p) variables nil)
                   (resolve-variable-conflicts (bicond2 p) variables nil)))
        (t p)))

(setf *constant-transformation*
      '( ("all" . 'all) ("some" . 'some) ("&" . '&) ("v" . 'v)
                        ("->" . '->) ("<->" . '<->) ("@" . '@)))

(setf *bracket-transformation*
      '( ("[" . "(") ("]" . ")") ))

(defun reform- (s variables)
  (let ((form
          (fix-nest (parse (sublis= *bracket-transformation* (explode s)) variables))))
    (cond ((stringp form) form)
          ((equal (length form) 1) (car form))
          (t form))))

(defun reform (s &optional variables)
  (let ((s* (read-from-string s)))
    (cond ((and (listp s*) (equal (car s*) 'define)) s*)
          (t
            (resolve-variable-conflicts (convert-to-prefix-form (reform- s variables)))))))

(defun convert-to-prefix-form (P)
  (let ((P* nil))
    (cond ((listp P)
           (cond 
             ((equal (mem1 P) "~")
              (list '~ (convert-to-prefix-form (mem2 P))))
             ((equal (mem1 P) "?")
              (list '? (convert-to-prefix-form (mem2 P))))
             ((equal (mem1 P) "&")
              (gen-conjunction (mapcar #'convert-to-prefix-form (cdr P))))
             ((equal (mem1 P) "v")
              (gen-disjunction (mapcar #'convert-to-prefix-form (cdr P))))
             (t
               (let ((mem2 (mem2 p)))
                 (cond
                   ((equal mem2 "v")
                    (list 'v (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                   ((equal mem2 "&")
                    (list '& (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                   ((equal mem2 "->")
                    (list '-> (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                   ((equal mem2 "<->")
                    (list '<-> (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                   ((equal mem2 "@")
                    (list '@ (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))

                   ((equal mem2 '=)
                    (list '= (convert-to-prefix-form (mem1 P)) (convert-to-prefix-form (mem3 P))))
                   ;;========================================================
                   ((some
                      #'(lambda (rf)
                          (let ((m (match (mem1 rf) P (mem3 rf))))
                            (when m
                              (when (listp m)
                                (setf m
                                      (mapcar
                                        #'(lambda (x)
                                            (if (consp x)
                                              (cons (car x) (convert-to-prefix-form (cdr x)))
                                              (cdr x)))
                                        m)))
                              (setf P* (match-sublis m (mem2 rf))))))
                      *reform-list*)
                    P*)
                   ;;========================================================
                   ((listp (mem1 P))
                    (cond ((equal (mem1 (mem1 P)) "all")
                           (list 'all (mem2 (mem1 P)) (convert-to-prefix-form (mem2 P))))
                          ((equal (mem1 (mem1 P)) "some")
                           (list 'some (mem2 (mem1 P)) (convert-to-prefix-form (mem2 P))))
                          ((equal (mem1 (mem1 P)) "?")
                           (list '? (mem2 (mem1 P)) (convert-to-prefix-form (mem2 P))))
                          (t (mapcar #'convert-to-prefix-form P))))
                   (t (mapcar #'convert-to-prefix-form P)))))))
          (t P))))

(defun reform-if-string (p &optional variables)
  (if (stringp p) (reform p variables) p))


;;                              ******************  TERMS  ********************

#| the list of terms having unbound occurrences |#
(defun terms-of (p)
  (cond ((stringp p) nil)
        ((identityp p)
         (union= (constituent-terms-of (iden1 p))
                 (constituent-terms-of (iden2 p))))
        ((predicationp p)
         (remove-duplicates= (mapcan #'constituent-terms-of (arg-list p))))
        ((negationp p) (terms-of (negand p)))
        ((or (u-genp p) (e-genp p))
         (let ((x (q-variable p)))
           (subset #'(lambda (c) (and (not (occur x c)) (not (equal x c))))
                   (terms-of (q-matrix p)))))
        (t (union= (terms-of (subformula1 p)) (terms-of (subformula2 p))))))

#| the list of all terms occurring in p, bound or free. |#
(defun all-terms-of (p)
  (cond ((stringp p) nil)
        ((identityp p)
         (union= (constituent-terms-of (iden1 p))
                 (constituent-terms-of (iden2 p))))
        ((predicationp p)
         (remove-duplicates= (mapcan #'constituent-terms-of (arg-list p))))
        ((negationp p) (all-terms-of (negand p)))
        ((or (u-genp p) (e-genp p)) (all-terms-of (q-matrix p)))
        (t (union= (all-terms-of (subformula1 p)) (all-terms-of (subformula2 p))))))

#| this returns only terms serving as arguments of predications and identities
(not their subterms) |#
(defun arg-terms-of (p)
  (cond ((stringp p) nil)
        ((identityp p) (if (equal (iden1 p) (iden2 p)) (list (iden1 p))
                         (list (iden1 p) (iden2 p))))
        ((predicationp p) (remove-duplicates= (arg-list p)))
        ((negationp p) (arg-terms-of (negand p)))
        ((or (u-genp p) (e-genp p))
         (let ((x (q-variable p)))
           (subset #'(lambda (c) (and (not (occur x c)) (not (equal x c))))
                   (arg-terms-of (q-matrix p)))))
        (t (union= (arg-terms-of (subformula1 p)) (arg-terms-of (subformula2 p))))))

#| This is like arg-terms-of but does not delete repeated arguments |#
(defun arg-list-of (p)
  (cond ((stringp p) nil)
        ((identityp p) (if (equal (iden1 p) (iden2 p)) (list (iden1 p))
                         (list (iden1 p) (iden2 p))))
        ((predicationp p) (arg-list p))
        ((negationp p) (arg-list-of (negand p)))
        ((or (u-genp p) (e-genp p))
         (let ((x (q-variable p)))
           (subset #'(lambda (c) (and (not (occur x c)) (not (equal x c))))
                   (arg-list-of (q-matrix p)))))
        (t (append (arg-list-of (subformula1 p)) (arg-list-of (subformula2 p))))))

#| The constituent terms of a (possibly complex) term. |#
(defun constituent-terms-of (c)
  (cond ((stringp c) (list c))
        ((symbolp c) (list c))
        (t (cons c (remove-duplicates=
                     (unionmapcar #'constituent-terms-of (arg-list c)))))))

(defun NON-ATOMIC-SUBTERMS (x)
  (subset #'(lambda (y) (not (stringp y))) (constituent-terms-of x)))

(defun PROPER-SUBTERMS (x)
  (remove-if-equal x (constituent-terms-of x)))


;;                        ******************  VARIABLES  ********************
#| the variables in the initial universal quantifiers of p |#
(defun u-vars (p)
  (cond ((not (u-genp p)) nil)
        (t (cons (q-variable p) (u-vars (q-matrix p))))))

#| If p begins with a string of universal quantifiers, this returns the matrix |#
(defun u-matrix (p)
  (cond ((not (u-genp p)) p)
        (t (u-matrix (q-matrix p)))))

#| The universal closure of p with respect to the variables in X. |#
(defun u-closure (p X)
  (cond ((null X) p)
        (t (u-gen (mem1 X) (u-closure p (cdr X))))))

#| the variables in the initial existential quantifiers of p. |#
(defun e-vars (p)
  (cond ((not (e-genp p)) nil)
        (t (cons (q-variable p) (e-vars (q-matrix p))))))

#| If p begins with a string of existential quantifiers, this returns the
matrix. |#
(defun e-matrix (p)
  (cond ((not (e-genp p)) p)
        (t (e-matrix (q-matrix p)))))


;;       ***************  DISJUNCTIONS AND CONJUNCTIONS  ********************

;This returns the list of disjuncts of a long disjunction, or '(p) if p is
;not a disjunction:
(defun disjuncts (p)
  (cond ((disjunctionp p)
         (union= (disjuncts (mem2 p)) (disjuncts (mem3 p))))
        (t (list p))))

;This returns the list of conjuncts of a long conjunction, or '(p) if p is
;not a conjunction:
(defun conjuncts (p)
  (cond ((conjunctionp p)
         (union= (conjuncts (mem2 p)) (conjuncts (mem3 p))))
        (t (list p))))

;This conjoins a finite list of formulas, in order:
(defun gen-conjunction (X)
  (cond ((null X) nil)
        ((eq (length X) 1) (car X))
        (t (conj (car X) (gen-conjunction (cdr X))))))

;This disjoins a finite list of formulas, in order:
(defun gen-disjunction (X)
  (cond ((null X) nil)
        ((eq (length X) 1) (car X))
        (t (disj (car X) (gen-disjunction (cdr X))))))

;This differs from (disjuncts p) in that it lists redundant disjuncts:
(defun disjunct-list (p)
  (cond ((disjunctionp p)
         (append (disjunct-list (car p)) (disjunct-list (mem3 p))))
        (t (list p))))

(defun generalized-e-gen (variables P)
  (cond ((null variables) P)
        (t (e-gen (car variables) (generalized-e-gen (cdr variables) P)))))

#| x and y occur in the same atomic part of P. |#
(defun occurs-with (x y P)
  (cond
    ((conditionalp P) (or (occurs-with x y (antecedent P)) (occurs-with x y (consequent P))))
    ((biconditionalp P) (or (occurs-with x y (bicond1 P)) (occurs-with x y (bicond2 P))))
    ((disjunctionp P) (or (occurs-with x y (disjunct1 P)) (occurs-with x y (disjunct2 P))))
    ((conjunctionp P) (or (occurs-with x y (conjunct1 P)) (occurs-with x y (conjunct2 P))))
    ((negationp P) (occurs-with x y (negand P)))
    ((u-genp P) (occurs-with x y (u-matrix P)))
    ((e-genp P) (occurs-with x y (e-matrix P)))
    (t (and (occur x P) (occur y P)))))

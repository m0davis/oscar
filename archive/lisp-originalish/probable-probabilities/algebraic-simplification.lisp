#|								ARITHMETICAL SIMPLIFICATION

D-SIMPLIFY simplifies terms to the form ((t1 ... tn) (tm ... tk)), representing (- (+ t1 ... tn) (+ tm ... tk)) where the ti are atoms or products of atoms. 
Then SIMPLIFY converts them into standard form. |#

;; (d-simplify '(- (- (- (- de ade) (- bde abde)) (- (- cde acde) (- bcde abcde))) (- (- (- def adef) (- bdef abdef)) (- (- cdef acdef) (- bcdef abcdef)))))
;; (d-simplify '(- bcdef abcdef))
;; (d-simplify '(+ abcdef))

;; (expand-times (d-simplify '(- (+ ab c) abc d)) (d-simplify '(- (+ acd abc) cde ab)))
;; (simplify '(* (- (+ ab c) abc d) (- (+ acd abc) cde ab)))
;; (simplify '(- (* (- (+ ab (+ c 1)) abc d) (- (+ acd abc) cde ab)) (* (- (+ ab c) abc d) (- (+ acd abc) cde ab))))

(defun as-sum (x)
    (cond ((eq (car x) 'expt) x)
                ((cdr x) (cons '+ x))
                ((and (listp (car x)) (eq (mem1 (car x)) '*))
                  (let ((y (remove 1 (cdr (car x)))))
                     (cond ((cdr y) (cons '* y))
                                 (y y)
                                 (t 1))))
                (t (car x))))

#|
(defun as-product (x) 
    (cond ((atom x) x)
                ((eq (car x) 'expt) x)
                ((cdr x) (cons '* x))
                (t (car x))))
|#

(defun as-product (x) 
    (cond ((null x) 1)
                ((atom x) x)
                ((eq (car x) 'expt) x)
                ((cdr x)
                  (cond ((member 0 (cdr x)) 0)
                              (t
                                (let ((y (remove 1 x)))
                                   (cond ((cdr y) (cons '* y))
                                               (y (car y))
                                               (t 1))))))
                (t (car x))))

(defun as-product* (x) 
    (cond ((null x) 1)
                ((atom x) x)
                ((eq (car x) 'expt) x)
                ((cdr x)
                  (cond ((member 0 (cdr x)) 0)
                              (t
                                (let ((y (remove 1 x)))
                                   (cond ((cdr y) (combine-exponents (collect-multipliers y)))
                                               (y (car y))
                                               (t 1))))))
                (t (car x))))

(defun simplify (x &key (expand-times nil))
    (cond
      ((atom x) x)
      ((eq (car x) '-) (simplify-difference x))
      ((eq (car x) '+) (simplify-sum x))
      ((eq (car x) '*) (simplify-product x :expand-times expand-times))
      ((eq (car x) '/) (simplify-quotient x))
      ((eq (car x) 'expt) (simplify-exponentiation x :expand-times expand-times))))

#|
(defun a-simplify (x &key (expand-times nil))
    (cond ((atom x) x)
                (t (format-difference (d-simplify x :expand-times expand-times)))))
|#

(defun simplified-form (x)
    (cond ((atom x) (list (list x) nil))
                ((eq (car x) '+) (list (cdr x) nil))
                ((eq (car x) '-)
                  (cond ((null (mem3 x))
                               (cond ((atom (mem2 x)) (list nil (list (mem2 x))))
                                           ((eq (car (mem2 x)) '+) (list nil (cdr (mem2 x))))
                                           (t (list nil (list (mem2 x))))))
                              ((atom (mem3 x))
                                (cond ((atom (mem2 x)) (list (list (mem2 x)) (list (mem3 x))))
                                            ((eq (car (mem2 x)) '+) (list (cdr (mem2 x)) (list (mem3 x))))
                                            (t (list (list (mem2 x)) (list (mem3 x))))))
                              ((eq (car (mem3 x)) '+)
                                (cond ((atom (mem2 x)) (list (list (mem2 x)) (cdr (mem3 x))))
                                            ((eq (car (mem2 x)) '+) (list (cdr (mem2 x)) (cdr (mem3 x))))
                                            (t (list (list (mem2 x)) (cdr (mem3 x))))))
                              (t (cond ((atom (mem2 x)) (list (list (mem2 x)) (list (mem3 x))))
                                             ((eq (car (mem2 x)) '+) (list (cdr (mem2 x)) (list (mem3 x))))
                                             (t (list (list (mem2 x)) (list (mem3 x))))))))))

;; x is a simplified term
(defun format-difference (x)
    (cond
      ((mem1 x)
        (cond ((mem2 x) (list '- (as-sum (mem1 x)) (as-sum (mem2 x))))
                    (t (as-sum (mem1 x)))))
      ((mem2 x) (list '- (as-sum (mem2 x))))
     ; ((mem2 x) (negate (as-sum (mem2 x))))
      (t 0)))

#| D-SIMPLIFY leaves sums and differences in normal form. SIMPLIFY converts them into LISP terms. |#
(defun d-simplify (x &key (expand-times nil))
    (cond
      ((atom x) (list (list x) nil))
      ((eq (car x) '-) (d-simplify-difference x))
      ((eq (car x) '+) (d-simplify-sum x))
      ((eq (car x) '*) (d-simplify-product x :expand-times expand-times))
      ((eq (car x) '/) (d-simplify-quotient x))
      ((eq (car x) 'expt) (d-simplify-exponentiation x :expand-times expand-times))))

(defun d-simplify-difference (x)
    (when (eq (car x) '-) (setf x (cdr x)))
    (cond ((cdr x)
                 (let* ((x2 (d-simplify (mem1 x) :expand-times t))
                          ; (x3 (if (cddr x) (d-simplify-sum (cdr x))
                          ;            (d-simplify (cadr x) :expand-times t)))
                           (x3 (d-simplify (cadr x) :expand-times t))
                           (x+ (append (mem1 x2) (mem2 x3)))
                           (x- (append (mem2 x2) (mem1 x3))))
                    (let ((x+0 nil))
                       (dolist (y x+)
                           (block x+
                               (dolist (z x-)
                                   (when (=== y z) (setf x- (remove z x- :count 1)) (return-from x+ nil)))
                               (push y x+0)))
                       (setf x+ x+0))
                    (cond ((equal x- (list 0)) (list x+ nil))
                                ((equal x+ (list 0)) (list nil x-))
                                (t (list x+ x-)))))
                (t (let ((d (d-simplify (mem1 x) :expand-times t)))
                      (list (mem2 d) (mem1 d))))))

(defun simplify-difference (x)
    (format-difference (d-simplify-difference x)))

;; x and y are in simplified form
(defun compute-simplified-difference (x y)
    (let* ((x+ (append (mem1 x) (mem2 y)))
              (x- (append (mem2 x) (mem1 y))))
       (let ((x+0 nil))
          (dolist (y x+)
              (block x+
                  (dolist (z x-)
                      (when (=== y z) (setf x- (remove z x- :count 1)) (return-from x+ nil)))
                  (push y x+0)))
          (setf x+ x+0))
       (list x+ x-)))

(defun d-simplify-sum (x)
    (when (eq (car x) '+) (setf x (cdr x)))
    (setf x (remove 0 x))
    (cond ((null x) (list (list 0) nil))
                ((cdr x)
                 (let ((c (mapcar #'(lambda (z) (d-simplify z :expand-times t)) x))
                         (x+ nil)
                         (x- nil))
                    (dolist (y c)
                        (setf x+ (append (car y) x+))
                        (setf x- (append (cadr y) x-)))
                    (let ((x+0 nil))
                       (dolist (y x+)
                           (block x+
                               (dolist (z x-)
                                   (when (=== y z) (setf x- (remove z x- :count 1)) (return-from x+ nil)))
                               (push y x+0)))
                       (setf x+ x+0))
                    (list x+ x-)))
                (t (d-simplify (car x) :expand-times t))))

(defun simplify-sum (x)
    (format-difference (d-simplify-sum x)))

;; w is a pair (a b). This removes common terms in the two parts of a difference
;; if it encounters an exponent of the term no-exponent, it throws to SOLVE-FOR-TERM.
(defun remove-common-terms (w &key (no-exponents nil))
    (let ((a (car w)) (b (mem2 w)) (x nil))
       (dolist (y a)
           (block x
               (dolist (z b)
                   (when (=== y z) (setf b (remove z b :count 1)) (return-from x nil)))
               (when (and (listp y)
                                     (some #'(lambda (z) (and (listp z) (eq (car z) 'expt) (eq (mem2 z) no-exponents))) y))
                    (throw 'no-exponents nil))
               (push y x)))
       (list x b)))

(defun d-simplify-product (x &key expand-times)
    (when (member 0 (cdr x)) (return-from d-simplify-product (list '(0) nil)))
    (setf x (remove 1 x))
    (when (mem '(- 1) (cdr x))
         (setf x (remove '(- 1) x :test 'equal))
         (cond ((cdr x) (setf x (negate x)))
                     (t (return-from d-simplify-product (list nil '(1))))))
    (let ((w (find-if #'(lambda (y) (and (listp y) (eq (car y) 'expt) (eq (mem2 y) (- 1)) (numberp (mem3 y))))
                              (cdr x))))
       (cond ((and w (evenp (mem3 w))) (setf x (remove w x :test 'equal)))
                   (w (setf x (remove w x :test 'equal))
                         (setf x (cons '* (cons (negate (mem2 x)) (cddr x)))))))
    (cond ((null (cdr x)) 1)
                ((cddr x)
                  (cond ((every #'atom x) (list (list x) nil))
                              (expand-times (expand-product (cdr x)))
                              (t (list (list (cons '* (mapcar #'(lambda (z) (simplify z)) (cdr x)))) nil))))
                (t (d-simplify (mem2 x)))))

(defun simplify-product (x &key expand-times)
    (format-difference (d-simplify-product x :expand-times expand-times)))

(defun negate (x)
    (cond ((eq x 0) 0)
                ((atom x) (list '- x))
                ((eq (car x) '-)
                  (cond
                    ((mem3 x) (list '- (mem3 x) (mem2 x)))
                    (t (mem2 x))))
                ((eq (car x) '*)
                  (let ((y (find-if #'(lambda (z) (and (listp z) (eq (car z) '-))) (cdr x))))
                     (cond (y (cons '* (cons (negate y) (remove y (cdr x) :test 'equal))))
                                 (t (cons '* (cons (negate (mem2 x)) (cddr x)))))))
                ((eq (car x) '/)
                  (list '/ (negate (mem2 x)) (mem3 x)))
                (t (list '- x))))

(defun neg-atom (x) (and (listp x) (null (cddr x)) (eq (car x) '-) (atom (mem2 x))))

(defun d-simplify-quotient (x)
    (cond ((term-equal (mem2 x) (mem3 x)) (list  (list 1) nil))
                ((term-neg-equal (mem2 x) (mem3 x)) (list (list -1) nil))
                (t
                  (list (list (combine-exponents
                                   (collect-quotient-multipliers
                                     (list '/ (factor-atoms (mem2 x)) (factor-atoms (mem3 x)))))) nil))))

(defun simplify-quotient (x)
    (format-difference (d-simplify-quotient x)))

#|
;; This converts 1/(1/x) to x. It is not used.
(defun invert-double-quotients (x)
    (cond ((and (listp x) (eq (car x) '/) (eq (mem2 x) 1)
                          (listp (mem3 x)) (eq (car (mem3 x)) '/)
                          (eq (mem2 (mem3 x)) 1))
                 (mem3 (mem3 x)))
                (t x)))
|#

(defun d-simplify-exponentiation (x &key recursive-call expand-times)
    (let ((base (mem2 x))
            (n (if recursive-call (mem3 x) (simplify (mem3 x)))))
       (let ((y (ignore-errors (eval n))))
          (when (integerp y) (setf n y)))
       (cond ((eq n 0) (list (list 1) nil))
                   ((eq n 1) (d-simplify base))
                   ((equal n -1) (list (list (list '/ 1 (simplify base))) nil))
                   ((and (integerp n) expand-times)
                     (let ((y nil) (s-base (simplify base)))
                        (cond ((atom s-base) (list (list (list 'expt s-base n)) nil))
                                    (t (dotimes (i n) (push s-base y))
                                        (d-simplify-product (cons '* y) :expand-times t)))))
                   ((eq base 1) (list (list 1) nil))
                   ((eq base 0) (list (list 0) nil))
                   ((and (listp base) (eq (car base) '/))
                    (list (list (list '* (simplify-exponentiation (list 'expt (mem2 base) n) :recursive-call t)
                                           (simplify-exponentiation (list 'expt (mem3 base) (negate n)) :recursive-call t)))
                            nil))
                   ((and (listp base) (eq (car base) '*))
                     (list
                       (list
                         (cons
                           '* (mapcar #'(lambda (y) (simplify-exponentiation (list 'expt y n) :recursive-call t))
                                               (cdr base))))))
                   ((equal base '(- 1)) (list (list 'expt base n) nil))
                  ; ((and (listp base) (eq n 2) (or (eq (car base) '+) (eq (car base) '-)))
                  ;   (d-simplify-product (list '* base base) t))
                   (t (list (list (list 'expt (simplify base) n)) nil)))))

(defun simplify-exponentiation (x &key recursive-call expand-times)
    (format-difference
      (d-simplify-exponentiation x :recursive-call recursive-call :expand-times expand-times)))

;; x and y are simplified terms
(defun expand-times (x y)
    (let ((x+ (append (crossproduct (mem1 x) (mem1 y))
                                   (crossproduct (mem2 x) (mem2 y))))
            (x- (append (crossproduct (mem1 x) (mem2 y))
                                  (crossproduct (mem2 x) (mem1 y)))))
       (list (mapcar #'(lambda (z)
                                     (setf z (remove 1 z))
                                     (when (null z) (setf z  '(1)))
                                    (if (cdr z) (combine-exponents 
                                                      (collect-multipliers 
                                                        (cdr (flatten-product (cons '* z))))) (car z))) x+)
               (mapcar #'(lambda (z)
                                     (setf z (remove 1 z))
                                     (when (null z) (setf z  '(1)))
                                    (if (cdr z) (combine-exponents 
                                                      (collect-multipliers 
                                                        (cdr (flatten-product (cons '* z))))) (car z))) x-))))

;; x is a product or the cdr of a product. This returns a simplified term.
(defun expand-product (x)
    (when (eq (car x) '*) (setf x (cdr x)))
    (cond ((cdr x)
                 (expand-times (d-simplify (car x) :expand-times t) (expand-product (cdr x))))
                (t (d-simplify (car x) :expand-times t))))

#|
;; x is a product. This turns (* x (* y z)) into (* x y z)
(defun flatten-product (x)
    (cond ((atom x) x)
                ((productp x)
                  (cond ((cddr x)
                               (cons '* (apply #'append
                                                          (mapcar
                                                            #'(lambda (y)
                                                                  (if (atom y) (list y) 
                                                                       (let ((z (flatten-product y)))
                                                                          (if (eq (car z) '*) (cdr z) z))))
                                                            (cdr x)))))
                             (t (flatten-product (mem2 x)))))
                (t (list x))))
|#

;; x is a product. This turns (* x (* y z)) into (* x y z)
(defun flatten-product (x)
    (cond ((atom x) x)
                ((productp x)
                  (cond ((cddr x)
                               (cons '* (apply #'append
                                                          (mapcar
                                                            #'(lambda (y)
                                                                  (if (atom y) (list y) 
                                                                       (let ((z (flatten-product y)))
                                                                          (if (eq (car z) '*) (cdr z) (list z)))))
                                                            (cdr x)))))
                             (t (flatten-product (mem2 x)))))
                (t x)))

;; This also flattens products within products of quotients
(defun flatten-product+ (x)
    (cond
      ((productp x)
        (let ((y (mapcar #'flatten-product (cdr x)))
                (num nil) (den nil))
           (dolist (z y)
               (cond ((quotientp z) (push (mem2 z) num) (push (mem3 z) den))
                           (t (push z num))))
           (cond (den (list '/ (flatten-product (as-product num)) (flatten-product (as-product den))))
                       (t (flatten-product (as-product num))))))
      ((quotientp x)
        (let ((num0 (flatten-product (mem2 x)))
                (den0 (flatten-product (mem3 x)))
                (num nil) (den nil))
           (cond ((quotientp num0) (push (mem2 num0) num) (push (mem3 num0) den))
                       (t (push num0 num)))
           (cond ((quotientp den0) (push (mem2 den0) den) (push (mem3 den0) num))
                       (t (push den0 den)))
           (list '/ (flatten-product (as-product num)) (flatten-product (as-product den)))))
      (t x)))

;; This returns the expanded list of multipliers for a multiplication term
;; x is the cdr of the term. The multipliers are represented in the form
;; (x n) where n is the exponent.
(defun collect-multipliers (x)
    (let ((mult nil))
       (dolist (y x)
           (cond ((listp y)
                        (cond ((equal (car y) '*) (setf mult (append mult (collect-multipliers (cdr y)))))
                                    ((equal (car y) '/) (setf mult (append mult (collect-quotient-multipliers y))))
                                    ((equal (car y) 'expt) (push (list (mem2 y) (mem3 y)) mult))
                                    (t (push (list y 1) mult))))
                       ((not (eq y 1)) (push (list y 1) mult))))
       mult))

;; This returns the list of multipliers resulting from turning a quotient into a multiplication
(defun collect-quotient-multipliers (x)
    (let ((mult nil))
       (cond ((listp (mem2 x))
                    (cond ((eq (car (mem2 x)) '*) (setf mult (collect-multipliers (cdr (mem2 x)))))
                                ((eq (car (mem2 x)) '/) (setf mult (collect-quotient-multipliers (mem2 x))))
                                ((eq (car (mem2 x)) 'expt) (setf mult (list (list (mem2 (mem2 x)) (mem3 (mem2 x))))))
                                (t (setf mult (list (list (mem2 x) 1))))))
                   ((not (eq (mem2 x) 1)) (setf mult (list (list (mem2 x) 1)))))
       (append mult (mapcar #'(lambda (z) (list (car z) (list '- (mem2 z)))) (collect-multipliers (cddr x))))))

;; (collect-multipliers (cdr '(* x (* y z) (/ u v)))) = ((x 1) (z 1) (y 1) (u 1) (v (- 1)))

(proclaim '(special *repeated-exponents*))

(setf *repeated-exponents* nil)

;; x is the list of multipliers returned by COLLECT-MULTIPLIERS
(defun combine-exponents (x)
   ; (setf xxx x)
    (or (e-assoc x *repeated-exponents*)
          (let ((y (f-simplify-quotient (combine-exponents0 x)))) (push (cons x y) *repeated-exponents*) y)))

(defun as-quotient (x y)
    (cond ((eq x 0) 0)
                ((eq y 1) x)
                (t (list '/ x y))))

#| We want to factor the denominator, and then divide the numerator by each factor. If that returns nil,
we retain that factor in the denominator, otherwise we drop it and simplify the numerator. |#
;; This factors the denominator and tries dividing each factor into the numerator.
(defun f-simplify-quotient (x)
    ;(setf xx x) (terpri) (princ "f-simplify-quotient: ") (print-tree x) ;(break)
    (cond
      ((and (quotientp x) (not (occur '/ (mem2 x))) (not (occur '/ (mem3 x))))
        (let ((num (simplify (mem2 x)))
                (den (factor (simplify (mem3 x)))))
           (f-simplify num den)))
      (t x)))

#|
(defun f-simplify (num den)
    (cond
      ((atom num)
        (cond
          ((atom den) (if (eq num den) 1 (list '/ num den)))
          ((subproduct num den) (as-quotient 1 (factor-atom num den)))
          (t (list '/ num den))))
      ((or (eq (car num) '-) (eq (car num) '+) (eq (car num) 'expt))
        (cond 
          ((not (productp den)) (or (divide-difference num den) (as-quotient num den)))
          (t
            (let ((factors (cdr den))
                    (new-den nil))
               (loop
                  (let ((d (divide-difference num (car factors))))
                     (cond (d (setf num d))
                                 (t (push (car factors) new-den)))
                     (setf factors (cdr factors))
                     (when (null factors) (return (if new-den (as-quotient num (as-product new-den)) num)))))))))
      ((productp num)
        (let ((x0 (f-simplify (mem2 num) den)))
           (cond ((quotientp x0)
                        (let ((x1 (f-simplify  (as-product (cddr num)) (mem3 x0))))
                           (cond ((quotientp x1)
                                        (as-quotient (flatten-product (as-product (list (mem2 x0) (mem2 x1)))) (mem3 x1)))
                                       (t (flatten-product (as-product (list (mem2 x0) x1)))))))
                       (t (as-product (cons x0 (cddr num)))))))
     ; ((and (exponentiationp num) (eq (mem3 num) 1)) (f-simplify (mem2 num) den))
     ; ((and (exponentiationp num) (integerp (mem3 num)) (> (mem3 num) 1))
      ;  (f-simplify (list '* (mem2 num) (list 'expt (mem2 num) (1- (mem3 num)))) den))
      (t
        (let ((d (divide-difference num den)))
           (or d (as-quotient num den))))))
|#

(defun f-simplify (num den)
    (cond
      ((atom num)
        (cond
          ((atom den) (if (eq num den) 1 (list '/ num den)))
          ((subproduct num den) (as-quotient 1 (factor-atom num den)))
          (t (list '/ num den))))
      ((or (eq (car num) '-) (eq (car num) '+) )
        (cond 
          ((not (productp den)) (or (divide-difference num den) (as-quotient num den)))
          (t
            (let ((factors (cdr den))
                    (new-den nil))
               (loop
                  (let ((d (divide-difference num (car factors))))
                     (cond (d (setf num d))
                                 (t (push (car factors) new-den)))
                     (setf factors (cdr factors))
                     (when (null factors) (return (if new-den (as-quotient num (as-product new-den)) num)))))))))
      ((productp num)
        (let ((x0 (f-simplify (mem2 num) den)))
           (cond ((quotientp x0)
                        (let ((x1 (f-simplify  (as-product (cddr num)) (mem3 x0))))
                           (cond ((quotientp x1)
                                        (as-quotient (flatten-product (as-product (list (mem2 x0) (mem2 x1)))) (mem3 x1)))
                                       (t (flatten-product (as-product (list (mem2 x0) x1)))))))
                       (t (as-product (cons x0 (cddr num)))))))
      ((and (exponentiationp num) (eq (mem3 num) 1)) (f-simplify (mem2 num) den))
      ((and (exponentiationp num) (integerp (mem3 num)) (> (mem3 num) 1))
        (f-simplify (list '* (mem2 num) (list 'expt (mem2 num) (1- (mem3 num)))) den))
      (t
        (let ((d (divide-difference num den)))
           (or d (as-quotient num den))))))

#|
(defun f-simplify-quotient (x)
    ;(setf xx x) (terpri) (princ "f-simplify-quotient: ") (print-tree x) ;(break)
    (cond
      ((and (listp x) (eq (car x) '/) (not (occur '/ (mem2 x))) (not (occur '/ (mem3 x)))) ;(not (atom (mem3 x))))
        (let ((num (simplify (mem2 x)))
                (den (factor (simplify (mem3 x)))))
           (cond
             ((atom num)
               (cond
                 ((atom den) (if (eq num den) 1 x))
                 ((subproduct num den) (as-quotient 1 (factor-atom num den)))
                 (t x)))
             ((or (eq (car num) '-) (eq (car num) '+) (eq (car num) 'expt))
               (cond 
                 ((not (and (listp den) (eq (car den) '*))) (or (divide-difference num den) (as-quotient num den)))
                 (t
                   (let ((factors nil)
                           (new-den nil))
                      (dolist (d (cdr den))
                          (cond ((and (listp d) (eq (car d) 'expt) (integerp (mem3 d)))
                                       (dotimes (i (mem3 d)) (push (mem2 d) factors)))
                                      (t (push d factors))))
                      (setf factors (reverse factors))
                      (loop
                         (let ((d (divide-difference num (car factors))))
                            (cond (d (setf num d))
                                        (t (push (car factors) new-den)))
                            (setf factors (cdr factors))
                            (when (null factors) (return (if new-den (as-quotient num (as-product new-den)) num)))))))))
             ((and (listp num) (eq (car num) '*))
               (let ((x0 (f-simplify-quotient (as-quotient (mem2 num) den))))
                  (cond ((and (listp x0) (eq (car x0) '/))
                               (let ((x1 (f-simplify-quotient (as-quotient (as-product (cddr num)) (mem3 x0)))))
                                  (cond ((and (listp x1) (eq (car x1) '/))
                                               (as-quotient (flatten-product (as-product (list (mem2 x0) (mem2 x1)))) (mem3 x1)))
                                              (t (flatten-product (as-product (list (mem2 x0) x1)))))))
                              (t (as-product (cons x0 (cddr num)))))))
             (t
               (let ((d (divide-difference num den)))
                  (or d (as-quotient num den)))))))
      (t x)))

(defun f-simplify-quotient (x)
    (cond
      ((and (listp x) (eq (car x) '/) (not (occur '/ (mem2 x))) (not (occur '/ (mem3 x))))
        (let ((num (mem2 x))
                (den (factor (mem3 x))))
           (cond
             ((eq num 0) 0)
             ((and (not (eq num 1)) (listp den) (eq (car den) '*))
               (let ((factors nil)
                       (new-den nil))
                  (dolist (d (cdr den))
                      (cond ((and (listp d) (eq (car d) 'expt) (integerp (mem3 d)))
                                   (dotimes (i (mem3 d)) (push (mem2 d) factors)))
                                  (t (push d factors))))
                  (setf factors (reverse factors))
                  (loop
                     (let ((d (divide-difference num (car factors))))
                        (cond (d (setf num d))
                                    (t (push (car factors) new-den)))
                        (setf factors (cdr factors))
                        (when (null factors) (return (if new-den (list '/ num (as-product new-den)) num)))))))
             (t
               (let ((d (divide-difference num den)))
                  (or d x))))))
      (t x)))
|#

(defun combine-exponents0 (x)
    (let ((x-rest x) (mult1 nil) (mult2 nil) (sign nil))
       (loop (let* ((y (car x-rest))
                           (y-terms (subset #'(lambda (z) (term-equal (car z) (car y))) x-rest))
                           (neg-y-terms (subset #'(lambda (z) (term-neg-equal (car z) (car y))) x-rest)))
                    (setf x-rest (setdifference (setdifference x-rest y-terms) neg-y-terms))
                    (when (eq (car y) 0) (return-from combine-exponents0 0))
                    (when (not (eq (car y) 1))
                         (let* ((pos-ex (mapcar #'(lambda (z) (mem2 z)) y-terms))
                                   (neg-ex (mapcar #'(lambda (z) (mem2 z)) neg-y-terms))
                                   (ex (simplify-sum (cons '+ (append pos-ex neg-ex)))))
                            (let ((y (ignore-errors (eval ex))))
                               (when (integerp y) (setf ex y)))
                            (setf neg-ex (if neg-ex (cons '+ neg-ex) 0))
                            (let ((y (ignore-errors (eval neg-ex))))
                               (when (integerp y) (setf neg-ex y)))
                            (cond ((equal (car y) '(- 1)) (push (cons '+ pos-ex) sign))
                                        ((not (eq neg-ex 0)) (push neg-ex sign)))
                            (when (not (equal (car y) '(- 1)))
                                 (cond ((eq ex 1) (push (car y) mult1))
                                             ((equal ex -1) (push (car y) mult2))
                                             ((not (eq (car y) 1))
                                               (cond ((and (numberp ex) (< ex 0)) (push (list 'expt (car y) (- ex)) mult2))
                                                           ((and (listp ex) (eq (car ex) '-) (null (cddr ex)))
                                                             (push (list 'expt (car y) (mem2 ex)) mult2))
                                                           ((and (not (eq ex 0)) (not (eq ex -1))) (push (list 'expt (car y) ex) mult1)))))))))
                  (when (null x-rest)
                       (let* ((sign-ex (if sign (simplify-sum (cons '+ sign)) 0))
                                 (y (ignore-errors (eval sign-ex))))
                          (cond ((integerp y)
                                       (cond ((oddp y) (setf sign -1))
                                                   (t (setf sign 1))))
                                      (t (setf sign (list 'expt '(- 1) sign-ex)))))
                       (cond ((eq sign 1)
                                    (return (cond ((and (null mult1) (null mult2)) 1)
                                                             ((null mult1) (list '/ 1 (as-product mult2)))
                                                             ((null mult2) (as-product mult1))
                                                             (t (list '/ (as-product mult1) (as-product mult2))))))
                                   ((eq sign -1)
                                     (return (cond ((and (null mult1) (null mult2)) -1)
                                                              ((null mult1) (list '/ 1 (negate (as-product mult2))))
                                                              ((null mult2) (negate (as-product mult1)))
                                                              (t (list '/ (negate (as-product mult1)) (as-product mult2))))))
                                   (t
                                     (return (cond ((and (null mult1) (null mult2)) sign)
                                                              ((null mult1) (list '/ sign (as-product mult2)))
                                                              ((null mult2) (if (cdr mult1) (cons '* (cons sign mult1)) (list '* sign (car mult1))))
                                                              (t (list '/ (if (cdr mult1) (cons '* (cons sign mult1)) (list '* sign (car mult1)))
                                                                         (as-product mult2)))))))))))

;; Converts prefix notation to infix notation (Mathematica-readable)
(defun convert-to-infix (x)
    (cond ((atom x) x)
                ((eq (car x) '+)
                  (cond ((every #'(lambda (y) (eq y 1)) (cdr x)) (length (cdr x)))
                              (t (cons (convert-to-infix (mem2 x)) (apply 'append (mapcar #'(lambda (y) (list '+ (convert-to-infix y))) (cddr x)))))))
                ((eq (car x) '*) (cons (convert-to-infix (mem2 x)) (apply 'append (mapcar #'(lambda (y) (list '* (convert-to-infix y))) (cddr x)))))
                ((eq (car x) '- )
                  (cond ((cddr x) (list (convert-to-infix (mem2 x)) '- (convert-to-infix (if (cdddr x) (cons '+ (cddr x)) (caddr x)))))
                              (t (list '- (convert-to-infix (mem2 x))))))
                ((eq (car x) '/) (list (convert-to-infix (mem2 x)) '/ (convert-to-infix (mem3 x))))
                ((eq (car x) 'expt) (list (convert-to-infix (mem2 x)) '^ (convert-to-infix (mem3 x))))
                ((eq (car x) 'log) (cons 'log[ (append (convert-to-infix (mem2 x)) (list ']))))
                ((listp x) (mapcar #'convert-to-infix x))
                ))

(defun convert-to-prefix (x)
    (cond ((atom x) x)
                ((equal (car x) '-) (list '- (convert-to-prefix (mem2 x))))
                ((equal (mem2 x) '+) (cons '+ (cons (convert-to-prefix (mem1 x)) (convert-list-to-prefix (cddr x)))))
                ((equal (mem2 x) '-) (cons '- (cons (convert-to-prefix (mem1 x)) (convert-list-to-prefix (cddr x)))))
                ((equal (mem2 x) '*) (cons '* (cons (convert-to-prefix (mem1 x)) (convert-list-to-prefix (cddr x)))))
                ((equal (mem2 x) '/) (list '/ (convert-to-prefix (mem1 x)) (convert-to-prefix (mem3 x))))
                ((equal (mem2 x) '^) (list 'expt (convert-to-prefix (mem1 x)) (convert-to-prefix (mem3 x))))
                (t x)))

(defun convert-list-to-prefix (x)
    (let ((results nil))
       (dolist (y x)
           (when (and (not (eq y '+)) (not (eq y '-)) (not (eq y '*)))
                (push (convert-to-prefix y) results)))
       (reverse results)))

(defun expand-quotients (x)
    ;(progn (terpri) (princ "expand-quotients: ") (princ x))
    (cond
      ((atom x) x)
      ((eq (car x) '+) (expand-quotients-in-sum x))
      ((eq (car x) '-) (expand-quotients-in-difference x))
      ((eq (car x) '*)  ;; cancel common multipliers here
        (let ((x1 (expand-quotients (mem2 x)))
                (x2 (expand-quotients (if (cdddr x) (cons '* (cddr x)) (mem3 x)))))
           (cond
             ((and (listp x1) (eq (car x1) '/))
               (cond
                 ((and (listp x2) (eq (car x2) '/))
                   (list '/ (prod (mem2 x1) (mem2 x2)) (prod (mem3 x1) (mem3 x2))))
                 (t (list '/ (prod (mem2 x1) x2) (mem3 x1)))))
             ((and (listp x2) (eq (car x2) '/))
               (list '/ (prod (mem2 x2) x1) (mem3 x2))) (t x))))
      ((eq (car x) '/) (expand-quotients-in-quotient x))
      ((eq (car x) 'expt)
        (let ((n (mem3 x)))
           (cond
             ((integerp n)
               (let ((prod nil))
                  (cond
                    ((< n 0) 
                      (dotimes (i (- n)) (push (mem2 x) prod))
                      (expand-quotients (list '/ 1 (cons '* prod))))
                    (t (dotimes (i n) (push (mem2 x) prod))
                        (expand-quotients (cons '* prod))))))
             (t x))))))

#|
(defun expand-quotients-in-sum (x)
   ; (setf xx x)
    (let ((x1 (expand-quotients (mem2 x)))
            (x2 (expand-quotients (if (cdddr x) (cons '+ (cddr x)) (mem3 x)))))
       (cond 
         ((and (listp x1) (eq (car x1) '/))
           (cond
             ((and (listp x2) (eq (car x2) '/))
               (cond
                 ((term-equal (mem3 x1) (mem3 x2))
                   (list '/ (simplify-sum (list '+ (mem2 x1) (mem2 x2))) (mem3 x1)))
                 ((term-neg-equal (mem3 x1) (mem3 x2))
                   (list '/ (simplify-difference (list '- (mem2 x1) (mem2 x2))) (mem3 x1)))
                 ((and (listp (mem3 x1)) (eq (car (mem3 x1)) '*))
                   (cond
                     ((and (listp (mem3 x2))  (eq (car (mem3 x2)) '*))
                       (multiple-value-bind
                            (common den1 den2)
                            (compare-lists (cdr (mem3 x1)) (cdr (mem3 x2)) :test 'term-equal)
                            (list '/ (simplify-sum (list '+ (as-product* (cons (mem2 x1) den2)) (as-product* (cons (mem2 x2) den1))))
                                    (as-product* (append common den1 den2)))))
                     ((member (mem3 x2) (cdr (mem3 x1)) :test 'term-equal)
                       (list '/ 
                               (simplify-sum
                                 (list '+ (mem2 x1)
                                         (as-product* (cons (mem2 x2)
                                                                           (remove (mem3 x2) (cdr (mem3 x1))
                                                                                           :test 'term-equal :count 1)))))
                               (mem3 x1)))
                     (t
                       (list '/ (simplify-sum (list '+ (prod (mem2 x1) (mem3 x2)) (prod (mem3 x1) (mem2 x2))))
                               (prod (mem3 x1) (mem3 x2))))))
                 ((and (listp (mem3 x2))  (eq (car (mem3 x2)) '*))
                   (cond
                     ((member (mem3 x1) (cdr (mem3 x2)) :test 'term-equal)
                       (list '/ 
                               (simplify-sum
                                 (list '+ (mem2 x2)
                                         (as-product* (cons (mem2 x1)
                                                                           (remove (mem3 x1) (cdr (mem3 x2))
                                                                                           :test 'term-equal :count 1)))))
                               (mem3 x2)))
                     (t
                       (list '/ (simplify-sum (list '+ (prod (mem2 x1) (mem3 x2)) (prod (mem3 x1) (mem2 x2))))
                               (prod (mem3 x1) (mem3 x2))))))
                 (t (list '/ (simplify-sum (list '+ (prod (mem2 x1) (mem3 x2)) (prod (mem3 x1) (mem2 x2))))
                            (prod (mem3 x1) (mem3 x2))))))
             (t (list '/ (simplify-sum (list '+ (mem2 x1) (prod (mem3 x1) x2))) (mem3 x1)))))
         ((and (listp x2) (eq (car x2) '/))
           (list '/ (simplify-sum (list '+ (mem2 x2) (prod (mem3 x2) x1))) (mem3 x2)))
         (t x))))
|#

(defun expand-quotients-in-sum (x)
    (let ((x-terms (mapcar #'expand-quotients (cdr x)))
            (new-x-terms nil)
            (denominators nil))
       (dolist (y x-terms)
           (cond ((and (listp y) (eq (car y) '/))
                        (let ((den0 nil)
                                (den1 nil))
                           (cond ((and (exponentiationp (mem3 y)) (integerp (mem3 (mem3 y))))
                                        (dotimes (xx (mem3 (mem3 y))) (push (mem2 y) den0)))
                                       ((productp (mem3 y))
                                         (dolist (z (cdr (mem3 y)))
                                             (cond ((and (exponentiationp z) (integerp (mem3 z)))
                                                          (dotimes (xx (mem3 z) (push (mem2 z) den0))))
                                                         (t (push z den0)))))
                                       (t (push (mem3 y) den0)))
                           (let ((dens denominators))
                              (dolist (z den0)
                                  (let ((z* (find-if #'(lambda (w) (term-equal w z)) dens)))
                                     (cond (z* (push z* den1) (setf dens (remove z* dens :count 1 :test 'equal)))
                                                 (t (push z den1) (push z denominators))))))
                           (push (list (mem2 y) den1) new-x-terms)))
                       (t (push (list y nil) new-x-terms))))
       (cond ((null denominators) x)
                   (t 
                     (list '/
                             (simplify
                             (as-sum
                               (mapcar 
                                 #'(lambda (y)
                                       (let ((den denominators))
                                          (dolist (z (mem2 y)) (setf den (remove z den :count 1 :test 'equal)))
                                          (as-product (cons (car y) den))))
                                 new-x-terms))
                             :expand-times t)
                             (as-product denominators))))))

(defun expand-quotients-in-difference (x)
    (cond
      ((null (mem3 x)) (negate (expand-quotients (mem2 x))))
      (t
        (let ((x1 (expand-quotients (mem2 x)))
                (x2 (expand-quotients (if (cdddr x) (cons '+ (cddr x)) (mem3 x)))))
           (cond
             ((and (listp x1) (eq (car x1) '/))
               (cond
                 ((and (listp x2) (eq (car x2) '/))
                   (cond
                     ((term-equal (mem3 x1) (mem3 x2))
                       (list '/ (simplify-difference (list '- (mem2 x1) (mem2 x2))) (mem3 x1)))
                     ((term-neg-equal (mem3 x1) (mem3 x2))
                       (list '/ (simplify-sum (list '+ (mem2 x2) (mem2 x1))) (mem3 x1)))
                     ((and (listp (mem3 x1)) (eq (car (mem3 x1)) '*))
                       (cond
                         ((and (listp (mem3 x2))  (eq (car (mem3 x2)) '*))
                           (multiple-value-bind
                                (common den1 den2)
                                (compare-lists (cdr (mem3 x1)) (cdr (mem3 x2)) :test 'term-equal)
                                (list '/ (simplify-difference (list '- (as-product* (cons (mem2 x1) den2))
                                                                      (as-product* (cons (mem2 x2) den1))))
                                        (as-product* (append common den1 den2)))))
                         ((member (mem3 x2) (cdr (mem3 x1)) :test 'term-equal)
                           (list '/ 
                                   (simplify-difference
                                     (list '- (mem2 x1)
                                             (as-product* (cons (mem2 x2)
                                                                               (remove (mem3 x2) (cdr (mem3 x1))
                                                                                               :test 'term-equal :count 1)))))
                                   (mem3 x1)))
                         (t
                           (list '/ (simplify-difference (list '- (prod (mem2 x1) (mem3 x2)) (prod (mem3 x1) (mem2 x2))))
                                   (prod (mem3 x1) (mem3 x2))))))
                     ((and (listp (mem3 x2))  (eq (car (mem3 x2)) '*))
                       (cond
                         ((member (mem3 x1) (cdr (mem3 x2)) :test 'term-equal)
                           (list '/ 
                                   (simplify-difference
                                     (list '- (as-product* (cons (mem2 x1)
                                                                                 (remove (mem3 x1) (cdr (mem3 x2))
                                                                                                 :test 'term-equal :count 1)))
                                             (mem2 x2)))
                                   (mem3 x2)))
                         (t
                           (list '/ (simplify-difference (list '- (prod (mem2 x1) (mem3 x2)) (prod (mem3 x1) (mem2 x2))))
                                   (prod (mem3 x1) (mem3 x2))))))
                     (t (list '/ (simplify-difference (list '- (prod (mem2 x1) (mem3 x2)) (prod (mem3 x1) (mem2 x2))))
                                (prod (mem3 x1) (mem3 x2))))))
                 (t (list '/ (simplify-difference (list '- (mem2 x1) (prod (mem3 x1) x2))) (mem3 x1)))))
             ((and (listp x2) (eq (car x2) '/))
               (list '/ (simplify-difference (list '- (prod (mem3 x2) x1) (mem2 x2))) (mem3 x2)))
             (t x))))))

(defun sump (x) (and (listp x) (eq (car x) '+)))

(defun differencep (x) (and (listp x) (eq (car x) '-)))

(defun productp (x) (and (listp x) (eq (car x) '*)))

(defun quotientp (x) (and (listp x) (eq (car x) '/)))

(defun exponentiationp (x) (and (listp x) (eq (car x) 'expt)))

;; y is a product and x is one of the terms in the product
(defun term-of (x y) (member x (cdr y) :test 'term-equal))

;; x is a quotient
(defun num-terms (x)
    (if (productp (mem2 x)) (cdr (mem2 x)) (list (mem2 x))))

;; x is a quotient
(defun den-terms (x)
    (if (productp (mem3 x)) (cdr (mem3 x)) (list (mem3 x))))

(defun as-quotient (x y)
    (cond
      ((eq y 1) x)
      ((and (listp x) (eq (car x) '-) (null (mem3 x)) (listp y) (eq (car y) '-) (null (mem3 y)))
        (list '/ (mem2 x) (mem2 y)))
      (t (list '/ x y))))

(defun expand-quotients-in-product (x)
    (let ((x1 (expand-quotients (mem2 x)))
            (x2 (expand-quotients (as-product* (cddr x)))))
       (cond
         ((and (listp x1) (eq (car x1) '/))
           (cond
             ((and (listp x2) (eq (car x2) '/))
               (multiple-value-bind
                    (common num1 den1)
                    (compare-lists (num-terms x1) (den-terms x2) :test 'term-equal)
                    (declare (ignore common))
                    (multiple-value-bind
                         (common num2 den2)
                         (compare-lists (num-terms x2) (den-terms x1) :test 'term-equal)
                         (declare (ignore common))
                         (as-quotient (as-product* (append num1 num2)) (as-product* (append den1 den2))))))
             (t ;; x1 is a quotient but x2 is not
               (let ((x1* (if (productp (mem2 x1)) (cdr (mem2 x1)) (list (mem2 x1))))
                       (x2* (if (productp x2) (cdr x2) (list x2))))
                  (multiple-value-bind
                       (common num den)
                       (compare-lists x2* (den-terms x1) :test 'term-equal)
                       (declare (ignore common))
                       (as-quotient (as-product* (append x1* num)) (as-product* den)))))))
         ((and (listp x2) (eq (car x2) '/))  ;; x2 is a quotient but x1 is not
               (let ((x2* (if (productp (mem2 x2)) (cdr (mem2 x2)) (list (mem2 x2))))
                       (x1* (if (productp x1) (cdr x1) (list x1))))
                  (multiple-value-bind
                       (common num den)
                       (compare-lists x1* (den-terms x2) :test 'term-equal)
                       (declare (ignore common))
                       (as-quotient (as-product* (append x2* num)) (as-product* den)))))
         (t x))))

(defun expand-quotients-in-quotient (x)
    (let ((x1 (expand-quotients (mem2 x)))
            (x2 (expand-quotients (mem3 x))))
       (cond
         ((and (listp x1) (eq (car x1) '/))
           (cond
             ((and (listp x2) (eq (car x2) '/))
               (multiple-value-bind
                    (common num1 den1)
                    (compare-lists (num-terms x1) (num-terms x2) :test 'term-equal)
                    (declare (ignore common))
                    (multiple-value-bind
                         (common num2 den2)
                         (compare-lists (den-terms x2) (den-terms x1) :test 'term-equal)
                         (declare (ignore common))
                         (as-quotient (as-product* (append num1 num2)) (as-product* (append den1 den2))))))
             (t ;; x1 is a quotient but x2 is not
               (let ((x1* (if (productp (mem3 x1)) (cdr (mem3 x1)) (list (mem3 x1))))
                       (x2* (if (productp x2) (cdr x2) (list x2))))
                  (multiple-value-bind
                       (common num den)
                       (compare-lists (num-terms x1) x2* :test 'term-equal)
                       (declare (ignore common))
                       (as-quotient (as-product* num) (as-product* (append x1* den))))))))
         ((and (listp x2) (eq (car x2) '/))  ;; x2 is a quotient but x1 is not
           (let ((x2* (if (productp (mem3 x2)) (cdr (mem3 x2)) (list (mem3 x2))))
                   (x1* (if (productp x1) (cdr x1) (list x1))))
              (multiple-value-bind
                   (common num den)
                   (compare-lists x1* (num-terms x2) :test 'term-equal)
                   (declare (ignore common))
                   (as-quotient (as-product* (append x2* num)) (as-product* den)))))
         (t x))))

(defun term-equal (x y)
    (cond
      ((and (atom x) (atom y)) (eq x y))
      ((and (listp x) (listp y))
        (cond ((and (eq (car x) '+) (eq (car y) '+))
                     (=== (cdr x) (cdr y) :test 'term-equal))
                    ((and (eq (car x) '-) (eq (car y) '-))
                      (and (term-equal (mem2 x) (mem2 y))
                                (term-equal (mem3 x) (mem3 y))))
                    ((and (eq (car x) '*) (eq (car y) '*))
                      (=== (cdr x) (cdr y) :test 'term-equal))
                    ((and (eq (car x) '/) (eq (car y) '/))
                      (and (term-equal (mem2 x) (mem2 y))
                                (term-equal (mem3 x) (mem3 y))))
                    ((and (eq (car x) 'expt) (eq (car y) 'expt))
                      (and (term-equal (mem2 x) (mem2 y))
                                (term-equal (mem3 x) (mem3 y))))
                    (t (equal x y))))))

;; (x - y) and (y - x) are term-neg-equal
(defun term-neg-equal (x y)
    (or (and (listp x) (listp y) (eq (car x) '-) (eq (car y) '-)
                    (=== (mem2 x) (mem3 y) :test 'term-equal) (=== (mem3 x) (mem2 y) :test 'term-equal))
          (and (listp x) (null (cddr x)) (eq (car x) '-) (=== (mem2 x) y) :test 'term-equal)
          (and (listp y) (null (cddr y)) (eq (car y) '-) (=== (mem2 y) x) :test 'term-equal)))

#|
(defun prod (x y)
    (cond ((eq x 1) y)
                ((eq y 1) x)
                ((eq x 0) 0)
                ((eq y 0) 0)
                ((and (listp x) (eq (car x) '*))
                 (cond ((and (listp y) (eq (car y) '*)) (cons '* (append (cdr x) (cdr y))))
                             (t (cons '* (cons y (cdr x))))))
                ((and (listp y) (eq (car y) '*)) (cons '* (cons x (cdr y))))
                (t (list '* x y))))
|#

(defun prod (x y) (as-product* (list x y)))

;; Where left and right are sums of products, this returns the list of the results of
;; factoring atoms out of left and right, and returns the list of powers of
;; the atoms factored out.
(defun remove-common-factors (left &optional right)
    ; (setf lft left rt right)
    (cond
      ((and (null right) (listp left) (eq (car left) '-))
        (cond
          ((and (listp (mem2 left)) (eq (car (mem2 left)) '+))
            (cond ((and (listp (mem3 left)) (eq (car (mem3 left)) '+))
                         (remove-common-factors (mem2 left) (mem3 left)))
                        ((mem3 left) (remove-common-factors (mem2 left) (list '+ (mem3 left))))
                        (t (multiple-value-bind
                                 (terms factors)
                                 (remove-common-factors (mem2 left))
                                 (values (if (mem2 terms) (list (mem2 terms) (mem1 terms))
                                                    (list (negate (mem1 terms)) nil))
                                                factors)))))
          ((and (listp (mem3 left)) (eq (car (mem3 left)) '+))
            (remove-common-factors (list '+ (mem2 left)) (mem3 left)))
          ((mem3 left) (remove-common-factors (list '+ (mem2 left)) (list '+ (mem3 left))))
          (t (multiple-value-bind
                                 (terms factors)
                                 (remove-common-factors (list '+ (mem2 left)))
                                 (values (if (mem2 terms) (list (mem2 terms) (mem1 terms))
                                                    (list (negate (mem1 terms)) nil))
                                                factors)))))
      ((and (and (listp left) (or (eq (car left) '+) (eq (car left) '*)))
                 (or (null right) (and (listp right) (or (eq (car right) '+) (eq (car right) '*)))))
        (when (and (listp left) (eq (car left) '*)) (setf left (list '+ left)))
        (when (and (listp right) (eq (car right) '*)) (setf right (list '+ right)))
        (let ((factors nil))
           ;; collect a sample term and the list of the rest of the terms
           (let ((term nil) (left-terms nil) (right-terms nil))
              (cond ((atom left) (setf term left))
                          ((eq (car left) '-)
                            (cond ((and (listp (mem2 left)) (eq (car (mem2 left)) '+))
                                         (when (eq (mem2 (mem2 left)) 1)
                                              (return-from remove-common-factors
                                                 (list (as-sum (cdr left)) (as-sum (cdr right)))))
                                         (setf term (mem2 (mem2 left)))
                                         (setf left-terms (cddr (mem2  left))))
                                        (t (setf term (mem2 left))))
                            (cond ((and (listp (mem3 left)) (eq (car (mem3 left)) '+))
                                         (setf left-terms (append left-terms (cdr (mem3 left)))))
                                        (t (setf left-terms (cons (mem3 left) left-terms)))))
                          ((eq (car left) '+)
                            (when (eq (mem2 left) 1)
                                 (return-from remove-common-factors
                                    (list (as-sum (cdr left)) (as-sum (cdr right)))))
                            (setf term (mem2 left))
                            (setf left-terms (cddr left)))
                          (t (setf term left)))
              (when right
                   (cond ((atom right) (setf right-terms (list right)))
                               ((eq (car right) '-)
                                 (cond ((and (listp (mem2 right)) (eq (car (mem2 right)) '+))
                                              (setf right-terms (cdr (mem2  right))))
                                             (t (setf right-terms (list right))))
                                 (cond ((and (listp (mem3 right)) (eq (car (mem3 right)) '+))
                                              (setf right-terms (append right-terms (cdr (mem3 right)))))
                                             (t (setf right-terms (cons (mem3 right) right-terms)))))
                               ((eq (car right) '+)
                                 (setf right-terms (cdr right)))
                               (t (setf right-terms (list right)))))
              ;; term is either a single term or a product
              ;; find atoms occurring in it that occur in all terms
              (let ((atoms nil))
                 (cond ((atom term)
                              (when (and
                                            (every #'(lambda (y) (subproduct term y)) left-terms)
                                            (every #'(lambda (y) (subproduct term y)) right-terms))
                                   (setf atoms (list term))))
                             ((eq (car term) 'expt)
                               (let ((x (mem2 term)))
                                  (cond ((atom x)
                                               (when (and
                                                             (every #'(lambda (y) (subproduct x y)) left-terms)
                                                             (every #'(lambda (y) (subproduct x y)) right-terms))
                                                    (setf atoms (list x)))))))
                             ((eq (car term) '*)
                               (dolist (x (cdr term))
                                   (cond ((atom x)
                                                (when (and
                                                              (every #'(lambda (y) (subproduct x y)) left-terms)
                                                              (every #'(lambda (y) (subproduct x y)) right-terms))
                                                     (pushnew x atoms)))
                                               ((and (eq (car x) 'expt)
                                                          (every #'(lambda (y) (subproduct (mem2 x) y)) left-terms)
                                                          (every #'(lambda (y) (subproduct (mem2 x) y)) right-terms))
                                                 (pushnew (mem2 x) atoms))))))
                 (dolist (x atoms)
                     ; (terpri) (princ x) (princ "     ")
                     (let ((count (term-count x term)))
                        (dolist (y left-terms)
                            (let ((new-count (term-count x y)))
                               (when (< new-count count) (setf count new-count))))
                        ; (princ count) (princ "     ")
                        (dolist (y right-terms)
                            (let ((new-count (term-count x y)))
                               (when (< new-count count) (setf count new-count))))
                        ; (princ count)
                        (when (not (zerop count)) (push (list x count) factors))
                        ;; remove the common occurrences of x
                        (when (not (zerop count))
                             (cond ((atom left) (setf left 1))
                                         ((eq (car left) '-)
                                           (cond ((and (listp (mem2 left)) (eq (car (mem2 left)) '+))
                                                        (let ((left1 
                                                                  (mapcar #'(lambda (y) (decrease-term-count x y count))
                                                                                   (cdr (mem2 left)))))
                                                           (cond ((and (listp (mem3 left)) (eq (car (mem3 left ))'+))
                                                                        (let ((left2 
                                                                                  (mapcar #'(lambda (y) (decrease-term-count x y count))
                                                                                                   (cdr (mem3 left)))))
                                                                           (setf left (list '- (as-sum left1) (as-sum left2)))))
                                                                       (t (setf left (list - (as-sum left1) (decrease-term-count x (mem3 left) count)))))))
                                                       ((and (listp (mem3 left)) (eq (car (mem3 left ))'+))
                                                         (let ((left2 
                                                                   (mapcar #'(lambda (y) (decrease-term-count x y count))
                                                                                    (cdr (mem3 left)))))
                                                            (setf left (list '- (decrease-term-count x (mem2 left) count) (as-sum left2)))))
                                                       (t (setf left (list '- (decrease-term-count x (mem2 left) count)
                                                                                  (decrease-term-count x (mem3 left) count))))))
                                         ((eq (car left) '+)
                                           (setf left (as-sum (mapcar #'(lambda (y) (decrease-term-count x y count)) (cdr left) ))))
                                         (left (setf left (decrease-term-count x left count))))
                             (when right
                                  (cond ((atom right) (setf right 1))
                                              ((eq (car right) '-)
                                                (cond ((and (listp (mem2 right)) (eq (car (mem2 right)) '+))
                                                             (let ((right1 
                                                                       (mapcar #'(lambda (y) (decrease-term-count x y count))
                                                                                        (cdr (mem2 right)))))
                                                                (cond ((and (listp (mem3 right)) (eq (car (mem3 right ))'+))
                                                                             (let ((right2 
                                                                                       (mapcar #'(lambda (y) (decrease-term-count x y count))
                                                                                                        (cdr (mem3 right)))))
                                                                                (setf right (list '- (as-sum right1) (as-sum right2)))))
                                                                            (t (setf right (list '- (as-sum right1) (decrease-term-count x (mem3 right) count)))))))
                                                            ((and (listp (mem3 right)) (eq (car (mem3 right ))'+))
                                                              (let ((right2 
                                                                        (mapcar #'(lambda (y) (decrease-term-count x y count))
                                                                                         (cdr (mem3 right)))))
                                                                 (setf right (list '- (decrease-term-count x (mem2 right) count) (as-sum right2)))))
                                                            (t (setf right (list '- (decrease-term-count x (mem2 right) count)
                                                                                         (decrease-term-count x (mem3 right) count))))))
                                              ((eq (car right) '+)
                                                (setf right (as-sum (mapcar #'(lambda (y) (decrease-term-count x y count)) (cdr right) ))))
                                              (right (setf right (decrease-term-count x right count))))))))))
           (when (and (listp left) (eq (car left) '+) (null (mem3 left))) (setf left (mem2 left)))
           (when (and (listp right) (eq (car right) '+) (null (mem3 right))) (setf right (mem2 right)))
           (values (list left right) factors)))
      (t (values (list left right) nil))))

;; The number of powers of x in term
(defun term-count (x term)
    ;;(setf xx x tt term)
    (cond ((eq x term) 1)
                ((listp term)
                  (cond ((and (eq (car term) 'expt) (eq (mem2 term) x))
                               (let ((y (ignore-errors (eval (mem3 term)))))
                                  (or y 1)))
                              ((member x (cdr term)) 1)  ;; this assumes that multiple occurrences are collected into expts.
                            ;  ((member x (cdr term)) (length (subset #'(lambda (y) (eq y x)) (cdr term))))
                              (t (let ((ex (find-if #'(lambda (y) (and (listp y) (eq (car y) 'expt) (eq (mem2 y) x))) (cdr term))))
                                    (cond ((and (listp (mem3 ex)) (eq (mem1 (mem3 ex)) '+)
                                                          (every #'(lambda (z)  (eq z 1)) (cdr (mem3 ex))))
                                                 (eval (mem3 ex)))
                                                ((numberp (mem3 ex)) (mem3 ex))
                                                (t 0))))))
                (t 0)))

;; (term-count 'cd '(* (expt cd (+ 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)) f1 f4 c (expt d (+ 1 1 1))))
;; (term-count 'cd '(expt cd (+ 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)))
;; (term-count 'cd '(* a b cd d))
;; (term-count 'cd '(* a b d))

#|
;; This assumes that x occurs in term.
(defun decrease-term-count (x term n)
    ;(setf xx x tt term nn n)
    (cond
      ((eq n 1)
        (cond
          ((eq x term) 1)
          ((listp term)
            (cond
              ((and (eq (car term) 'expt) (eq (mem2 term) x))
                (cond
                  ((and (listp (mem3 term)) (eq (mem1 (mem3 term)) '+) (every #'(lambda (z)  (eq z 1)) (cdr (mem3 term))))
                    (cond ((null (cdddr (mem3 term))) x)
                                (t (list 'expt x (as-sum (cddr (mem3 term)))))))
                  ((numberp (mem3 term))
                    (let ((m (- (mem3 term) 1)))
                       (cond ((eq m 1) x)
                                   (t (list 'expt x m)))))))
              ((member x term)  ;; this assumes that term is a product of atoms
                (as-product (remove x (cdr term) :count 1)))
              (t (let ((ex (find-if #'(lambda (y) (and (listp y) (eq (car y) 'expt) (eq (mem2 y) x))) (cdr term))))
                    (when ex
                         (cond
                           ((atom (mem3 ex))
                             (cons (car term) (cons (decrease-term-count x ex 1) (remove ex (cdr term) :test 'equal))))
                           ((and (eq (mem1 (mem3 ex)) '+) (every #'(lambda (z)  (eq z 1)) (cdr (mem3 ex))))
                             (cond
                               ((null (cddr (mem3 ex))) (remove ex term :test 'equal))
                               ((null (cdddr (mem3 ex))) (cons (car term) (cons x (remove ex (cdr term) :test 'equal))))
                               (t (cons (car term)
                                              (cons (list 'expt x (cons '+ (cddr (mem3 ex))))
                                                          (remove ex (cdr term) :test 'equal))))))))))))))
      ((listp term)
        (cond
          ((and (eq (car term) 'expt) (eq (mem2 term) x))
            (cond
              ((and (listp (mem3 term)) (eq (mem1 (mem3 term)) '+) (every #'(lambda (z)  (eq z 1)) (cdr (mem3 term))))
                (cond ((null (nthcdr (1+ n) (mem3 term))) 1)
                            ((null (cdr (nthcdr (1+ n) (mem3 term)))) x)
                            (t (list 'expt x (cons '+ (nthcdr (1+ n) (mem3 term)))))))
              ((numberp (mem3 term))
                (let ((m (- (mem3 term) n)))
                   (cond ((eq m 1) x)
                               (t (list 'expt x m)))))))
          (t (let ((ex (find-if #'(lambda (y) (and (listp y) (eq (car y) 'expt) (eq (mem2 y) x))) (cdr term))))
                (when ex
                     (cond
                       ((atom (mem3 ex))
                         (cons (car term) (cons (decrease-term-count x ex n) (remove ex (cdr term) :test 'equal))))
                       ((and (eq (mem1 (mem3 ex)) '+) (every #'(lambda (z)  (eq z 1)) (cdr (mem3 ex))))
                         (cond ((null (nthcdr (1+ n) (mem3 ex))) (remove ex term :test 'equal))
                                     ((null (cdr (nthcdr (1+ n) (mem3 ex)))) (cons (car term) (cons x (remove ex (cdr term) :test 'equal))))
                                     (t (cons (car term)
                                                    (cons (list 'expt x (cons '+ (nthcdr (1+ n) (mem3 ex))))
                                                                (remove ex (cdr term) :test 'equal))))))))))))))
|#

;; x is an atom and n an integer
(defun decrease-term-count (x term n)
    (cond
      ((atom term)
        (when (and (eq term x) (eq n 1)) 1))
      ((eq (car term) 'expt)
        (when (eq (mem2 term) x)
             (cond
               ((numberp (mem3 term))
                 (let ((m (- (mem3 term) n)))
                    (cond ((eq m 0) 1)
                                ((eq m 1) x)
                                (t (list 'expt x m)))))
               (t (list 'expt x (list '- (mem3 term) n))))))
      ((eq (car term) '*)  ;; this assumes that multiple occurrences are collected into powers
        (cond ((and (eq n 1) (member x (cdr term))) (as-product (remove x (cdr term) :count n)))
                    (t (let ((unexamined-terms (cdr term))
                                (examined-terms nil))
                          (loop
                             (when (null unexamined-terms) (return))
                             (let ((z (car unexamined-terms)))
                                (when (and (listp z) (eq (car z) 'expt) (eq (mem2 z) x) (integerp (mem3 z)))
                                     (return
                                       (as-product (append
                                                               examined-terms
                                                               (cons (decrease-term-count x z n)
                                                                           (cdr unexamined-terms))))))
                                (push z examined-terms)
                                (setf unexamined-terms (cdr unexamined-terms))))))))
      ((eq (car term) '+)
        (let ((terms (mapcar #'(lambda (y) (decrease-term-count x y n)) (cdr term))))
           (when (not (mem nil terms)) (cons '+ terms))))
      ((eq (car term) '-)
        (cond ((mem3 term)
                     (let ((s1 (decrease-term-count x (mem2 term) n))
                             (s2 (decrease-term-count x (mem3 term) n)))
                        (when (and s1 s2) (list '- s1 s2))))
                    (t (let ((s1 (decrease-term-count x (mem2 term) n)))
                          (when s1 (list '- s1))))))
      ((eq (car term) '/)
        (let ((s1 (decrease-term-count x (mem2 term) n)))
           (when s1 (list '/ s1 (mem3 term)))))))

;; (decrease-term-count 'cd '(* (expt cd (+ 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)) f1 f4 c (expt d (+ 1 1 1))) 15)
;; (decrease-term-count 'cd '(expt cd (+ 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)) 15)
;; (decrease-term-count 'cd '(* (expt cd (+ 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)) f1 f4 c (expt d (+ 1 1 1))) 1)
;; (decrease-term-count 'cd '(expt cd (+ 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)) 1)
;; (decrease-term-count 'cd 'cd 1)
;; (decrease-term-count 'cd '(expt cd (+ 1 1)) 1)
;; (decrease-term-count 'cd '(* (expt cd (+ 1 1 )) f1 f4 c (expt d (+ 1 1 1))) 1)
;; (decrease-term-count 'cd '(* cd f1 f4 c (expt d (+ 1 1 1))) 1)

;; decrease-term-count assumes that x is an atom occurring in term. Here,
;; term is either an atom or a product of atoms or a list of atoms
(defun decrement-term-count (x term)
    (decrease-term-count x term 1))

(defun factor-atoms (x)
    (cond
      ((atom x) x)
      ((eq (car x) '+)
        (multiple-value-bind
             (base factors)
             (remove-common-factors x nil)
             (as-product
               (cons (car base)
                           (mapcar 
                             #'(lambda (z) (if (eq (mem2 z) 1) (mem1 z) (list 'expt (car z) (mem2 z)))) factors)))))
      ((eq (car x) '-)
        (multiple-value-bind
             (base factors)
             (remove-common-factors (mem2 x) (mem3 x))
             (cond (factors
                          (as-product
                            (cons 
                              (if (mem2 base) (list '- (car base) (mem2 base)) (list '- (car base)))
                              (mapcar 
                                #'(lambda (z) (if (eq (mem2 z) 1) (mem1 z) (list 'expt (car z) (mem2 z)))) factors))))
                         ((mem2 base) (list '- (car base) (mem2 base)))
                         (t (list '- (car base))))))
      ((eq (car x) '*)
        (let ((xx (mapcar #'factor-atoms (cdr x))))
           (cond ((equal (cdr x) xx) x)
                       (t (simplify (as-product xx))))))
      ((eq (car x) '/) 
        (combine-exponents
          (collect-quotient-multipliers (list '/ (factor-atoms (mem2 x)) (factor-atoms (mem3 x))))))
      ((eq (car x) 'expt)
        (multiple-value-bind
             (base factors)
             (remove-common-factors (mem2 x) nil)
             (as-product
               (cons (list 'expt (if (mem2 base) (list '- (car base) (mem2 base)) (car base))
                                  (mem3 x))
                           (mapcar #'(lambda (z)
                                                 (let ((ex (list '* (mem2 z) (mem3 x))))
                                                    (if (eq ex 1) (mem1 z) (list 'expt (mem1 z) ex)))) factors)))))))

;; This divides a sum or difference of products (or exponentials), or in the limiting case, a single
;; product or exponential, by atom, where it is already know that atom is a subproduct
;; of each of them.
(defun factor-atom (atom x)
   ; (setf aa atom xx x)
    (cond
      ((atom x) 1)
      ((eq (car x) '+)
        (multiple-value-bind
             (base factors)
             (remove-common-factor atom x nil)
             (as-product
               (cons (car base)
                           (mapcar #'(lambda (z)
                                                 (if (eq (mem2 z) 1) (mem1 z) 
                                                      (list 'expt (car z) (mem2 z)))) factors)))))
      ((eq (car x) '-)
        (multiple-value-bind
             (base factors)
             (remove-common-factor atom (mem2 x) (mem3 x))
             (cond (factors
                          (as-product
                            (cons 
                              (if (mem2 base) (list '- (car base) (mem2 base)) (list '- (car base)))
                              (mapcar #'(lambda (z) 
                                                    (if (eq (mem2 z) 1) (mem1 z) 
                                                         (list 'expt (car z) (mem2 z)))) factors))))
                         ((mem2 base) (list '- (car base) (mem2 base)))
                         (t (list '- (car base))))))
      ((eq (car x) '*)
        (as-product (remove atom (cdr x))))
      ((eq (car x) '/)
        (simplify-quotient (list '/ (factor-atom atom (mem2 x)) (mem3 x))))
      ((eq (car x) 'expt)
        (cond
          ((atom (mem2 x)) (if (eq (mem2 x) atom) (decrement-term-count atom x) x))
          ((eq (mem1 (mem2 x)) '*)
            (let ((y (as-product (remove atom (cdr (mem2 x))))))
               (simplify-product
                 (list '* (list 'expt y (mem3 x))
                         (simplify-exponentiation (list 'expt atom (simplify-difference (list - (mem3 x) 1)))
                                                                      :recursive-call t)))))))))

;; ====================FACTORING POLYNOMIALS ==================
;; For a sketch of the algorithm, see "factoring.doc".

#| The terms we get from factoring are actually area measurements (relativized to u). As such, if ordered
in the right order, they will have non-negative values for all possible assignments to the variables.
One possible assignment is to let single-atom terms have the value .5, double-atom terms .25, triple-atom
terms .125, etc. Call these the "default values" of the variables, and call the result of substituting these
into a term its "default value". Then we can order two terms in a difference by making sure that the
default value is non-negative.
    The default values of atoms should be set by ANALYZE-PRODUCT-STRUCTURE.
|#

(proclaim '(special *default-atom-values*))

(setf *default-atom-values* nil)

(defun default-term-value (term)
    (or (ignore-errors (eval (sublis *default-atom-values* term)))
          1))

#|
(default-term-value
    '(- (+ abc c b a) (+ ab 1 (* f1 c) (* f3 c)))
    (default-atom-values '(a b c) '(f1 f2 f3 f4))) = -0.125
|#

(defun order-factors (factor1 factor2)
    (cond ((< (default-term-value factor1) 0) (list '* (negate factor1) (negate factor2)))
                (t (list '* factor1 factor2))))

(defun order-factor (factor)
    (if (< (default-term-value factor) 0) (negate factor) factor))

#|
(defun factor (x)
    (let ((x* (factor-difference x)))
       (cond ((equal x x*) x)
                   (t (flatten-product (cons '* (mapcar #'factor (cdr x*))))))))
|#

(defun factor (x)
    (cond ((atom x) x)
                ((or (eq (car x) '+) (eq (car x) '-) (eq (car x) 'expt))
                  (let ((x* (factor-difference x)))
                     (cond ((atom x*) x*)
                                 ((equal (car x*) '*)
                                   (flatten-product (cons '* (mapcar #'factor (cdr x*)))))
                                 (t x*))))
                ((eq (car x) '*)
                  (flatten-product (as-product (mapcar #'factor (cdr x)))))
                ((eq (car x) '/) (as-quotient (factor (mem2 x)) (factor (mem3 x))))
                (t x)))

;; If dif is such that if itcan be factored then there is cancellation, this returns the list
;; of two lists of atoms, where there are no terms mixing atoms from the two lists.
(defun possible-cancellation (dif)
    (let ((atoms (dif-atoms dif)))
       (when (every #'(lambda (x) (exponentiation-in-formula x dif)) atoms)
            (let* ((x (car atoms))
                      (terms (factor-terms dif))
                      (excluded-atoms
                        (subset
                          #'(lambda (y)
                                (not
                                  (some
                                    #'(lambda (term) (and (subproduct x term) (subproduct y term)))
                                    terms)))
                          atoms)))
               (when excluded-atoms
                    (list (setdifference atoms excluded-atoms) excluded-atoms))))))

;; This tries to factor dif as the square of a single factor
(defun factor-square (dif)
    (let* ((terms (factor-terms dif))
              (square-terms
                (mapcar
                  #'root-of-square
                  (subset
                    #'(lambda (term)
                          (or (square-term term)
                                (and (listp term)
                                          (eq (car term) '*)
                                          (every #'square-term (cdr term)))))
                    terms)))
              (sq-terms nil))
       (when square-terms
            (dolist (y (remove-duplicates square-terms :test 'term-equal))
                (let* ((y2-num (length (subset #'(lambda (z) (term-equal z y)) square-terms)))
                          (y-num (float-integer (expt y2-num (/ 1 2)))))
                   (when (not (eq y2-num (* y-num y-num))) (return-from factor-square nil))
                   (dotimes (i y-num) (push y sq-terms))))
            (let* ((x (car sq-terms))
                      (pos (list x))
                      (neg nil)
                      (neg-terms nil) 
                      (pos-terms nil))
               (cond
                 ((and (listp dif) (eq (car dif) '-))
                   (setf neg-terms
                            (cond
                              ((mem3 dif)
                                (cond ((and (listp (mem3 dif)) (eq (car (mem3 dif)) '+)) (cdr (mem3 dif)))
                                            (t (list (mem3 dif)))))
                              (t
                                (cond ((and (listp (mem2 dif)) (eq (car (mem2 dif)) '+)) (cdr (mem2 dif)))
                                            (t (list (mem2 dif)))))))
                   (when (mem3 dif) 
                        (setf pos-terms
                                 (cond
                                   ((and (listp (mem2 dif)) (eq (car (mem2 dif)) '+)) (cdr (mem2 dif)))
                                   (t (list (mem2 dif))))))
                   (when (mem x neg-terms) (push 1 neg))
                   (when (mem x pos-terms) (push 1 pos))
                   (dolist (y (cdr sq-terms))
                       (if
                          (and
                            (not (eq x y))
                            (some
                              #'(lambda (term) (eq (subtract-terms term (multiply-terms x y)) 0))
                              neg-terms))
                          (push y neg)
                          (push y pos))))
                 (t (setf pos sq-terms)
                     (when (occur 1 dif) (push 1 pos))))
               (let ((factor
                         (cond (neg (list '- (as-sum pos) (as-sum neg)))
                                     (t (as-sum pos)))))
                  (when (eq 0 (subtract-terms dif (multiply-terms factor factor)))
                       (order-factors factor factor)))))))

#|
(factor-square '(+ (expt a 2) (* a b) (* b a) (expt b 2)))
(factor-square '(- (+ (expt a 2) (expt b 2)) (+ (* a b) (* b a))))
(factor-square '(- (+ (* (expt a 2) (expt x 4)) (* (expt b 2) (expt y 6)))
                             (+ (* a b (expt x 2) (expt y 3)) (* b a (expt x 2) (expt y 3)))))
|#

;; term is an even power of an atom
(defun square-term (term)
    (and (listp term) (eq (car term) 'expt) (integerp (mem3 term)) (evenp (mem3 term))))

;; term is an even power of an atom or a product of even powers of atoms
(defun root-of-square (term)
    (when (listp term)
         (cond ((eq (car term) 'expt)
                      (let ((n (/ (mem3 term) 2)))
                         (cond ((eq n 1) (mem2 term))
                                     (t (list 'expt (mem2 term) n)))))
                     ((eq (car term) '*)
                       (cons '* (mapcar #'root-of-square (cdr term)))))))

;; This returns the integer for a floating point number
(defun float-integer (x)
    (multiple-value-bind
         (a b c)
         (decode-float x)
         (declare (ignore a c))
         b))

#|
(multiply-terms '(+ (* a x) (* b y)) '(+ (* a x) (* b y)))
= (+ (* (expt b 2) (expt y 2)) (* b y a x) (* a x b y) (* (expt a 2) (expt x 2)))

(factor-difference '(+ (* (expt b 2) (expt y 2)) (* b y a x) (* a x b y) (* (expt a 2) (expt x 2))))

(multiply-terms '(+ (* a x) (* b y)) '(+ (* a x) (* c y)))
= (+ (* b c (expt y 2)) (* b y a x) (* a x c y) (* (expt a 2) (expt x 2)))

(factor-difference '(+ (* b c (expt y 2)) (* b y a x) (* a x c y) (* (expt a 2) (expt x 2))))

(factor-difference '(- (expt x 2) (expt y 2)))

|#

(defun factor-with-cancellation (dif partition)
    (let* ((f1 (factor-square 
                     (subterm-of
                       #'(lambda (x) (some #'(lambda (y) (occur* y x)) (mem1 partition)))
                       dif)))
              (f2 (factor-square
                     (negate
                       (subterm-of
                         #'(lambda (x) (some #'(lambda (y) (occur* y x)) (mem2 partition)))
                         dif)))))
       (when (and f1 f2)
            (let ((factor1 (list '+ f1 f2))
                    (factor2 (list '- f1 f2)))
               (when (eq 0 (subtract-terms dif (multiply-terms factor1 factor2)))
                    (order-factors factor1 factor2))))))

(defun factor-without-cancellation (dif)
    (let ((b (find-if #'(lambda (x) (unique-power-in-formula x dif)) (dif-atoms dif))))
       (cond
         ((null b) (factor-square dif))
         (t (let ((f0 (subterm-of #'(lambda (x) (subproduct b x)) dif)))
               (cond
                 ((or (atom f0)
                         (and (eq (car f0) '-) (null (mem3 f0)) (atom (mem2 f0))))
                   dif)
                 (t
                   (let* ((f1 (factor (order-factor (decrement-term-count b f0))))   ;; order factors here
                             (factors
                               (cond ((and (listp f1) (eq (car f1) '*)) (cdr f1))
                                           (t (list f1))))
                             (dif* dif)
                             (final-factors nil))
                      (dolist (f factors)
                          (let ((d (divide-difference dif* f))) 
                             (when d
                                  (push f final-factors) 
                                  (setf dif* d))))
                      (when final-factors
                           (as-product (cons dif* final-factors)))))))))))

;; This fails in the special case in which every atom the occurs in one factor
;;  but not the other occurs with multiple powers in that factor.
(defun factor-difference (dif)
    (let ((n (ignore-errors (eval dif))))
       (cond
         ((integerp n) (factor-number n))
         ((and (listp dif) (eq (car dif) 'expt) (integerp (mem3 dif)))
           (let ((y nil)) (dotimes (i (mem3 dif)) (push (mem2 dif) y))
                  (cons '* y)))
         ((eq (car dif) '*) dif)
         (t 
           (let ((f-dif (factor-atoms dif))
                   (dif* dif))
              (when (and (listp f-dif) (eq (car f-dif) '*)) (setf dif* (mem2 f-dif)))
              (let* ((partition (possible-cancellation dif*))
                        (factorization
                          (cond (partition (factor-with-cancellation dif* partition))
                                      (t (factor-without-cancellation dif*)))))
                 (cond (factorization
                              (cond ((eq (car f-dif) '*) (flatten-product (list '* factorization (as-product (cddr f-dif)))))
                                          (t factorization)))
                             (t f-dif))))))))

(defun factor-number (n)
    (cond ((< n 0) (negate (factor-number (- n))))
                ((eq n 4) '(* (+ 1 1) (+ 1 1)))
                ((eq n 6) '(* (+ 1 1) (+ 1 1 1)))
                ((eq n 8) '(* (+ 1 1) (+ 1 1) (+ 1 1)))
                ((eq n 9) '(* (+ 1 1 1) (+ 1 1 1)))
                ((eq n 10) '(* (+ 1 1) (+ 1 1 1 1 1)))
                (t (let ((y nil)) (dotimes (i n) (push 1 y)) (as-sum y)))))

;; atom x occurs with a unique power in fm
(defun unique-power-in-formula (x fm)
    (when (not (integerp x))
         (cond ((atom fm) (term-count x fm))
                     ((null fm) 0)
                     ((eq (car fm) '*) (term-count x fm))
                     ((eq (car fm) 'expt) (term-count x fm))
                     ((eq (car fm) '+)
                       (let ((n 0))
                          (dolist (y (cdr fm))
                              (when n
                                   (let ((m (unique-power-in-formula x y)))
                                      (when (and m (not (eq 0 m)))
                                           (cond ((eq n 0) (setf n m))
                                                       ((not (eq m n)) (setf n nil)))))))
                          n))
                     ((eq (car fm) '-)
                       (cond ((mem3 fm)
                                    (let ((n (unique-power-in-formula x (mem2 fm))))
                                       (when n
                                            (cond ((eq n 0) (unique-power-in-formula x (mem3 fm)))
                                                        ((eq n (unique-power-in-formula x (mem3 fm))) n)))))
                                   (t (unique-power-in-formula x (mem2 fm))))))))

(defun term-atoms (terms)
    (cond ((and (atom terms)
                          terms
                          (not (eq terms '-))
                          (not (eq terms '+))
                          (not (eq terms '*))
                          (not (eq terms '/))
                          (not (eq terms 'expt))
                          (not (numberp terms)))
                 (list terms))
                ((listp terms) (unionmapcar= #'term-atoms terms))))

(defun no-exponentiation-in-formula (x fm)
    (cond
      ((atom fm) t)
      ((eq (car fm) 'expt) (not (eq (mem2 fm) x)))
      ((eq (car fm) '*) (every #'(lambda (y) (no-exponentiation-in-formula x y)) (cdr fm)))
      ((eq (car fm) '+) (every #'(lambda (y) (no-exponentiation-in-formula x y)) (cdr fm)))
      ((eq (car fm) '-) (and (no-exponentiation-in-formula x (mem2 fm))
                                           (no-exponentiation-in-formula x (mem3 fm))))
      ((eq (car fm) '/) (and (no-exponentiation-in-formula x (mem2 fm))
                                           (no-exponentiation-in-formula x (mem3 fm))))))

(defun exponentiation-in-formula (x fm)
    (cond
      ((atom fm) nil)
      ((eq (car fm) 'expt) (eq (mem2 fm) x))
      ((eq (car fm) '*) (some #'(lambda (y) (exponentiation-in-formula x y)) (cdr fm)))
      ((eq (car fm) '+) (some #'(lambda (y) (exponentiation-in-formula x y)) (cdr fm)))
      ((eq (car fm) '-) (or (exponentiation-in-formula x (mem2 fm))
                                           (exponentiation-in-formula x (mem3 fm))))
      ((eq (car fm) '/) (or (exponentiation-in-formula x (mem2 fm))
                                           (exponentiation-in-formula x (mem3 fm))))))

;; Where left and right are sums of products, this returns the list of the results of
;; factoring an atom x out of left and right, and returns the list of powers of
;; the atoms factored out.
(defun remove-common-factor (x left right)
    (cond ((atom left) (setf left 1))
                ((eq (car left) '-)
                  (cond ((and (listp (mem2 left)) (eq (car (mem2 left)) '+))
                               (let ((left1 
                                         (mapcar #'(lambda (y) (decrement-term-count x y))
                                                          (cdr (mem2 left)))))
                                  (cond ((and (listp (mem3 left)) (eq (car (mem3 left ))'+))
                                               (let ((left2 
                                                         (mapcar #'(lambda (y) (decrement-term-count x y))
                                                                          (cdr (mem3 left)))))
                                                  (setf left (list '- (cons '+ left1) (cons '+ left2)))))
                                              (t (setf left (list - (cons '+ left1) (decrement-term-count x (mem3 left))))))))
                              ((and (listp (mem3 left)) (eq (car (mem3 left ))'+))
                                (let ((left2 
                                          (mapcar #'(lambda (y) (decrement-term-count x y))
                                                           (cdr (mem3 left)))))
                                   (setf left (list '- (decrement-term-count x (mem2 left)) (cons '+ left2)))))
                              (t (setf left (list '- (decrement-term-count x (mem2 left))
                                                         (decrement-term-count x (mem3 left)))))))
                ((eq (car left) '+)
                  (setf left (as-sum (mapcar #'(lambda (y) (decrement-term-count x y)) (cdr left) ))))
                (left (setf left (decrement-term-count x left))))
    (when right
         (cond ((atom right) (setf right 1))
                     ((eq (car right) '-)
                       (cond ((and (listp (mem2 right)) (eq (car (mem2 right)) '+))
                                    (let ((right1 
                                              (mapcar #'(lambda (y) (decrement-term-count x y))
                                                               (cdr (mem2 right)))))
                                       (cond ((and (listp (mem3 right)) (eq (car (mem3 right ))'+))
                                                    (let ((right2 
                                                              (mapcar #'(lambda (y) (decrement-term-count x y))
                                                                               (cdr (mem3 right)))))
                                                       (setf right (list '- (cons '+ right1) (cons '+ right2)))))
                                                   (t (setf right (list '- (cons '+ right1) (decrement-term-count x (mem3 right))))))))
                                   ((and (listp (mem3 right)) (eq (car (mem3 right ))'+))
                                     (let ((right2 
                                               (mapcar #'(lambda (y) (decrement-term-count x y))
                                                                (cdr (mem3 right)))))
                                        (setf right (list '- (decrement-term-count x (mem2 right)) (cons '+ right2)))))
                                   (t (setf right (list '- (decrement-term-count x (mem2 right))
                                                                (decrement-term-count x (mem3 right)))))))
                     ((eq (car right) '+)
                       (setf right (as-sum (mapcar #'(lambda (y) (decrement-term-count x y)) (cdr right) ))))
                     (right (setf right (decrement-term-count x right)))))
    (list left right))

;; x is an atom, exponentiation, or product of the latter
(defun subproduct (x y)
    (or
      (term-equal x y)
      (cond ((and (atom x) (atom y)) (eq x y))
                  ((and (atom x) (productp y))
                    (some #'(lambda (z) (or (eq x z) (and (listp z) (eq (car z) 'expt) (eq (mem2 z) x)))) (cdr y)))
                  ((and (listp x) (listp y))
                    (cond
                      ((eq (car x) 'expt)
                        (cond
                          ((eq (car y) 'expt)
                            (and (term-equal (mem2 x) (mem3 y)) (integerp (mem3 x))
                                      (integerp (mem3 y)) (<= (mem3 x) (mem3 y))))
                          ((eq (car y) '*) (some #'(lambda (z) (subproduct x z)) (cdr y)))))
                      ((eq (car x) '*)
                        (and (eq (car y) '*)
                                  (every #'(lambda (z) (some #'(lambda (w) (subproduct z w)) (cdr y))) (cdr x)))))))))

#|
(dolist (x '(
                  (/ (- (+ (* f1 (expt c 2)) (* c bc) (* c cd) (* f1 bcd c) (* bc acd) (* cd c) (* cd acd) (* cd bcd))
                              (+ (* c bcd) (* c acd) (expt c 2) (* bcd acd) (* f1 bc c) (expt cd 2) (* cd bc) (* f1 cd c)))
                        (- cd c))
                  (/ (- (+ (expt cd 2) (* bcd acd)) (+ (* cd bcd) (* cd acd))) cd)
                  (/ (- (+ a (* cd a) b (* cd b) c (* cd c) bcd (* cd bcd) acd (* cd acd) d (* cd d) (* bc acd) (* bd acd) (* bc a)
                                    (* bd a) (* f1 bcd c) (* f1 b c) (* f2 bcd d) (* f2 b d) d c (* f1 d c) (* f1 (expt c 2)) (* d bc)
                                    (* c bc) (* f2 (expt d 2)) (* f2 c d) (* d bd) (* c bd) (* d cd) (* c cd))
                              (+ (expt cd 2) cd (* cd bd) bd (* f2 cd d) (* f2 d) (* cd bc) bc (* f1 cd c) (* f1 c) cd 1 (* f1 bc c)
                                    (* f1 bd c) (* f2 bc d) (* f2 bd d) (* bcd acd) (* b acd) (* bcd a) (* b a) (* c d) (expt d 2) (* c acd)
                                    (* d acd) (* c bcd) (* d bcd) (expt c 2) (* d c) (* c b) (* d b) (* c a) (* d a)))
                        (- (+ c d) (+ 1 cd)))
                  (/ (- (+ (* f2 (expt d 2)) (* d bd) (* d cd) (* f2 bcd d) (* bd acd) (* cd d) (* cd acd) (* cd bcd))
                              (+ (* d bcd) (* d acd) (expt d 2) (* bcd acd) (* f2 bd d) (expt cd 2) (* cd bd) (* f2 cd d)))
                        (- cd d))
                  (/ (- (+ (* f1 bc c) (* bcd acd) (* c bcd) (* cd bc))
                              (+ (* c bc) (* cd bcd) (* bc acd) (* f1 bcd c)))
                        (- cd c))
                  (/ (* (- cd acd) bcd) cd)
                  (/ (- (+ (* b a) (* bcd a) (* b acd) (* bcd acd) (* f2 bd d) (* f2 bc d) (* f1 bd c) (* f1 bc c) bc (* cd bc) bd
                                    (* cd bd) (* d bcd) (* c bcd) (* d b) (* c b))
                              (+ (* cd b) b (* cd bcd) bcd (* c bd) (* d bd) (* c bc) (* d bc) (* f2 b d) (* f2 bcd d) (* f1 b c) (* f1 bcd c)
                                    (* bd a) (* bc a) (* bd acd) (* bc acd)))
                        (- (+ c d) (+ 1 cd)))
                  (/ (- (+ (* f2 bd d) (* bcd acd) (* d bcd) (* cd bd))
                              (+ (* d bd) (* cd bcd) (* bd acd) (* f2 bcd d)))
                        (- cd d))
                  (/ (- (+ (* f1 bc c) (* bcd acd) (* c acd) (* f1 cd c))
                              (+ (* f1 (expt c 2)) (* cd acd) (* bc acd) (* f1 bcd c)))
                        (- cd c))
                  (/ (* (- cd bcd) acd) cd)
                  (/ (- (+ (* b a) (* bcd a) (* b acd) (* bcd acd) (* f2 bd d) (* f2 bc d) (* f1 bd c) (* f1 bc c) (* f1 c) (* f1 cd c)
                                    (* f2 d) (* f2 cd d) (* d acd) (* c acd) (* d a) (* c a))
                              (+ (* cd a) a (* cd acd) acd (* f2 c d) (* f2 (expt d 2)) (* f1 (expt c 2)) (* f1 d c) (* f2 b d)
                                    (* f2 bcd d) (* f1 b c) (* f1 bcd c) (* bd a) (* bc a) (* bd acd) (* bc acd)))
                        (- (+ c d) (+ 1 cd)))
                  (/ (- (+ (* f2 bd d) (* bcd acd) (* d acd) (* f2 cd d))
                              (+ (* f2 (expt d 2)) (* cd acd) (* bd acd) (* f2 bcd d)))
                        (- cd d))
                  (/
                        (- (+ (* f1 bcd c) (* bc acd)) (+ (* bcd acd) (* f1 bc c)))
                        (- cd c))
                  (/ (* bcd acd) cd)
                  (/ (- (+ (* bc acd) (* bd acd) (* bc a) (* bd a) (* f1 bcd c) (* f1 b c) (* f2 bcd d) (* f2 b d))
                              (+ (* f1 bc c) (* f1 bd c) (* f2 bc d) (* f2 bd d) (* bcd acd) (* b acd) (* bcd a) (* b a)))
                        (- (+ c d) (+ 1 cd)))
                  (/
                        (- (+ (* f2 bcd d) (* bd acd)) (+ (* bcd acd) (* f2 bd d)))
                        (- cd d))))
    (terpri) (print-tree (factor (mem2 x))))
|#
    
#|
;; This will factor (a^2 + 2ab + b^2), but still not (a^2 - b^2).
(defun factor1 (term)
    (cond
      ((atom term) term)
      ((or (eq (car term) '+) (eq (car term) '-))
        (let* ((a (first-non-number (dif-atoms term)))
                  (d* (simplified-form term))
                  (d1* (mem1 d*))
                  (d2* (mem2 d*)))
           (dolist (a* (term-atoms a))  ;; we need subterms rather than term-atoms
               (let ((d1 (subset #'(lambda (x) (subproduct a* x)) d1*))
                       (d2 (subset #'(lambda (x) (subproduct a* x)) d2*)))
                  (cond
                    ((or d1 d2)
                      (let* ((ff (decrement-term-count a* (format-difference (list d1 d2))))
                                (factors (possible-factors ff)))
                         (dolist (f factors)
                             (let ((f2 (divide-difference term f)))
                                (when f2 (return-from factor1 (list '* f f2)))))))
                    (t term))))))
      (t term)))

(defun possible-factors (factor)
    (let* ((f* (simplified-form factor))
              (sd1 (powerset (mem1 f*)))
              (sd2 (powerset (mem2 f*)))
              (factors (remove '(nil nil) (crossproduct sd1 sd2) :test 'equal)))
       (mapcar
         #'format-difference
         (order factors
                     #'(lambda (x y) (> (+ (length (mem1 x)) (length (mem2 x)))
                                                     (+ (length (mem1 y)) (length (mem2 y)))))))))
|#

;; This divides difference by term.
(defun divide-difference (dif fac &optional (recursive-call nil))
    ; (progn (terpri) (prin1 dif) (princ " / ") (prin1 fac))
    (cond
      ((eq fac 1) dif)
      ((equal fac '(- 1)) (negate dif))
      ((atom fac) (decrement-term-count fac dif))
      ((and (eq (car fac) '-) (null (mem3 fac)))
        (cond
          ((atom (mem2 fac)) (decrement-term-count (mem2 fac) (negate dif)))
          (t (divide-difference (negate dif) (mem2 fac)))))
      ((term-equal dif fac) 1)
      ((term-neg-equal dif fac) -1)
      ((listp dif)
        (let ((n (ignore-errors (eval fac))))
           (cond
             ((and (not (eq n 0)) (integerp n)) (divide-by-integer dif n))
             (t
               (let ((terms (factor-terms fac))
                       (atoms (dif-atoms fac)))
                  ;; if dif contains a term in which no atoms from fac occur, division is impossible.
                  (when
                       (or (member 1 atoms) (member -1 atoms)
                             (not
                               (or
                                 (and (atom dif) (not (member dif atoms)))
                                 (and
                                   (listp dif)
                                   (or (and
                                           (eq (car dif) '+)
                                           (some #'(lambda (x) (not (some #'(lambda (y) (occur* y x)) atoms))) (cdr dif)))
                                         (and
                                           (eq (car dif) '-)
                                           (or
                                             (and (atom (mem2 dif)) (not (member (mem2 dif) atoms)))
                                             (and
                                               (listp (mem2 dif)) (eq (mem1 (mem2 dif)) '+)
                                               (some #'(lambda (x) (not (some #'(lambda (y) (occur* y x)) atoms)))
                                                            (cdr (mem2 dif))))
                                             (and
                                               (listp (mem2 dif)) (eq (mem1 (mem2 dif)) 'expt)
                                               (not (member (mem2 (mem2 dif)) atoms)))
                                             (and (mem3 dif) (atom (mem3 dif)) (not (member (mem3 dif) atoms)))
                                             (and
                                               (mem3 dif) (listp (mem3 dif)) (eq (mem1 (mem3 dif)) 'expt)
                                               (not (member (mem2 (mem3 dif)) atoms)))
                                             (and
                                               (mem3 dif) (listp (mem3 dif)) (eq (mem1 (mem3 dif)) '+)
                                               (some 
                                                 #'(lambda (x) (not (some #'(lambda (y) (occur* y x)) atoms)))
                                                 (cdr (mem3 dif)))))))))))
                       (let ((s-atoms (subset #'(lambda (x) (no-exponentiation-in-formula x dif)) (term-atoms fac))))
                          (cond    ;; case (2)
                            (s-atoms (divide-simple-difference dif fac s-atoms terms))
                            (t
                              (let* ((x (first-non-number atoms)))
                                 (when (occur* x dif)
                                      (let* ((n (max-exponent x dif))  ;; we know that n >= 2.
                                                (m (max-exponent x fac))
                                                (fx (subterm-of #'(lambda (y)
                                                                                 (cond ((> m 1) (subproduct (list 'expt x m) y))
                                                                                             (t (subproduct x y)))) fac))
                                                (f (factor-atom x fx))
                                                (axn-1 (divide-difference
                                                              (decrement-term-count
                                                                x (subterm-of #'(lambda (g) (subproduct (list 'expt x n) g)) dif))
                                                              f))
                                                (dif* (subtract-terms dif (multiply-terms fac axn-1))))
                                         (when axn-1
                                              (cond ((eq dif* 0) axn-1)
                                                          (t
                                                            (let ((factor (divide-difference dif* fac t)))
                                                               (when factor
                                                                    (setf factor (simplify-sum (list '+ axn-1 factor)))
                                                                    (cond ((null recursive-call)
                                                                                 (when (eq 0 (subtract-terms dif (multiply-terms factor fac)))
                                                                                      factor))
                                                                                (t factor)))))))))))))))))))))

;; n is an integer
(defun divide-by-integer (dif n)
    (when (listp dif)
         (cond ((eq (car dif) '+)
                      (as-sum
                        (unionmapcar 
                          #'(lambda (y)
                                (multiple-value-bind
                                     (k remainder)
                                     (round (/ (count y (cdr dif) :test #'term-equal) n))
                                     (when (not (zerop remainder)) (return-from divide-by-integer))
                                     (let ((z nil)) (dotimes (i k) (push y z))
                                            z)))
                          (remove-duplicates (cdr dif) :test 'term-equal))))
                     ((eq (car dif) '-)
                       (cond ((mem3 dif)
                                    (let ((d1 (divide-by-integer (mem2 dif) n)))
                                       (when d1
                                            (let ((d2 (divide-by-integer (mem3 dif) n)))
                                               (when d2 (list '- d1 d2))))))
                                   (t 
                                     (let ((d1 (divide-by-integer (mem2 dif) n)))
                                        (when d1 (list '- d1)))))))))

#|

(divide-difference
  '(- (+ (* cd f1 c) (* f1 c) (* cd f1 c) (* f1 c) 1 cd (expt cd 2) (* cd f1 c) (* cd f1 c) cd (* f1 c) (* f1 c)
           (* c a) (* c a) (expt c 2) (* c acd) (* c acd) (expt c 2) (* c a) (* c a) (expt c 2) (* c acd) (* c acd)
           (expt c 2) (expt a 2) (* a acd) (* acd a) (expt acd 2) (* (expt f1 2) (expt c 2))
           (* (expt f1 2) (expt c 2)) (* (expt f1 2) (expt c 2))
           (* (expt f1 2) (expt c 2)))
    (+ (* a f1 c) (* a f1 c) (* acd f1 c) (* acd f1 c) (* f1 c a) (* f1 c acd) (* f1 c a) (* f1 c acd)
         (* f1 (expt c 2)) (* f1 (expt c 2)) (* c cd) (* f1 (expt c 2)) (* f1 (expt c 2))
         (* c cd) c acd acd c a a (* cd c) (* cd acd) (* cd acd) (* cd c) (* cd a) (* cd a) c c (* f1 (expt c 2))
         (* f1 (expt c 2)) (* f1 (expt c 2)) (* f1 (expt c 2))))
  '(- (+ 1 cd (* c f1) (* c f1)) (+ a acd c c)))
  
|#

(defun subtract-terms (x y)
    (simplify-difference (list '- x y)))

(defun multiply-terms (x y)
    (format-difference (expand-product (list '* x y))))

(defun first-non-number (X)
    (if (numberp (car X)) (first-non-number (cdr X)) (car X)))

#| s-atoms is the set of atoms from fac occuring without exponents in dif. When
s-atoms is non-empty, we can just find the subset of terms of dif in which an
s-atom occurs, divide by the s-atom and its coefficient, and return the result. |#
(defun divide-simple-difference (dif fac s-atoms terms)
    (let ((s-atom (find-if #'(lambda (x) (occurs-once-in x terms)) s-atoms)))
       (when (null s-atom) (setf s-atom (car s-atoms)))
       (let ((sa (subterm-for s-atom fac)))
          (when sa
               (let* ((a (factor-atom s-atom sa))
                         (sf (subterm-for s-atom dif)))
                  (when sf
                       (let ((factor (divide-difference (factor-atom s-atom sf) a)))
                          (when (eq 0 (subtract-terms dif (multiply-terms factor fac))) factor))))))))

;; fac is an atom, an exponentiation, a power of the latter, or a sum or difference of such products and terms.
(defun dif-atoms (fac)
       (cond ((null fac) nil)
                   ((atom fac) (list fac))
                   ((eq (car fac) 'expt) (list (mem2 fac)))
                   ((eq (car fac) '*) (unionmapcar+ #'dif-atoms (cdr fac)))
                   ((eq (car fac) '+) (unionmapcar+ #'dif-atoms (cdr fac)))
                   ((eq (car fac) '-) (union (dif-atoms (mem2 fac)) (dif-atoms (mem3 fac))))))

;; fac is an atom, an exponentiation, a power of the latter, or a sum or difference of such products and terms.
;; This lists duplicate terms separately.
(defun factor-terms (fac)
       (cond ((null fac) nil)
                   ((atom fac) (list fac))
                   ((eq (car fac) 'expt) (list fac))
                   ((eq (car fac) '*) (list fac))
                   ((eq (car fac) '+) (cdr fac))
                   ((eq (car fac) '-) (append (factor-terms (mem2 fac)) (factor-terms (mem3 fac))))))

;; x occurs in only one term in terms
(defun occurs-once-in (x terms)
    (let* ((z (find-if #'(lambda (y) (occur* x y)) terms)))
       (and z (every #'(lambda (w) (not (occur* x w))) (remove z terms :count 1)))))

;; This is the subterm of dif (usually a sum or difference) consisting of all subterms of dif satisfying F. 
(defun subterm-of (F dif)
    (cond ((atom dif) (when (funcall F dif) dif))
                ((eq (car dif) 'expt) (when (funcall F dif) dif))
                ((eq (car dif) '*) (when (funcall F dif) dif))
                ((eq (car dif) '+) (as-sum (remove nil (mapcar #'(lambda (y) (subterm-of F y)) (cdr dif)))))
                ((eq (car dif) '-) 
                  (let ((s1 (subterm-of F (mem2 dif)))
                          (s2 (subterm-of F (mem3 dif))))
                     (cond (s2
                                  (cond (s1 (list '- s1 s2))
                                              (t (list '- s2))))
                                 ((mem3 dif) s1)
                                 (s1 (list '- s1)))))))

;; x is an atom and dif an atom, product, exponentation, sum or difference of the latter.
(defun subterm-for (x dif)
    (cond ((atom dif) (when (eq x dif) dif))
                ((eq (car dif) 'expt) (when (eq (mem2 dif) x) dif))
                ((eq (car dif) '*)
                  (when (or (mem x (cdr dif))
                                     (some #'(lambda (y) (and (exponentiationp y) (eq (mem2 y) x))) (cdr dif))) dif))
                ((eq (car dif) '+) (as-sum (remove nil (mapcar #'(lambda (y) (subterm-for x y)) (cdr dif)))))
                ((eq (car dif) '-) 
                  (let ((s1 (subterm-for x (mem2 dif)))
                          (s2 (subterm-for x (mem3 dif))))
                     (cond (s2
                                  (cond (s1 (list '- s1 s2))
                                              (t (list '- s2))))
                                 ((mem3 dif) s1)
                                 (s1 (list '- s1)))))))

;; sum is a list of atoms, exponentiations, or products of the latter. This returns the highest exponent 
;; of x occurring in any of the terms in sum. We know it is >= 1, so we only need check exponentiations.
(defun max-exponent (x sum)
    (let ((terms (factor-terms sum))
            (n 1))
       (dolist (y terms)
           (when (listp y)
                (cond
                  ((and (eq (car y) 'expt) (eq (mem2 y) x) (numberp (mem3 y)) (> (mem3 y) n)) (setf n (mem3 y)))
                  ;; otherwise y is a product
                  (t (dolist (z (cdr y))
                         (when
                              (and (listp z) (eq (car z) 'expt) (eq (mem2 z) x) (numberp (mem3 z)) (> (mem3 z) n))
                              (setf n (mem3 z))))))))
       n))

(defun term-length (x)
    (let ((y (ignore-errors (eval x))))
       (or y
             (cond ((null x) 0)
                         ((atom x) 1)
                         ((eq (car x) '+) (apply '+ (mapcar #'term-length (cdr x))))
                         ((eq (car x) '-) (+ (term-length (mem2 x)) (term-length (mem3 x))))
                         ((eq (car x) '/) (+ (term-length (mem2 x)) (term-length (mem3 x))))
                         ((eq (car x) '*) (apply '+ (mapcar #'term-length (cdr x))))
                         ((eq (car x) 'expt) (* (term-length (mem2 x)) (term-length (mem3 x))))
                         (t 1)))))

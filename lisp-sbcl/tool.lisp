(proclaim
  '(special pause-flag *metered-calls* *callees* *blank-line* *line-columns* *uncalled-callers*))

(setf *tools-loaded* t)
(defvar *old-definitions* nil)

;                                                           *MACROS*

(defmacro mem1 (x) `(car ,x))
(defmacro mem2 (x) `(cadr ,x))
(defmacro mem3 (x) `(nth 2 ,x))
(defmacro mem4 (x) `(nth 3 ,x))
(defmacro mem5 (x) `(nth 4 ,x))
(defmacro mem6 (x) `(nth 5 ,x))
(defmacro mem7 (x) `(nth 6 ,x))
(defmacro mem8 (x) `(nth 7 ,x))
(defmacro mem9 (x) `(nth 8 ,x))
(defmacro mem10 (x) `(nth 9 ,x))
(defmacro mem11 (x) `(nth 10 ,x))
(defmacro mem12 (x) `(nth 11 ,x))
(defmacro mem13 (x) `(nth 12 ,x))
(defmacro mem14 (x) `(nth 13 ,x))
(defmacro mem15 (x) `(nth 14 ,x))
(defmacro mem16 (x) `(nth 15 ,x))
(defmacro mem17 (x) `(nth 16 ,x))
(defmacro mem18 (x) `(nth 17 ,x))

;nth element of sequence x:
(defmacro element (n x) `(nth ,n ,x))

(defmacro lastmember (x) `(car (last ,x)))

(defmacro for-all (x f) (list 'mapc f x))

(defmacro do-until (P Q)
  (list 'loop Q (list 'if P '(return))))

;pretty print function definition (takes unquoted argument):
(defmacro pp (f) `(let ((pv *print-level*)
                        (pl *print-length*))
                    (setq *print-level* nil)
                    (setq *print-length* nil)
                    (pprint (symbol-function ,f))
                    (setq *print-level* pv)
                    (setq *print-length* pl)))

;to test the efficiency of different values of the parameter param in
;the list A.  Takes unquoted arguments for param and prog:
(defmacro parameter-test (A param prog)
  `(progn (o-terpri) (gc)
          (for-all ,A #'(lambda (n)
                          (setq ,param n)
                          (o-princ "for ") (o-prin1 ',param)
                          (o-princ " = ") (o-prin1 n) (o-princ ":")
                          (time ,prog)
                          (gc)))))

(defmacro image (K f)
  `(mapcar ,f ,K))

(defmacro unionimage (K f)
  `(genunion (mapcar ,f ,K)))

#| The following is unnecessary, because genunion already deletes duplicates. |#
(defmacro unionimage+ (K f)
  `(remove-duplicates (genunion (mapcar ,f ,K)) :test 'equal))

;This puts something at the front of a queue with index 0:
(defmacro 0-insert (F x A)
  `(setf (,F ,A) (cons 0 (cons (cons 0 ,x) (cadr (,F ,A))))))

(defmacro pull (x s)
  `(setf ,s (remove-if-equal ,x ,s)))

#| This redefines a constant defined by defconstant. |#
(defmacro redefine-constant (x val)
  `(progn
     (makunbound ',x)
     (defconstant ,x ,val)))

(defmacro unionmapcar (f A) `(apply 'append (mapcar, f ,A)))

;This removes duplicates with test eq.
(defmacro unionmapcar+ (f X)
  `(let ((U nil))
     (dolist (y ,X)
       (dolist (z (funcall ,f y))
         (pushnew z U)))
     U))

;This removes duplicates with test equal.
(defmacro unionmapcar= (f X)
  `(let ((U nil))
     (dolist (y ,X)
       (dolist (z (funcall ,f y))
         (pushnew z U :test 'equal)))
     U))

;This removes duplicates with test equal.
(defmacro unionmapcar2= (f X Y)
  `(let ((U nil)
         (X* ,X)
         (Y* ,Y))
     (loop
       (when (null X*) (return U))
       (dolist (z (funcall ,f (mem1 X*) (mem1 Y*)))
         (pushnew z U :test 'equal))
       (setf X* (cdr X*))
       (setf Y* (cdr Y*)))))

(defmacro unionmapcar- (f X &key (test 'eq))
  `(let ((U nil))
     (dolist (y ,X)
       (dolist (z (funcall ,f y))
         (pushnew z U :test ,test)))
     U))

(defun print-pretty (x &optional stream)
  (let ((pp *print-pretty*))
    (setf *print-pretty* t)
    (prin1 x stream)
    (setf *print-pretty* pp)))

(proclaim '(special *indent-depth* *call-number*))

;                        * SET FUNCTIONS *

(defun mem (element  set)
  (member element set :test 'equal))

;set-equality:
(defun == (x y)
  (or (eq x y)
      (and (listp x) (listp y)
           (subsetp x y :test 'equal)
           (subsetp y x :test 'equal))))

;; this returns three values: (union x y), (setdifference x y), and (setdifference y x),
;; but if a symbol occurs multiple times in x or y, they are treated as different smbols.
(defun compare-lists (x y &key (test #'eq))
  (let ((xy nil))
    (dolist (z x)
      (block x+
             (dolist (w y)
               (cond ((funcall test z w)
                      (setf x (remove z x :count 1 :test test))
                      (setf y (remove z y :count 1 :test test))
                      (push z xy) (return-from x+ nil))))))
    (values xy x y)))

#|
(compare-lists '(a a b c) '(a b c d)) returns
(c b a)
(a)
(d)
|#

(defun === (x y &key (test 'equal))
  (or (eq x y)
      (and (listp x) (listp y)
           (multiple-value-bind
             (u d1 d2)
             (compare-lists x y :test test)
             (declare (ignore u))
             (and (null d1) (null d2))))))

(defun << (x y) (< (round (* 10000 x)) (round (* 10000 y))))

(defun >> (x y) (> (round (* 10000 x)) (round (* 10000 y))))

(defun <<= (x y)
  (or (eql x y) (<= (round (* 10000 x)) (round (* 10000 y)))))

(defun >>= (x y)
  (or (eql x y) (>= (round (* 10000 x)) (round (* 10000 y)))))

(defun >< (x y)
  (or (eql x y) (eql (round (* 10000 x)) (round (* 10000 y)))))

(defun union= (x y) (union x y :test 'equal))

(defun adjoin= (x y) (adjoin x y :test 'equal))

(defun remove-duplicates= (x)
  (remove-duplicates x :test 'equal))

(proclaim '(sb-ext:maybe-inline subset))
(defun subset (f l)
  (remove-if-not f l))

(defun subsetp= (X Y)
  (subsetp X Y :test 'equal))

(defun proper-subset (X Y)
  (and (subsetp= X Y) (not (subsetp= Y X))))

;x and y are disjoint, with test 'equal:
(defun disjoint (x y)
  (not (some #'(lambda (z) (mem z y)) x)))

;x and y are disjoint, with test 'eq:
(defun disjointp (x y)
  (not (some #'(lambda (z) (member z y)) x)))

(defun crossproduct (A B)
  (let ((U nil))
    (dolist (x A)
      (dolist (y B)
        (push (list x y) U)))
    U))

(defun dot-product (x y)
  (unionmapcar #'(lambda (w) (mapcar #'(lambda (z) (cons w z)) y)) x))

;domain, range, and inverse of a set of ordered pairs:
(defun domain (x) (remove-duplicates (mapcar #'car x) :test 'equal))

(defun range (x) (remove-duplicates (mapcar #'cadr x) :test 'equal))

;range of an association list:
(defun a-range (x) (remove-duplicates (mapcar #'cdr x) :test 'equal))

(defun inverse (R) (mapcar #'reverse R))

;(defun genunion (x) (apply 'append x))
#| The following removes duplicates too. |#
(defun genunion (x)
  (let ((union nil))
    (dolist (y x)
      (dolist (z y)
        (when (not (mem z union)) (push z union))))
    union))

(defun genunion+ (x)
  (let ((union nil))
    (dolist (y x) (dolist (z y) (pushnew z union)))
    union))

(defun =intersection (x y) (intersection x y :test 'equal))

(defun gen-intersection (x)
  (cond ((null x) nil)
        ((equal (length x) 1) (mem1 x))
        (t (=intersection (mem1 x) (gen-intersection (cdr x))))))

(defun gencrossproduct (A)
  (let ((U nil))
    (cond ((cddr A)
           (dolist (x (car A))
             (dolist (y (gencrossproduct (cdr A)))
               (push (cons x y) U)))
           U)
          ((cdr A) (crossproduct (car A) (cadr A)))
          (t (mapcar #'list (car A))))))

(defun powerset (X)
  (cond ((null X) (list nil))
        (t (let ((p (powerset (cdr X))))
             (union= p (mapcar #'(lambda (Y) (cons (car X) Y)) p))))))

(defun setdifference (x y) (set-difference x y :test 'equal))

(defun list-complexity (x)
  (cond ((null X) 0)
        ((stringp x) 1)
        ((atom x) 1)
        ((listp x) (apply #'+ (mapcar #'list-complexity x)))))


;;                        * LIST FUNCTIONS *
;
;
;(defun cadadr (x) (cadr (cadr x)))
;(defun cddddr (x) (cdr (cdddr x)))
(defun cdddddr (x) (cdr (cddddr x)))
(defun caddddr (x) (car (cddddr x)))
(defun cadddddr (x) (car (cdddddr x)))
(defun cddddddr (x) (cdr (cdddddr x)))
(defun caddddddr (x) (car (cddddddr x)))
(defun member1 (x) (car x))
(defun member2 (x) (cadr x))
(defun member3 (x) (nth 2 x))
(defun member4 (x) (nth 3 x))
(defun member5 (x) (nth 4 x))
(defun member6 (x) (nth 5 x))
(defun member7 (x) (nth 6 x))
(defun member8 (x) (nth 7 x))
(defun member9 (x) (nth 8 x))
(defun member10 (x) (nth 9 x))
(defun member11 (x) (nth 10 x))
(defun member12 (x) (nth 11 x))
(defun member13 (x) (nth 12 x))
(defun member14 (x) (nth 13 x))
(defun member15 (x) (nth 14 x))
(defun member16 (x) (nth 15 x))
(defun member17 (x) (nth 16 x))
(defun member18 (x) (nth 17 x))

;list of first n members of s:
(proclaim '(sb-ext:maybe-inline first-n))
(defun first-n (n s)
  (subseq s 0 n))

;This returns the (max m n) if both are non-null:
(defun max+ (m n)
  (if m
    (if n (max m n) m)
    n))

#|  This returns the maximum of an nonempty set of numbers.  |#
(defun maximum (X) (apply #'max X))

#|  This returns the maximum of an nonempty set of numbers.  |#
(defun minimum (X) (apply #'min X))

#|  This returns 0.0 if X is empty, otherwise the maximum of X.  |#
(defun maximum0 (X) (if X (apply #'max X) 0.0))

#|  This returns 0.0 if X is empty, otherwise the minimum of X.  |#
(defun minimum0 (X) (if X (apply #'min X) 0.0))

#| This returns T if F is nil, otherwise it funcalls F. |#

(defun funcall* (f x) (or (null f) (funcall f x)))

(defmacro funcall+ (F &rest x)
  `(or (null ,F) (funcall ,F ,@x)))

;Given a list of lists, this returns the (or a) longest member:
(defun longest (s) (prog (m n rest)
                         (setq rest (cdr s))
                         (setq m (car s))
                         (setq n (length m))
                         loop
                         (cond ((null rest) (return m)))
                         (cond ((> (length (car rest)) n)
                                (setq m (car rest)) (setq n (length m))))
                         (setq rest (cdr rest))
                         (go loop)))

;first member of sequence x having property p, or "none" if there is none:
(defun first-p (x P) (cond ((null x) "none")
                           ((funcall P (car x)) (car x))
                           (t (first-p (cdr x) P))))

;R-first member of sequence x, or "none" if x is nil:
(defun r-first (x R)
  (cond ((null x) "none")
        (t
          (do ((rest (cdr x) (cdr rest))
               (first (car x) (cond
                                ((funcall R first (car rest)) first)
                                (t (car rest)))))
            ((null rest) first)))))

(defun order (X R)
  (let ((X* (copy-list X)))
    (sort X* R)))

#| This returns the set of non-repeating subsets of length i of X. |#
(defun fixed-length-subsets (n set)
  (cond  ((> n (length set)) nil)
         ((zerop n) (list nil))
         ((= n 1) (mapcar #'list set))
         (t  (append (mapcar #'(lambda (a) (cons (car set) a))
                             (fixed-length-subsets (- n 1) (cdr set)))
                     (fixed-length-subsets n (cdr set))))))

#| This returns the set of all minimal subsets of X that have the property P. |#
(defun minimal-subsets (X P)
  (cond ((funcall P nil) (list nil))
        (t
          (let ((S nil))
            (dotimes (i (length X))
              (let ((candidates
                      (subset #'(lambda (fs)
                                  (every #'(lambda (s*) (not (subsetp= s* fs))) S))
                              (fixed-length-subsets (1+ i) X))))
                (when (null candidates) (return S))
                (dolist (y candidates)
                  (when (funcall P y) (push y S)))))
            S))))

#| This returns the set of all maximal subsets of X that have the property P. |#
(defun maximal-subsets (X P)
  (cond ((funcall P X) (list X))
        (t
          (let ((S nil))
            (dotimes (i (length X))
              (let ((candidates
                      (subset #'(lambda (fs)
                                  (every #'(lambda (s*) (disjoint s* fs)) S))
                              (fixed-length-subsets (1+ i) X))))
                (when (null candidates) (return S))
                (dolist (y candidates)
                  (let ((y* (setdifference X y)))
                    (when (funcall P y*) (push y* S))))))
            S))))

(defun ordered-insert (x queue R)
  "queue is a list ordered by R, and x is a new member to be inserted
  into the right position in the ordering.  This returns the new ordered list."
  (let ((head nil)
        (tail queue))
    (loop
      (when (null tail) (return (reverse (cons x head))))
      (let ((y (mem1 tail)))
        (cond ((funcall R y x)
               (push y head)
               (setf tail (cdr tail)))
              (t
                (push x tail)
                (dolist (z head) (push z tail))
                (return tail)))))))

;depth of a list:
(defun depth (s)
  (cond ((atom s) 1)
        (t (max (1+ (depth (car s))) (depth (cdr s))))))

(defun occur (x s &key (test 'eq))
  (and s (listp s)
       (or (funcall test (car s) x)
           (occur x (car s) :test test)
           (occur x (cdr s) :test test))))

(defun occur* (x s &key (test 'eq))
  (or (funcall test x s) (occur x s :test test)))

#| x occurs as a function-call in x. |#
(defun occur1 (x s &key (test 'eq))
  (and s (listp s) (not (eq (car s) 'quote))
       (cond ((eq (car s) 'dolist)
              (occur1 x (cddr s)))
             ((or (eq (car s) 'let) (eq (car s) 'let*))
              (or (occur1 x (cddr s))
                  (some #'(lambda (y) (occur1 x (mem2 y))) (cadr s))))
             (t
               (or (funcall test (car s) x)
                   (occur1 x (car s))
                   (and (listp (cdr s))
                        (some #'(lambda (y) (occur1 x y :test test)) (cdr s))))))))

;; the number of occurrences of x in s
(defun number-of-occurrences (x s)
  (cond ((atom s) (if (equal x s) 1 0))
        ((null s) 0)
        ((listp s) (+ (number-of-occurrences x (car s)) (number-of-occurrences x (cdr s))))))

(defun substructures (s)
  ;   (declare (inline unionmapcar))
  (cond ((atom s) nil)
        (t (cons s (unionmapcar #'substructures s)))))

;find substructures of s containing x:
(defun s-find (x s)
  (subset #'(lambda (y) (mem x y)) (substructures s)))

;substitution of one subsequence for another in a sequence:
(defun seq-subst (new old s)
  (declare (inline first-n))
  (cond ((< (length s) (length old)) s)
        ((equal old (first-n (length old) s))
         (append new (seq-subst new old (nthcdr (length old) s))))
        (t (cons (car s) (seq-subst new old (cdr s))))))

(defun =subst (a b c)
  (cond ((equal b c) a)
        ((listp c) (subst a b c :test 'equal))
        (t c)))

(defun subst* (a b c &key (test 'eq))
  (cond ((atom c) (if (funcall test b c) a c))
        (t (subst a b c :test test))))

(defun sublis= (m x)
  (cond ((listp x) (sublis m x :test 'equal))
        (t (car (sublis m (list x) :test 'equal)))))

(defun sublis-in-tree (m tree &key test)
  (cond ((atom tree) (car (sublis m (list tree) :test test)))
        (t (sublis m (mapcar #'(lambda (y) (sublis-in-tree m y :test test)) tree) :test test))))


;                  * INSERTION AND DELETION *

;remove uses 'eql'.  This uses 'equal':
(defun remove-if-equal (x y)
  (remove-if #'(lambda (z) (equal z x)) y))

#| replace first occurrence of x by y in S. |#
(defun replace-item-in-list (x y S)
  (let ((S0 S)
        (S* nil))
    (loop
      (when (equal x (car S0)) (return (append (reverse S*) (cons y (cdr S0)))))
      (push (car S0) S*)
      (setf S0 (cdr S0))
      (when (null S0) (return S)))))

;nondestructively delete nth member of y:
(defun delete-n (n y)
  (cond ((equal n (length y)) (first-n (1- n) y))
        ((> n (length y)) y)
        (t (append (first-n (1- n) y) (nthcdr n y)))))

;nondestructively splice x into y at the nth place:
(defun splice (x n y)
  (cond ((> n (length y)) (append y (list x)))
        (t (append (first-n (1- n) y) (list x) (nthcdr (1- n) y)))))

;This inserts x into its appropriate place in A where A is ordered by R.  If R
;is a < relation, this puts x at the end of the sublist of equivalent items, and if
;R is a <= relation, this puts it at the start of the sublist.
(defun insert (x A R)
  (let ((head nil)
        (tail A))
    (loop
      (cond ((null tail) (setq tail (list x)) (return))
            ((funcall R x (mem1 tail))
             (setq tail (cons x tail)) (return))
            (t (setq head (cons (mem1 tail) head))
               (setq tail (cdr tail)))))
    (loop
      (cond ((null head) (return))
            (t (setq tail (cons (mem1 head) tail))
               (setq head (cdr head)))))
    tail))


;                        * QUANTIFICATION *
#|
(defun unionmapcar (f A) (apply 'append (mapcar f A)))

;This removes duplicates with test eq.
(defun unionmapcar+ (f X)
  (let ((U nil))
    (dolist (y X)
      (dolist (z (funcall f y))
        (pushnew z U)))
    U))

;This removes duplicates with test equal.
(defun unionmapcar= (f X)
  (let ((U nil))
    (dolist (y X)
      (dolist (z (funcall f y))
        (pushnew z U :test 'equal)))
    U))

;This removes duplicates with test equal.
(defun unionmapcar2= (f X Y)
  (let ((U nil)
        (X* X)
        (Y* Y))
    (loop
      (when (null X*) (return U))
      (dolist (z (funcall f (mem1 X*) (mem1 Y*)))
        (pushnew z U :test 'equal))
      (setf X* (cdr X*))
      (setf Y* (cdr Y*)))))
|#
;an assignment is a function in extension.  The following checks to see
;whether a putative assignment is consistent, in the sense of assigning
;only one object to each element of the domain:

(defun consistent-assignment (s)
  (equal (length s) (length (domain s))))

;this returns the value of assignment for object obj:
(defun value (assignment obj)
  (declare (inline subset))
  (cadr (apply #'append
               (subset #'(lambda (val-arg) (equal (car val-arg) obj))
                       assignment))))

;This maps a binary function f onto a set x, holding y fixed:
(defun mapcar1 (f x y) (mapcar #'(lambda (z) (apply f (list z y))) x))


;                        * MISCELLANEOUS *

(defun e-assoc (x l)
  (cdr (assoc x l :test #'equal)))

;; The number of members of X satisfying F.
(defun number-of (X F)
  (cond ((null X) 0)
        ((funcall F (car x)) (1+ (number-of (cdr X) F)))
        (t (number-of (cdr X) F))))

;this returns the difference between two times t1 and t2 presented in
;the format of (multiple-value-list (get-decoded-time)):
(defun time-dif (t1 t2)
  (let ((X t1))
    (cond ((<= (car t2) (car t1))
           (setq X (list (- (car t1) (car t2)) (cadr X) (mem3 X))))
          (t (setq X (list (+ 60 (- (car X) (car t2))) (1- (cadr X))
                           (mem3 X)))))
    (cond ((<= (cadr t2) (cadr X))
           (setq X (list (car X) (- (cadr X) (cadr t2))
                         (mem3 X))))
          (t (setq X (list (car X) (+ 60 (- (cadr X) (cadr t2)))
                           (1- (mem3 X))))))
    (cond ((<= (mem3 t2) (mem3 X))
           (setq X (list (car X) (cadr X) (- (mem3 X) (mem3 t2)))))
          (t (setq X (list (car X) (cadr X)
                           (+ 24 (- (mem3 X) (mem3 t2)))))))))

(defun nseq (n)
  (do ((i 1 (1+ i))
       (s nil (cons i s)))
    ((> i n) (reverse s))))

(defun gdisc (f)
  (cond ((macro-function f) 'macro)
        ((special-operator-p f) 'nlambda)
        ((functionp f) 'lambda)
        (t f)))

(defun pl ()
  (if (null *print-level*) (setq *print-level* 4) (setq *print-level* nil)))

(defun unboundp (x) (not (boundp x)))

;                        * STRINGS *

(proclaim '(sb-ext:maybe-inline explode))
(defun explode (s)
  (mapcar #'string (coerce s 'list)))

(defun char-list (x)
  (declare (inline explode))
  (cond ((numberp x) (list (string (error "(+ 48 x)"))))
        ((characterp x) (list x))
        ((atom x) (explode (string x)))
        ((stringp x) (explode x))
        ))

(defun char-num (x)
  (mapcar
    #'(lambda (i) (char x i))
    (mapcar #'1- (nseq (length x)))))

(defun implode (x)
  "where x is a list of strings, this concatenates them into a single string"
  (if (null x) nil
    (concatenate 'string (car x) (implode (cdr x)))))

(defun string-rep (n) (write-to-string n))

(defun imp (s)
  (cond ((symbolp s) (string s))
        ((numberp s) (string-rep s))
        (t (coerce (mapcan #'char-num
                           (mapcan #'char-list s)) 'string))))

;this returns the integer named by a string:
(defun named-integer (s)
  (read-from-string s))

;this returns the decimal-number named by a string:
(defun named-decimal-number (string)
  (float (read-from-string string)))

;concatenate two strings:
(defun cat (x y)
  (concatenate 'string x y))

;(defun cat (x y)
;   (imp (append (explode x) (explode y))))

;concatenate a list of strings:
(defun cat-list (s)
  (cond ((null s) nil)
        (t (cat (mem1 s) (cat-list (cdr s))))))

;;This returns the substring of s from n through m inclusive.  If m is
;;omitted, it is set to the length of the string.
;;(defun substring (s n &optional (m))
;;   (subseq s n m))

#| This returns the word-strings in a string with spaces. |#
(defun word-list (string)
  (let ((letters (explode string))  ;; strings of length 1
        (words nil)
        (word nil))
    (dolist (letter letters)
      (cond ((equal letter " ")
             (push (implode (reverse word)) words)
             (setf word nil))
            (t (push letter word))))
    (if word (push (implode (reverse word)) words))
    (reverse words)))

#| example:
? (word-list "Who is Henry's father")
("Who" "is" "Henry's" "father")
|#

#| This turns a list of strings into a string with spaces. |#
(defun concatenate-words (word-list)
  (cond ((cdr word-list)
         (cat (car word-list)
              (cat " " (concatenate-words (cdr word-list)))))
        (t (car word-list))))

#| example:
? (concatenate-words '("Who" "is" "Henry's" "father"))
"Who is Henry's father"
|#

;This returns the length of a string representation of the tree s:
(defun string-length (s)
  (cond ((and s (listp s)) (+ 1 (length s) (apply #'+ (mapcar #'string-length s))))
        ((numberp s) (length (string-rep s)))
        (t (length (string s)))))

;	** MATCHING **

(defun match (pat exp var)
  (labels ((match* (pat exp var bindings)
                   (cond ((atom pat)
                          (cond ((mem pat var)
                                 (let ((assoc (assoc pat bindings :test 'equal)))
                                   (cond (assoc (equal exp (cdr assoc)))
                                         (t (list (cons pat exp))))))
                                (t (equal pat exp))))
                         ((listp pat)
                          (when (listp exp)
                            (let ((m (match* (car pat) (car exp) var bindings)))
                              (cond ((eq m t) (match* (cdr pat) (cdr exp) var bindings))
                                    (m (let ((m* (match* (cdr pat) (cdr exp) var (append m bindings))))
                                         (cond ((eq m* t) m)
                                               (m* (union= m m*))))))))))))
    (match* pat exp var nil)))

;this returns the association list of a match of variables to elements
;of s which, when substituted in l yields s.  So l is the pattern and s
;is the target.  If X is given, the match must be to members of X.
; This assumes that members of var do not occur in s.
;(defun match (pattern expression var &optional X)
;   (catch 'match (pattern-match pattern expression var X)))
;
;(defun pattern-match (l s var &optional X)
;   (cond ((equal l s) t)
;             ((atom l)
;              (cond ((and (mem l var)
;                                 (if X (mem s X) t))
;                         (list (cons l s)))
;                        (t (throw 'match nil))))
;             ((listp l)
;              (cond ((not (listp s)) (throw 'match nil))
;                        ((not (eq (length l) (length s))) (throw 'match nil))
;                        ((eql (length l) 1) (pattern-match (car l) (car s) var X))
;                        (t (let ((m (pattern-match (car l) (car s) var X)))
;                             (cond ((null m) (throw 'match nil)))
;                             (let ((l* (cond ((eq m t) (cdr l))
;                                                   (t (sublis= m (cdr l))))))
;                                 (cond ((eq m t) (pattern-match l* (cdr s) var X))
;                                           (t (let ((m* (pattern-match l* (cdr s)
;                                                      (setdifference var (domain m)) X)))
;                                                (cond ((eq m* t) m)
;                                                          (t (append m m*)))))))))))))

(defun merge-matches (m m*)
  (cond ((equal m t) m*)
        ((equal m* t) m)
        (t (union= m m*))))

(defun nseq< (n)
  (do ((i 0 (1+ i))
       (s nil (cons i s)))
    ((>= i n) (reverse s))))

;this substitutes in accordance with a match m:
(defun match-sublis (m x &key (test 'eq))
  (cond ((eq m t) x)
        (t (sublis m x :test test))))

(defun match-domain (m)
  (if (equal m t) nil (domain m)))

(defun consistent-match (p1 p2)
  (not (some #'(lambda (s)
                 (some #'(lambda (v) (and (equal (car s) (car v))
                                          (not (equal (cdr s) (cdr v)))))
                       p2)) p1)))

#| (set-match patterns data vars) returns the set of pairs (X m) where m is an a-list of
substitutions for members of vars and X is (mapcar #'(lambda (p) (match-sublis m p))
                                                   patterns), and X is a subset of data.  This asssumes that vars do not occur in data. |#
;(defun set-match (patterns data vars)
;   (catch 'match (set-match-no-catch patterns data vars)))
;
;(defun set-match-no-catch (patterns data vars)
;   (let ((matches nil)
;           (open nil)
;           (closed nil))
;     (dolist (P patterns)
;        (if (some #'(lambda (v) (occur v P)) vars)
;          (push P open)
;          (if (mem P data)
;            (push P closed)
;            (throw 'match nil))))
;     (cond (open
;                 (let ((P (mem1 open)))
;                   (dolist (Q data)
;                      (let ((m (match P Q vars)))
;                        (when m
;                            (dolist (sm (set-match-no-catch
;                                                 (match-sublis m (cdr open))
;                                                 data
;                                                 (setdifference vars (match-domain m))))
;                               (push (list (adjoin= Q (union= closed (mem1 sm)))
;                                                 (merge-matches m (mem2 sm)))
;                                          matches)))))))
;                (t (setf matches (list (list closed T)))))
;     (when (null matches) (throw 'match nil))
;     matches))

(defun set-match (patterns data vars)
  (catch 'match
         (let ((matches nil)
               (open nil)
               (closed nil))
           (dolist (P patterns)
             (if (some #'(lambda (v) (occur v P)) vars)
               (push P open)
               (if (mem P data)
                 (push P closed)
                 (throw 'match nil))))
           (cond (open
                   (let ((P (mem1 open)))
                     (dolist (Q data)
                       (let ((m (match P Q vars)))
                         (when m
                           (dolist (sm (set-match
                                         (match-sublis m (cdr open))
                                         data
                                         (setdifference vars (match-domain m))))
                             (push (list (adjoin= Q (union= closed (mem1 sm)))
                                         (merge-matches m (mem2 sm)))
                                   matches)))))))
                 (t (setf matches (list (list closed T)))))
           (when (null matches) (throw 'match nil))
           matches)))


;                        * CONFIGURATION *

(defun verbose-on ()
  (setq *load-verbose* t *verbose-eval-selection* t))

(defun verbose-off ()
  (setq *load-verbose* nil *verbose-eval-selection* nil))

(defun warn-on ()
  (setq *warn-if-redefine* t))

(defun warn-off ()
  (setq *warn-if-redefine* nil))

(defun lessp (x y)
  (cond ((characterp x)
         (cond ((characterp y) (char< x y))
               (t t)))
        ((stringp x)
         (cond ((stringp y) (string< x y))
               (t t)))
        ((symbolp x)
         (cond ((equal x y) nil)
               ((symbolp y)
                (string<  (string x) (string y)))
               ((listp y) t)
               (t nil)))
        ((and (listp x) (listp y))
         (cond ((equal x y) nil)
               ((lessp (car x) (car y)) t)
               ((lessp (car y) (car x)) nil)
               (t (lessp (cdr x) (cdr y)))))))

;This takes quoted arguments:
(defun gfunc (f)
  (eval (list 'function f)))

(setq *print-level* nil)

(defun factorial (n)
  (cond ((zerop n) 1)
        (t (* n (factorial (1- n))))))

;(setq param-list '(1.0 1.1 1.2 1.3 1.4 1.5 1.6 1.7 1.8 1.9 2.0))

(defun pause ()
  (when (and (equal pause-flag t) (equal (read-char) 98)) (break)))

(defun pause-flag-on (&optional x)
  (cond (x (setq pause-flag x))
        (t (setq pause-flag t))))

(defun pause-flag-off () (setq pause-flag nil))

(when (null *syntax-loaded*)
  (load (concatenate 'string oscar-pathname "syntax"))
  (setf *syntax-loaded* t))

(defun blank-indent (depth &optional stream)
  (dotimes (i depth) (princ "  " stream)))

(defun bar-indent (depth)
  (dotimes (i depth)
    (if (zerop (rem i 4)) (princ "|") (princ ". "))))

(defun indent (depth &optional stream)
  (dotimes (i depth) (princ ". " stream)))

;print members of a sequence on consecutive lines:
(defun p-print (x &optional indent)
  (terpri)
  (mapc #'(lambda (l) (when indent (blank-indent indent)) (prin1 l) (terpri)) x)
  nil)

(defun p-princ (x)
  (mapc #'(lambda (l) (princ l) (terpri)) x)
  nil)

#| This prints a list, putting at most n items on a line. |#
(defun print-list (L &optional (n 1) (indent-depth 0) stream)
  (indent indent-depth stream)
  (princ "(" stream)
  (let ((i 1)
        (to-print L))
    (dolist (y L)
      (princ y stream)
      (setf to-print (cdr to-print))
      (cond ((eql i n)
             (setf i 1)
             (when (not (null to-print)) (terpri stream) (indent indent-depth stream)
               (princ "  " stream)))
            ((not (null to-print))
             (incf i)
             (princ " " stream))))
    (princ ")" stream)
    ; (terpri)
    ))

(defun princ-list (L)
  (princ (car L))
  (when (cdr L)
    (dolist (x (cdr L))
      (princ ", ") (princ x))))

(defun p-print-list (L &optional (n 1) (indent-depth 0))
  (indent indent-depth)
  (princ "(") (terpri)
  (dolist (X L)
    (cond ((listp L) (print-list X n (1+ indent-depth)) (terpri))
          (t (princ X) (terpri))))
  (indent indent-depth)
  (princ ")") (terpri))

(defun prinp (P &optional stream)
  "pretty-print a putative formula"
  (princ (pretty P) stream))

(defun set-prinp (X &optional stream)
  "pretty-print a set of formulas"
  (princ "{ " stream)
  (when X
    (prinp (mem1 X) stream)
    (for-all (cdr X) #'(lambda (Q) (princ " , " stream) (prinp Q stream))))
  (princ " }" stream))

(defun prinp-sequent (X &optional stream)
  "pretty-print a sequent"
  (prinp (sequent-formula X) stream)
  (when (sequent-supposition X)
    (princ " supposing " stream)
    (set-prinp (sequent-supposition X) stream))
  X)

(defun princ-set (X &optional stream)
  "pretty-print a set"
  (princ "{ " stream)
  (when X
    (princ (mem1 X) stream)
    (for-all (cdr X) #'(lambda (Q) (princ " , " stream) (princ Q stream))))
  (princ " }" stream))

;pretty print a set of sequents
(defun princ-sequent-set (X &optional stream)
  (princ "{ " stream)
  (when X
    (prinp-sequent (mem1 X) stream)
    (for-all (cdr X) #'(lambda (Q) (princ " , " stream) (prinp-sequent Q stream))))
  (princ " }" stream))


(defun order-1 (x y) (< (mem1 x) (mem1 y)))

(defun order-2 (x y) (< (mem2 x) (mem2 y)))

(defun order-3 (x y) (< (mem3 x) (mem3 y)))

(defun order-4 (x y) (< (mem4 x) (mem4 y)))

;This returns the ratio of m and n as a real number, to two decimal places:
(defun real-ratio (m n)
  (cond ((zerop n) nil)
        (t (/ (coerce (round (coerce (* 100 (/ m n)) 'float)) 'float) 100))))

;This returns (expt m (/ 1 n)) as a real number, to two decimal places:
(defun real-root (m n)
  (cond ((zerop n) nil)
        (t (/ (coerce (round (coerce (* 100 (expt m (/ 1 n))) 'float)) 'float) 100))))

(defun line-indent (n)
  (dotimes (x n)
    (princ "	") (when (mem (1+ x) *line-columns*) (princ "|"))))

(defvar *tools-loaded* t)

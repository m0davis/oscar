
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

;;================================

(defun occur (x s &key (test 'eq))
    (and s (listp s)
              (or (funcall test (car s) x)
                    (occur x (car s) :test test)
                    (occur x (cdr s) :test test))))

(defun occur* (x s &key (test 'eq))
   (or (funcall test x s) (occur x s :test test)))

(defun mem (element  set)
   (member element set :test 'equal))

(defun union= (x y) (union x y :test 'equal))

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

(defun subset (f l)
   (remove-if-not f l))

(defun subsetp= (X Y)
   (subsetp X Y :test 'equal))

(defun crossproduct (A B)
    (let ((U nil))
       (dolist (x A)
           (dolist (y B)
               (push (list x y) U)))
       U))

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

(defun nseq (n)
   (do ((i 1 (1+ i))
          (s nil (cons i s)))
         ((> i n) (reverse s))))

(defun domain (x) (remove-duplicates (mapcar #'car x) :test 'equal))

(defun e-assoc (x l)
   (cdr (assoc x l :test #'equal)))

(defun order (X R)
   (let ((X* (copy-list X)))
     (sort X* R)))

;concatenate two strings:
(defun cat (x y)
    (concatenate 'string x y))

;concatenate a list of strings:
(defun cat-list (s)
   (cond ((null s) nil)
             (t (cat (mem1 s) (cat-list (cdr s))))))

(defun explode (s)
   (mapcar #'string (coerce s 'list)))

;remove uses 'eq'.  This uses 'equal':
(defun remove-if-equal (x y)
   (remove-if #'(lambda (z) (equal z x)) y))

(defun subst* (a b c &key (test 'eq))
    (cond ((atom c) (if (funcall test b c) a c))
                (t (subst a b c :test test))))

(defun indent (depth &optional stream)
    (dotimes (i depth) (princ ". " stream)))

(defun blank-indent (depth &optional stream)
    (dotimes (i depth) (princ "  " stream)))

(defun bar-indent (depth)
    (dotimes (i depth)
        (if (zerop (rem i 4)) (princ "|") (princ ". "))))

(defun princ-list (L)
    (princ (car L))
    (when (cdr L)
         (dolist (x (cdr L))
             (princ ", ") (princ x))))

;print members of a sequence on consecutive lines:
(defun p-print (x &optional indent)
   (terpri)
   (mapc #'(lambda (l) (when indent (blank-indent indent)) (prin1 l) (terpri)) x)
   nil)

(defun display-run-time-in-seconds (time)
   (let* ((sec (truncate (/ time internal-time-units-per-second)))
            (thousandths
             (round (/ (* 1000 (- time (* internal-time-units-per-second sec)))
                             internal-time-units-per-second))))
      (when (eql thousandths 1000)
           (incf sec)
           (setf thousandths 0))
     (princ sec) (princ ".")
     (cond ((< thousandths 10) (princ "00"))
               ((< thousandths 100) (princ "0")))
     (princ thousandths) (princ " sec")))

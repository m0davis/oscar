(proclaim '(optimize (debug 3)))

(proclaim
  '(special *act-executors* *altered-nodes* *answered-discount*
            *auxiliary-backwards-rules* *auxiliary-forwards-rules*
            *auxiliary-forwards-rules* *backwards-logical-reasons* *backwards-reasons* *backwards-rules*
            *backwards-substantive-reasons* *base-interest* *base-priority* *blocked-conclusions*
            *cancelled-c-lists* *comparison-log* *concluded-interest-priority* *d-trace*
            *dependent-interests* *dependent-nodes* *desires* *direct-reductio-interests*
            *display-inference-queue* *display?* *environmental-input* *executable-operations*
            *forwards-logical-reasons* *forwards-reasons* *forwards-rules* *forwards-substantive-reasons*
            *independent-reductio-suppositions* *inference-graph* *inference-number* *inference-number*
            *inference-queue* *inherited-non-reductio-suppositions* *interest-links* *interest-map*
            *interest-number* *interest-record* *interest-scheme-number* *interest-schemes* *interests*
            *link-number* *log-on* *non-reductio-supposition-nodes* *optative-dispositions* *pause* *percepts*
            *permanent-ultimate-epistemic-interests* *premises* *priority-interests* *prob-compiler-loaded*
            *problem-number* *problems* *problems-loaded* *processed-conclusions* *processed-desires*
            *q&i-modules* *query-number* *queue-number* *reasoning-log* *reductio-discount*
            *reductio-interest* *reductio-supposition-nodes* *skolem-free-suppositions* *skolem-multiplier*
            *start-trace* *support-link-number* *support-links* *test-log* *time-limit* *tools-loaded*
            *trees-loaded* *ultimate-epistemic-interests* *unused-suppositions* *proofs?*
            *use-logic* *use-reductio* *version* ei adjunction is-desire is-inference is-percept oscar-pathname reductio
            *deleted-arguments* *relevant-nodes* *open-position-for-assignment-tree-window*
            *flash-affected-nodes* *flash-defeatees* *flash-defeaters* *flash-ancestors*
            *flash-consequences* *flash-support-link-bases* *flash-support-links* *deductive-only*
            *flash-relevant-nodes* *graph-ancestors* *graph-relevant-nodes* *menu-dialog*
            *message* *start-display* *cycle* *assignment-tree-window* *assignment-tree-subview*
            *monitor-assignment-tree* *assignment-tree-window-size* *assignment-tree-dialog*
            *graphics-initialized* *graphics-on* *graph-log* *graphics-pause* *nodes-displayed*
            *og-nodes* *og* *graph-interests* *speak* *d-node-number* *discrimination-net*
            *top-d-node* *operators* *quantifier-number* *conditional-node* *disjunction-node*
            *undercutter-node* *conjunctive-undercutter-node* *ip-number* *is-number* *display-box*
            *quantifier-discount* *package-name* *display-button* *trace-button* *constructed-plans*
            *constructed-goals* *constructed-desires* *plan-number* *goal-number*
            *fixed-ultimate-epistemic-interests* *temporal-decay* *temporal-projection* *causal-implication*
            *new-links* *used-nodes* *used-interests* *unprocessed-nodes* *unprocessed-interests*
            *interests-used-in-proof* *temporal-decay-minimum* *instantiated-premise-number*
            *strictly-relevant-nodes* *not-strictly-relevant-nodes* ug))

(setf *version* "OSCAR_4.02")

(princ "Loading ") (princ *version*) (terpri)

(defvar *package-name* (package-name *package*))

(defvar *temporal-projection* nil)
(defvar *causal-implication* nil)
(defvar *temporal-decay* .9999)
(defvar *temporal-decay-minimum* (/ (log .5) (log *temporal-decay*)))
(defvar *pause* nil)
(defvar *time-limit* 5)
(defvar *syntax-loaded* nil)
(defvar *prob-compiler-loaded* nil)
(defvar *problems-loaded* nil)
(defvar *tools-loaded* nil)
(defvar *premises* nil)
(defvar *ultimate-epistemic-interests* nil)
(defvar *permanent-ultimate-epistemic-interests* nil)
(defvar *fixed-ultimate-epistemic-interests* nil)
(defvar *forwards-rules* nil)
(defvar *backwards-rules* nil)
(defvar *auxiliary-forwards-rules* nil)
(defvar *auxiliary-backwards-rules* nil)
(defvar *optative-dispositions* nil)
(defvar *doxastic-optative-dispositions* nil)
(defvar *trees-loaded* nil)
(defvar *display-inference-queue* nil)
(defvar *display?* nil)
(defvar *trace* nil)
(defvar *d-trace* nil)
(defvar *start-trace* nil)
(defvar *start-display* nil)
(defvar *proofs?* nil)
(defvar *use-logic* t)
(defvar *use-reductio* t)
(defvar *log-on* nil)
(defvar *priority-interests* nil)
(defvar *blocked-conclusions* nil)
(defvar *answered-discount* .5)
(defvar *base-priority* .1)
(defvar *reductio-interest* .23)
(defvar *reductio-discount* .23)
(defvar *quantifier-discount* .95)
(defvar *EI-adjustment* 2.5)
(defvar *skolem-multiplier* 10)
(defvar *concluded-interest-priority* .001)
(defvar *forwards-substantive-reasons* nil)
(defvar *backwards-substantive-reasons* nil)
(defvar *environmental-input* nil)
(defvar *executable-operations* nil)
(defvar *assignment-tree-dialog* nil)
(defvar *assignment-tree-subview* nil)
(defvar *monitor-assignment-tree* nil)
(defvar *deductive-only* nil)
(defvar *affected-nodes* nil)
(defvar *graphics-on* nil)
(defvar *graph-log* nil)
(defvar *graphics-pause* nil)
(defvar *graph-interests* nil)
(defvar *nodes-displayed* nil)
(defvar *og* nil)

(setf oscar-pathname "./")

(proclaim
  '(special *act-executors* *altered-nodes* *answered-discount* *auxiliary-backwards-rules*
            *auxiliary-forwards-rules* *auxiliary-forwards-rules* *backwards-logical-reasons*
            *backwards-reasons* *backwards-rules* *backwards-substantive-reasons* *base-interest* *base-priority*
            *blocked-conclusions* *cancelled-c-lists* *causal-implication* *comparison-log* *concluded-interest-priority*
            *conditional-node* *conjunctive-undercutter-node* *constructed-desires* *constructed-goals*
            *constructed-plans* *cycle* *d-node-number* *d-trace* *deductive-only* *hyper-defeat-link-number*
            *hyper-defeat-links* *deleted-arguments* *dependent-interests* *dependent-nodes* *desires*
            *direct-reductio-interests* *discrimination-net* *disjunction-node* *display-box* *display-button*
            *display-inference-queue* *display?* *environmental-input* *executable-operations*
            *fixed-ultimate-epistemic-interests* *flash-affected-nodes* *flash-ancestors* *flash-consequences*
            *flash-defeatees* *flash-defeaters* *flash-relevant-nodes* *flash-hyperlink-bases*
            *flash-hyperlinks* *forwards-logical-reasons* *forwards-reasons* *forwards-rules*
            *forwards-substantive-reasons* *goal-number* *graph-ancestors* *graph-interests*
            *graph-log* *graph-relevant-nodes* *graphics-initialized* *graphics-on* *graphics-pause* *hypergraphs-loaded*
            *independent-reductio-suppositions* *hypergraph* *hypernode-number* *hypernode-number*
            *inference-queue* *inherited-non-reductio-suppositions* *instantiated-premise-number*
            *interest-links* *interest-map* *interest-number* *interest-record* *interest-scheme-number*
            *interest-schemes* *interests* *interests-used-in-proof* *ip-number* *is-number* *interest-link-number*
            *log-on* *menu-dialog* *menus-loaded* *message* *new-beliefs* *new-links* *new-retractions*
            *nodes-displayed* *non-reductio-supposition-nodes* *not-strictly-relevant-nodes* *og* *og-nodes*
            *operators* *optative-dispositions* *package-name* *pause* *percepts*
            *permanent-ultimate-epistemic-interests* *plan-number* *premises* *priority-interests*
            *prob-compiler-loaded* *problem-number* *problems* *problems-loaded* *processed-conclusions*
            *processed-desires* *proofs?* *q&i-modules* *quantifier-discount* *quantifier-number* *query-number*
            *queue-number* *reasoning-log* *reductio-discount* *reductio-interest* *reductio-supposition-nodes*
            *relevant-nodes* *skolem-free-suppositions* *skolem-multiplier* *speak* *start-display* *start-trace*
            *strictly-relevant-nodes* *hyperlink-number* *hyperlinks* *temporal-decay*
            *temporal-decay-minimum* *temporal-projection* *test-log* *time-limit* *tools-loaded*
            *top-d-node* *trace-button* *trees-loaded* *ultimate-epistemic-interests* *undercutter-node*
            *unprocessed-interests* *unprocessed-nodes* *unused-suppositions* *use-logic* *use-reductio*
            *used-interests* *used-nodes* *version* adjunction ei is-desire is-inference is-percept
            oscar-pathname reductio ug
	    *VERBOSE-EVAL-SELECTION* *warn-if-redefine*))

(defvar *package-name* (package-name *package*))

(defvar *temporal-projection* nil)
(defvar *causal-implication* nil)
(defvar *temporal-decay* .995)
(defvar *temporal-decay-minimum* (/ (log .5) (log *temporal-decay*)))
(defvar *pause* nil)
(defvar *time-limit* 5)
(defvar *syntax-loaded* nil)
(defvar *prob-compiler-loaded* nil)
(defvar *problems-loaded* nil)
(defvar *tools-loaded* nil)
(defvar *menus-loaded* nil)
(defvar *hypergraphs-loaded* nil)
(defvar *premises* nil)
(defvar *ultimate-epistemic-interests* nil)
(defvar *permanent-ultimate-epistemic-interests* nil)
(defvar *fixed-ultimate-epistemic-interests* nil)
(defvar *forwards-rules* nil)
(defvar *backwards-rules* nil)
(defvar *auxiliary-forwards-rules* nil)
(defvar *auxiliary-backwards-rules* nil)
(defvar *optative-dispositions* nil)
(defvar *doxastic-optative-dispositions* nil)
(defvar *trees-loaded* nil)
(defvar *display-inference-queue* nil)
(defvar *display?* nil)
(defvar *trace* nil)
(defvar *d-trace* nil)
(defvar *start-trace* nil)
(defvar *start-display* nil)
(defvar *proofs?* nil)
(defvar *use-logic* t)
(defvar *use-reductio* t)
(defvar *log-on* nil)
(defvar *priority-interests* nil)
(defvar *blocked-conclusions* nil)
(defvar *answered-discount* .5)
(defvar *base-priority* .1)
(defvar *reductio-interest* .23)
(defvar *reductio-discount* .23)
(defvar *quantifier-discount* .95)
(defvar *EI-adjustment* 2.5)
(defvar *skolem-multiplier* 10)
(defvar *concluded-interest-priority* .001)
(defvar *forwards-substantive-reasons* nil)
(defvar *backwards-substantive-reasons* nil)
(defvar *environmental-input* nil)
(defvar *executable-operations* nil)
(defvar *deductive-only* nil)
(defvar *graphics-on* nil)
(defvar *graph-log* nil)
(defvar *graphics-pause* nil)
(defvar *graph-interests* nil)
(defvar *comparison-log* nil)

(proclaim
 '(special pause-flag *metered-calls* *callees* *blank-line* *line-columns* *uncalled-callers*))

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


;;                              ******************  TERMS  ********************

#| The constituent terms of a (possibly complex) term. |#
(defun constituent-terms-of (c)
  (cond ((stringp c) (list c))
        ((symbolp c) (list c))
        (t (cons c (remove-duplicates=
                     (unionmapcar #'constituent-terms-of (arg-list c)))))))

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

(defun convert-to-string (s)
  (let ((string (get s 'pretty-form)))
    (or string (princ-to-string s))))

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
		(labels ((pretty-cons (x)
                           (when x
                             (cond ((listp x)
                                    (cond ((cdr x) (cons (pretty (car x)) (cons " " (pretty-cons (cdr x)))))
                                          (t (list (pretty (car x))))))
                                   (t (list ". " (pretty x)))))))
                 (imp (cons "(" (append (pretty-cons p) (list ")")))))))))
          (t (write-to-string p))
          )))

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

(defun reform (s &optional variables)
  (let ((s* (read-from-string s)))
    (cond ((and (listp s*) (equal (car s*) 'define)) s*)
          (t
            (resolve-variable-conflicts (convert-to-prefix-form (reform- s variables)))))))

(defun reform-if-string (p &optional variables)
  (if (stringp p) (reform p variables) p))

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

(if (not (fboundp 'gc)) (defun gc () t))

#|
This file provides the code for the macros def-forwards-reason and
def-backwards-reason.

Premises and conclusions can be either pretty-formulas (strings) or formulas (S-expressions).
Note that pretty-formulas are case-sensitive.  Do not capitalize expressions
in one part of a reason and fail to capitalize it elsewhere, and make sure capitalization agrees in the
premises of problems.  If pretty-formulas are used, then the variable-list should be quoted to avoid
problems with case-sensitivity.  Otherwise the variables can simply be listed.
|#

;; ======================================================================

(defun term-lists (P vars descriptor)
  (cond ((listp P)
         (let ((elt-num 0) (term-lists nil))
           (dolist (Q P)
             (let ((Q-descriptor `(element ,elt-num ,descriptor)))
               (cond ((mem Q vars)
                      (let ((assoc (assoc Q term-lists :test 'equal)))
                        (cond (assoc (push Q-descriptor (cdr assoc)))
                              (t (push (list Q Q-descriptor) term-lists)))))
                     ((listp Q)
                      (let ((tl (term-lists Q vars Q-descriptor)))
                        (dolist (term-list tl)
                          (let ((assoc (assoc (car term-list) term-lists :test 'equal)))
                            (cond (assoc (setf (cdr assoc) (append (cdr term-list) (cdr assoc))))
                                  (t (push term-list term-lists)))))))))
             (incf elt-num))
           term-lists))
        ((mem P vars) `((,P ,descriptor)))))

;(term-lists '(& (F x y) (G x y)) '(x y) 'z)
;((x (element 1 (element 2 z)) (element 1 (element 1 z)))
;  (y (element 2 (element 2 z)) (element 2 (element 1 z))))

(defun formula-profile (P vars descriptor)
  (cond ((and P (listp P))
         (let ((description nil) (elt-num 0) (term-lists nil))
           (dolist (Q P)
             (let ((Q-descriptor `(element ,elt-num ,descriptor)))
               (cond ((mem Q vars)
                      (let ((assoc (assoc Q term-lists :test 'equal)))
                        (cond (assoc (push Q-descriptor (cdr assoc)))
                              (t (push (list Q Q-descriptor) term-lists)))))
                     ((not (listp Q)) (push `(equal ,Q-descriptor ',Q) description))
                     (t
                       (multiple-value-bind (d tl) (formula-profile Q vars Q-descriptor)
                         (setf description (append description d))
                         (dolist (term-list tl)
                           (let ((assoc (assoc (car term-list) term-lists :test 'equal)))
                             (cond (assoc (setf (cdr assoc) (append (cdr term-list) (cdr assoc))))
                                   (t (push term-list term-lists)))))))))
             (incf elt-num))
           (values (cons `(listp ,descriptor) description) term-lists)))
        ((mem P vars) (values nil `((,P ,descriptor))))
        ; (list (list (mem1 vars) '`,(list descriptor)))))
        (t (values `((equal ,descriptor ',P)) nil))))

#|
(formula-profile '(& (F x y) (G x y)) '(x y) 'z nil)

((listp z)
 ; (equal (element 0 z) '&)
 ; (listp (element 1 z))
 ; (equal (element 0 (element 1 z)) 'f)
 (listp (element 2 z))
 (equal (element 0 (element 2 z)) 'g))

((x (element 1 (element 2 z)) (element 1 (element 1 z)))
 (y (element 2 (element 2 z)) (element 2 (element 1 z))))
|#

(defun refined-profile* (profile n)
  (when profile
    (cond ((and (listp (car profile)) (equal (caar profile) 'listp))
           (let ((v (read-from-string (cat "%z" (write-to-string n))))
                 (term (cadar profile)))
             `((let ((,v ,term))
                 (and
                   (listp ,v)
                   ,@(=subst v term (refined-profile* (cdr profile) (1+ n))))))))
          (t (cons (car profile) (refined-profile* (cdr profile) n))))))

#| This turns the formula-profile into a description, and replaces repetitive computations with lets. |#
(defun refined-profile (profile)
  (cond ((equal (caar profile) 'listp) (cons 'and (cons (car profile) (refined-profile* (cdr profile) 0))))
        (t (cons 'and (refined-profile* profile 0)))))

(defun binding-function (P vars)
  (multiple-value-bind
    (profile term-lists)
    (formula-profile P vars '%z)
    (cond
      ((every #'(lambda (tl) (null (cddr tl))) term-lists)
       (cond
         (profile
           (if vars
             `#'(lambda (%z %v)
                  (declare (ignore %v))
                  (when
                    ,@ (list (if (cdr profile) (refined-profile profile) (car profile)))
                    (values
                      ,(cons 'list
                             (mapcar
                               #'(lambda (x) (cons 'cons (cons (list 'quote (car x)) (cdr x))))
                               term-lists))
                      t)))
             `#'(lambda (%z %v)
                  (declare (ignore %v))
                  (when
                    ,@ (list (if (cdr profile) (refined-profile profile) (car profile)))
                    (values nil t)))))
         (t
           `#'(lambda (%z %v)
                (declare (ignore %v))
                (values
                  ,(cons 'list
                         (mapcar
                           #'(lambda (x) (cons 'cons (cons (list 'quote (car x)) (cdr x))))
                           term-lists))
                  t)))))
      (profile
        `#'(lambda (%z %v)
             (when
               ,@ (list (if (cdr profile) (refined-profile profile) (car profile)))
               (unify-premise-terms
                 ,(cons 'list (mapcar #'(lambda (b) (cons 'list b)) (a-range term-lists)))
                 ',(domain term-lists) %v T))))
      (t
        `#'(lambda (%z %v)
             (unify-premise-terms
               ,(cons 'list (mapcar #'(lambda (b) (cons 'list b)) (a-range term-lists)))
               ',(domain term-lists) %v T))))))

;========================UNIFICATION=====================

#| This does the substitutions sequentially rather than in parallel, and in
the reverse order from their occurrence in m. |#
(defun sequential-sublis (m X)
  (cond ((eq (length m) 1)
         (subst (cdr (mem1 m)) (mem1 (mem1 m)) X))
        (t (subst (cdr (mem1 m)) (mem1 (mem1 m)) (sequential-sublis (cdr m) X)))))

#| This substitutes in accordance with a match m. |#
(defun match-sequential-sublis (m x)
  (cond ((eq m t) x)
        (t (sequential-sublis m x))))

#| This turns a sequential-match into a parallel match (to be applied by match-sublis). |#
(defun parallelize-match (sm vars)
  (cond ((eq sm t) t)
        (t (let ((m nil))
             (dolist (x vars)
               (let ((x* (sequential-sublis sm x)))
                 (if (not (equal x x*)) (push (cons x x*) m))))
             (if m m t)))))

(defun merge-sequential-matches (m m*)
  (cond ((equal m t) m*)
        ((equal m* t) m)
        (t (append m m*))))

#| This returns the list (terms1 terms quantifier-variables) where terms1 and terms are the lists
of corresponding terms to be unified and quantifier-variables is the list of pairs (x . y) of
corresponding quantifier-variables used for testing for notational variants. |#
(defun variable-correspondence (P Q P-vars Q-vars terms)
  (cond
    ((member P P-vars)
     (let ((quantifier-variables (mem3 terms)))
       (cond ((rassoc Q quantifier-variables) (throw 'unifier nil))
             (t (list (cons P (mem1 terms)) (cons Q (mem2 terms)) quantifier-variables)))))
    ((member Q Q-vars)
     (cond ((assoc P (mem3 terms)) (throw 'unifier nil))
           (t (list (cons P (mem1 terms)) (cons Q (mem2 terms)) (mem3 terms)))))
    ((null P)
     (cond ((null Q) terms)
           (t (throw 'unifier nil))))
    ((null Q) (throw 'unifier nil))
    ((not (listp P))
     (cond ((not (listp Q))
            (cond ((member Q Q-vars)
                   (list (cons P (mem1 terms)) (cons Q (mem2 terms)) (mem3 terms)))
                  ((eql P Q) terms)
                  ((eql (cdr (assoc P (mem3 terms))) Q) terms)
                  (t (throw 'unifier nil))))
           (t (throw 'unifier nil))))
    ((not (listp Q)) (throw 'unifier nil))
    ((or (eq (car P) 'all) (eq (car P) 'some))
     (cond ((eql (car P) (car Q))
            (variable-correspondence
              (mem3 P) (mem3 Q) P-vars Q-vars
              (list (mem1 terms) (mem2 terms)
                    (cons (cons (mem2 P) (mem2 Q)) (mem3 terms)))))
           (t (throw 'unifier nil))))
    (t
      (variable-correspondence
        (cdr P) (cdr Q) P-vars Q-vars
        (variable-correspondence (car P) (car Q) P-vars Q-vars terms)))))

#| (mgu p q) is a most general unifier for p and q for purposes of forwards
reasoning..  This assumes that they have no free variables in common.  vars are
the free variables (possibly) occurring in x y.  They are assumed to be
interest-variables and hypernode-variables.  This produces a serial match that
must be applied by match-sequential-sublis rather than match-sublis. |#
(defun mgu (x y vars)
  (cond ((atom x)
         (cond ((eql x y) t)
               ((member x vars)
                (cond ((and (listp y) (eq (car y) 'q-var)) (throw 'unifier nil))
                      ((occur x y) (throw 'unifier nil))
                      (t (list (cons x y)))))
               ((member y vars)
                (cond ((and (listp x) (eq (car x) 'q-var)) (throw 'unifier nil))
                      ((occur y x) (throw 'unifier nil))
                      ((not (eq x '=))
                       (list (cons y x)))
                      (t (throw 'unifier nil))))
               (t (throw 'unifier nil))))
        ((atom y)
         (cond ((member y vars)
                (cond ((and (listp x) (eq (car x) 'q-var)) (throw 'unifier nil))
                      ((occur y x) (throw 'unifier nil))
                      (t (list (cons y x)))))
               (t (throw 'unifier nil))))
        ((listp x)
         (cond ((not (listp y)) (throw 'unifier nil))
               ((and (listp (cdr x)) (listp (cdr y)) (not (eql (length x) (length y)))) (throw 'unifier nil))
               (t (labels ((mgu-list (x y vars)
				     (let ((m (mgu (mem1 x) (mem1 y) vars)))
				       (cond ((null m) (throw 'unifier nil)))
				       (cond ((null (cdr x)) m)
					     ((eq m t)
					      (mgu-list (cdr x) (cdr y) vars))
					     (t (let ((m* (mgu-list
							   (sequential-sublis m (cdr x))
							   (sequential-sublis m (cdr y))
							   vars)))
						  (cond ((eq m* t) m)
							(t (append m* m)))))))))
			  (mgu-list x y vars)))))))

#| This returns the multiple values result unifier |#
(defun unify-list (term-list vars unifier)
  (labels
    ((unify-list-aux (term terms vars unifier0)
                     (cond ((null terms) (values (match-sublis unifier0 term) unifier0))
                           (t
                             (let* ((m (parallelize-match
                                         (mgu (match-sublis unifier0 term)
                                              (match-sublis unifier0 (car terms))
                                              vars) vars))
                                    (m* m))
                               (when (not (eq unifier0 T))
                                 (cond ((eq m T) (setf m* unifier0))
                                       (t (dolist (assoc unifier0)
                                            (setf (cdr assoc) (match-sublis m (cdr assoc)))
                                            (push assoc m*)))))
                               (unify-list-aux
                                 (car terms) (cdr terms) vars m*))))))
    (unify-list-aux (car term-list) (cdr term-list) vars unifier)))

;(unify-list '(3) '(x) T)
;(unify-list '(x y z) '(x y z) T)

#| (unify-list '((f x y) (f a (g z)) (f w (g b))) '(x y z w) T)
produces
(f a (g b))
((x . a) (y g b) (z . b) (w . a))  |#

(defun unify-premise-terms* (term-lists vars unifier0)
  (multiple-value-bind (term unifier) (unify-list (car term-lists) vars unifier0)
    (let ((m unifier))
      (when (not (eq unifier0 T))
        (cond ((eq unifier T) (setf m unifier0))
              (t (dolist (assoc unifier0)
                   (setf (cdr assoc) (match-sublis unifier (cdr assoc)))
                   (pushnew assoc m :test 'equal)))))
      (cond ((null (cdr term-lists)) (values (list term) m))
            (t (multiple-value-bind
                 (terms unifier*) (unify-premise-terms* (cdr term-lists) vars m)
                 (values (cons (match-sublis unifier* term) terms) (merge-matches m unifier*))))))))

#| term-lists is the list of terms corresponding to the premise-variables.  This
returns the list of terms that instantiate the premise-variables and the match. |#
(defun unify-premise-terms (term-lists premise-variables vars unifier0)
  (catch 'unifier
         (multiple-value-bind
           (terms unifier) (unify-premise-terms* term-lists vars unifier0)
           (values
             (mapcar #'(lambda (x y) (cons x y)) premise-variables terms)
             unifier))))

#| (unify-premise-terms* '(((f x y) (f a (g z))) ((k x)) ((h w (g b)) (h b y))) '(x y z w) T)
returns:
((f a (g b)) (k a) (h b (g b)))
((x . a) (y g b) (z . b) (w . b))
|#

(defun conditionally-write-to-string (s)
  (if (stringp s) s (write-to-string s)))

#| =====================================================================

Forwards-reasons can be defined in either of two forms:

(def-forwards-reason symbol
                     :reason-forwards-premises list of formulas or formula-condition pairs (listed one after another)
                     :reason-backwards-premises  list of formulas or pairs (formula,(condition1,condition2))
                     :conclusions formula
                     :strength number
                     :variables list of symbols
                     :defeasible? T or NIL (NIL is default)
                     :description an optional string (quoted) describing the reason
                     )

(def-forwards-reason symbol
                     :reason-forwards-premises list of formulas or formula-condition pairs
                     :reason-backwards-premises  list of formulas or pairs (formula (condition1 condition2))
                     :reason-conclusions-function lambda expression or function
                     :strength number
                     :variables list of symbols
                     :defeasible? T or NIL (NIL is default)
                     :description an optional string (quoted) describing the reason
                     )

If no premise-condition is supplied for a particular premise, the default condition
#'is-inference is used.
What is generated is forwards-reasons with reason-functions.  For example

(def-forwards-reason *THERMOMETER*
                     :reason-forwards-premises   (thermometer-reads x)
                     :conclusions   (Patient-temperature-is x)
                     :strength   .98
                     :variables   x
                     :defeasible? t)

produces the following code:

(progn
  (proclaim (list 'special '*thermometer*))
  (when (boundp '*thermometer*) (pull *thermometer* *forwards-substantive-reasons*))
  (setf *thermometer*
        (make-forwards-reason
          :reason-name '*thermometer*
          :reason-forwards-premises
          (list (list '(thermometer-reads x)
                      #<Compiled-function is-inference #x17C13C6>
                      #'(lambda (%z %v)
                          (declare (ignore %v))
                          (when (and (listp %z) (equal (element 0 %z) 'thermometer-reads))
                            (values (list (cons 'x (element 1 %z))) t)))
                      '(x)))
          :reason-backwards-premises nil
          :reason-conclusions '(patient-temperature-is x)
          :reason-conclusions-function nil
          :reason-variables '(x)
          :reason-strength 0.98
          :reason-defeasible-rule t
          :reason-description nil))
  (push *thermometer* *forwards-substantive-reasons*))

On the other hand

(def-forwards-reason GREEN-SLYME
                     :reason-forwards-premises
                     (Patient-has-had-green-slyme-running-out-of-his-nose-for  x  hours)
                     (:condition (and (is-inference c) (numberp x)))
                     :variables   x
                     :reason-conclusions-function
                     `(The-probability-that the-patient-ingested-silly-putty is ,(* .5 (- 1 (exp (- x)))))
                     :strength   .95
                     :defeasible? T)

constructs a reason with the reason-function:

(progn
  (proclaim (list 'special 'green-slyme))
  (when (boundp 'green-slyme) (pull green-slyme *forwards-substantive-reasons*))
  (setf green-slyme
        (make-forwards-reason
          :reason-name 'green-slyme
          :reason-forwards-premises
          (list
            (list
              '(patient-has-had-green-slyme-running-out-of-his-nose-for x hours)
              #'(lambda (c binding) (let* ((x (cdr (assoc 'x binding)))) (and (is-inference c) (numberp x))))
              #'(lambda (%z %v)
                  (declare (ignore %v))
                  (when (and (listp %z)
                             (equal (element 2 %z) 'hours)
                             (equal (element 0 %z) 'patient-has-had-green-slyme-running-out-of-his-nose-for))
                    (values (list (cons 'x (element 1 %z))) t)))
              '(x)))
          :reason-backwards-premises nil
          :reason-conclusions nil
          :reason-conclusions-function
          #'(lambda (x)
              (list* 'the-probability-that
                     (list* 'the-patient-ingested-silly-putty (list* 'is (list (* 0.5 (- 1 (exp (- x)))))))))
          :reason-variables '(x)
          :reason-strength 0.95
          :reason-defeasible-rule t
          :reason-description nil))
  (push green-slyme *forwards-substantive-reasons*))

|#

;=========================================================================

(defun rectify-conclusions-list (conclusions default)
  (let ((rectified-conclusions nil))
    (loop
      (let ((P (car conclusions)))
        (setf conclusions (cdr conclusions))
        (cond
          ((and (listp (car conclusions)) (equal (caar conclusions) :defeasible?))
           (push (list 'cons P (cadar conclusions)) rectified-conclusions)
           (setf conclusions (cdr conclusions)))
          (t (push (list 'cons P default) rectified-conclusions)))
        (when (null conclusions) (return (reverse rectified-conclusions)))))))

(defun arithmetical-terms (formula &optional terms)
  (cond ((null formula) terms)
        ((listp formula)
         (cond
           ((or (eq (car formula) '<) (eq (car formula) '<=) (eq (car formula) '=))
            (union= (remove '*cycle* (cdr formula)) terms))
           (t (arithmetical-terms (cdr formula) (arithmetical-terms (car formula) terms)))))
        (t terms)))

(defun rectify-formula-condition (formula)
  (let* ((p (subst '*cycle* 'now formula))
         (terms (arithmetical-terms p)))
    (if terms
      (progn
        (let ((terms* nil) (a-list nil))
          (dolist (v terms)
            (cond ((and (not (eq v '*cycle*)) (not (numberp v)))
                   (let ((v* (gensym)))
                     (push v* terms*)
                     (push (cons v v*) a-list)))
                  (t (pull v terms))))
          `(let
             ,@
             (list (mapcar #'(lambda (v) `(,(cdr (assoc v a-list)) (ignore-errors (eval ,v)))) terms)
                   `(and ,@ terms* ,(sublis a-list p))))))
      p)))

(defun occur-unquoted (x s &key (test 'eq))
  (and s (listp s) (not (eq (car s) 'quote))
       (or (funcall test (car s) x)
           (occur-unquoted x (car s) :test test)
           (occur-unquoted x (cdr s) :test test))))

(defun occur-quoted (x s &key (test 'eq))
  (and s (listp s)
       (or (and (eq (car s) 'quote) (occur x (cdr s) :test test))
           (occur-quoted x (car s) :test test)
           (occur-quoted x (cdr s) :test test))))

(defun o-occur (x s &key (test 'eq))
  (and (listp s)
       (or (some #'(lambda (y) (funcall test y x)) s)
           (some #'(lambda (y) (o-occur x y :test test)) s))))

(defun o-occur+ (x s &key (test 'eq))
  (and (listp s)
       (or (some #'(lambda (y) (funcall test y x)) (cdr s))
           (some #'(lambda (y) (o-occur+ x y :test test)) s))))

(defun o-occur* (x s &key (test 'eq))
  (or (funcall test x s)
      (o-occur x s :test test)))

(defun o-occur++ (x s &key (test 'eq))
  (or (funcall test x s)
      (o-occur+ x s :test test)))

(defun parse-arithmetical-formula (p)
  (cond ((null p) nil)
        ((listp p)
         (let ((p2 (cadr p)))
           (cond ((and
                    (mem3 p)
                    (or (eq p2 '<) (eq p2 '<=) (eq p2 '+) (eq p2 '-) (eq p2 '*) (eq p2 '/) (eq p2 '=)))
                  (list p2 (parse-arithmetical-formula (car p)) (parse-arithmetical-formula (mem3 p))))
                 (t (mapcar #'parse-arithmetical-formula p)))))
        (t p)))

#| This allows us to write the conditions in forwards-reasons in the form '(x < y) or '(x <= y), or logical
combinations thereof, without incorporating a check that x and y have arithmetical values.  +, *, -, /, and
= can be used in infix notation. |#
(defun formula-condition (formula premise-variables)
  (let ((formula* (rectify-formula-condition (parse-arithmetical-formula formula)))
        (variables (subset #'(lambda (v) (o-occur* v formula)) premise-variables)))
    (cond ((null premise-variables)
           (list '(declare (ignore binding)) formula*))
          ((occur 'c formula)
           `((let*
               ,@
               (list
                 (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables)
                 formula*))))
          (t
            `((declare (ignore c))
              (let*
                ,@
                (list
                  (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables)
                  formula*)))))))

(defstruct (forwards-premise
	    (:print-function
	     (lambda (premise stream depth)
               (declare (ignore depth))
               (princ "#<premise: " stream)
               (prinp (fp-formula premise) stream)
               (princ ">" stream)))
	    (:conc-name fp-))
  (formula nil)
  (kind :inference)
  (condition nil)
  (binding-function nil)
  (variables nil)
  (instantiator nil)
  (clue? nil)
  (hypernode-specifier nil)  ;; bound to the node instantiating the premise in a link
  )

(defun def-instantiator (def vars)
  (eval
    `#'(lambda (binding)
         (let* ((new-binding binding)
                (new-vars nil)
                ,@
                (mapcar
                  #'(lambda (v)
                      `(,v
                         (let ((v* (assoc ',v binding)))
                           (cond
                             (v* (cdr v*))
                             (t
                               (setf v* (make-interest-variable))
                               (push v* new-vars)
                               (push (cons ',v v*) new-binding)
                               v*)))))
                  vars))
           (values ,def new-binding new-vars)))))

(defun formula-instantiator (P variables)
  (cond
    ((listp P)
     (if (eq (car P) :defeasible?) P
       (cons 'list (mapcar #'(lambda (x) (formula-instantiator x variables)) P))))
    ((member P variables) P)
    (t `',P)))

#| The reason-instantiator binds unbound premise-variables in the premise to new interest-variables,
and returns three values: the instantiated premise-formula, the new interest-variables, and the
extended binding. |#
(defun reason-instantiator (P variables)
  (cond ((and (listp P) (equal (car P) 'define))
         (def-instantiator (mem3 P) (remove-if-equal (mem2 P) variables)))
        (variables
          (eval
            `#'(lambda (binding)
                 (let* ((new-vars nil)
                        (new-binding binding)
                        ,@
                        (mapcar
                          #'(lambda (v)
                              `(,v
                                 (let ((v* (assoc ',v binding)))
                                   (cond
                                     (v* (cdr v*))
                                     (t
                                       (setf v* (make-interest-variable))
                                       (push v* new-vars)
                                       (push (cons ',v v*) new-binding)
                                       v*)))))
                          variables))
                   (values ,(formula-instantiator P variables) new-vars new-binding)))))
        (t #'(lambda (binding) (values P nil binding)))))

(defun rectify-forwards-premises (premise-list variables &optional c-vars)
  (let ((premises nil)
        (used-premise-variables c-vars))
    (loop
      (let* ((premise (reform-if-string (car premise-list) variables))
             (premise-variables
               (if (and (listp premise) (eq (car premise) 'define))
                 (subset #'(lambda (v) (o-occur++ v  premise)) variables)
                 (subset #'(lambda (v) (o-occur* v  premise)) variables)))
             (premise-variables* (intersection premise-variables used-premise-variables))
             (binding-function (binding-function premise premise-variables)))
        (setf premise-list (cdr premise-list))
        (let ((conditions nil))
          (dolist (p premise-list)
            (if (stringp p) (return))
            (push p conditions)
            (setf premise-list (cdr premise-list)))
          (let* ((kind (cadr (find-if #'(lambda (c) (eq (car c) :kind)) conditions)))
                 (clue? (cadr (find-if #'(lambda (c) (eq (car c) :clue?)) conditions)))
                 (hypernode-specifier (cadr (find-if #'(lambda (c) (eq (car c) :node)) conditions)))
                 (condition (cadr (find-if #'(lambda (c) (eq (car c) :condition)) conditions)))
                 (new-premise
                   (make-forwards-premise
                     :formula premise
                     :kind (if kind (read-from-string (cat ":" (write-to-string kind))) :inference)
                     :condition
                     (if condition (eval `#'(lambda (c binding) ,@(formula-condition condition variables))))
                     :binding-function (eval binding-function)
                     :clue? clue?
                     :variables premise-variables
                     :hypernode-specifier hypernode-specifier
                     :instantiator (reason-instantiator premise premise-variables*))))
            (push new-premise premises)
            (setf used-premise-variables
                  (union used-premise-variables premise-variables))))
        (when (null premise-list) (return (reverse premises)))))))

(defun make-clauses (body)
  (let ((newbody nil))
    (loop
      (let ((clause (list (mem1 body))))
        (loop
          (setf body (cdr body))
          (when (null body) (push (reverse clause) newbody) (return))
          (when (keywordp (car body)) (push (reverse clause) newbody) (return))
          (push (car body) clause))
        (when (null body) (return))))
    newbody))

(defun rectify-strength (formula premise-variables)
  (cond
    ((numberp formula) formula)
    (t
      (let ((formula* (rectify-formula-condition (parse-arithmetical-formula formula)))
            (variables (subset #'(lambda (v) (o-occur* v formula)) premise-variables)))
        (cond ((null premise-variables)
               (eval `#'(lambda (binding) (declare (ignore binding)) ,formula*)))
              (t
                (eval
                  `#'(lambda (binding basis)
                       ,@ (cond ((not (occur 'basis formula)) `((declare (ignore basis))))
                                ((null variables) `((declare (ignore binding)))))
                       (let*
                         ,@
                         (list
                           (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables)
                           formula*))))))))))

(defstruct (interest (:print-function
		      (lambda (x stream depth)
                        (declare (ignore depth))
                        (princ "#<" stream) (princ "Interest " stream)
                        (princ (interest-number x) stream)
                        ; (princ ": " stream) (prinp-sequent (interest-sequent x) stream)
                        (princ ">" stream)))
                     (:conc-name nil))   ; "An interest-graph-node"
  (interest-number 0)
  (interest-sequent nil)
  (interest-formula nil)
  (interest-supposition nil)
  (interest-right-links nil)
  (interest-left-links nil)
  (interest-degree-of-interest *base-priority*)
  (interest-last-processed-degree-of-interest nil)
  (interest-defeat-status nil)
  (interest-discharged-degree nil)  ;; used in computing priorities
  (interest-deductive nil)
  (interest-cancelled nil)
  (interest-queue-node nil)
  (interest-i-list nil)
  (interest-maximum-degree-of-interest 0)
  (interest-defeatees nil)
  (interest-reductio nil)
  (interest-direct-reductio nil)
  (interest-generated-suppositions nil)
  (interest-generating-nodes nil)
  (interest-priority 0)
  (interest-variables nil)
  (interest-discharge-condition nil)  ;;a function of node, unifier, and interest-link
  (interest-supposition-variables nil)
  (interest-cancelling-node nil)
  (interest-discharging-nodes nil)
  (interest-supposition-nodes nil)
  (interest-generated-interest-schemes nil)
  (interest-defeater-binding nil)
  (interest-generating-defeat-nodes nil)
  (interest-cancelled-left-links nil)
  (interest-non-reductio? t)
  (interest-anchored-nodes nil)
  (interest-text-discharge-condition nil)  ;; a text statement of the discharge condition
  (interest-enabled-nodes nil)  ;; the nodes for which this is an enabling-interest
  (interest-decision-plans nil)  ;; the nodes this interest is relevant to deciding on
  )

(defun backwards-formula-condition (formula)
  `#'(lambda (interest) ,formula))

#| Condition1 is a predicate that an existing interest must satisfy to be used in
backwards reasoning as the left terminus of a link encoding this reason, and condition2
is a function which is applied to a new interest constructed for that purpose.
The application of this condition will normally be such as to set the values of slots
so that the resulting interest satisffies condition1. |#
(defstruct (backwards-premise
	    (:print-function
	     (lambda (premise stream depth)
               (declare (ignore depth))
               (princ "#<premise: " stream)
               (prinp (bp-formula premise) stream)
               (princ ">" stream)))
	    (:conc-name bp-))
  (formula nil)
  (condition1 nil)
  (condition2 nil)
  (instantiator nil)
  (clue? nil)
  (text-condition nil)  ;; text specification of the discharge condition
  (hypernode-specifier nil)  ;; bound to the node instantiating the premise in a link
  )

(defun simple-backwards-formula-condition (formula premise-variables)
  (let ((formula* (rectify-formula-condition (parse-arithmetical-formula formula))))
    (cond ((null premise-variables)
           (list '(declare (ignore binding)) formula*))
          (t
            (if premise-variables
              (progn
                (let ((terms* nil) (a-list nil))
                  (dolist (v premise-variables)
                    (cond ((and (not (eq v '*cycle*)) (not (numberp v)))
                           (let ((v* (gensym)))
                             (push v* terms*)
                             (push (cons v v*) a-list)))
                          (t (pull v premise-variables))))
                  `#'(lambda (node unifier binding)
                       (declare (ignore node))
                       (let* (,@(mapcar
                                  #'(lambda (v)
                                      (let ((v* (cdr (assoc v a-list))))
                                        `(,v (let ((,v* (cdr (assoc ',v binding))))
                                               (match-sublis (mem2 unifier) ,v*)))))
                                  premise-variables))
                         ,formula*))))
              `#'(lambda (node unifier binding) ,formula*))))))

(defun rectify-backwards-premises (premise-list variables &optional c-vars)
  ; (setf p premise-list v variables) (break)
  ;; (step (rectify-backwards-premises p v))
  (let ((premises nil))
    (loop
      (let* ((premise? (stringp (car premise-list)))
             (premise (reform-if-string (car premise-list) variables))
             (premise-variables
               (if (and (listp premise) (eq (car premise) 'define))
                 (subset #'(lambda (v) (o-occur++ v  premise)) variables)
                 (subset #'(lambda (v) (o-occur* v  premise)) variables))))
        (setf premise-list (cdr premise-list))
        (let ((conditions nil))
          (dolist (p premise-list)
            (if (or (stringp p) (and (listp p) (not (keywordp (car p))))) (return))
            (push p conditions)
            (setf premise-list (cdr premise-list)))
          (let* ((clue? (cadr (find-if #'(lambda (c) (eq (car c) :clue?)) conditions)))
                 (hypernode-specifier (cadr (find-if #'(lambda (c) (eq (car c) :node)) conditions)))
                 (condition (cadr (find-if #'(lambda (c) (eq (car c) :condition)) conditions)))
                 (variables* (if condition (subset #'(lambda (v) (o-occur v condition)) variables)))
                 (condition*  (if condition (eval (simple-backwards-formula-condition condition variables*))))
                 (d-condition
                   (when (and condition (listp premise) (eq (car premise) 'define))
                     (eval `#'(lambda (c binding) ,@(formula-condition condition variables*)))))
                 (condition1 (cadr (find-if #'(lambda (c) (eq (car c) :condition1)) conditions)))
                 (condition2 (cadr (find-if #'(lambda (c) (eq (car c) :condition2)) conditions)))
                 (new-premise
                   (cond
                     (premise?
                       (make-backwards-premise
                         :formula premise
                         :condition1
                         (cond
                           ((and (listp premise) (eq (car premise) 'define)) d-condition)
                           (condition1 (backwards-formula-condition condition1))
                           (condition #'(lambda (i) (eq (interest-discharge-condition i) condition*))))
                         :condition2
                         (cond (condition2 (backwards-formula-condition condition2))
                               (condition #'(lambda (i) (setf (interest-discharge-condition i) condition*))))
                         :text-condition condition
                         :clue? clue?
                         :hypernode-specifier hypernode-specifier
                         :instantiator (reason-instantiator premise premise-variables)))
                     (t
                       (setf c-vars (subset #'(lambda (v) (o-occur* v premise))
                                            variables))
                       (let ((new-vars
                               (subset #'(lambda (v) (occur-quoted v premise)) c-vars)))
                         `#'(lambda (**b** binding)
                              (declare (ignore **b**))
                              (let (,@ (mapcar
                                         #'(lambda (v) `(,v (cdr (assoc ',v binding))))
                                         (subset
                                           #'(lambda (v) (occur-unquoted v premise))
                                           c-vars)))
                                (make-backwards-premise
                                  :formula ,premise
                                  :condition1
                                  ,(cond (condition1 (backwards-formula-condition condition1))
                                         (condition #'(lambda (i) (eq (interest-discharge-condition i) condition*))))
                                  :condition2
                                  ,(cond (condition2 (backwards-formula-condition condition2))
                                         (condition #'(lambda (i) (setf (interest-discharge-condition i) condition*))))
                                  :text-condition condition
                                  :clue? ,clue?
                                  :hypernode-specifier ,hypernode-specifier
                                  :instantiator
                                  (reason-instantiator
                                    ,premise ',(subset #'(lambda (v) (occur-quoted v premise)) new-vars))))))))))
            (push new-premise premises)))
        (when (null premise-list) (return (reverse premises)))))))

(defun rectify-reason-condition (formula premise-variables)
  (let ((vars (subset #'(lambda (v) (o-occur v formula)) premise-variables)))
    (when vars
      `(let*
         ,@
         (list (mapcar #'(lambda (v) `(,v (e-assoc ',v binding))) vars)
               (rectify-formula-condition (parse-arithmetical-formula formula)))))))

(defun conclusion-instantiator (formula variables default)
  (cond (variables
          (eval
            `#'(lambda (binding)
                 (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables))
                   (list (cons ,(formula-instantiator formula variables) ,default))))))
        (t #'(lambda (binding) (declare (ignore binding)) (list (cons formula default))))))

#|
(defun reason-instantiator- (P variables)
  (cond (variables
          `#'(lambda (binding)
               (let* ((new-vars nil)
                      (new-binding binding)
                      ,@
                      (mapcar
                        #'(lambda (v)
                            `(,v
                               (let ((v* (cdr (assoc ',v binding))))
                                 (when (null v*)
                                   (setf v* (make-interest-variable))
                                   (push v* new-vars)
                                   (push (cons ',v v*) new-binding))
                                 v*)))
                        variables))
                 (values ,(formula-instantiator P variables) new-vars new-binding))))
        (t `#'(lambda (binding) (values ',P nil binding)))))

(defun reason-instantiator- (P variables)
  `#'(lambda (binding)
       (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables))
         ,(formula-instantiator P variables))))
|#

(defmacro def-forwards-reason (name &rest body)
  (let* ((newbody (make-clauses body))
         (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
         (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
         (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
         (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
         (discount (cadr (find-if #'(lambda (x) (eq (car x) :reason-discount-factor)) newbody)))
         (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :reason-temporal?)) newbody)))
         (conclusion (find-if #'(lambda (x)
                                  (or (eq (car x) :conclusions)
                                      (eq (car x) :conclusion))) newbody))
         (conclusion-function
           (find-if #'(lambda (x) (eq (car x) :reason-conclusions-function)) newbody))
         (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-backwards-premises)) newbody)))
         (premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-forwards-premises)) newbody))))
    (when description (setf description (mem2 description)))
    (when defeasible? (setf defeasible? (mem2 defeasible?)))
    (when variables (setf variables (list 'quote (cdr variables))))
    (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
    (when conclusion
      (setf conclusion
            (list 'quote
                  (mapcar #'(lambda (x) (reform-if-string x (eval variables))) (cdr conclusion)))))
    (cond
      (conclusion-function
        (let ((c-vars (subset #'(lambda (v) (o-occur* v (mem2 conclusion-function)))
                              (eval variables))))
          (setf conclusion-function
                `#'(lambda (binding)
                     (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                       ,(mem2 conclusion-function))))))
      (t
        (let ((c-vars (subset #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables))))
          (cond
            (c-vars
              (setf conclusion-function
                    `#'(lambda (binding)
                         (let* ((i-vars nil) ,@ (mapcar
                                                  #'(lambda (v)
                                                      `(,v
                                                         (let ((assoc (assoc ',v binding)))
                                                           (if assoc (cdr assoc)
                                                             (let ((i-var (make-interest-variable)))
                                                               (push i-var i-vars) i-var)))))
                                                  c-vars))
                           (values
                             ,(cons 'list
                                    (rectify-conclusions-list
                                      (mapcar
                                        #'(lambda (x) (formula-instantiator x c-vars))
                                        (eval conclusion)) defeasible?))
                             i-vars)
                           ))))
            (t
              (setf conclusion-function
                    `#'(lambda (binding) (declare (ignore binding))
                         (values
                           ,(cons 'list (rectify-conclusions-list
                                          (mapcar
                                            #'(lambda (x) (formula-instantiator x nil))
                                            (eval conclusion)) defeasible?) )
                           i-vars)
                         ))))
          )))
    (when backwards-premises
      (setf backwards-premises
            (cons 'list (rectify-backwards-premises backwards-premises (eval variables)))))
    (when premises
      (setf premises (cons 'list (rectify-forwards-premises premises (eval variables)))))

    (when (stringp name) (setf name (read-from-string name)))

    `(progn
       (proclaim (list 'special ',name))

       (let ((defeaters nil))
         (when (and (boundp ',name) ,name)
           (pull ,name *forwards-substantive-reasons*)
           (dolist (R defeaters) (pull ,name (reason-defeatees R)))
           (setf defeaters (reason-undercutting-defeaters ,name)))

         (setf ,name
               (make-forwards-reason
                 :reason-name ',name
                 :reason-forwards-premises ,premises
                 :reason-backwards-premises ,backwards-premises
                 :reason-conclusions ,conclusion
                 :reason-conclusions-function ,conclusion-function
                 :reason-variables ,variables
                 :reason-strength ,strength
                 :reason-discount-factor (or ,discount 1.0)
                 :reason-defeasible-rule ,defeasible?
                 :reason-temporal? ,temporal?
                 :reason-description ,description))

         (setf (reason-undercutting-defeaters ,name) defeaters)
         (dolist (R defeaters) (push ,name (reason-defeatees R)))
         (push ,name *forwards-substantive-reasons*)))))

;=========================================================================

#|
Backwards-reasons are defined using the following form:

(def-backwards-reason symbol
                      :reason-forwards-premises list of formulas or formula-condition pairs
                      :reason-backwards-premises  list of formulas or pairs (formula,(condition1,condition2))
                      :conclusions formula
                      :condition  this is a predicate applied to the binding produced by thetarget sequent
                      :strength number (default is 1.0)
                      :variables list of symbols
                      :defeasible? T or NIL (NIL is default)
                      :description  an optional string (quoted) describing the reason
                      )

The conditions on reason-forwards-premises are  predicates on c interest, and the values
of the binding.  The default is #'(lambda (c interest &rest r) (declare (ignore interest r)) (is-inference c)).

For example,

(def-backwards-reason R
                      :reason-forwards-premises   (F x y)   (G y z) (:condition (numberp z))
                      :reason-backwards-premises   (H z w)
                      :conclusions   (K x w)
                      :variables   x y z w
                      :strength   .95
                      :defeasible? T)

expands into the following code:

(progn
  (proclaim (list 'special 'r))
  (when (boundp 'r) (pull r *backwards-substantive-reasons*))
  (let* ((c-vars (remove-if-not #'(lambda (v) (o-occur* v '(k x w))) '(x y z w)))
         (c-binding-function (eval (binding-function '(k x w) c-vars))))
    (setf r
          (make-backwards-reason
            :reason-name 'r
            :reason-forwards-premises
            (list
              (list
                '(f x y)
                #<Compiled-function is-inference #x17C13C6>
                #'(lambda (%z %v)
                    (declare (ignore %v))
                    (when (and (listp %z) (equal (element 0 %z) 'f))
                      (values (list (cons 'y (element 2 %z)) (cons 'x (element 1 %z))) t)))
                '(x y))
              (list
                '(g y z)
                #'(lambda (c binding) (and (eq (hypernode-kind c) :inference)
                                           (let* ((z (cdr (assoc 'z binding)))) (numberp z))))
                #'(lambda (%z %v)
                    (declare (ignore %v))
                    (when (and (listp %z) (equal (element 0 %z) 'g))
                      (values (list (cons 'z (element 2 %z)) (cons 'y (element 1 %z))) t)))
                '(y z)))
            :reason-backwards-premises (list (list '(h z w) '(nil nil)))
            :reason-conclusions '(k x w)
            :reason-conclusions-function nil
            :reason-variables '(x y z w)
            :b-reason-length 1
            :reason-strength 0.95
            :reason-defeasible-rule t
            :b-reason-conclusions-binding-function c-binding-function
            :b-reason-condition nil
            :reason-description nil)))
  (push r *backwards-substantive-reasons*))

|#

(defmacro def-backwards-reason (name &rest body)
  (let* ((newbody (make-clauses body))
         (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
         (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
         (condition (find-if #'(lambda (x) (eq (car x) :condition)) newbody))
         (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
         (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
         (discount (cadr (find-if #'(lambda (x) (eq (car x) :reason-discount-factor)) newbody)))
         (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :reason-temporal?)) newbody)))
         (immediate (cadr (find-if #'(lambda (x) (eq (car x) :immediate)) newbody)))
         (conclusion (find-if #'(lambda (x)
                                  (or (eq (car x) :conclusions)
                                      (eq (car x) :conclusion))) newbody))
         (conclusion-function
           (find-if #'(lambda (x) (eq (car x) :reason-conclusions-function)) newbody))
         (c-vars nil)
         (discharge (find-if #'(lambda (x) (eq (car x) :discharge)) newbody))
         (forwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-forwards-premises)) newbody)))
         (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-backwards-premises)) newbody))))
    (when description (setf description (mem2 description)))
    (when defeasible? (setf defeasible? (mem2 defeasible?)))
    (when variables (setf variables (list 'quote (cdr variables))))
    (when condition
      (setf condition
            `#'(lambda (binding) ,(rectify-reason-condition (mem2 condition) (eval variables)))))
    (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
    (when discharge
      (setf discharge (list 'quote (reform-if-string (mem2 discharge) (eval variables)))))
    (when conclusion
      (setf conclusion
            (list 'quote
                  (mapcar #'(lambda (x) (reform-if-string x (eval variables))) (cdr conclusion)))))
    (cond
      (conclusion-function
        (setf c-vars (subset #'(lambda (v) (o-occur* v (mem2 conclusion-function)))
                             (eval variables)))
        (setf conclusion-function
              `#'(lambda (binding)
                   (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                     ,(mem2 conclusion-function)))))
      (t
        (setf c-vars (subset #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables)))
        (cond
          (c-vars
            (setf conclusion-function
                  `#'(lambda (binding)
                       (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                         ,(cons 'list
                                (rectify-conclusions-list
                                  (mapcar
                                    #'(lambda (x) (formula-instantiator x c-vars))
                                    (eval conclusion)) defeasible?))))))
          (t
            (setf conclusion-function
                  `#'(lambda (binding) (declare (ignore binding))
                       ,(cons 'list (rectify-conclusions-list
                                      (mapcar
                                        #'(lambda (x) (formula-instantiator x nil))
                                        (eval conclusion)) defeasible?) )))))))
    (when forwards-premises
      (setf forwards-premises
            (cons 'list (rectify-forwards-premises forwards-premises (eval variables) c-vars))))
    (when backwards-premises
      (setf backwards-premises
            (cons 'list (rectify-backwards-premises backwards-premises (eval variables) c-vars))))
    (when (stringp name) (setf name (read-from-string name)))
    (let* ((c-vars (remove-if-not #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables)))
           (c-binding-function (binding-function (mem1 (eval conclusion)) c-vars)))

      `(progn
         (proclaim (list 'special ',name))

         (let ((defeaters nil))
           (when (and (boundp ',name) ,name)
             (pull ,name *backwards-substantive-reasons*)
             (dolist (R defeaters) (pull ,name (reason-defeatees R)))
             (setf defeaters (reason-undercutting-defeaters ,name)))

           (setf ,name
                 (make-backwards-reason
                   :reason-name ',name
                   :reason-forwards-premises ,forwards-premises
                   :reason-backwards-premises ,backwards-premises
                   :reason-conclusions ,conclusion
                   :b-reason-discharge ,discharge
                   :reason-conclusions-function ,conclusion-function
                   :reason-variables ,variables
                   :b-reason-length ,(length (eval backwards-premises))
                   :reason-discount-factor (or ,discount 1.0)
                   :reason-strength ,strength
                   :reason-defeasible-rule ,defeasible?
                   :reason-temporal? ,temporal?
                   :b-reason-immediate ,immediate
                   :b-reason-conclusions-binding-function ,c-binding-function
                   :b-reason-condition ,condition
                   :reason-description ,description))

           (setf (reason-undercutting-defeaters ,name) defeaters)
           (dolist (R defeaters) (push ,name (reason-defeatees R)))
           (push ,name *backwards-substantive-reasons*))))))

;; ======================================================================

(defun fp-formula* (premise)
  (let ((p (fp-formula premise)))
    (cond ((eq (fp-kind premise) :percept)
           (list 'it-appears-to-me-that (mem2 p) (mem3 p)))
          (t p))))

; --------------------------------------  FORWARDS-REASONS --------------------------------------

#| This defines a generic structure whose slots are those used in common by both
backwards and forwards reasons.  If use-basis is nil, when a hyperlink is constructed,
the basis is nil.  This is used by def-prob-rule. |#

(defstruct (reason (:print-function
		    (lambda (x stream depth)
		      (declare (ignore depth)) (princ (reason-name x) stream)))
		   (:conc-name nil))
  (reason-name nil)
  (reason-function nil)
  (reason-conclusions nil)
  (reason-conclusions-function nil)
  (reason-forwards-premises nil)
  (reason-backwards-premises nil)
  (reason-variables nil)
  (reason-defeasible-rule nil)
  (reason-strength 1.0)
  (reason-discount-factor 1.0)
  (reason-description nil)
  (reason-instantiated-premise nil)
  (reason-backwards-premises-function nil)
  (reason-temporal? nil)
  (reason-undercutting-defeaters nil)
  (reason-defeatees)
  )

;(defun reason-strength+ (reason)
;    (if (stringp reason) 1.0 (reason-strength reason)))

(defun reason (name)
  (let ((R (find-if #'(lambda (x) (equal (reason-name x) name)) *forwards-reasons*)))
    (when (null R)
      (setf R (find-if #'(lambda (x) (equal (reason-name x) name)) *backwards-reasons*)))
    R))

(defun premise-hypernode-specifier (premise)
  (cond ((backwards-premise-p premise) (bp-hypernode-specifier premise))
        ((forwards-premise-p premise) (fp-hypernode-specifier premise))))

(defun undercutters-for (reason)
  (mapcar
    #'(lambda (c)
        (make-@
          (gen-conjunction
            (append
              (subset #'(lambda (p) (or (not (listp p)) (not (equal (car p) 'define))))
                      (mapcar #'fp-formula* (remove-if #'fp-clue? (reason-forwards-premises reason))))
              (subset #'(lambda (p) (or (not (listp p)) (not (equal (car p) 'define))))
                      (mapcar #'bp-formula (reason-backwards-premises reason)))))
          c))
    (reason-conclusions reason)))

(defmacro def-forwards-undercutter (name &rest body)
  (let* ((newbody (make-clauses body))
         (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
         (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
         (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
         (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
         (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :reason-temporal?)) newbody)))
         (discount (cadr (find-if #'(lambda (x) (eq (car x) :reason-discount-factor)) newbody)))
         (defeatee (find-if #'(lambda (x) (eq (car x) :defeatee)) newbody))
         (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-backwards-premises)) newbody)))
         (premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-forwards-premises)) newbody))))
    (when description (setf description (mem2 description)))
    (when defeasible? (setf defeasible? (mem2 defeasible?)))
    (when variables (setf variables (list 'quote (cdr variables))))
    (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
    (setf defeatee (mem2 defeatee))
    (let ((conclusion `',(undercutters-for (eval defeatee)))
          (conclusion-function nil))
      (let ((c-vars (subset #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables))))
        (cond
          (c-vars
            (setf conclusion-function
                  `#'(lambda (binding)
                       (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                         ,(cons 'list
                                (mapcar
                                  #'(lambda (x) (formula-instantiator x c-vars))
                                  (eval conclusion)))))))
          (t
            (setf conclusion-function
                  `#'(lambda (binding) (declare (ignore binding)) ',(eval conclusion))))))
      (when backwards-premises
        (setf backwards-premises
              (cons 'list (rectify-backwards-premises backwards-premises (eval variables)))))
      (when premises
        (setf premises (cons 'list (rectify-forwards-premises premises (eval variables)))))

      (when (stringp name) (setf name (read-from-string name)))

      `(progn
         (proclaim (list 'special ',name))

         (let ((defeaters nil))
           (when (and (boundp ',name) ,name)
             (pull ,name *backwards-substantive-reasons*)
             (dolist (R defeaters) (pull ,name (reason-defeatees R)))
             (setf defeaters (reason-undercutting-defeaters ,name)))

           (setf ,name
                 (make-forwards-reason
                   :reason-name ',name
                   :reason-forwards-premises ,premises
                   :reason-backwards-premises ,backwards-premises
                   :reason-conclusions ,conclusion
                   :reason-conclusions-function ,conclusion-function
                   :reason-variables (union ,variables (reason-variables ,defeatee))
                   :reason-strength ,strength
                   :reason-discount-factor (or ,discount 1.0)
                   :reason-defeasible-rule ,defeasible?
                   :reason-temporal? ,temporal?
                   :reason-description ,description))

           (setf (reason-undercutting-defeaters ,name) defeaters)
           (dolist (R defeaters) (push ,name (reason-defeatees R)))
           (push ,name *forwards-substantive-reasons*))))))

(defmacro def-backwards-undercutter (name &rest body)
  (let* ((newbody (make-clauses body))
         (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
         (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
         (condition (find-if #'(lambda (x) (eq (car x) :condition)) newbody))
         (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
         (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
         (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :reason-temporal?)) newbody)))
         (discount (cadr (find-if #'(lambda (x) (eq (car x) :reason-discount-factor)) newbody)))
         (defeatee (find-if #'(lambda (x) (eq (car x) :defeatee)) newbody))
         (discharge (find-if #'(lambda (x) (eq (car x) :discharge)) newbody))
         (forwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-forwards-premises)) newbody)))
         (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :reason-backwards-premises)) newbody)))
         ; (conclusion (find-if #'(lambda (x) (eq (car x) :conclusions)) newbody))
         )
    (when description (setf description (mem2 description)))
    (when defeasible? (setf defeasible? (mem2 defeasible?)))
    (when variables (setf variables (list 'quote (cdr variables))))
    (when condition
      (setf condition
            `#'(lambda (binding) ,(rectify-reason-condition (mem2 condition) (eval variables)))))
    (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
    (when discharge
      (setf discharge (list 'quote (reform-if-string (mem2 discharge) (eval variables)))))
    (setf defeatee (cons 'list (cdr defeatee)))
    (when forwards-premises
      (setf forwards-premises
            (cons 'list (rectify-forwards-premises forwards-premises (eval variables) variables))))
    (when backwards-premises
      (setf backwards-premises
            (cons 'list (rectify-backwards-premises backwards-premises (eval variables) variables))))
    (when (stringp name) (setf name (read-from-string name)))

    `(progn
       (proclaim (list 'special ',name))

       (let ((defeaters nil))
         (when (and (boundp ',name) ,name)
           (pull ,name *backwards-substantive-reasons*)
           (setf defeaters (reason-undercutting-defeaters ,name))
           (dolist (d ,defeatee) (pull ,name (reason-undercutting-defeaters d))))

         (setf ,name
               (make-backwards-reason
                 :reason-name ',name
                 :reason-forwards-premises ,forwards-premises
                 :reason-backwards-premises ,backwards-premises
                 :reason-defeatees ,defeatee
                 :b-reason-discharge ,discharge
                 :reason-variables ',(union (eval variables) (unionmapcar+ #'reason-variables (eval defeatee)))
                 :b-reason-length ,(length (eval backwards-premises))
                 :reason-strength ,strength
                 :reason-discount-factor (or ,discount 1.0)
                 :reason-defeasible-rule ,defeasible?
                 :reason-temporal? ,temporal?
                 :b-reason-condition ,condition
                 :reason-description ,description))

         (setf (reason-undercutting-defeaters ,name) defeaters)
         (push ,name *backwards-substantive-reasons*)
         (dolist (d ,defeatee) (push ,name (reason-undercutting-defeaters d)))
         ))))
#|This is the  agent-architecture OSCAR, described in chapter nine of COGNITIVE
CARPENTRY.|#

#| This is based upon OSCAR_3.32.  It introduces the new computation for hypergraphs.
It requires Hypergraphs11.lisp. |#

;========================== OSCAR =========================

(defun print-sequent (S &optional stream)
  (prinp (sequent-formula S) stream) (princ "/" stream) (set-prinp (sequent-supposition S) stream))

(defstruct (hypernode (:print-function
		       (lambda (x stream depth)
                         (declare (ignore depth))
                         (princ "#<" stream) (princ "Hypernode " stream)
                         (princ (hypernode-number x) stream)
                         (princ ": " stream)
                         (if (hypernode-supposition x) (print-sequent (hypernode-sequent x) stream)
                           (princ (pretty (hypernode-formula x)) stream))
                         (princ ">" stream)))
                      (:conc-name nil))
  (hypernode-number 0)
  (hypernode-sequent nil)
  (hypernode-formula nil)
  (hypernode-supposition nil)
  (hypernode-kind nil)   ;;:percept, :desire, or :inference
  (hypernode-hyperlinks nil)
  (hypernode-justification nil)  ;; a keyword if the node is given or a supposition
  (hypernode-consequent-links nil)
  (hypernode-old-degree-of-justification nil) ;; the degree prior to the last computation of defeat statuses
  (hypernode-reductio-ancestors nil)
  (hypernode-non-reductio-supposition nil)
  (hypernode-supported-hyper-defeat-links nil)  ;; hyper-defeat-links for which the node is the root
  (hypernode-degree-of-justification nil)
  (hypernode-maximal-degree-of-justification 0)  ;; maximal possible dj, ignoring defeat
  (hypernode-ancestors nil)
  (hypernode-nearest-defeasible-ancestors nil)
  (hypernode-answered-queries nil)
  (hypernode-deductive-only nil)   ;; If conclusion is for deductive purposes only, this is t.
  (hypernode-generated-interests nil)
  (hypernode-generating-interests nil);; interest generating sup
  (hypernode-cancelled-node nil)
  (hypernode-discounted-node-strength nil)
  (hypernode-processed? nil)  ;;  T if node has been processed.
  (hypernode-variables nil)
  (hypernode-discharged-interests nil)  ;; triples (interest unifier unifiers) where unifiers is produced by
  ;; appropriately-related-suppositions.  unifier and unifiers are
  ;; left nil in cases where they will not be used.
  (hypernode-supposition-variables nil)
  (hypernode-interests-discharged? nil)   ;; records whether interests have been discharged
  (hypernode-reductios-discharged (not *use-reductio*))  ;; records whether reductio-interests have been discharged
  (hypernode-readopted-supposition 0)  ;; number of times the node has been readopted as a supposition
  (hypernode-discount-factor 1.0)  ;; This is the discount-factor provided by the hypernode-rule.
  ;;  it's only use is in ei.
  (hypernode-c-list nil)
  (hypernode-queue-node nil)
  (hypernode-enabling-interests nil)  ;; if the node is obtained by discharging inference-links, this is the
  ;; list of resultant-interests of the links.
  (hypernode-motivating-nodes nil)  ;; nodes motivating the inference, not included in the basis.
  (hypernode-generated-direct-reductio-interests nil)
  (hypernode-generated-defeat-interests nil)
  (hypernode-generating-defeat-interests nil)  ;; interest in defeaters discharged by this node
  (hypernode-temporal-node nil)  ;; nil or the cycle on which the node was constructed
  (hypernode-background-knowledge nil)
  (hypernode-non-reductio-supposition? nil)
  (hypernode-anchoring-interests nil)
  (hypernode-justifications nil)  ;; list of pairs (sigma.val) used by justification
  (hypernode-in (list nil))  ;; list of  lists of links
  (hypernode-dependencies nil)   ;; list of sigmas
  )

;---------------------------------  hyperlinkS ----------------------------------

(defstruct (hyperlink (:print-function
		       (lambda (x stream depth)
                         (declare (ignore depth))
                         (princ "#<" stream) (princ "hyperlink #" stream)
                         (princ (hyperlink-number x) stream) (princ " for hypernode " stream)
                         (princ (hypernode-number (hyperlink-target x)) stream)
                         (princ ">" stream)))
                      (:conc-name nil))
  (hyperlink-number 0)
  (hyperlink-target nil)   ;; the node supported by the link
  (hyperlink-basis nil)   ;; a list of hypernodes
  (hyperlink-rule nil)  ;; a substantive reason or a string describing an inference rule
  (hyperlink-defeasible? nil)  ;; t if the inference is a defeasible one
  (hyperlink-defeaters nil)  ;; a list of hyper-defeat-links
  (hyperlink-degree-of-justification nil)
  (hyperlink-discount-factor 1.0)  ;; This is the discount-factor provided by the link-rule.
  (hyperlink-nearest-defeasible-ancestors nil)
  (hyperlink-reason-strength 1.0)  ;; the strength of the reason
  (hyperlink-binding nil)
  (hyperlink-conclusive-defeat-status nil)
  (hyperlink-temporal nil)
  (hyperlink-generating-interest-link nil)
  (hyperlink-clues nil)
  (hyperlink-unsecured? nil) ;; list of sigmas
  (hyperlink-defeat-loops T) ;; defeat-loops from link to link
  (hyperlink-justifications nil)  ;; list of pairs (sigma.val) used by justification
  (hyperlink-in (list nil))  ;; list of sigmas
  (hyperlink-dependencies nil)  ;; list of sigmas
  )

#| This finds the hyperlink with hyperlink-number n. |#
(defun hyperlink (n)
  (find-if #'(lambda (L) (equal (hyperlink-number L) n))
           *hyperlinks*))

; -------------------------------------- hypernodeS --------------------------------------

(defstruct (hyper-defeat-link (:print-function
			       (lambda (x stream depth)
                                 (declare (ignore depth))
                                 (princ "#<" stream) (princ "hyper-defeat-link #" stream)
                                 (princ (hyper-defeat-link-number x) stream) (princ " for hyperlink " stream)
                                 (princ (hyperlink-number (hyper-defeat-link-target x)) stream) (princ " for hypernode " stream)
                                 (princ (hypernode-number (hyperlink-target (hyper-defeat-link-target x))) stream)
                                 (princ ">" stream)))
                              (:conc-name nil))
  (hyper-defeat-link-number 0)
  (hyper-defeat-link-target nil)   ;; the hyperlink defeated by the link
  (hyper-defeat-link-root nil)   ;; an hypernode
  (hyper-defeat-link-critical? nil)  ;; list of (X.t) or (sigma.nil)
  (hyper-defeat-link-justifications nil)  ;; list of pairs (sigma.val).
  (hyper-defeat-link-in (list nil))  ;; list of  lists of links
  )

(defun build-hyper-defeat-link (root target)
  (let ((DL (make-hyper-defeat-link
              :hyper-defeat-link-number (incf *hyper-defeat-link-number*)
              :hyper-defeat-link-target target
              :hyper-defeat-link-root root)))
    (push DL *hyper-defeat-links*)
    DL))

#| This finds the hyper-defeat-link with hyper-defeat-link-number n. |#
(defun hyper-defeat-link (n)
  (find-if #'(lambda (L) (equal (hyper-defeat-link-number L) n))
           *hyper-defeat-links*))

(defun hypernode (n)
  (find-if #'(lambda (node) (equal (hypernode-number node) n))
           *hypergraph*))

(defun nf (n)
  (when (numberp n) (setf n (hypernode n)))
  (prinp (hypernode-formula n))
  (hypernode-formula n))

(defun adjust-for-time (strength node)
  (let ((delta (- *cycle* (hypernode-temporal-node node))))
    (cond ((>= delta *temporal-decay-minimum*) 0.0)
          ((zerop strength) 0.0)
          (t (- (* (+ strength 1) (expt *temporal-decay* delta)) 1)))))

(defun adjust-for-decay (strength decay)
  (if (or (zerop strength) (< decay .5)) 0.0 (- (* (+ strength 1) decay) 1)))

(defun current-maximal-degree-of-justification (node)
  (cond
    (*deductive-only* 1.0)
    ((hypernode-temporal-node node)
     (adjust-for-time (hypernode-maximal-degree-of-justification node) node))
    (t (hypernode-maximal-degree-of-justification node))))

(defun current-degree-of-justification (node)
  (cond
    (*deductive-only* 1.0)
    ((hypernode-temporal-node node)
     (adjust-for-time (hypernode-degree-of-justification node) node))
    (t (hypernode-degree-of-justification node))))

(defun compute-old-degree-of-justification (node)
  (if (and (hypernode-temporal-node node) (hypernode-old-degree-of-justification node))
    (adjust-for-time (hypernode-old-degree-of-justification node) node)
    (hypernode-old-degree-of-justification node)))

(defun compute-discounted-node-strength (node)
  (if (hypernode-temporal-node node)
    (adjust-for-time (hypernode-discounted-node-strength node) node)
    (hypernode-discounted-node-strength node)))

(defun deductive-node (n)
  (and (not (hypernode-background-knowledge n))
       (member nil (hypernode-nearest-defeasible-ancestors n))))

(defun hypernode-consequences (n)
  (mapcar #'hyperlink-target (hypernode-consequent-links n)))

(defun subsumes (sequent1 sequent2)
  (and (equal (sequent-formula sequent1) (sequent-formula sequent2))
       (subsetp= (sequent-supposition sequent1) (sequent-supposition sequent2))))

(defun hypernode-defeatees (node)
  (mapcar #'hyper-defeat-link-target (hypernode-supported-hyper-defeat-links node)))

(defun hyperlink-hypernode-defeaters (link)
  (mapcar #'hyper-defeat-link-root (hyperlink-defeaters link)))

;======================================================
; -------------------------------------- CONCLUSIONS --------------------------------------

(defstruct (d-node (:conc-name nil)
		   (:print-function
		    (lambda (x stream depth)
                      (declare (ignore depth))
                      (princ "#<" stream) (princ "d-node: " stream)
                      (princ (d-node-number x) stream) (princ ">" stream))))
  d-node-number
  (d-node-description nil)
  (d-node-discrimination-tests nil)
  (d-node-c-lists nil)
  (d-node-i-lists nil)
  (d-node-parent nil)
  (d-node-forwards-reasons nil)  ;; a list of partially-instantiated-premises
  (d-node-backwards-reasons nil)  ;; a list of non-degenerate backwards-reasons
  (d-node-interest-schemes nil)  ;; a list of partially-instantiated-premises
  (d-node-degenerate-backwards-reasons nil)
  )

(defun d-node (n)
  (find-if #'(lambda (dn) (eql (d-node-number dn) n)) *discrimination-net*))

(defun formula-code* (P descriptor)
  (cond ((listp P)
         (let ((description nil) (elt-num 1) (term-list nil))
           (cond
             ;; This handles notational variants.
             ((or (eq (car p) 'all) (eq (car P) 'some))
              (setf P
                    (cons (car P) (subst (list 'q-var (incf *quantifier-number*)) (mem2 P) (cddr P)))))
             ((eq (car P) 'at)
              (setf term-list (cddr P))
              (setf P (list (car P) (cadr P))))
             ((eq (car P) 'throughout)
              (setf term-list (cdr (mem3 P)))
              (setf P (list (car P) (cadr P) (list (car (mem3 P))))))
             ((and (symbolp (car P))
                   (not (member (car P) *operators*))
                   (not (member (car P) '(~ & v -> <-> all some ? @))))
              (setf term-list (cdr P))
              (setf P (list (car P)))))
           (dolist (Q P)
             (let ((Q-descriptor (cons elt-num descriptor)))
               (cond ((not (listp Q))
                      (push (cons (reverse Q-descriptor) Q) description))
                     (t
                       (multiple-value-bind (d tl) (formula-code* Q Q-descriptor)
                         (setf term-list (append tl term-list))
                         (setf description (append d description))
                         )))
               (incf elt-num)))
           (values description term-list)))
        (t (values (list (cons descriptor P)) nil))))

(defun formula-code (P)
  (setf *quantifier-number* 0)
  (multiple-value-bind (code term-list) (formula-code* P nil)
    (values (reverse code) term-list)))

(defun prinp-test (test)
  (princ "(") (princ (caar test)) (princ " . ") (prinp (cdar test)) (princ ") : ") (princ (cdr test)))

(defstruct (c-list (:print-function
		    (lambda (x stream depth)
                      (declare (ignore depth))
                      (princ "#<c-list for " stream)
                      (prinp (c-list-formula x) stream) (princ ">" stream)))
                   (:conc-name nil))
  (c-list-formula nil)
  (c-list-corresponding-i-lists nil)
  (c-list-nodes nil)
  (c-list-processed-nodes nil)
  (c-list-link-defeatees nil)
  (c-list-reductio-interests nil)
  (c-list-variables nil)
  (c-list-contradictors nil)
  (c-list-term-list nil)
  (c-list-d-node nil)
  (c-list-generated-instantiated-premises nil)
  (c-list-supported-interest-schemes nil))

(defun notational-variant (p q &optional vars)
  (cond ((null p) (null q))
        ((listp p)
         (and (listp q)
              (cond ((and (or (eq (car p) 'some) (eq (car p) 'all))
                          (eq (car p) (car q)))
                     (notational-variant (cdr p) (cdr q)
                                         (cons (cons (cadr p) (cadr q)) vars)))
                    ((listp (car q)) (and (notational-variant (car p) (car q) vars)
                                          (notational-variant (cdr p) (cdr q) vars)))
                    ((or (eql (car p) (car q))
                         (and vars
                              (mem (cons (car p) (car q)) vars)))
                     (notational-variant (cdr p) (cdr q) vars)
                     ))))
        (t (and (not (listp q))
                (or (eql p q)
                    (mem (cons p q) vars))))))

(defun processed-c-list-for (formula)
  (cdr (find-if #'(lambda (cl) (notational-variant formula (car cl))) *processed-conclusions*)))

(defun processed-nodes-for (formula)
  (let ((c-list (processed-c-list-for formula)))
    (if c-list (c-list-nodes c-list))))

(defun display-conclusion (n)
  (terpri) (princ n)
  (when (not (equal (hypernode-kind n) :inference))
    (terpri) (princ "  kind: ") (princ (hypernode-kind n)))
  (terpri) (princ "  degree-of-justification: ")
  (princ (current-degree-of-justification n))
  (dolist (Q (hypernode-answered-queries n))
    (terpri) (princ "  This answers ") (princ Q)))

(defun display-conclusions ()
  (princ "(") (terpri)
  (princ "================== CONCLUSIONS ===================")
  (let* ((star-conclusions
           (unionmapcar
             #'(lambda (dn)
                 (unionmapcar
                   #'(lambda (cl) (c-list-nodes cl)) (d-node-c-lists dn)))
             *discrimination-net*))
         (conclusions
           (order star-conclusions
                  #'(lambda (c1 c2)
                      (< (hypernode-number c1) (hypernode-number c2))))))
    (dolist (conclusion conclusions)
      (display-conclusion conclusion)
      (terpri) (princ "---------------------------------------------------")))
  (princ ")") (terpri))

(defun display-conclusions-by-supposition ()
  (princ "(") (terpri)
  (let ((suppositions nil))
    (dolist (dn *discrimination-net*)
      (dolist (cl (d-node-c-lists dn))
        (dolist (c (c-list-nodes cl))
          (pushnew (hypernode-supposition c) suppositions :test '==)
          (setf suppositions
                (order suppositions
                       #'(lambda (s1 s2)
                           (or (< (length s1) (length s2))
                               (and (= (length s1) (length s2))
                                    (lessp s1 s2)))))))))
    (let* ((star-conclusions
             (unionmapcar
               #'(lambda (dn)
                   (unionmapcar
                     #'(lambda (cl) (c-list-nodes cl)) (d-node-c-lists dn)))
               *discrimination-net*)))
      (dolist (sup suppositions)
        (princ "==========================================") (terpri)
        (princ "Conclusions with supposition ") (set-prinp sup) (princ ":") (terpri)
        (let* ((sup-conclusions
                 (subset #'(lambda (c) (== (hypernode-supposition c) sup))
                         star-conclusions))
               (conclusions
                 (order sup-conclusions
                        #'(lambda (c1 c2)
                            (< (hypernode-number c1) (hypernode-number c2))))))
          (dolist (c conclusions)
            (when (== (hypernode-supposition c) sup)
              (princ "    #") (princ (hypernode-number c)) (princ "  ")
              (prinp (hypernode-formula c)) (terpri)))))))
  (princ ")") (terpri))

(defun display-c-lists ()
  (princ "(") (terpri)
  (dolist (dn *discrimination-net*)
    (dolist (cl (d-node-c-lists dn))
      (princ "==========================================") (terpri)
      (princ "c-list-formula: ") (prinp (c-list-formula cl)) (terpri)
      (let ((conclusions
              (order (c-list-nodes cl)
                     #'(lambda (c1 c2)
                         (let ((s1 (hypernode-supposition c1))
                               (s2 (hypernode-supposition c2)))
                           (or (< (length s1) (length s2))
                               (and (= (length s1) (length s2))
                                    (lessp s1 s2))))))))
        (dolist (c conclusions)
          (princ "    #") (princ (hypernode-number c))
          (princ "   sup = ") (set-prinp (hypernode-supposition c))
          (terpri)))))
  (princ ")") (terpri))

(defun display-processed-c-lists ()
  (princ "(") (terpri)
  (dolist (cl *processed-conclusions*)
    (princ "==========================================") (terpri)
    (princ "c-list-formula: ") (prinp (car cl)) (terpri)
    (let ((conclusions
            (order (c-list-nodes (cdr cl))
                   #'(lambda (c1 c2)
                       (let ((s1 (hypernode-supposition c1))
                             (s2 (hypernode-supposition c2)))
                         (or (< (length s1) (length s2))
                             (and (= (length s1) (length s2))
                                  (lessp s1 s2))))))))
      (dolist (c conclusions)
        (princ "    #") (princ (hypernode-number c))
        (princ "   sup = ") (set-prinp (hypernode-supposition c))
        (terpri))))
  (princ ")") (terpri))

(defun ?-variables (formula)
  (cond ((and formula (listp formula))
         (union (?-variables (car formula)) (?-variables (cdr formula))))
        ((atom formula)
         (if (equal (car (explode (write-to-string formula))) "?") (list formula)))))

(defun search-d-nodes (formula d-node)
  (let ((nodes nil)
        (?-vars (?-variables formula)))
    (dolist (c-list (d-node-c-lists d-node))
      (dolist (node (c-list-nodes c-list))
        (when (and (null (hypernode-supposition node))
                   (match formula (hypernode-formula node) ?-vars))
          (push node nodes))))
    (append nodes
            (unionmapcar #'(lambda (dt) (search-d-nodes formula (cdr dt)))
                         (d-node-discrimination-tests d-node)))))

(defun pursue-d-node-for (profile d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node))))
    (when dn
      (let ((new-profile (cdr profile)))
        (cond
          (new-profile (pursue-d-node-for new-profile dn))
          (t dn))))))

(defun d-node-for (formula)
  (let ((profile (formula-code formula)))
    (pursue-d-node-for profile *top-d-node*)))

(defstruct (i-list (:print-function
		    (lambda (x stream depth)
                      (declare (ignore depth))
                      (princ "#<i-list for " stream)
                      (prinp (i-list-formula x) stream) (princ ">" stream)))
                   (:conc-name nil))
  (i-list-formula nil)
  (i-list-corresponding-c-lists nil)
  (i-list-interests nil)
  (i-list-queries nil)
  (i-list-reductio-trigger nil)
  (i-list-reductio-supposition nil)
  (i-list-variables)
  (i-list-term-list nil)
  (i-list-d-node nil))

(defun fetch-I-list-for (term-list d-node)
  (find-if #'(lambda (il)
               (equal term-list (i-list-term-list il)))
           (d-node-i-lists d-node)))

; ---------------------------- ULTIMATE-EPISTEMIC-INTERESTS -----------------------------

(defstruct (query (:print-function
		   (lambda (x stream depth)
                     (declare (ignore depth))
                     (princ "#<" stream) (princ "Query " stream) (princ (query-number x) stream)
                     (princ ": " stream) (princ (pretty (query-formula x)) stream)
                     (princ ">" stream)))
                  (:conc-name nil))
  (query-number 0)
  (query-formula nil)
  (query-strength 0)
  (query-queue-node nil)
  (query-deductive nil)  ;; t if the query is whether the query formula is deductively provable
  (query-positive-instructions nil) ;; a list of functions applicable to an hypernode
  (query-negative-instructions nil) ;; a list of functions applicable to an hypernode
  (query-answers nil)  ;;a list of hypernodes
  (query-answered? nil)  ;; t if some answer is justified to degree greater than or equal
  ;; to the degree of interest, nil otherwise
  (query-interest nil)   ;; the interest recording the query
  (query-negative-interest nil)  ;; the negative-interest for a whether-query
  (query-?-constraint nil))  ;; a function which when applied to the ?-vars yields a discharge-condition
;; for the query-interest, constraining the instantiating terms.

;========================SKOLEMIZATION=====================

(defun var-kind (var) (get var 'var-kind))

(defun interest-variable (x)
  (and (symbolp x) (eq (var-kind x) :variable)))

(defun conclusion-variable (x)
  (and (symbolp x) (eq (var-kind x) :variable)))

(defun make-interest-variable ()
  (let ((var (gensym "^@y")))
    (setf (get var 'var-kind) :variable)
    (setf (get var 'i-var) t)
    var))

(defun make-conclusion-variable ()
  (let ((var (gensym "x")))
    (setf (get var 'var-kind) :variable)
    var))

;; This converts interest-variables into conclusion-variables in formula.
(defun convert-interest-variables (formula variables)
  (let* ((vars nil)
         (substitution
           (mapcar #'(lambda (x)
                       (let ((var (make-conclusion-variable)))
                         (push var vars)
                         (cons x var)))
                   variables)))
    (values (sublis substitution formula) vars)))

;; This converts conclusion-variables into interest-variables in formula.
(defun convert-conclusion-variables (formula variables)
  (let* ((vars nil)
         (substitution
           (mapcar #'(lambda (x)
                       (let ((var (make-interest-variable)))
                         (push var vars)
                         (cons x var)))
                   variables)))
    ; (setf substitution (mapcar #'(lambda (x) (cons (cdr x) (car x))) substitution))
    (values (sublis substitution formula) vars substitution)))

;; This converts conclusion-variables into interest-variables in a unifier
(defun convert-unifier-variables (unifier variables)
  ; (when (> *gensym-counter* 78) (setf u unifier v variables) (break))
  (let ((u1 (mem1 unifier)) (u2 (mem2 unifier)))
    (if (eq u2 t) unifier
      (let* ((vars nil)
             (substitution
               (mapcar #'(lambda (x)
                           (let ((var (make-interest-variable)))
                             (push var vars)
                             (cons x var)))
                       variables)))
        (list u1 (mapcar #'(lambda (x) (cons (car x) (sublis substitution (cdr x)))) u2))))))

#| These are changed to allow conses in formulas. |#
(defun formula-hypernode-variables (p)
  (cond ((and (symbolp p) (eq (get p 'var-kind) :variable)) (list p))
        ((and (listp p) p)
         (union (formula-hypernode-variables (car p)) (formula-hypernode-variables (cdr p))))))

(defun make-skolem-e-function ()
  (let ((fun (gensym "s")))
    (setf (get fun 'var-kind) :skolem-function)
    fun))

(defun make-skolem-i-function ()
  (let ((fun (gensym "s")))
    (setf (get fun 'var-kind) :skolem-function)
    fun))

(defun make-skolem-e-constant ()
  (let ((fun (gensym "c")))
    (setf (get fun 'var-kind) :skolem-function)
    fun))

(defun make-skolem-i-constant ()
  (let ((fun (gensym "c")))
    (setf (get fun 'var-kind) :skolem-function)
    fun))

(defun skolem-function (x)
  (and (symbolp x) (eq (get x 'var-kind) :skolem-function)))

(defun skolem-functions (p)
  (cond ((symbolp p)
         (if (skolem-function p) (list p)))
        ((stringp p) nil)
        ((listp p) (unionmapcar= #'skolem-functions p))))

#| P contains no skolem constants, functions, or variables. |#
(defun skolem-free (P)
  (cond ((symbolp P)
         (let ((kind (get P 'var-kind)))
           (and (not (eq kind :variable)) (not (eq kind :skolem-function)))))
        ((listp P) (every #'skolem-free P))
        (t t)))

(defun ?-query-p (Q)
  (and (query-p Q) (?-genp (query-formula Q))))

#| This returns two values: the matrix, and the list of ?-variables. |#
(defun ?-matrix (p &optional vars)
  (push (q-variable p) vars)
  (let ((formula (q-matrix p)))
    (cond ((?-genp formula) (?-matrix formula vars))
          (t (values formula vars)))))

(defun whether-query-p (Q)
  (and (query-p Q) (whether-formula (query-formula Q))))

(defun query (n)
  (find-if #'(lambda (c) (equal (query-number c) n))
           *ultimate-epistemic-interests*))

(defun show-query (Q)
  (if (numberp Q) (setf Q (query Q)))
  (princ Q) (princ ": ")
  (prinp (query-formula Q)) (terpri))

(defun show-queries ()
  (terpri)
  (princ
    "================== ULTIMATE EPISTEMIC INTERESTS ===================")
  (terpri)
  (dolist (Q *ultimate-epistemic-interests*)
    (show-query Q)))

(defun inclusive-hypernode-ancestors (node)
  (cons node (hypernode-ancestors node)))

(defun ancestral-links (node)
  (unionmapcar+ #'hypernode-hyperlinks (inclusive-hypernode-ancestors node)))

(defun display-query (Q)
  (princ "  Interest in ") (prinp (query-formula Q)) (terpri)
  (cond ((null (query-answered? Q))
         (princ "  is unsatisfied.")
         (when (null (query-answers Q)) (princ "  NO ARGUMENT WAS FOUND."))
         (terpri))
        ((or (whether-query-p Q) (?-query-p Q))
         (dolist (C (query-answers Q))
           (when (>= (current-degree-of-justification C) (query-strength Q))
             (princ "  is answered by node ")
             (princ (hypernode-number C)) (princ ":  ")
             (princ (pretty (hypernode-formula C))) (terpri)
             (let ((skolem-functions (skolem-functions (hypernode-formula C))))
               (when skolem-functions
                 (let* ((sf (mem1 skolem-functions))
                        (hyperlink
                          (find-if #'(lambda (SL)
                                       (and (eq (hyperlink-rule SL) EI)
                                            (occur sf (hypernode-formula (hyperlink-target SL)))
                                            (not (occur sf (hypernode-formula (mem1 (hyperlink-basis SL)))))))
                                   (ancestral-links C))))
                   (when hyperlink
                     (let* ((node (mem1 (hyperlink-basis hyperlink)))
                            (formula (hypernode-formula node))
                            (var (q-variable formula)))
                       (princ "  where ") (princ sf) (princ " is any ") (princ var)
                       (princ " such that ") (princ (q-matrix formula)) (princ ",") (terpri)
                       (princ "  and the existence of such")
                       (if (equal var "x") (princ " an ") (princ " a ")) (princ var)
                       (princ " is guaranteed by node ") (princ (hypernode-number node)) (terpri))))))
             )))
        (t (dolist (C (query-answers Q))
             (when (>= (current-degree-of-justification C) (query-strength Q))
               (princ "  is answered affirmatively by node ")
               (princ (hypernode-number C)) (terpri)))))
  (princ "---------------------------------------------------") (terpri))

(defun display-queries ()
  (terpri)
  (princ
    "================== ULTIMATE EPISTEMIC INTERESTS ===================")
  (terpri)
  (dolist (Q *ultimate-epistemic-interests*)
    (display-query Q)))

#| This assumes that formula2 is indefinite. |#
(defun instance-of (formula1 formula2)
  (match (mem2 formula2) formula1 (list (mem2 (mem1 formula2)))))

(defun answers (formula query)
  (let ((query-formula (query-formula query)))
    (if (?-genp query-formula)
      (instance-of formula query-formula)
      (equal formula query-formula))))

(defun complexity (x)
  (cond ((null X) 0)
        ((stringp x) 1)
        ((atom x) 1)
        ((listp x)
         (cond ((skolem-function (car x))
                (cond ((null (cdr x)) 1)
                      ((and (not (listp (cadr x))) (not (eq (cadr x) '=)))
                       *skolem-multiplier*)
                      ((and (listp (cadr x)) (skolem-function (caar (cdr x))))
                       (* *skolem-multiplier* (1+ (complexity (cdr x)))))
                      (t (apply #'+ (mapcar #'complexity x)))))
               ;; the following handles functions that occur within their own scopes
               ((and (not (null (cdr x)))
                     (symbolp (car x))
                     (not (member (mem1 x) *logical-constants*))
                     (occur (car x) (cdr x)))
                (* *skolem-multiplier* (1+ (complexity (cdr x)))))
               ((or (u-genp x) (e-genp x)) (* *quantifier-discount* (complexity (q-matrix x))))
               ((consp (cdr x)) (apply #'+ (mapcar #'complexity x)))
               (t (+ (complexity (car x)) (complexity (cdr x))))))))

; --------------------------------------  THE INFERENCE-QUEUE --------------------------------------

(defstruct (inference-queue-node
	    (:print-function
	     (lambda (x stream depth)
               (declare (ignore depth))
               (princ "#<" stream) (princ "Item " stream)
               (princ (queue-number x) stream) (princ ">" stream)))
	    (:conc-name nil))
  (queue-number 0)
  (queue-item nil)  ;; either an interest or a conclusion or a query
  (queue-item-kind nil)   ;; this will be :conclusion, :interest, or :query
  (queue-item-complexity 0)
  (queue-discounted-strength 0)
  (queue-degree-of-preference 0))

#| *inference-queue* is ordered by i-preference: |#
(defun i-preferred (node1 node2)
  (> (queue-degree-of-preference node1) (queue-degree-of-preference node2)))

#| The following is the default computation of the degree-of-preference for queries. |#
(defun query-preference (query)
  (let ((complexity (complexity (query-formula query)))
        (strength
          (cond ((member query *permanent-ultimate-epistemic-interests*)
                 (query-strength query))
                ((query-answered? query)
                 (* (query-strength query) *answered-discount*))
                (t (query-strength query)))))
    (/ strength complexity)))

(defun queue-query-for-interest (query)
  (let ((node
          (make-inference-queue-node
            :queue-number (incf *queue-number*)
            :queue-item query
            :queue-item-kind :query
            :queue-item-complexity (complexity (query-formula query))
            :queue-discounted-strength (query-strength query)
            :queue-degree-of-preference (query-preference query))))
    (setf (query-queue-node query) node)
    (setf *inference-queue* (ordered-insert node *inference-queue* #'i-preferred))))

; -------------------------------------- INTERESTS --------------------------------------

(defstruct (instantiated-premise (:print-function
				  (lambda (x stream depth)
                                    (declare (ignore depth))
                                    (princ "<instantiated-premise " stream) (princ (ip-number x) stream) (princ " for " stream)
                                    (princ (ip-reason x) stream)
                                    (princ ">" stream)))
				 (:conc-name ip-))
  (reason nil)
  (binding nil)  ;; cumulative binding prior to this premise
  (basis nil)
  (premise nil)
  (remaining-premises nil)  ;; premises left to be instantiated
  (instantiations nil)  ;; instantiations of hypernode-variables in previous premises
  (used-premise-variables nil)  ;; premise-variables bound in earlier premises
  (used-variables nil)  ;; conclusion-variables occurring in basis
  (derived-premises nil)  ;; instantiated-premises immediately following this one
  (d-node nil)
  (number 0)
  (clues nil)
  (initial?  nil))   ;; records whether the premise is the initial premise of the reason

(defstruct (interest-scheme (:include instantiated-premise)
                            (:print-function
			     (lambda (x stream depth)
                               (declare (ignore depth))
                               (princ "<<interest-scheme " stream) (princ (is-number x) stream) (princ " for " stream)
                               (princ (is-target-interest x) stream) (princ " by " stream) (princ (ip-reason x) stream) (princ ">>" stream)))
 			    (:conc-name is-))
  (target-interest nil)
  (supposition nil)
  (supposition-variables nil)
  (instance-function nil)
  (generating-node nil))

#| This finds the interest-scheme with is-number n. |#
(defun interest-scheme (n)
  (let ((is nil))
    (some #'(lambda (dn)
              (find-if #'(lambda (i)
                           (and (equal (is-number i) n)
                                (setf is i)))
                       (d-node-interest-schemes dn)))
          *discrimination-net*)
    is))

#| This finds the instantiated-premise with ip-number n. |#
(defun instantiated-premise (n)
  (let ((ip nil))
    (some #'(lambda (dn)
              (find-if #'(lambda (i)
                           (and (equal (ip-number i) n)
                                (setf ip i)))
                       (d-node-forwards-reasons dn)))
          *discrimination-net*)
    ip))

(defmacro is-derived-interest-schemes (is) `(is-derived-premises ,is))

(defstruct (interest-link (:print-function
			   (lambda (x stream depth)
                             (declare (ignore depth))
                             (princ "#<" stream) (princ "Link " stream)
                             (princ (link-number x) stream)
			     (let ((result (link-resultant-interest x)))
			       (when result
				 (cond ((interest-p result)
					(princ ": for  interest #" stream) (princ (interest-number result) stream))
				       ((query-p result)
					(princ ": for  query #" stream) (princ (query-number result) stream))
				       (t
					(princ ": for UNKNOWN" stream)))))
                             (princ " by " stream) (princ (link-rule x) stream)
                             (princ ">" stream)))
                          (:conc-name nil))   ; "An interest-graph-link"
  (link-number 0)
  (link-resultant-interest nil)
  (link-interest nil)
  (link-interest-formula nil)
  (link-interest-condition nil)
  (link-binding nil)
  (link-rule nil)
  (link-remaining-premises nil)
  (link-supporting-nodes nil)
  (link-instantiations nil)
  (link-supposition nil)
  (link-defeaters nil)
  (link-defeat-status nil)
  (link-strength 0)  ; maximum-degree-of-interest conveyed
  (link-generating-node nil)
  (link-discharged nil)
  (link-interest-match nil)
  (link-interest-reverse-match nil)
  (link-generating nil)
  (link-premise nil)
  (link-clues nil)
  )

(defun link (n)
  (find-if #'(lambda (node) (equal (link-number node) n)) *interest-links*))

(defun display-links ()
  (dolist (L *interest-links*) (princ L) (terpri)))

(defun display-link (L)
  (princ "INTEREST-LINK #") (princ (link-number L)) (terpri)
  (princ "  resultant-interest: ") (princ (link-resultant-interest L)) (terpri)
  (princ "  supporting-nodes: ") (princ (link-supporting-nodes L)) (terpri)
  (princ "  link-interest: ") (princ (link-interest L)) (terpri)
  (princ "  remaining-premises: ") (princ (link-remaining-premises L)) (terpri)
  (princ "  reason: ") (princ (link-rule L)) (terpri)
  (princ "  link-interest: ") (princ-set (link-interest L)) (terpri)
  )

(defun reverse-match (m)
  (if (eq m t) t
    (mapcar #'(lambda (x) (cons (cdr x) (mem1 x))) m)))

#| If p and q match one-one, this returns the match and its reverse-match. |#
(defun one-one-match (p q p-vars q-vars)
  (let* ((match (match p q p-vars))
         (match* (reverse-match match)))
    (when
      (and match
           (or (eq match t)
               (and
                 (subsetp (a-range match) q-vars)
                 (equal (match-sublis match* q) p))))
      (values match match*))))

#| This returns three values -- the i-list and the match and its reverse. |#
(defun i-list-for (formula i-vars)
  (multiple-value-bind (profile term-list) (formula-code formula)
    (let ((d-node (pursue-d-node-for profile *top-d-node*)))
      (when d-node
        (some
          #'(lambda (il)
              (multiple-value-bind
                (match match*)
                (one-one-match term-list (i-list-term-list il) i-vars (i-list-variables il))
                (when match
                  (return-from i-list-for (values il match match*)))))
          (d-node-i-lists d-node))))))

#| This returns two values -- the list of interests, and the match |#
(defun interests-for (formula i-vars)
  (multiple-value-bind
    (i-list match)
    (i-list-for formula i-vars)
    (if i-list (values (i-list-interests i-list) match))))

(defun in-interest (sequent)
  (let ((interests (interests-for (sequent-formula sequent) nil)))
    (when interests
      (some #'(lambda (interest) (null (interest-supposition interest)))
            interests))))

(defun adopt-ultimate-interest (query)
  (push query *ultimate-epistemic-interests*)
  (when (not (in-interest (list nil (query-formula query))))
    (queue-query-for-interest query)))

(defun unifier* (p q p-vars q-vars)
  ; (let ((intersection (intersection p-vars q-vars :test 'equal)))
  (let ((intersection (intersection p-vars q-vars)))
    (cond (intersection
            (let ((mr nil)
                  (p*-vars (setdifference p-vars intersection)))
              (setf mr
                    (mapcar
                      #'(lambda (x)
                          (if (interest-variable x)
                            (let ((x* (make-interest-variable)))
                              (push x* p*-vars)
                              (cons x x*))
                            (let ((x* (make-conclusion-variable)))
                              (push x* p*-vars)
                              (cons x x*))))
                      intersection))
              (let* ((mgu (mgu (sublis mr p) q (append p*-vars q-vars)))
                     (rm (reverse-match mr)))
                (list
                  (parallelize-match
                    (append rm (merge-sequential-matches mgu mr)) p-vars)
                  (parallelize-match (merge-sequential-matches rm mgu) q-vars)))))
          (t (let ((mgu (mgu p q (append p-vars q-vars))))
               (list
                 (parallelize-match mgu p-vars)
                 (parallelize-match mgu q-vars)))))))

#| If p and q have free variables in common, they must be rewritten before we can
apply the unification algorithm.  The following produces a pair of substitutions
(m1 m2) such that applying m1 to p and m2 to q unifies them.  m1 and m2 are
parallel matches to be applied by match-sublis.  The p-vars and q-vars are the
hypernode-variables. |#
(defun unifier (p q p-vars q-vars)
  (cond ((and (null p-vars) (null q-vars))
         ;  (if (equal p q) (list t t)))
         (if (or (equal p q) (notational-variant p q)) (list t t)))
        (t (catch 'unifier
                  (let ((terms (variable-correspondence p q p-vars q-vars (list nil nil nil))))
                    (unifier* (mem1 terms) (mem2 terms) p-vars q-vars))))))

#| This finds the interest with interest-number n. |#
(defun interest (n)
  (find-if #'(lambda (i) (eql (interest-number i) n)) *interests*))

(defun ni-unifier (n m)
  (unifier (hypernode-formula (hypernode n)) (interest-formula (interest m))
           (hypernode-variables (hypernode n)) (interest-variables (interest m))))

(defun hypernode-unifier (n m)
  (unifier (hypernode-formula (hypernode n)) (hypernode-formula (hypernode m))
           (hypernode-variables (hypernode n)) (hypernode-variables (hypernode m))))

(defun reductio-unifier (n m)
  (unifier (neg (hypernode-formula (hypernode n))) (hypernode-formula (hypernode m))
           (hypernode-variables (hypernode n)) (hypernode-variables (hypernode m))))

(defun permutations (X)
  (cond ((null X) (list nil))
        ((null (cdr X)) (list X))
        (t (let ((X1 nil) (X2 X) (permutations nil) (done nil))
             (loop
               (let ((y (car X2)))
                 (setf X2 (cdr X2))
                 (when (not (mem y done))
                   (push y done)
                   (dolist (Z (mapcar #'(lambda (p) (cons y p)) (permutations (append X1 X2))))
                     (push Z permutations)))
                 (when (null X2) (return permutations))
                 (setf X1 (cons y X1))))))))

#| (Set-unifier X Y c-vars i-vars) returns the list of unifiers unifying X into Y. |#
;(defun set-unifier (X Y x-vars y-vars)
;    (let ((length-x (length X))
;            (length-y (length Y)))
;       (when (<= length-x length-y)
;            (let ((unifiers nil)
;                    (n (- length-y length-x)))
;               (dolist (Y* (permutations Y))
;                   (let ((unifier (unifier X (nthcdr n Y*) x-vars y-vars)))
;                      (when unifier (pushnew unifier unifiers :test 'equal))))
;               unifiers))))

#| This produces a match equivalent to applying m1 first and then m2. |#
(defun merge-matches* (m1 m2)
  (cond ((null m1) m2)
        ((null m2) m1)
        ((eq m1 t) m2)
        ((eq m2 t) m1)
        (t
          (let* ((m1* (mapcar #'(lambda (x) (cons (car x) (match-sublis m2 (cdr x)))) m1))
                 (domain (domain m1*))
                 (m2* (subset #'(lambda (x) (not (member (car x) domain))) m2)))
            (append m1* m2*)))))

(defun set-mgu (X Y vars)
  (cond (X
          (let ((p (mem1 X))
                (unifiers nil))
            (dolist (q Y)
              (let ((mgu (catch 'unifier (mgu p q vars))))
                (when mgu (pushnew mgu unifiers :test 'equal))))
            (when unifiers
              (cond ((cdr X)
                     (let ((new-unifiers nil))
                       (dolist (unifier unifiers)
                         (let ((unifiers*
                                 (set-mgu (match-sublis unifier (cdr X))
                                          (match-sublis unifier Y)
                                          vars)))
                           (dolist (U unifiers*)
                             (push (merge-matches* unifier U) new-unifiers))))
                       new-unifiers))
                    (t unifiers)))))
        (t (list t))))

(defun set-unifier (X Y X-vars Y-vars)
  ; (setf x0 x y0 y xv x-vars yv y-vars)
  (let ((intersection (intersection X-vars Y-vars)))
    (cond (intersection
            (let ((mr nil)
                  (X*-vars (setdifference X-vars intersection)))
              (setf mr
                    (mapcar
                      #'(lambda (x)
                          (if (interest-variable x)
                            (let ((x* (make-interest-variable)))
                              (push x* X*-vars)
                              (cons x x*))
                            (let ((x* (make-conclusion-variable)))
                              (push x* X*-vars)
                              (cons x x*))))
                      intersection))
              (let* ((mgus (set-mgu (sublis mr X) Y (append X*-vars Y-vars)))
                     (rm (reverse-match mr)))
                (mapcar
                  #'(lambda (mgu)
                      (list
                        (parallelize-match
                          (append rm (merge-sequential-matches mgu mr)) X-vars)
                        (parallelize-match (merge-sequential-matches rm mgu) Y-vars)))
                  mgus))))
          (t (let ((mgus (set-mgu X Y (append X-vars Y-vars))))
               (mapcar
                 #'(lambda (mgu)
                     (list
                       (parallelize-match mgu X-vars)
                       (parallelize-match mgu Y-vars)))
                 mgus))))))

#|
(set-unifier '((F c) (G y)) '((G a) (H c) (G b) (F z)) '(x y) '(z))
yields ((((y . a)) ((z . c))) (((y . b)) ((z . c))))
|#

#| This checks that interest-variables in vars1 and vars2 do not instantiate
each other.
(defun constrained-assignment (unifier vars1 vars2)
  (let ((u1 (mem1 unifier)))
    (or (eq u1 t)
        (not (some
               #'(lambda (v)
                   (some #'(lambda (w) (occur w (e-assoc v u1))) vars2))
               vars1))))
  (let ((u2 (mem2 unifier)))
    (or (eq u2 t)
        (not (some
               #'(lambda (v)
                   (some #'(lambda (w) (occur w (e-assoc v u2))) vars1))
               vars2)))))
|#

#| This checks that interest-variables in vars1 and vars2 are not instantiated
by terms containing those same variables. |#
(defun constrained-assignment (unifier vars1 vars2)
  (let ((u1 (mem1 unifier)))
    (or (eq u1 t)
        (not (some #'(lambda (v) (occur v (e-assoc v u1))) vars1))))
  (let ((u2 (mem2 unifier)))
    (or (eq u2 t)
        (not (some #'(lambda (v) (occur v (e-assoc v u2))) vars2)))))

#| c-variables is the list of hypernode-variables. |#
(defun matching-i-lists-for (term-list c-variables d-node)
  (let ((i-lists nil))
    (dolist (il (d-node-i-lists d-node))
      (let ((unifier (unifier term-list (i-list-term-list il) c-variables (i-list-variables il))))
        (if unifier (push (list il unifier) i-lists))))
    i-lists))

#| c-variables is the list of hypernode-variables. |#
(defun matching-c-lists-for (term-list i-variables d-node)
  (let ((c-lists nil))
    (dolist (cl (d-node-c-lists d-node))
      (let ((unifier (unifier  (c-list-term-list cl) term-list (c-list-variables cl) i-variables)))
        (if unifier (push (list cl unifier) c-lists))))
    c-lists))

(defun appropriate-for-reductio-supposition (formula)
  (and
    (not (conjunctionp formula))
    (not (conditionalp formula))
    (not (biconditionalp formula))
    (not (disjunctionp formula))
    (not (u-genp formula))
    (not (undercutterp formula))
    (or (not (negationp formula))
        (atomic-formula (mem2 formula)))))

#| Test is the final member of the formula-profile for the hypernode-formula. |#
(defun store-interest-at-new-d-node (interest term-list d-node test)
  ; (when (eq interest (interest 7)) (setf i interest tl term-list d d-node ts test) (break))
  ;; (step (store-interest-at-new-node i tl d ts))
  (let* ((i-variables (interest-variables interest))
         (formula (interest-formula interest))
         (dn (make-d-node
               :d-node-number (incf *d-node-number*)
               :d-node-description (cons test (d-node-description d-node))
               :d-node-parent d-node))
         (i-list (make-i-list
                   :i-list-formula formula
                   :i-list-interests (list interest)
                   :i-list-reductio-trigger
                   (appropriate-for-reductio-supposition formula)
                   :i-list-variables i-variables
                   :i-list-term-list term-list
                   :i-list-d-node dn
                   )))
    (push dn *discrimination-net*)
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (setf (d-node-i-lists dn) (list i-list))
    (setf (interest-i-list interest) i-list)))

(defun index-interest-at-new-nodes (interest term-list d-node profile test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (push dn *discrimination-net*)
    (let ((desc (cdr profile)))
      (cond (desc (index-interest-at-new-nodes interest term-list dn desc (car profile)))
            (t (store-interest-at-new-d-node interest term-list dn (car profile)))))))

(defun store-interest-at-d-node (interest term-list dn)
  ; (when (eq interest (interest 11)) (setf i interest tl term-list d dn) (break))
  ;; (step (store-interest-at-d-node i tl d))
  (let* ((formula (interest-formula interest))
         (i-variables (interest-variables interest))
         (i-list (fetch-i-list-for term-list dn)))
    (cond (i-list
            (push interest (i-list-interests i-list))
            (let ((reductio-sup (i-list-reductio-supposition i-list)))
              (when reductio-sup
                (push interest  (hypernode-generating-interests reductio-sup))
                (push reductio-sup (interest-generated-suppositions interest)))))
          (t (let ((c-lists (matching-c-lists-for term-list i-variables dn)))
               (setf i-list (make-i-list
                              :i-list-formula formula
                              :i-list-corresponding-c-lists c-lists
                              :i-list-interests (list interest)
                              :i-list-reductio-trigger
                              (appropriate-for-reductio-supposition formula)
                              :i-list-variables i-variables
                              :i-list-term-list term-list
                              :i-list-d-node dn
                              ))
               (push i-list (d-node-i-lists dn))
               (dolist (cl c-lists)
                 (push (cons i-list (cdr cl)) (c-list-corresponding-i-lists (mem1 cl)))))))
    (setf (interest-i-list interest) i-list)))

#| (descrimination-tests d-node) is an a-list of pairs (test . dn), where test has the form of the
car of a formula-code, and dn is a d-node. |#
(defun index-interest (interest profile term-list d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node)))
        (new-profile (cdr profile)))
    (cond (dn
            (if new-profile (index-interest interest new-profile term-list dn)
              (store-interest-at-d-node interest term-list dn)))
          (new-profile
            (index-interest-at-new-nodes interest term-list d-node new-profile (car profile)))
          (t (store-interest-at-new-d-node
               interest term-list d-node (car profile))))))

(defun store-interest (interest &optional i-list)
  (push interest *interests*)
  (cond (i-list
          (push interest (i-list-interests i-list))
          (let ((reductio-sup (i-list-reductio-supposition i-list)))
            (when reductio-sup
              (push interest  (hypernode-generating-interests reductio-sup))
              (push reductio-sup (interest-generated-suppositions interest))))
          (setf (interest-i-list interest) i-list))
        (t
          (multiple-value-bind (profile term-list) (formula-code (interest-formula interest))
            (index-interest interest profile term-list *top-d-node*)))))

(defun pursue-i-lists-for (formula profile term-list variables d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node))))
    (when dn
      (let ((new-profile (cdr profile)))
        (cond
          (new-profile (pursue-i-lists-for formula new-profile term-list variables dn))
          (t (matching-i-lists-for term-list variables dn)))))))

(defun find-matching-i-lists-for (formula variables)
  (multiple-value-bind (profile term-list) (formula-code formula)
    (pursue-i-lists-for formula profile term-list variables *top-d-node*)))

(defun store-interest-with-c-lists (interest c-lists)
  ;  (when (eq (interest-number interest) 25) (setf i interest cl c-lists) (break))
  ;; (step (store-interest-with-c-lists i cl))
  (multiple-value-bind (profile term-list) (formula-code (interest-formula interest))
    (declare (ignore profile))
    (cond
      (c-lists
        (push interest *interests*)
        (let* ((formula (interest-formula interest))
               (dn (c-list-d-node (caar c-lists)))
               (i-list (fetch-i-list-for term-list dn))
               (i-variables (interest-variables interest)))
          (cond (i-list
                  (push interest (i-list-interests i-list))
                  (let ((reductio-sup (i-list-reductio-supposition i-list)))
                    (when reductio-sup
                      (push interest  (hypernode-generating-interests reductio-sup))
                      (push reductio-sup (interest-generated-suppositions interest)))))
                (t (setf i-list (make-i-list
                                  :i-list-formula formula
                                  :i-list-corresponding-c-lists c-lists
                                  :i-list-interests (list interest)
                                  :i-list-reductio-trigger
                                  (appropriate-for-reductio-supposition formula)
                                  :i-list-variables i-variables
                                  :i-list-term-list term-list
                                  :i-list-d-node dn
                                  ))
                   (push i-list (d-node-i-lists dn))
                   (dolist (cl c-lists)
                     (push (cons i-list (cdr cl)) (c-list-corresponding-i-lists (mem1 cl))))))
          (setf (interest-i-list interest) i-list)))
      (t (store-interest interest)))))

(defun appropriate-for-reductio-interest (formula)
  (and
    (not (conjunctionp formula))
    (not (disjunctionp formula))   ;; if we use disj-simp
    (not (biconditionalp formula))
    (or (not (conditionalp formula))                                         ;; these assume:
        (and (not (conjunctionp (antecedent formula)))       ;; exportation
             (not (disjunctionp (antecedent formula)))        ;; disj-antecedent-simp
             (not (conditionalp (antecedent formula)))))     ;; cond-antecedent-simp
    (not (u-genp formula))
    (not (e-genp formula))
    (or (not (negationp formula))
        (atomic-formula (negand formula))
        (undercutterp (negand formula)))))

(defun appropriate-for-contradictors (formula)
  (and
    (not (conjunctionp formula))
    (not (disjunctionp formula))   ;; if we use disj-simp
    (not (biconditionalp formula))
    (not (u-genp formula))
    (not (e-genp formula))
    (or (not (negationp formula))
        (atomic-formula (mem2 formula))
        (undercutterp (mem2 formula))
        (conditionalp (mem2 formula)))))

(defun pursue-c-lists-for (formula profile term-list variables d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node))))
    (when dn
      (let ((new-profile (cdr profile)))
        (cond
          (new-profile (pursue-c-lists-for formula new-profile term-list variables dn))
          (t (matching-c-lists-for term-list variables dn)))))))

(defun find-matching-c-lists-for (formula variables)
  (multiple-value-bind (profile term-list) (formula-code formula)
    (pursue-c-lists-for formula profile term-list variables *top-d-node*)))

#| Test is the final member of the formula-profile for the hypernode-formula. |#
(defun store-hypernode-at-new-d-node (node term-list d-node test)
  (let* ((c-variables (hypernode-variables node))
         (dn (make-d-node
               :d-node-number (incf *d-node-number*)
               :d-node-description (cons test (d-node-description d-node))
               :d-node-parent d-node))
         (formula (hypernode-formula node))
         (c-list (make-c-list
                   :c-list-formula formula
                   :c-list-nodes (list node)
                   :c-list-reductio-interests
                   (appropriate-for-reductio-interest formula)
                   :c-list-variables c-variables
                   :c-list-term-list term-list
                   :c-list-d-node dn
                   )))
    (push dn *discrimination-net*)
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (setf (d-node-c-lists dn) (list c-list))
    (when
      (appropriate-for-contradictors formula)
      (setf (c-list-contradictors c-list)
            (find-matching-c-lists-for (neg formula) (c-list-variables c-list)))
      (dolist (cl (c-list-contradictors c-list))
        (push (list c-list (reverse (mem2 cl)))
              (c-list-contradictors (mem1 cl)))))
    (setf (hypernode-c-list node) c-list)))

(defun index-hypernode-at-new-nodes (node term-list d-node profile test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (push dn *discrimination-net*)
    (let ((desc (cdr profile)))
      (cond (desc (index-hypernode-at-new-nodes node term-list dn desc (car profile)))
            (t (store-hypernode-at-new-d-node node term-list dn (car profile)))))))

(defun fetch-c-list-for (formula d-node)
  (find-if #'(lambda (cl) (notational-variant formula (c-list-formula cl)))
           (d-node-c-lists d-node)))

(defun is-inference (c &rest r) (declare (ignore r)) (eq (hypernode-kind c) :inference))

(defun is-desire (c &rest r) (declare (ignore r)) (eq (hypernode-kind c) :desire))

(defun is-percept (c &rest r) (declare (ignore r)) (eq (hypernode-kind c) :percept))

(setf is-inference #'is-inference)

(setf is-desire #'is-desire)

(setf is-percept #'is-percept)

(defun store-hypernode-at-d-node (node term-list dn)
  (let* ((formula (hypernode-formula node))
         (c-list (fetch-c-list-for formula dn))
         (c-variables (hypernode-variables node)))
    (cond (c-list
            (if (is-inference node) (push node (c-list-nodes c-list))))
          (t (let ((i-lists (matching-i-lists-for term-list c-variables dn)))
               (setf c-list (make-c-list
                              :c-list-formula formula
                              :c-list-corresponding-i-lists i-lists
                              :c-list-nodes (if (is-inference node) (list node))
                              :c-list-reductio-interests
                              (appropriate-for-reductio-interest formula)
                              :c-list-variables c-variables
                              :c-list-term-list term-list
                              :c-list-d-node dn
                              ))
               (push c-list (d-node-c-lists dn))
               (dolist (il i-lists)
                 (push (cons c-list (cdr il)) (i-list-corresponding-c-lists (mem1 il)))))
             (when
               (appropriate-for-contradictors formula)
               (setf (c-list-contradictors c-list)
                     (find-matching-c-lists-for (neg formula) (c-list-variables c-list)))
               (dolist (cl (c-list-contradictors c-list))
                 (push (list c-list (reverse (mem2 cl)))
                       (c-list-contradictors (mem1 cl)))))))
    (setf (hypernode-c-list node) c-list)))

#| (descrimination-tests d-node) is an a-list of pairs (test . dn), where test has the form of the
car of a formula-code, and dn is a d-node. |#
(defun index-hypernode (node profile term-list d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node)))
        (new-profile (cdr profile)))
    (cond (dn
            (if new-profile (index-hypernode node new-profile term-list dn)
              (store-hypernode-at-d-node node term-list dn)))
          (new-profile
            (index-hypernode-at-new-nodes node term-list d-node new-profile (car profile)))
          (t
            (store-hypernode-at-new-d-node
              node term-list d-node (car profile))))))

(defun store-hypernode (node formula)
  ; (when (eql (hypernode-number node) 14) (setf n node f formula) (break))
  ;; (step (store-hypernode n f))
  (multiple-value-bind (profile term-list) (formula-code formula)
    (index-hypernode node profile term-list *top-d-node*)))

(defun c-list-for (formula)
  (let ((d-node (d-node-for formula)))
    (if d-node
      (fetch-c-list-for formula d-node))))

(defun nodes-for (formula)
  (let ((c-list (c-list-for formula)))
    (if c-list (c-list-nodes c-list))))

(defun pursue-c-list-for (formula profile d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node))))
    (when dn
      (let ((new-profile (cdr profile)))
        (cond
          (new-profile (pursue-c-list-for formula new-profile dn))
          (t (fetch-c-list-for formula dn)))))))

(defun store-hypernode-with-c-list (node formula c-list)
  ; (when (equal *hypernode-number* 31) (setf c node f formula cl c-list) (break))
  ;; (step (store-hypernode-with-c-list c f cl))
  (cond (c-list
          (push node (c-list-nodes c-list))
          (setf (hypernode-c-list node) c-list))
        (t (store-hypernode node formula))))

(defun cancelled-c-list-for (formula)
  (e-assoc formula *cancelled-c-lists*))

(defun store-processed-node (node)
  (setf (hypernode-processed? node) T)
  (push node (c-list-processed-nodes (hypernode-c-list node))))

#| (? formula), where formula can contain variables of the form "?x",  returns a list of all
known conclusions matching the formula. |#
(defun ? (formula)
  (when (stringp formula) (setf formula (reform formula)))
  (let* ((d-node (d-node-for formula))
         (nodes (search-d-nodes formula d-node)))
    (cond (nodes
            (terpri)
            (princ "The following answers are known for the query (? ") (prinp formula) (princ "):") (terpri)
            (princ "------------------------------------------------------------------------------------------------------------------------------------------------------------")
            (terpri)
            (dolist (node nodes)
              (princ "    ") (princ (hypernode-formula node)) (princ "    by node #")
              (princ (hypernode-number node)) (terpri))
            (terpri))
          (t
            (terpri) (princ "No answers are known for the query (? ") (prinp formula) (princ ").") (terpri)
            (princ "------------------------------------------------------------------------------------------------------------------------------------------------------------")
            (terpri)
            (terpri)))
    nodes))

#| This returns the degree of interest for either an interest or a query. |#
(defun degree-of-interest* (n)
  (if (interest-p n) (interest-degree-of-interest n) (query-strength n)))

(defun interest-sequent* (n)
  (if (interest-p n) (interest-sequent n) (list nil (query-formula n))))

(defun clue? (premise)
  (cond ((forwards-premise-p premise) (fp-clue? premise))
        ((backwards-premise-p premise) (bp-clue? premise))))

(defun construct-forwards-premise (P C V &optional B)
  (make-forwards-premise
    :formula P
    :condition C
    :binding-function B
    :variables V
    :instantiator (reason-instantiator P V)))

(defmacro cfp (P V &optional B) `(construct-forwards-premise ,P nil ,V ,B))

(defun construct-backwards-premise (P C1 C2 V)
  (let ((V* (subset #'(lambda (x) (occur* x P)) V)))
    (make-backwards-premise
      :formula P
      :condition1 C1
      :condition2 C2
      :instantiator (reason-instantiator P V*))))

(defmacro cbp (P C1 C2 V) `(construct-backwards-premise ,P ,C1 ,C2 ,V))

(defstruct (forwards-reason (:include reason)
			    (:print-function
			     (lambda (x stream depth)
			       (declare (ignore depth)) (princ (reason-name x) stream)))
                            (:conc-name nil)))

; --------------------------------------  BACKWARDS-REASONS --------------------------------------

(defstruct (backwards-reason (:include reason)
			     (:print-function
			      (lambda (x stream depth)
				(declare (ignore depth)) (princ (reason-name x) stream)))
                             (:conc-name nil))
  (b-reason-condition nil)  ;; this is a predicate applied to the binding
  (b-reason-discharge nil)
  (b-reason-length 1)  ;; this is the number of backwards-premises
  (b-reason-conclusions-binding-function nil)
  (b-reason-conclusion-variables nil)
  (b-reason-immediate nil))

#| The list of instantiated-premises for a forwards-reason. |#
(defun reason-ips (reason)
  (let ((ips nil))
    (dolist (dn *discrimination-net*)
      (dolist (ip (d-node-forwards-reasons dn))
        (when (equal (ip-reason ip) reason) (push ip ips))))
    ips))

#| The list of interest-schemes for a backwards-reason. |#
(defun reason-iss (reason)
  (let ((iss nil))
    (dolist (dn *discrimination-net*)
      (dolist (is (d-node-interest-schemes dn))
        (when (equal (ip-reason is) reason) (push is iss))))
    iss))

(defun display-d-node (dn depth test)
  ; (setf d dn de depth te test)
  ;; (step (display-d-node d de te))
  (let ((pp *print-pretty*))
    (setf *print-pretty* nil)
    (line-indent depth)
    (princ "--")
    (if test (prinp-test test) (princ dn))
    (princ "   ")
    (terpri)
    (dolist (cl (d-node-c-lists dn)) (line-indent depth) (princ "       ") (princ cl) (terpri))
    (dolist (il (d-node-i-lists dn)) (line-indent depth) (princ "       ") (princ il) (terpri))
    (dolist (ip (d-node-forwards-reasons dn))
      (line-indent depth)
      (cond ((ip-basis ip) (princ "       instantiated-premise ") (princ (ip-number ip)) (princ " for "))
            (t (princ "       first premise for ")))
      (princ (ip-reason ip))
      (princ ": ")
      (let ((p (match-sublis (ip-binding ip) (fp-formula (ip-premise ip)))))
        (if (and (negationp p) (negationp (negand p))) (setf p (negand (negand p))))
        (prinp p))
      (terpri))
    (dolist (br (d-node-backwards-reasons dn)) (line-indent depth) (princ "       conclusion for ")
      (princ br) (terpri))
    (dolist (br (d-node-degenerate-backwards-reasons dn)) (line-indent depth) (princ "       conclusion for ")
      (princ br) (terpri))
    (dolist (is (d-node-interest-schemes dn))
      (line-indent depth)
      (princ "       interest-scheme ") (princ (is-number is)) (princ " for interest ")
      (princ (interest-number (is-target-interest is)))
      (princ " by ")
      (princ (is-reason is))
      (princ ": ")
      (let ((p (match-sublis (is-binding is) (fp-formula (is-premise is)))))
        (if (and (negationp p) (negationp (negand p))) (setf p (negand (negand p))))
        (prinp p))
      (terpri))
    (setf *print-pretty* pp)))

(defun display-discrimination-node (d-node listees depth last? nodes &optional test)
  (when (member d-node nodes)
    (when (null depth)
      (setf depth 0) (setf listees nil))
    (cond ((or (mem d-node listees) (mem d-node *callees*))
           (line-indent depth)
           (when (not (mem depth *line-columns*)) (princ "|"))
           (princ "--") (princ d-node) (princ " .....") (terpri)
           (setf *blank-line* nil)
           (cond (last? (pull depth *line-columns*))
                 (t (pushnew depth *line-columns* :test 'eql))))
          (t
            (let* ((DC (d-node-discrimination-tests d-node))
                   (number (length (d-node-discrimination-tests d-node)))
                   (number* (round (/ number 2)))
                   (draw-line?
                     (or (mem d-node listees)
                         (mem d-node *callees*)
                         (some #'(lambda (C) (not (mem c listees))) (d-node-discrimination-tests d-node)))))
              (pushnew d-node listees :test 'equal)
              (push d-node *callees*)
              (when (and (not *blank-line*) (> number* 0))
                (line-indent depth) (terpri) (setf *blank-line* t))
              (dotimes (n number*)
                (let ((test (mem1 DC)))
                  (cond
                    ((zerop n)
                     (display-discrimination-node (cdr test) listees (1+ depth) nil nodes test))
                    ((cdr DC) (display-discrimination-node (cdr test) listees (1+ depth) nil nodes test))
                    (t (display-discrimination-node (cdr test) listees (1+ depth) t nodes test))))
                (setf DC (cdr DC)))
              (pushnew depth *line-columns* :test 'eql)
              (display-d-node d-node depth test)
              (setf *blank-line* nil)
              (when last? (pull depth *line-columns*))
              (when (> number 0) (pushnew (1+ depth) *line-columns* :test 'eql))
              (dolist (test DC)
                (cond
                  ((cdr DC)
                   (display-discrimination-node (cdr test) listees (1+ depth) nil nodes test))
                  (t (display-discrimination-node (cdr test) listees (1+ depth) t nodes test)))
                (setf DC (cdr DC)))
              (when
                (and (not *blank-line*) draw-line?)
                (line-indent depth) (terpri) (setf *blank-line* t))
              )))))

(defun display-discrimination-net (&optional (nodes *discrimination-net*))
  (setf *callees* nil)
  (setf *blank-line* nil)
  (setf *line-columns* nil)
  (display-discrimination-node *top-d-node* nil 0 t nodes)
  nil)

(defun ddn (&optional (nodes *discrimination-net*)) (display-discrimination-net nodes))

(defun d-node-ancestors (dn)
  (let ((pn (d-node-parent dn)))
    (when pn (cons pn (d-node-ancestors pn)))))

(defun d-node-descendants (dn)
  (when (d-node-discrimination-tests dn)
    (let ((nodes (a-range (d-node-discrimination-tests dn))))
      (append nodes (unionmapcar #'d-node-descendants nodes)))))

#| Display the part of the discrimination-net that contains d-node number n. |#
(defun show-d-node (n)
  (let* ((dn (if (numberp n) (d-node n) n))
         (nodes (cons dn (append (d-node-ancestors dn) (d-node-descendants dn)))))
    (display-discrimination-net nodes)))

(defun show-interest (n)
  (let* ((in (if (numberp n) (interest n) n))
         (dn (i-list-d-node (interest-i-list in)))
         (nodes (cons dn (append (d-node-ancestors dn) (d-node-descendants dn)))))
    (display-discrimination-net nodes)))

(defun show-hypernode (n)
  (let* ((node (if (numberp n) (hypernode n) n))
         (dn (c-list-d-node (hypernode-c-list node)))
         (nodes (cons dn (append (d-node-ancestors dn) (d-node-descendants dn)))))
    (display-discrimination-net nodes)))

#| This displays all d-nodes directly relevant to the reason. |#
(defun show-reason (reason)
  (let ((nodes nil))
    (cond ((forwards-reason-p reason)
           (dolist (dn *discrimination-net*)
             (when (some #'(lambda (ip) (equal (ip-reason ip) reason)) (d-node-forwards-reasons dn))
               (push dn nodes))))
          ((backwards-reason-p reason)
           (dolist (dn *discrimination-net*)
             (when
               (or (member reason (d-node-backwards-reasons dn))
                   (member reason (d-node-degenerate-backwards-reasons dn))
                   (some #'(lambda (is) (equal (is-reason is) reason)) (d-node-interest-schemes dn)))
               (push dn nodes)))))
    (setf nodes
          (unionmapcar+
            #'(lambda (dn) (cons dn (append (d-node-ancestors dn) (d-node-descendants dn))))
            nodes))
    (display-discrimination-net nodes)))

(defun display-hypernode (n)
  (if (numberp n) (setf n (hypernode n)))
  (princ "  # ") (princ (hypernode-number n)) (princ "   ")
  (when (not (equal (hypernode-kind n) :inference)) (princ (hypernode-kind n)) (princ "         "))
  (prinp (hypernode-formula n))
  (when (hypernode-supposition n)
    (princ "    supposition: ") (set-prinp (hypernode-supposition n)))
  (if (zerop (hypernode-degree-of-justification n)) (princ "                  DEFEATED"))
  (terpri)
  (cond ((hypernode-justification n) (princ "  ") (princ (hypernode-justification n)) (terpri))
        ((hypernode-hyperlinks n)
         (princ "  Inferred by:") (terpri)
         (dolist (L* (hypernode-hyperlinks n))
           (princ "                hyperlink #") (princ (hyperlink-number L*))
           (princ " from ") (princ-set (mapcar #'hypernode-number (hyperlink-basis L*)))
           (princ " by ") (princ (hyperlink-rule L*))
           (when (hyperlink-defeaters L*)
             (princ "  defeaters: ")
             (princ-set (mapcar #'hypernode-number
                                (mapcar #'hyper-defeat-link-root (hyperlink-defeaters L*)))))
           ; (when (defeating-assignment-trees L*) (princ "   DEFEATED"))
           (terpri))))
  (princ "  degree-of-justification: ") (princ (hypernode-degree-of-justification n)) (terpri)
  (cond ((deductive-node n)
         (princ "  This node encodes a deductive argument.") (terpri)))
  (when (hypernode-supported-hyper-defeat-links n)
    (princ "  defeatees: ")
    (princ "{ ")
    (let ((L (hyper-defeat-link-target (car (hypernode-supported-hyper-defeat-links n)))))
      (princ "link ")
      (princ (hyperlink-number L)) (princ " for node ")
      (princ (hypernode-number (hyperlink-target L))))
    (dolist (L (cdr (hypernode-supported-hyper-defeat-links n)))
      (setf L (hyper-defeat-link-target L))
      (princ " , ")
      (princ "link ")
      (princ (hyperlink-number L)) (princ " for node ")
      (princ (hypernode-number (hyperlink-target L))))
    (princ " }")
    (terpri)))

(defun display-hyperlink (L)
  (if (numberp L) (setf L (hyperlink L)))
  (let ((n (hyperlink-target L)))
    (princ "  # ") (princ (hypernode-number n)) (princ "   ")
    (when (not (equal (hypernode-kind n) :inference)) (princ (hypernode-kind n)) (princ "         "))
    (prinp (hypernode-formula n))
    (when (hypernode-supposition n)
      (princ "    supposition: ") (set-prinp (hypernode-supposition n)))
    (terpri)
    (princ "  Inferred by hyperlink #") (princ (hyperlink-number L))
    (princ " from ") (princ-set (mapcar #'hypernode-number (hyperlink-basis L)))
    (princ " by ") (princ (hyperlink-rule L))
    (when (hyperlink-clues L)
      (princ " with clues ")
      (princ-set (mapcar #'hypernode-number (hyperlink-clues L))))
    (when (hyperlink-defeaters L)
      (princ "  defeaters: ") (princ-set
                                (mapcar #'hypernode-number
                                        (mapcar #'hyper-defeat-link-root (hyperlink-defeaters L)))))
    (terpri)
    (when (and (reason-p (hyperlink-rule L)) (reason-description (hyperlink-rule L)))
      (princ "  ") (princ (reason-description (hyperlink-rule L))) (terpri))
    (let ((links (remove L (hypernode-hyperlinks n))))
      (when links
        (princ "  Previously inferred by:") (terpri)
        (dolist (L* links)
          (princ "                hyperlink #") (princ (hyperlink-number L*))
          (princ " from ") (princ-set (mapcar #'hypernode-number (hyperlink-basis L*)))
          (princ " by ") (princ (hyperlink-rule L*))
          (when (hyperlink-clues L*)
            (princ " with clues ")
            (princ-set (mapcar #'hypernode-number (hyperlink-clues L*))))
          (when (hyperlink-defeaters L*)
            (princ "  defeaters: ")
            (princ-set (mapcar #'hypernode-number
                               (mapcar #'hyper-defeat-link-root (hyperlink-defeaters L*)))))
          (terpri))))
    ; (princ "  nearest-defeasible-ancestors: ")
    ; (princ (hypernode-nearest-defeasible-ancestors n)) (terpri)
    (when (hypernode-supported-hyper-defeat-links n)
      (princ "  defeatees: ")
      (princ "{ ")
      (let ((L (hyper-defeat-link-target (car (hypernode-supported-hyper-defeat-links n)))))
        (princ "link ")
        (princ (hyperlink-number L)) (princ " for node ")
        (princ (hypernode-number (hyperlink-target L))))
      (dolist (L (cdr (hypernode-supported-hyper-defeat-links n)))
        (setf L (hyper-defeat-link-target L))
        (princ " , ")
        (princ "link ")
        (princ (hyperlink-number L)) (princ " for node ")
        (princ (hypernode-number (hyperlink-target L))))
      (princ " }") (terpri)))
  (terpri))

(defun make-oscar-window () nil)
(defun draw-n (x y z) (declare (ignore x y z)))
(defun flash-nodes (x y z w) (declare (ignore x y z w)))
(defun hypernode-position (x y) (declare (ignore x y)))
(defun interest-position (x y) (declare (ignore x y)))
(defun hypernode-color (x y) (declare (ignore x y)))
(defun draw-just-node (x y z w) (declare (ignore x y z w)))
(defun draw-just-undefeated-node (x y z) (declare (ignore x y z)))
(defun draw-just-defeated-node (x y z) (declare (ignore x y z)))
(defun pause-graphics ())
(defun draw-i (x y) (declare (ignore x y)))
(defun draw-interest (x y z) (declare (ignore x y z)))
(defun speak-text (x) (declare (ignore x)))
(defun pranc-to-string (x) (declare (ignore x)))
(defun monitor-assignment-tree (x) (declare (ignore x)))

(defun display-unsupported-hypernode (n )
  (if (numberp n) (setf n (hypernode n)))
  (terpri) (princ "  # ") (princ (hypernode-number n)) (princ "   ")
  (when (not (equal (hypernode-kind n) :inference)) (princ (hypernode-kind n)) (princ "         "))
  (prinp (hypernode-formula n))
  (when (hypernode-supposition n)
    (princ "    supposition: ") (set-prinp (hypernode-supposition n)))
  (if (zerop (hypernode-degree-of-justification n)) (princ "                  DEFEATED"))
  (terpri)
  (when (keywordp (hypernode-justification n)) (princ "  ") (princ (hypernode-justification n)) (terpri))
  ; (princ "  degree-of-justification: ")
  ; (princ (current-degree-of-justification n)) (terpri)
  (when (and *display?* *graphics-on*)
    (when *graphics-pause* (pause-graphics))
    (draw-n n *og* *nodes-displayed*)
    (push n *nodes-displayed*)))

(defun display-discharge-condition (interest link)
  (let ((binding
          (mapcar
            #'(lambda (x) (cons (car x) (if (and (cdr x) (listp (cdr x))) (list 'quote (cdr x)) (cdr x))))
            (link-binding link))))
    (print-pretty  (sublis binding (interest-text-discharge-condition interest)))))

(defun display-interest (interest)
  (if (numberp interest) (setf interest (interest interest)))
  (princ "                                        # ") (princ (interest-number interest)) (princ "  ")
  (when (interest-deductive interest) (princ "deductive "))
  (when (interest-reductio interest) (princ "reductio "))
  (princ "interest:")
  (terpri)
  (princ "                                           ") (prinp  (interest-formula interest))
  (when (interest-supposition interest)
    (princ "    supposition: ")
    (set-prinp (interest-supposition interest)))
  (terpri)
  (when
    (some #'(lambda (L) (query-p (link-resultant-interest L)))
          (interest-right-links interest))
    (princ "                                        This is of ultimate interest") (terpri))
  (let ((L (lastmember (interest-right-links interest))))
    (when (and L (not (query-p (link-resultant-interest L))))
      (princ "                                        For ")
      (when (interest-reductio (link-resultant-interest L)) (princ "reductio "))
      (princ "interest ")
      (princ (interest-number (link-resultant-interest L)))
      (princ " by ") (princ (link-rule L))
      (let ((nodes (link-supporting-nodes L)))
        (when nodes
          (cond ((equal (length nodes) 1)
                 (princ " using node ")
                 (princ (hypernode-number (mem1 nodes))))
                (t
                  (princ " using nodes ")
                  (print-list (mapcar
                                #'(lambda (conclusion)
                                    (hypernode-number conclusion))
                                nodes) 40)))))
      (let ((nodes (link-clues L)))
        (when nodes
          (cond ((equal (length nodes) 1)
                 (princ " with clue ")
                 (princ (hypernode-number (mem1 nodes))))
                (t
                  (princ " with clues ")
                  (print-list (mapcar
                                #'(lambda (conclusion)
                                    (hypernode-number conclusion))
                                nodes) 40)))))
      (terpri))
    (when (interest-discharge-condition interest)
      (princ "                                        Discharge condition: ") (terpri)
      (princ "                                             ")
      (display-discharge-condition interest L) (terpri)))
  (terpri))

(defun display-interests ()
  (princ "(") (terpri)
  (princ "================== INTERESTS ===================")
  (terpri)
  (let* ((star-interests
           (unionmapcar
             #'(lambda (dn)
                 (unionmapcar #'(lambda (il) (i-list-interests il)) (d-node-i-lists dn)))
             *discrimination-net*))
         (interests
           (order star-interests
                  #'(lambda (c1 c2)
                      (< (interest-number c1) (interest-number c2))))))
    (dolist (interest interests)
      (princ "#") (princ (interest-number interest))
      (cond ((interest-deductive interest) (princ "  deductive interest: "))
            ((interest-reductio interest) (princ "  reductio interest: "))
            (t (princ "  interest: ")))
      (prinp (interest-formula interest))
      (when (interest-supposition interest)
        (princ "    supposition: ")
        (set-prinp (interest-supposition interest)))
      (terpri)
      (when
        (some #'(lambda (L) (query-p (link-resultant-interest L)))
              (interest-right-links interest))
        (princ "     This is of ultimate interest") (terpri))
      (dolist (L (interest-right-links interest))
        (when (not (query-p (link-resultant-interest L)))
          (princ "     For ")
          (when (interest-reductio (link-resultant-interest L)) (princ "reductio "))
          (princ "interest ")
          (princ (interest-number (link-resultant-interest L)))
          (princ " by ") (princ (link-rule L))
          (let ((nodes (link-supporting-nodes L)))
            (when nodes
              (cond ((equal (length nodes) 1)
                     (princ " using node ")
                     (princ (hypernode-number (mem1 nodes))))
                    (t
                      (princ " using nodes ")
                      (print-list (mapcar
                                    #'(lambda (conclusion)
                                        (hypernode-number conclusion))
                                    nodes) 40)))))
          (let ((nodes (link-clues L)))
            (when nodes
              (cond ((equal (length nodes) 1)
                     (princ " with clue ")
                     (princ (hypernode-number (mem1 nodes))))
                    (t
                      (princ " with clues ")
                      (print-list (mapcar
                                    #'(lambda (conclusion)
                                        (hypernode-number conclusion))
                                    nodes) 40)))))
          (terpri)))
      (when (interest-defeatees interest)
        (princ "     For the defeat of ")
        (print-list (mapcar #'hypernode-number (interest-defeatees interest)))
        (terpri))
      (princ "---------------------------------------------------") (terpri)))
  (princ ")") (terpri))

#| This builds chains of inference-ancestors. |#
(defun interest-ancestor-chains (interest)
  (cond ((interest-p interest)
         (let ((links (interest-right-links interest)))
           (cond ((null links) (list (list (list interest))))
                 (t
                   (unionmapcar
                     #'(lambda (L)
                         (mapcar
                           #'(lambda (c)
                               (cons (list interest L) c))
                           (interest-ancestor-chains (link-resultant-interest L))))
                     links)))))
        (t (list nil))))

#| This is like interest-ancestor-chains, but leaves out the links. |#
(defun right-branches (interest)
  (if (interest-p interest)
    (let ((links (interest-right-links interest)))
      (cond ((null links) (list (list interest)))
            (t
              (unionmapcar
                #'(lambda (L)
                    (mapcar
                      #'(lambda (c)
                          (cons interest c))
                      (right-branches (link-resultant-interest L))))
                links))))))

(defun good-interest-ancestor-chains (interest)
  (if (interest-p interest)
    (let ((links (interest-right-links interest)))
      (cond ((null links) (list (list (list interest))))
            (t
              (let ((i-list (interest-i-list interest)))
                (unionmapcar
                  #'(lambda (L)
                      (remove nil
                              (mapcar
                                #'(lambda (c)
                                    (when
                                      (and
                                        (not
                                          (and
                                            (equal (link-rule L) reductio)
                                            (or
                                              (and
                                                (mem2 (mem1 c))
                                                (equal (link-rule (mem2 (mem1 c))) reductio))
                                              (some #'(lambda (x)
                                                        (and (mem2 x)
                                                             (equal (link-rule (mem2 x)) reductio)
                                                             (equal (interest-i-list (mem1 x))
                                                                    i-list)))
                                                    c)))))
                                      (cons (list interest L) c)))
                                (good-interest-ancestor-chains (link-resultant-interest L)))))
                  links)))))))

(defun derived-interests (interest)
  (mapcar #'link-interest (interest-left-links interest)))

(defun display-interests-by-supposition ()
  (princ "(") (terpri)
  (let ((suppositions nil))
    (dolist (dn *discrimination-net*)
      (dolist (il (d-node-i-lists dn))
        (dolist (c (i-list-interests il))
          (pushnew (interest-supposition c) suppositions :test '==)
          (setf suppositions
                (order suppositions
                       #'(lambda (s1 s2)
                           (or (< (length s1) (length s2))
                               (and (= (length s1) (length s2))
                                    (lessp s1 s2)))))))))
    (let* ((star-interests
             (unionmapcar
               #'(lambda (dn)
                   (unionmapcar #'(lambda (il) (i-list-interests il)) (d-node-i-lists dn)))
               *discrimination-net*)))
      (dolist (sup suppositions)
        (princ "==========================================") (terpri)
        (princ "Interests with supposition ") (set-prinp sup) (princ ":") (terpri)
        (let* ((sup-interests
                 (subset #'(lambda (c) (== (interest-supposition c) sup))
                         star-interests))
               (interests
                 (order sup-interests
                        #'(lambda (c1 c2)
                            (< (interest-number c1) (interest-number c2))))))
          (dolist (c interests)
            (when (== (interest-supposition c) sup)
              (princ "    #") (princ (interest-number c)) (princ "  ")
              (prinp (interest-formula c)) (princ "     ")
              (when (interest-reductio c) (princ "reductio "))
              (princ "for  ")
              (print-list
                (remove-duplicates=
                  (mapcar
                    #'(lambda (L) (interest-number (link-resultant-interest L)))
                    (interest-right-links c))) 40)
              (terpri)))))))
  (princ ")") (terpri))

(defun display-i-lists ()
  (princ "(") (terpri)
  (dolist (dn *discrimination-net*)
    (dolist (il (d-node-i-lists dn))
      (princ "==========================================") (terpri)
      (princ "i-list-formula: ") (prinp (i-list-formula il)) (terpri)
      (let ((interests
              (order (i-list-interests il)
                     #'(lambda (c1 c2)
                         (let ((s1 (interest-supposition c1))
                               (s2 (interest-supposition c2)))
                           (or (< (length s1) (length s2))
                               (and (= (length s1) (length s2))
                                    (lessp s1 s2))))))))
        (dolist (c interests)
          (princ "    #") (princ (interest-number c)) (princ "  ")
          (princ "   sup = ") (set-prinp (interest-supposition c)) (princ "     ")
          (when (interest-reductio c) (princ "reductio "))
          (princ "for  ")
          (print-list
            (remove-duplicates=
              (mapcar
                #'(lambda (L) (interest-number (link-resultant-interest L)))
                (interest-right-links c))) 40)
          (let ((derived-interests (derived-interests c)))
            (when derived-interests
              (princ "  generates ")
              (print-list (mapcar #'interest-number derived-interests) 40)))
          (terpri)))))
  (princ ")") (terpri))

(defun binding-unifier (binding1 binding2 premise-variables vars1 vars2)
  (let ((term-list1 nil)
        (term-list2 nil))
    (dolist (v premise-variables)
      (let ((assoc1 (assoc v binding1))
            (assoc2 (assoc v binding2)))
        (when (and assoc1 assoc2)
          (push (cdr assoc1) term-list1) (push (cdr assoc2) term-list2))))
    (unifier term-list1 term-list2 vars1 vars2)))

(defun funcall** (f x y) (if f (funcall f x y) t))

(defun applied-forwards-reason-strength (reason binding basis)
  (let ((strength
          (cond ((keywordp reason) 1.0)
                ((numberp (reason-strength reason)) (reason-strength reason))
                (t (funcall (reason-strength reason) binding basis)))))
    (if (and (not (keywordp reason)) (reason-temporal? reason))
      (* strength (minimum (mapcar #'current-degree-of-justification basis)))
      (minimum (cons strength (mapcar #'current-degree-of-justification basis))))))

#| For non-reductio-interests, this returns the list of unifiers unifying the hypernode-supposition of
node into the the interest-supposition of interest.  For reductio-interests, this returns the list of
unifiers unifying the non-inherited part of the hypernode-non-reductio-supposition into the
interest-supposition. |#
(defun appropriately-related-suppositions (node interest unifier &optional a-list target)
  (when (null target) (setf target interest))
  (let* ((i-sup (match-sublis (mem2 unifier) (interest-supposition interest)))
         (c-vars (match-sublis (mem1 unifier) (hypernode-supposition-variables node)))
         (i-vars (match-sublis (mem2 unifier) (interest-variables interest))))
    (if (and (not (query-p target)) (interest-reductio target))
      (let ((domain nil))
        (dolist (S (hypernode-non-reductio-supposition node))
          (let ((sup (cdr S)))
            (when (not (member sup *inherited-non-reductio-suppositions*))
              (push (car S) domain))))
        (set-unifier (match-sublis (mem1 unifier) (match-sublis a-list domain)) i-sup c-vars i-vars))
      (set-unifier
        (match-sublis (mem1 unifier)
                      (match-sublis a-list (hypernode-supposition node)))
        i-sup c-vars i-vars))))

(defun appropriately-related-reductio-suppositions (node interest unifier)
  (when (and (not (query-p interest)) (interest-reductio interest))
    (let* ((i-sup (match-sublis (mem2 unifier) (interest-supposition interest)))
           (c-vars (match-sublis (mem1 unifier) (hypernode-supposition-variables node)))
           (i-vars (match-sublis (mem2 unifier) (interest-variables interest))))
      (let ((domain nil))
        (dolist (S (hypernode-non-reductio-supposition node))
          (let ((sup (cdr S)))
            (when (not (member sup *inherited-non-reductio-suppositions*))
              (push (car S) domain))))
        (set-unifier (match-sublis (mem1 unifier) domain) i-sup c-vars i-vars)))))

(defun appropriately-related-non-reductio-suppositions (node interest unifier)
  (let* ((i-sup (match-sublis (mem2 unifier) (interest-supposition interest)))
         (c-vars (match-sublis (mem1 unifier) (hypernode-supposition-variables node)))
         (i-vars (match-sublis (mem2 unifier) (interest-variables interest))))
    (set-unifier (match-sublis (mem1 unifier) (hypernode-supposition node)) i-sup c-vars i-vars)))

#| This returns the list of unifiers unifying the hypernode-supposition of  node into the the
hypernode-supposition of node*. |#
(defun appropriately-related-node-suppositions (node node* unifier)
  (let* ((sup (match-sublis (mem1 unifier) (hypernode-supposition node)))
         (sup* (match-sublis (mem2 unifier) (hypernode-supposition node*)))
         (vars (match-sublis (mem1 unifier) (hypernode-supposition-variables node)))
         (vars* (match-sublis (mem2 unifier) (hypernode-supposition-variables node*))))
    (set-unifier sup sup* vars vars*)))

(defun appropriately-related-supposition (node interest supposition supposition-variables unifier)
  (let* ((i-sup (match-sublis (mem2 unifier) supposition))
         (c-vars (match-sublis (mem1 unifier) (hypernode-supposition-variables node)))
         (i-vars (match-sublis (mem2 unifier) supposition-variables)))
    (if (and (not (query-p interest)) (interest-reductio interest))
      (let ((domain nil))
        (dolist (S (hypernode-non-reductio-supposition node))
          (let ((sup (cdr S)))
            (when (not (member sup *inherited-non-reductio-suppositions*))
              (push (car S) domain))))
        (set-unifier (match-sublis (mem1 unifier) domain) i-sup c-vars i-vars))
      (set-unifier
        (match-sublis (mem1 unifier) (hypernode-supposition node)) i-sup c-vars i-vars))))

(defun compute-interest-supposition-nodes (interest)
  (when (interest-supposition interest)
    (dolist (n (interest-generating-nodes interest))
      (when (not (member n (interest-supposition-nodes interest)))
        (push n (interest-supposition-nodes interest))
        (dolist (in (hypernode-generating-interests n))
          (setf (interest-supposition-nodes interest)
                (union
                  (interest-supposition-nodes interest)
                  (interest-supposition-nodes in))))))
    (dolist (L (interest-right-links interest))
      (setf (interest-supposition-nodes interest)
            (union
              (interest-supposition-nodes interest)
              (interest-supposition-nodes (link-resultant-interest L)))))))

(defun construct-new-interest-for
  (link vars condition degree maximum-degree depth i-list text-condition)
  ; (when (equal link (link 6)) (setf l link v vars c condition d degree m* maximum-degree d* depth i i-list) (break))
  ;; (step (construct-new-interest-for l v c d m* d* i))
  (let* ((gn (link-generating-node link))
         (interest
           (make-interest
             :interest-number (incf *interest-number*)
             :interest-sequent (list (link-supposition link) (link-interest-formula link))
             :interest-formula (link-interest-formula link)
             :interest-variables vars
             :interest-supposition (link-supposition link)
             :interest-supposition-variables
             (unionmapcar= #'formula-hypernode-variables (link-supposition link))
             :interest-right-links (list link)
             :interest-generating-nodes (if gn (list gn))
             :interest-degree-of-interest degree
             :interest-text-discharge-condition text-condition
             :interest-maximum-degree-of-interest maximum-degree
             :interest-deductive (interest-deductive (link-resultant-interest link))
             :interest-defeat-status (link-defeat-status link)
             :interest-reductio (interest-reductio (link-resultant-interest link)))))
    (funcall* condition interest)
    (if gn (push interest (hypernode-generated-interests gn)))
    (compute-interest-supposition-nodes interest)
    (store-interest interest i-list)
    (when *trace* (indent (1+ depth)) (princ "CONSTRUCT-NEW-INTEREST-FOR LINK:") (terpri))
    (when *display?* (display-interest interest))
    (when *log-on* (push interest *reasoning-log*))
    (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
    interest))

(defun interest-for (sequent vars condition &optional link)
  (multiple-value-bind
    (i-list match match*)
    (i-list-for (sequent-formula sequent) vars)
    (let*
      ((sup
         (if i-list (match-sublis match (sequent-supposition sequent)) (sequent-supposition sequent)))
       (interest
         (if i-list
           (find-if
             #'(lambda (i)
                 (and (or condition (null (interest-discharge-condition i)))
                      (funcall* condition i) (== (interest-supposition i) sup)
                      (or (null link)
                          (eq (interest-deductive i) (interest-deductive (link-resultant-interest link))))))
             (i-list-interests i-list)))))
      (when (and (null interest) (not (eq match t))) (setf i-list nil))
      (values interest i-list match match*))))

#| If the interest is readopted as an interest in a defeater, defeated-nodes is the list of
nodes for which it is a defeater.  When this is called by DISCHARGE-LINK, link is the
link being discharged.  |#
(defun readopt-interest (interest defeated-links)
  (when *display?*
    (princ "                                   Readopting interest in:") (terpri)
    (display-interest interest)
    (when defeated-links
      (princ
        "                                        Of interest as defeater for hyperlink ")
      (princ (hyperlink-number (mem1 defeated-links))) (terpri)(terpri)))
  )

#| new-vars are new variables introduced by the inference-rule, as in EG. |#
(defun compute-link-interest
  (link condition1 condition2 degree max-degree depth priority &optional new-vars text-condition)
  (declare (ignore new-vars))
  ; (setf l link c1 condition1 c2 condition2 d degree md max-degree dp depth p priority nv new-vars) ; (break))
  ;; (step (compute-link-interest l c1 c2 d md dp p nv))
  (let* ((interest-priority
           (if priority
             (* priority (reason-discount-factor (link-rule link)))
             (interest-priority (link-resultant-interest link))))
         (vars (formula-hypernode-variables (link-interest-formula link))))
    (multiple-value-bind
      (interest i-list match match*)
      (interest-for (list (link-supposition link) (link-interest-formula link)) vars condition1 link)
      (cond
        (interest
          (setf (interest-degree-of-interest interest) (min (interest-degree-of-interest interest) degree))
          (setf (interest-maximum-degree-of-interest interest)
                (max (interest-maximum-degree-of-interest interest) max-degree))
          (when (not (interest-reductio interest))
            (setf (interest-reductio interest) (interest-reductio (link-resultant-interest link))))
          (setf (interest-priority interest) (max (interest-priority interest) interest-priority))
          (let ((gn (link-generating-node link)))
            (when gn
              (pushnew gn (interest-generating-nodes interest))
              (push interest (hypernode-generated-interests gn))))
          (if (interest-right-links interest)
            (setf (interest-right-links interest) (reverse (cons link (reverse (interest-right-links interest)))))
            (setf (interest-right-links interest) (list link)))
          (setf (link-interest-match link) match)
          (setf (link-interest-reverse-match link) match*)
          (readopt-interest interest nil))
        (t
          (setf interest
                (construct-new-interest-for
                  link vars condition2 degree max-degree depth i-list text-condition))
          (setf (interest-priority interest) interest-priority)
          ))
      (setf (link-interest link) interest)
      ; (dolist (p (interest-decision-plans (link-resultant-interest link)))
      ;     (pushnew p (interest-decision-plans interest)))
      )))

(defun cancel-d-node (d-node)
  (when (not (eq d-node *top-d-node*))
    (let* ((dn (d-node-parent d-node))
           (test (rassoc d-node (d-node-discrimination-tests dn))))
      (setf (d-node-discrimination-tests dn) (remove test (d-node-discrimination-tests dn)))
      (when (and (null (d-node-c-lists dn)) (null (d-node-i-lists dn))
                 (null (d-node-forwards-reasons dn))
                 (null (d-node-backwards-reasons dn))
                 (null (d-node-interest-schemes dn))
                 (null (d-node-discrimination-tests dn)))
        (cancel-d-node dn)))))

(defun cancel-instantiated-premise (IP)
  (let ((dn (ip-d-node IP)))
    (pull IP (d-node-forwards-reasons dn))
    (when (and (null (d-node-forwards-reasons dn))
               (null (d-node-interest-schemes dn))
               (null (d-node-c-lists dn))
               (null (d-node-i-lists dn))
               (null (d-node-backwards-reasons dn))
               (null (d-node-discrimination-tests dn)))
      (cancel-d-node dn)))
  (dolist (IP* (ip-derived-premises IP)) (cancel-instantiated-premise IP*)))

(defun cancel-interest-scheme (IS)
  (let ((dn (is-d-node IS)))
    (pull IS (d-node-interest-schemes dn))
    (when (and (null (d-node-interest-schemes dn))
               (null (d-node-c-lists dn))
               (null (d-node-i-lists dn))
               (null (d-node-forwards-reasons dn))
               (null (d-node-backwards-reasons dn))
               (null (d-node-discrimination-tests dn)))
      (cancel-d-node dn)))
  (dolist (IS* (is-derived-interest-schemes IS)) (cancel-interest-scheme IS*)))

#| These are redefined in oscar-graphics in MCL. |#
(when (not (equal (lisp-implementation-type) "Macintosh Common Lisp"))
  (defun invalidate-view (x &optional y) (declare (ignore x y))))

(labels ()
  (defun anchor-interest-relative-to-interest (interest I indent msg)
    (pull interest *dependent-interests*)
    (when *d-trace*
      (bar-indent indent) (princ msg) (princ interest) (terpri))
    (dolist (L (interest-left-links interest))
      (let ((in (link-interest L)))
        (when (member in *dependent-interests*)
          (let ((cn (interest-cancelling-node in)))
            (when cn (anchor-hypernode-relative-to-interest cn I  (1+ indent) "cancelling-node: ")))
          (when (and (not (eq I in)) (member in *dependent-interests*))
            (anchor-interest-relative-to-interest in I (1+ indent) "left-link: ")))))
    (dolist (n (interest-generated-suppositions interest))
      (when (member n *dependent-nodes*)
        (anchor-hypernode-relative-to-interest n I (1+ indent) "generated-supposition: "))))

  (defun anchor-hypernode-relative-to-interest (node I indent msg)
    (pull node *dependent-nodes*)
    (when *d-trace*
      (bar-indent indent) (princ msg) (princ node) (terpri))
    (dolist (n (hypernode-consequences node))
      (when
        (and
          (member n *dependent-nodes*)
          (some
            #'(lambda (L)
                (every #'(lambda (b)
                           (and (not (hypernode-cancelled-node b))
                                (not (member b *dependent-nodes*))))
                       (hyperlink-basis L)))
            (hypernode-hyperlinks n)))
        (anchor-hypernode-relative-to-interest n I (1+ indent) "hypernode-consequence: ")))
    (when (and (eq (hypernode-justification node) :reductio-supposition)
               (null *independent-reductio-suppositions*))
      (push node *independent-reductio-suppositions*)
      (dolist (in *direct-reductio-interests*)
        (when (and (not (eq I in)) (member in *dependent-interests*)
                   (some
                     #'(lambda (dr)
                         (and
                           (not (hypernode-cancelled-node (car dr)))
                           (not (member (car dr) *dependent-nodes*))))
                     (interest-direct-reductio in)))
          (anchor-interest-relative-to-interest
            in I (1+ indent) "*direct-reductio-interest*: "))
        (let ((n* (interest-cancelling-node in)))
          (when (and n* (member n* *dependent-nodes*))
            (anchor-hypernode-relative-to-interest
              n* I (1+ indent) "discharges direct reductio interest: ")))))
    (dolist (in (hypernode-generated-direct-reductio-interests node))
      (when *independent-reductio-suppositions*
        (when (and (not (eq I in)) (member in *dependent-interests*))
          (pull in *dependent-interests*)
          (anchor-interest-relative-to-interest
            in I (1+ indent) "generated-direct-reductio-interest: "))
        (let ((n* (interest-cancelling-node in)))
          (when (and n* (member n* *dependent-nodes*))
            (anchor-hypernode-relative-to-interest
              n* I (1+ indent) "discharges direct reductio interest: "))))))
  )

(labels ()

  (defun compute-interest-dependencies (interest indent msg)
    ; (when (eq interest (interest 105)) (setf i interest n indent m msg) (break))
    ;; (step (compute-interest-dependencies i n m))
    (when *d-trace*
      (bar-indent indent) (princ msg) (princ interest)
      (when (interest-cancelled interest) (princ " cancelled")) (terpri))
    (dolist (s (interest-generated-suppositions interest))
      (when (not (member s *dependent-nodes*))
        (push s *dependent-nodes*)
        (when (eq (hypernode-justification s) :reductio-supposition)
          (pull s *independent-reductio-suppositions*))
        (compute-hypernode-dependencies s (1+ indent) "generated-supposition: ")))
    (dolist (n (interest-anchored-nodes interest))
      (when (and (not (hypernode-cancelled-node n)) (not (member n *dependent-nodes*)))
        (push n *dependent-nodes*)
        (when (eq (hypernode-justification n) :reductio-supposition)
          (pull n *independent-reductio-suppositions*))
        (compute-hypernode-dependencies n (1+ indent) "partial-satisfier: ")))
    (dolist (L (interest-left-links interest))
      (let ((in (link-interest L)))
        (when (not (member in *dependent-interests*))
          (cond ((not (interest-cancelled in))
                 (push in *dependent-interests*)
                 (compute-interest-dependencies in (1+ indent) "left-link: "))
                (t
                  (dolist (n (interest-discharging-nodes in))
                    (when (and (not (member n *dependent-nodes*))
                               (not (hypernode-cancelled-node n)))
                      (push n *dependent-nodes*)
                      (compute-hypernode-dependencies
                        n (1+ indent) "discharging-node of left-link: ")))))))))

  (defun compute-hypernode-dependencies (node indent msg)
    (when *d-trace*
      (bar-indent indent) (princ msg) (princ node)
      (when (hypernode-cancelled-node node) (princ " cancelled")) (terpri))
    (dolist (n (hypernode-consequences node))
      (when (and (not (member n *dependent-nodes*))
                 (not (hypernode-cancelled-node n)))
        (push n *dependent-nodes*)
        (compute-hypernode-dependencies n (1+ indent) "hypernode-consequence: ")))
    (dolist (in (hypernode-generated-direct-reductio-interests node))
      (when (not (member in *dependent-interests*))
        (push in *dependent-interests*)
        (compute-interest-dependencies
          in (1+ indent) "generated-direct-reductio-interest: ")))
    (dolist (in (hypernode-generated-defeat-interests node))
      (when (not (member in *dependent-interests*))
        (push in *dependent-interests*)
        (compute-interest-dependencies
          in (1+ indent) "generated-defeat-interest: ")))
    (when (eq (hypernode-justification node) :reductio-supposition)
      (dolist (in *direct-reductio-interests*)
        (when (not (member in *dependent-interests*))
          (push in *dependent-interests*)
          (compute-interest-dependencies
            in (1+ indent) "*direct-reductio-interest*: ")))))
  )

(defun compute-dependencies (interest)
  ; (when (eq interest (interest 105)) (setf i interest) (break))
  ;; (step (compute-dependencies i))
  (setf *dependent-interests* (list interest) *dependent-nodes* nil
        *independent-reductio-suppositions* *reductio-supposition-nodes*)
  (compute-interest-dependencies
    interest 0 "COMPUTING DEPENDENCIES from ")
  (when *d-trace* (princ "ANCHORING-NODES AND INTERESTS") (terpri))
  (let ((anchored-nodes
          (subset
            #'(lambda (n)
                (or
                  (some
                    #'(lambda (in)
                        (and
                          (not (member in *dependent-interests*))
                          (not (interest-cancelled in))
                          (progn
                            (when *d-trace*
                              (princ "Hypernode ") (princ (hypernode-number n))
                              (princ " is directly anchored by the anchoring-interest ")
                              (princ (interest-number in)) (terpri)) t)))
                    (hypernode-anchoring-interests n))
                  (some #'(lambda (in)
                            (and
                              (not (member in *dependent-interests*))
                              (not (interest-cancelled in))
                              (progn
                                (when *d-trace*
                                  (princ "Hypernode ") (princ (hypernode-number n))
                                  (princ " is directly anchored by the generating-interest ")
                                  (princ (interest-number in)) (terpri)) t)))
                        (hypernode-generating-interests n))
                  (some #'(lambda (in)
                            (and
                              (not (member in *dependent-interests*))
                              (not (interest-cancelled in))
                              (progn
                                (when *d-trace*
                                  (princ "Hypernode ") (princ (hypernode-number n))
                                  (princ " is directly anchored by the enabling-interest ")
                                  (princ (interest-number in)) (terpri)) t)))
                        (hypernode-enabling-interests n))
                  (some
                    #'(lambda (L)
                        (and
                          (every #'(lambda (b)
                                     (and (not (member b *dependent-nodes*))
                                          (not (hypernode-cancelled-node b))))
                                 (hyperlink-basis L))
                          (progn
                            (when *d-trace*
                              (princ "Hypernode ") (princ (hypernode-number n))
                              (princ " is directly anchored by the hyperlink ")
                              (princ (hyperlink-number L)) (terpri)) t)))
                    (hypernode-hyperlinks n))
                  (and
                    *independent-reductio-suppositions*
                    (some
                      #'(lambda (in)
                          (some
                            #'(lambda (dr)
                                (let ((n* (car dr)))
                                  (and
                                    (not (hypernode-cancelled-node n*))
                                    (pushnew n (interest-anchored-nodes (car in)))
                                    (pushnew (car in) (hypernode-anchoring-interests n))
                                    (not (member n* *dependent-nodes*))
                                    (progn
                                      (when *d-trace*
                                        (princ "Hypernode ") (princ (hypernode-number n))
                                        (princ " is directly anchored by discharging a interest-direct-reductio from node ")
                                        (princ (hypernode-number n*)) (terpri)) t))))
                            (interest-direct-reductio (car in))))
                      (hypernode-discharged-interests n)))
                  (some
                    #'(lambda (in)
                        (and
                          (eq n (interest-cancelling-node in))
                          (some
                            #'(lambda (L)
                                (and (not (query-p (link-resultant-interest L)))
                                     (not (interest-cancelled (link-resultant-interest L)))
                                     (push n (interest-anchored-nodes (link-resultant-interest L)))
                                     (pushnew (link-resultant-interest L) (hypernode-anchoring-interests n))
                                     (not (member (link-resultant-interest L) *dependent-interests*))
                                     (progn
                                       (when *d-trace*
                                         (princ "Hypernode ") (princ (hypernode-number n))
                                         (princ " is directly anchored by being the interest-cancelling-node for interest ")
                                         (princ (interest-number in))
                                         (princ " which has a right-link to interest ")
                                         (princ (interest-number (link-resultant-interest L)))
                                         (terpri))
                                       t)))
                            (interest-right-links in))))
                    (hypernode-enabling-interests n))
                  ))
            *dependent-nodes*))
        (anchored-interests
          (subset
            #'(lambda (in)
                (and
                  (not (eq in interest))
                  (or
                    (some #'(lambda (n)
                              (and
                                (not (member n *dependent-nodes*))
                                (progn
                                  (when *d-trace*
                                    (princ "Interest ") (princ (interest-number in))
                                    (princ " is directly anchored by the generating-node ")
                                    (princ (hypernode-number n)) (terpri)) t)))
                          (interest-generating-nodes in))
                    (and *independent-reductio-suppositions*
                         (some #'(lambda (dr)
                                   (and
                                     (not (member (car dr) *dependent-nodes*))
                                     (progn
                                       (when *d-trace*
                                         (princ "Interest ") (princ (interest-number in))
                                         (princ " is directly anchored by being a interest-direct-reductio from the node ")
                                         (princ (hypernode-number (car dr))) (terpri)) t)))
                               (interest-direct-reductio in)))
                    (some #'(lambda (L)
                              (and
                                (not (member (link-resultant-interest L) *dependent-interests*))
                                (progn
                                  (when *d-trace*
                                    (princ "Interest ") (princ (interest-number in))
                                    (princ " is directly anchored by a right-link to interest ")
                                    (princ (interest-number (link-resultant-interest L))) (terpri)) t)))
                          (interest-right-links in)))))
            *dependent-interests*)))
    (dolist (n anchored-nodes)
      (anchor-hypernode-relative-to-interest n interest 0 "Directly-anchored node: "))
    (dolist (in anchored-interests)
      (anchor-interest-relative-to-interest in interest 0 "Directly-anchored interest: "))))

(defun cancel-interest-in-node (node depth)
  ; (when (eq node (node 353)) (break))
  (when (not (hypernode-cancelled-node node))
    (when *display?* (indent depth) (princ "Cancelling  ") (princ node) (terpri))
    (setf (hypernode-cancelled-node node) t)
    (when (eq (hypernode-justification node) :reductio-supposition)
      (pull node *reductio-supposition-nodes*)
      (when (hypernode-generating-interests node)
        (let ((i-list (interest-i-list (mem1 (hypernode-generating-interests node)))))
          (when (eq (i-list-reductio-supposition i-list) node)
            (setf (i-list-reductio-supposition i-list) nil)
            (setf (i-list-reductio-trigger i-list) t)))))
    (when (eq (hypernode-justification node) :supposition)
      (setf *skolem-free-suppositions*
            (remove-if-equal (hypernode-formula node) *skolem-free-suppositions*)))
    (pull node *inherited-non-reductio-suppositions*)
    (pull node *non-reductio-supposition-nodes*)
    (pull node *reductio-supposition-nodes*)
    (pull node *desires*)
    (pull node *processed-desires*)
    (dolist (IN (hypernode-generated-interests node))
      (pull node (interest-generating-nodes IN)))
    (dolist (IN (hypernode-generating-interests node))
      (pull node (interest-generated-suppositions IN)))
    (dolist (IN (hypernode-generated-direct-reductio-interests node))
      (setf (interest-direct-reductio IN) nil)) ; TODO why is this in v3.31?
      ; TODO why is this in v4.02? (pull node (c-list-reductio-interests IN)))
    (let ((c-list (hypernode-c-list node)))
      (when c-list
        (pull node (c-list-nodes c-list))
        (pull node (c-list-processed-nodes c-list))
        (when (null (c-list-processed-nodes c-list))
          (dolist (IS (c-list-supported-interest-schemes c-list))
            (cancel-interest-scheme IS))
          (dolist (IP (c-list-generated-instantiated-premises c-list))
            (cancel-instantiated-premise IP)))
        (when (null (c-list-nodes c-list))
          (let ((dn (c-list-d-node c-list)))
            (pull c-list (d-node-c-lists dn))
            (when (and (null (d-node-c-lists dn)) (null (d-node-i-lists dn))
                       (null (d-node-forwards-reasons dn))
                       (null (d-node-backwards-reasons dn))
                       (null (d-node-interest-schemes dn))
                       (null (d-node-discrimination-tests dn)))
              (cancel-d-node dn)))
          (dolist (cl (c-list-contradictors c-list))
            (pull (assoc c-list (c-list-contradictors (car cl)))
                  (c-list-contradictors (car cl))))
          (dolist (il (c-list-corresponding-i-lists c-list))
            (pull (assoc c-list (i-list-corresponding-c-lists (mem1 il)))
                  (i-list-corresponding-c-lists (mem1 il)))))))
    (let ((Q (hypernode-queue-node node)))
      (when Q (pull Q *inference-queue*)))
    (when (and *display?* *graphics-on*) (invalidate-view *og* t))))

(defun cancel-interest (interest depth)
  (when (and *display?* (not (interest-cancelled interest)))
    (indent depth) (princ "Cancelling  ") (princ interest) (terpri))
  (let ((i-list (interest-i-list interest)))
    (when i-list
      (pull interest (i-list-interests i-list))
      (when (null (i-list-interests i-list))
        (let ((dn (i-list-d-node i-list)))
          (pull i-list (d-node-i-lists dn))
          (when (and (null (d-node-c-lists dn))
                     (null (d-node-i-lists dn))
                     (null (d-node-forwards-reasons dn))
                     (null (d-node-backwards-reasons dn))
                     (null (d-node-interest-schemes dn))
                     (null (d-node-discrimination-tests dn)))
            (cancel-d-node dn)))
        (dolist (cl (i-list-corresponding-c-lists i-list))
          (pull (assoc i-list (c-list-corresponding-i-lists (mem1 cl)))
                (c-list-corresponding-i-lists (mem1 cl)))))))
  (setf (interest-cancelled interest) t)
  (let ((Q (interest-queue-node interest)))
    (when Q (pull Q *inference-queue*)))
  (dolist (IS (interest-generated-interest-schemes interest))
    (cancel-interest-scheme IS))
  (dolist (L (interest-left-links interest))
    (pull L (interest-right-links (link-interest L))))
  (dolist (L (interest-right-links interest))
    (when (not (query-p (link-resultant-interest L)))
      (pull L (interest-left-links (link-resultant-interest L)))
      (push L (interest-cancelled-left-links (link-resultant-interest L)))))
  (when (interest-direct-reductio interest) (pull interest *direct-reductio-interests*))
  (when (and *display?* *graphics-on* *graph-interests*) (invalidate-view *og* t)))

(defun cancel-interest-in (interest depth)
  (when  (and *display?* (zerop depth))
    (princ
      "..........................................................................................................................................")
    (terpri) (princ "Cancelling interest ") (princ (interest-number interest))
    (terpri))
  (compute-dependencies interest)
  (dolist (n *dependent-nodes*) (cancel-interest-in-node n (1+ depth)))
  (dolist (in *dependent-interests*) (cancel-interest in (1+ depth)))
  (when (and *display?* (zerop depth))
    (princ
      "..........................................................................................................................................")
    (terpri))
  ; (when (equal interest (interest 2)) (setf *d-trace* nil) (break))
  )

(labels ()

  (defun anchor-interest-relative-to-node (interest N0 indent msg)
    (pull interest *dependent-interests*)
    (when *d-trace*
      (bar-indent indent) (princ msg) (princ interest) (terpri))
    (dolist (L (interest-left-links interest))
      (let ((in (link-interest L)))
        (when (member in *dependent-interests*)
          (anchor-interest-relative-to-node in N0 (1+ indent) "left-link: ")
          (let ((cn (interest-cancelling-node in)))
            (when (and cn (member cn *dependent-nodes*))
              (anchor-hypernode-relative-to-interest cn N0  (1+ indent) "cancelling-node: "))))))
    (dolist (n (interest-generated-suppositions interest))
      (when (and (not (eq N N0)) (member n *dependent-nodes*))
        (anchor-hypernode-relative-to-node n N0 (1+ indent) "generated-supposition: "))))

  (defun anchor-hypernode-relative-to-node (node N0 indent msg)
    (pull node *dependent-nodes*)
    (when *d-trace*
      (bar-indent indent) (princ msg) (princ node) (terpri))
    (dolist (n (hypernode-consequences node))
      (when
        (and
          (not (eq N N0))
          (member n *dependent-nodes*)
          (some
            #'(lambda (L)
                (every #'(lambda (b)
                           (and (not (hypernode-cancelled-node b))
                                (not (member b *dependent-nodes*))))
                       (hyperlink-basis L)))
            (hypernode-hyperlinks n)))
        (anchor-hypernode-relative-to-node n N0 (1+ indent) "hypernode-consequence: ")))
    (when (and (eq (hypernode-justification node) :reductio-supposition)
               (null *independent-reductio-suppositions*))
      (push node *independent-reductio-suppositions*)
      (dolist (in *direct-reductio-interests*)
        (when (and (member in *dependent-interests*)
                   (some
                     #'(lambda (dr)
                         (and
                           (not (hypernode-cancelled-node (car dr)))
                           (not (member (car dr) *dependent-nodes*))))
                     (interest-direct-reductio in)))
          (anchor-interest-relative-to-node
            in N0 (1+ indent) "*direct-reductio-interest*: "))
        (let ((n* (interest-cancelling-node in)))
          (when (and n* (not (eq n* N0)) (member n* *dependent-nodes*))
            (anchor-hypernode-relative-to-node
              n* N0 (1+ indent) "discharges direct reductio interest: ")))))
    (dolist (in (hypernode-generated-direct-reductio-interests node))
      (when *independent-reductio-suppositions*
        (when (member in *dependent-interests*)
          (pull in *dependent-interests*)
          (anchor-interest-relative-to-node
            in N0 (1+ indent) "generated-direct-reductio-interest: "))
        (let ((n* (interest-cancelling-node in)))
          (when (and n* (not (eq n* N0)) (member n* *dependent-nodes*))
            (anchor-hypernode-relative-to-node
	     n* N0 (1+ indent) "discharges direct reductio interest: "))))))
  )

#| This computation is exhibited by setting *d-trace* to t. |#
(defun compute-dependencies-from-node (node)
  ; (when (eq node (node 703)) (break))
  (setf *dependent-interests* nil *dependent-nodes* (list node)
        *independent-reductio-suppositions* *reductio-supposition-nodes*)
  (compute-hypernode-dependencies
    node 0 "COMPUTING DEPENDENCIES from ")
  (when *d-trace* (princ "ANCHORING-NODES AND INTERESTS") (terpri))
  (let ((anchored-nodes
          (subset
            #'(lambda (n)
                (and
                  (not (eq n node))
                  (or
                    (some
                      #'(lambda (in)
                          (and
                            (not (member in *dependent-interests*))
                            (not (interest-cancelled in))
                            (progn
                              (when *d-trace*
                                (princ "Hypernode ") (princ (hypernode-number n))
                                (princ " is directly anchored by the anchoring-interest ")
                                (princ (interest-number in)) (terpri)) t)))
                      (hypernode-anchoring-interests n))
                    (some #'(lambda (in)
                              (and
                                (not (member in *dependent-interests*))
                                (not (interest-cancelled in))))
                          (hypernode-generating-interests n))
                    (some
                      #'(lambda (L)
                          (every #'(lambda (b)
                                     (and (not (member b *dependent-nodes*))
                                          (not (hypernode-cancelled-node b))))
                                 (hyperlink-basis L)))
                      (hypernode-hyperlinks n))
                    (and
                      *independent-reductio-suppositions*
                      (some
                        #'(lambda (in)
                            (some
                              #'(lambda (dr)
                                  (let ((n* (car dr)))
                                    (and
                                      (not (hypernode-cancelled-node n*))
                                      (pushnew n (interest-anchored-nodes (car in)))
                                      (pushnew (car in) (hypernode-anchoring-interests n))
                                      (not (member n* *dependent-nodes*))
                                      (progn
                                        (when *d-trace*
                                          (princ "Hypernode ") (princ (hypernode-number n))
                                          (princ " is directly anchored by discharging a interest-direct-reductio from node ")
                                          (princ (hypernode-number n*)) (terpri)) t))))
                              (interest-direct-reductio (car in))))
                        (hypernode-discharged-interests n)))
                    (some
                      #'(lambda (in)
                          (some
                            #'(lambda (L)
                                (and (not (query-p (link-resultant-interest L)))
                                     (not (interest-cancelled (link-resultant-interest L)))
                                     (pushnew n (interest-anchored-nodes in))
                                     (pushnew in (hypernode-anchoring-interests n))
                                     (not (member (link-resultant-interest L) *dependent-interests*))
                                     ))
                            (interest-right-links in)))
                      (hypernode-enabling-interests n))
                    )))
            *dependent-nodes*))
        (anchored-interests
          (subset
            #'(lambda (in)
                (or
                  (some #'(lambda (n) (not (member n *dependent-nodes*)))
                        (interest-generating-nodes in))
                  (some #'(lambda (n) (not (member n *dependent-nodes*)))
                        (interest-generating-defeat-nodes in))
                  (and *independent-reductio-suppositions*
                       (some #'(lambda (dr) (not (member (car dr) *dependent-nodes*)))
                             (interest-direct-reductio in)))
                  (some #'(lambda (L) (not (member (link-resultant-interest L) *dependent-interests*)))
                        (interest-right-links in))))
            *dependent-interests*)))
    (dolist (n anchored-nodes)
      (anchor-hypernode-relative-to-node n node 0 "Directly-anchored node: "))
    (dolist (in anchored-interests)
      (anchor-interest-relative-to-node in node 0 "Directly-anchored interest: "))))

(defun cancel-node (node depth)
  ; (when (eq node (node 21)) (setf n node d depth) (break))
  ;; (step (cancel-node n d))
  (compute-dependencies-from-node node)
  (let ((draw-lines?
          (and *display?* (zerop depth)
               (or (not (hypernode-cancelled-node node)) *dependent-nodes* *dependent-interests*))))
    (when  draw-lines?
      (princ
        "..........................................................................................................................................")
      (terpri) (princ "Cancelling node ") (princ (hypernode-number node))
      (terpri))
    (dolist (n *dependent-nodes*) (cancel-interest-in-node n (1+ depth)))
    (dolist (in *dependent-interests*) (cancel-interest in (1+ depth)))
    (when draw-lines?
      (princ
        "..........................................................................................................................................")
      (terpri))))

(defun deductive-link (L)
  (or (keywordp (hyperlink-rule L)) (not (reason-defeasible-rule (hyperlink-rule L)))))

#| n is deductive in m. |#
(defun deductive-in (n m)
  (and (member m (hypernode-ancestors n))
       (some
         #'(lambda (L)
             (and
               (deductive-link L)
               (let ((B (hyperlink-basis L)))
                 (and
                   (or (member m B)
                       (some #'(lambda (x) (member m (hypernode-ancestors x))) B))
                   (every
                     #'(lambda (x) (or (not (member m (hypernode-ancestors x)))
                                       (deductive-in x m)))
                     B)))))
         (hypernode-hyperlinks n))))

(defun display-belief-changes  (links new-beliefs new-retractions)
  ; (when (member (hyperlink 12) links) (setf l links nb new-beliefs nr new-retractions) (break))
  ;; (step (display-belief-changes l  nb nr))
  (when (or *display?* *log-on*)
    (cond
      ((and (not *deductive-only*) (or new-beliefs new-retractions))
       (when (and *display?* *graphics-on*)
         (when *graphics-pause* (pause-graphics))
         (dolist (link links) (draw-n (hyperlink-target link) *og* *nodes-displayed*)))
       (when
         (or new-retractions
             (some
               #'(lambda (N)
                   (or (not (some #'(lambda (L) (eq N (hyperlink-target L))) links))
                       (set-difference (hypernode-hyperlinks N) links)
                       (not (eql (hypernode-degree-of-justification N) 1.0))))
               new-beliefs))
         (when *log-on*
           (push "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" *reasoning-log*))
         (when *display?* (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))
       (dolist (N new-beliefs)
         (cond ((or (not (some #'(lambda (L) (eq N (hyperlink-target L))) links))
                    (set-difference (hypernode-hyperlinks N) links))
                (when *log-on*
                  (push (list :increased-support N (hypernode-degree-of-justification N))
                        *reasoning-log*))
                (when *display?*
                  (princ "               The degree-of-justification of ") (princ N)
                  (princ " has increased to ") (princ (hypernode-degree-of-justification N)) (terpri)
                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))  ;)
                (when (and *display?* *graphics-on*)
                  (let ((posi (hypernode-position N *og*)))
                    (when posi
                      (when (and (boundp '*speak*) *speak*)
                        (speak-text "The degree-of-support of N ")
                        (speak-text (write-to-string (hypernode-number N)))
                        (speak-text "has increased to")
                        (speak-text (write-to-string (hypernode-degree-of-justification N))))
                      (draw-just-undefeated-node posi *og* N)))))
               ((not (eql (hypernode-degree-of-justification N) 1.0))
                (when *log-on*
                  (push (list :new-support N (hypernode-degree-of-justification N)) *reasoning-log*))
                (when *display?*
                  (princ "               The degree-of-justification of ") (princ N)
                  (princ " is ") (princ (hypernode-degree-of-justification N)) (terpri)
                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                (when (and *display?* *graphics-on*)
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "The degree-of-support of N ")
                    (speak-text (write-to-string (hypernode-number N)))
                    (speak-text "is")
                    (speak-text (write-to-string (hypernode-degree-of-justification N))))
                  (let ((posi (hypernode-position n *og*)))
                    (cond (posi (draw-just-undefeated-node posi *og* n))
                          (t
                            (draw-n n *og* *nodes-displayed*)
                            (push n *nodes-displayed*)
                            (setf posi (hypernode-position n *og*))
                            (draw-just-undefeated-node posi *og* n))))))))
       (dolist (N new-retractions)
         (cond ((or (not (some #'(lambda (L) (eq N (hyperlink-target L))) links))
                    (> (length (hypernode-hyperlinks N)) 1))
                (cond
                  ((zerop (hypernode-degree-of-justification N))
                   (when *log-on*
                     (push (list :defeated N) *reasoning-log*))
                   (when *display?*
                     (princ "               ") (princ N) (princ " has become defeated.") (terpri)
                     (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                   (when (and *display?* *graphics-on*)
                     (let ((posi (hypernode-position N *og*)))
                       (when posi
                         (when (and (boundp '*speak*) *speak*)
                           (speak-text "Hypernode ")
                           (speak-text (write-to-string (hypernode-number N)))
                           (speak-text "has become defeated."))
                         (draw-just-defeated-node posi *og* N)))))
                  (t
                    (when *log-on*
                      (push (list :decreased-support N (hypernode-degree-of-justification N))
                            *reasoning-log*))
                    (when *display?*
                      (princ "               The degree-of-justification of ") (princ N)
                      (princ " has decreased to ") (princ (hypernode-degree-of-justification N)) (terpri)
                      (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))))
               ((zerop (hypernode-degree-of-justification N))
                (when *log-on*
                  (push (list :defeated N) *reasoning-log*))
                (when *display?*
                  (princ "               ") (princ N) (princ " is defeated.") (terpri)
                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                (when (and *display?* *graphics-on*)
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "Hypernode ")
                    (speak-text (write-to-string (hypernode-number N)))
                    (speak-text "is defeated."))
                  (let ((posi (hypernode-position n *og*)))
                    (cond (posi (draw-just-defeated-node posi *og* n))
                          (t
                            (draw-n n *og* *nodes-displayed*)
                            (push n *nodes-displayed*)
                            (setf posi (hypernode-position n *og*))
                            (draw-just-defeated-node posi *og* n)))))))
         ))
      ((and *display?* *graphics-on*)
       (when *graphics-pause* (pause-graphics))
       (dolist (link links) (draw-n (hyperlink-target link) *og* *nodes-displayed*)))))
  (when (and *display?* *graphics-on*)
    (setf *nodes-displayed* (union (mapcar #'hyperlink-target links) *nodes-displayed*))))

(defun adopt-interest-in-Q&I-defeaters-for (sequent)
  (declare (ignore sequent))
  T)

#| This assumes that N is a reductio-supposition-node. |#
(defun base-reductio-supposition (N)
  (not (some #'interest-reductio (hypernode-generating-interests N))))

(defun base-test (R RA)
  (or (not (base-reductio-supposition (cdr R)))
      (every #'(lambda (x) (or (eq x R) (hypernode-non-reductio-supposition? (cdr x)))) RA)))

#| L is an ancestor of hyperlink link, whose target is node. |#
(defun link-ancestor (L link)
  (some #'(lambda (N) (member L (hypernode-hyperlinks N)))
        (hypernode-ancestors (hyperlink-target link))))

(defun recursively-compute-hypernode-ancestors (node ancestors)
  (dolist (L (hypernode-consequent-links node))
    (let* ((target (hyperlink-target L))
           (new-ancestors (set-difference ancestors (hypernode-ancestors target))))
      (when new-ancestors
        (setf (hypernode-ancestors target) (append new-ancestors (hypernode-ancestors target)))
        (recursively-compute-hypernode-ancestors target new-ancestors)))))

(defun compute-nearest-defeasible-ancestors (basis rule)
  (if (or (keywordp rule)
          (not (reason-defeasible-rule rule)))
    (mapcar #'genunion
            (gencrossproduct
              (mapcar #'hypernode-nearest-defeasible-ancestors basis)))
    (list nil)))

#| RA does not contain two different base-reductio-suppositions, and if RA contains a
base-reductio-supposition then for some generating-interest of the base-reductio-supposition,
every member of NRS is an interest-supposition-node of that interest. |#
(defun potent-suppositions (NRS RA)
  ; (setf nr nrs r ra); (break)
  ;; (step (potent-suppositions nr r))
  (every
    #'(lambda (R)
        (or (hypernode-non-reductio-supposition? (cdr R))
            (not (base-reductio-supposition (cdr R)))
            (and
              (every #'(lambda (x)
                         (or (eq (cdr x) (cdr R))
                             (hypernode-non-reductio-supposition? (cdr x))
                             (not (base-reductio-supposition (cdr x))))) RA)
              (or (> (length RA) 1)
                  (some
                    #'(lambda (in)
                        (every
                          #'(lambda (nr)
                              (member (cdr nr) (interest-supposition-nodes in)))
                          NRS))
                    (hypernode-generating-interests (cdr R)))
                  ))))
    RA))

(defun conclusion-data (basis instantiations discharge supposition)
  ; (setf b basis i instantiations d discharge s supposition)
  ;  (princ sequent) (terpri) (break)
  (let* ((RA nil)
         (NR nil)
         (sup nil)
         (instantiations+ instantiations)
         (B+ basis))
    (when B+
      (loop
        (setf RA
              (union= RA
                      (subset #'(lambda (x)
                                  (if (not (eq supposition t))
                                    (member (car x) supposition)
                                    (not (equal (car x) discharge))))
                              (match-sublis (mem1 instantiations+)
                                            (hypernode-reductio-ancestors (mem1 B+))))))
        (setf B+ (cdr B+))
        (when (null B+) (return))
        (setf instantiations+ (cdr instantiations+))))
    (when  ;; this blocks multiple instantiations of hypernode-reductio-ancestors
      (not (some
             #'(lambda (R)
                 (some #'(lambda (R*)
                           (and (not (eq R R*))
                                (eq (cdr R) (cdr R*))
                                (zerop (hypernode-readopted-supposition (cdr R)))))
                       RA))
             RA))
      (let ((instantiations+ instantiations)
            (B+ basis))
        (when B+
          (loop
            (setf
              NR
              (union= NR
                      (subset #'(lambda (x)
                                  (if (not (eq supposition t))
                                    (member (car x) supposition)
                                    (not (equal (car x) discharge))))
                              (match-sublis (mem1 instantiations+)
                                            (hypernode-non-reductio-supposition (mem1 B+))))))
            (setf B+ (cdr B+))
            (when (null B+) (return))
            (setf instantiations+ (cdr instantiations+)))))
      (when   ;; this blocks multiple instantiations of non-reductio-suppositions
        (and
          (not (some
                 #'(lambda (R)
                     (some #'(lambda (R*)
                               (and (not (eq R R*))
                                    (eq (cdr R) (cdr R*))
                                    (zerop (hypernode-readopted-supposition (cdr R)))))
                           NR))
                 NR))
          (potent-suppositions NR RA))
        (let ((instantiations+ instantiations)
              (variables (unionmapcar+ #'hypernode-variables basis))
              (new-vars nil))
          (dolist (b basis)
            (let ((b-sup (hypernode-supposition b))
                  (b-vars (setdifference (hypernode-supposition-variables b) (hypernode-variables b))))
              (dolist (var b-vars)
                ;; rewrite supposition-variables to avoid collision with formula-variables
                ;; of other members of the basis
                (when (member var variables)
                  (let ((new-var (make-interest-variable)))
                    (push new-var new-vars)
                    (setf b-sup (subst new-var var b-sup)))))
              (setf
                sup
                (union= sup
                        (subset #'(lambda (x) (not (equal x discharge)))
                                (match-sublis (mem1 instantiations+)
                                              b-sup))))
              (setf instantiations+ (cdr instantiations+)))))
        (list RA NR (if (eq supposition t) sup (union= sup supposition)))))))

#| The following is the default computation of interest-priority for defeaters. |#
(defun defeater-priority (interest)
  (declare (ignore interest))
  *base-priority*)

(defun contradicting-nodes (n1 n2)
  (assoc (hypernode-c-list n1) (c-list-contradictors (hypernode-c-list n2))))

#| Combining the suppositions of the nodes in basis yields an inconsistent supposition. |#
(defun inconsistent-supposition (basis)
  (let ((B (cdr basis)) (n (mem1 basis)))
    (loop
      (when
        (some
          #'(lambda (m)
              (or
                (some #'(lambda (bm)
                          (or
                            (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                  (hypernode-reductio-ancestors n))
                            (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                  (hypernode-non-reductio-supposition n))))
                      (hypernode-reductio-ancestors m))
                (some #'(lambda (bm)
                          (or
                            (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                  (hypernode-reductio-ancestors n))
                            (some #'(lambda (bn) (contradicting-nodes (cdr bm) (cdr bn)))
                                  (hypernode-non-reductio-supposition n))))
                      (hypernode-non-reductio-supposition m))))
          B)
        (return t))
      (when (null (cdr b)) (return))
      (setf n (mem1 b))
      (setf b (cdr b)))))

(defun deductive-consequences (node)
  (let ((descendants (list node))
        (nodes (list node)))
    (loop
      (let ((node (car nodes)))
        (setf nodes (cdr nodes))
        (dolist (L (hypernode-consequent-links node))
          (when (not (hyperlink-defeasible? L))
            (let ((N (hyperlink-target L)))
              (when (not (member N descendants))
                (push N descendants)
                (push N nodes)))))
        (when (null nodes) (return descendants))))))

(defun supposition-variables (sup)
  (unionmapcar= #'formula-hypernode-variables sup))

(defun make-new-conclusion
  (sequent deductive-only reductio-ancestors non-reductio-supposition)
  (let* ((c-vars (formula-hypernode-variables (sequent-formula sequent)))
         (sup (sequent-supposition sequent))
         (i-vars (supposition-variables sup))
         (node
           (make-hypernode
             :hypernode-number (incf *hypernode-number*)
             :hypernode-sequent sequent
             :hypernode-formula (sequent-formula sequent)
             :hypernode-supposition sup
             :hypernode-kind :inference
             :hypernode-deductive-only deductive-only
             :hypernode-variables c-vars
             :hypernode-supposition-variables i-vars
             :hypernode-non-reductio-supposition non-reductio-supposition
             :hypernode-reductio-ancestors reductio-ancestors
             )))
    node))

(defun merge-unifiers* (u1 u2)
  (list (merge-matches* (mem1 u1) (mem1 u2))
        (merge-matches* (mem2 u1) (mem2 u2))))

(defun non-circular (sequent ancestors)
  (every
    #'(lambda (b)
        (or (not (is-inference b))
            (not (subsumes (hypernode-sequent b) sequent))))
    ancestors))

(defstruct (percept
	    (:print-function (lambda (percept stream depth)
			       (declare (ignore depth))
			       (princ "#<percept: " stream)
			       (princ (pretty (percept-content percept)) stream)
			       (princ ">" stream)))
	    (:conc-name nil))
  (percept-number 0)
  (percept-content nil)
  (percept-clarity 0)
  (percept-date 0))

#| This converts the supporting-nodes of node and its descendants to non-deductive-only
provided they are not inferred from other deductive-only conclusions.  It returns the list of
converted nodes. |#
(defun convert-from-deductive-only (node)
  (setf (hypernode-deductive-only node) nil)
  (let ((nodes (list node)))
    (dolist (L (hypernode-consequent-links node))
      (let ((N (hyperlink-target L)))
        (when
          (and (hypernode-deductive-only N)
               (not (some
                      #'(lambda (L)
                          (some
                            #'(lambda (b) (hypernode-deductive-only b))
                            (hyperlink-basis L)))
                      (hypernode-hyperlinks N))))
          (setf nodes
                (union nodes (convert-from-deductive-only N))))))
    nodes))

#| This is the default computation of degree-of-preference for an interest, where
priority is the interest-priority and complexity is the complexity of the interest-sequent. |#
(defun interest-preference (priority complexity)
  (if (zerop complexity) priority (/ priority complexity)))

(defun display-inference-queue ()
  (princ "---------------------------------------------------------------------------") (terpri)
  (princ "inference-queue: ") (terpri)
  (dolist (Q *inference-queue*) (princ "  ") (princ (queue-item Q))
    (princ "  degree-of-preference = ")
    (princ (float (/ (truncate (* 10000 (queue-degree-of-preference Q))) 10000)))
    (let ((priority
            (cond ((eq (queue-item-kind q) :conclusion)
                   (hypernode-discounted-node-strength (queue-item q)))
                  ((eq (queue-item-kind q) :query) 1.0)
                  ((eq (queue-item-kind q) :interest) (interest-priority (queue-item q)))
		  (t (error "UNEXPECTED")))))
      (princ "  priority = ")
      (princ (float (/ (truncate (* 1000 priority)) 1000))))
    (terpri)))

(defun formula-complexity (formula)
  (cond ((mem formula *skolem-free-suppositions*) 0)
        (t (complexity formula))))

(defun sequent-complexity (sequent)
  (let ((sup (sequent-supposition sequent))
        (formula (sequent-formula sequent)))
    (let ((complexity
            (cond (sup
                    (+ (max 1 (formula-complexity formula))
                       (apply
                         '+ (mapcar
                              #'(lambda (P)
                                  (cond ((mem P *skolem-free-suppositions*) 0)
                                        (t (complexity P))))
                              sup))))
                  (t (max 1 (formula-complexity formula))))))
      ;  (when *display?*
      ;       (princ "The complexity of ") (print-sequent sequent) (princ " is ") (princ complexity) (terpri))
      complexity)))

#|
(defun sequent-complexity (sequent)
  (let ((sup (sequent-supposition sequent))
        (formula (sequent-formula sequent))
        (length 0))
    (let ((complexity
            (cond (sup
                    (+ (max 1 (formula-complexity formula))
                       (apply
                         '+ (mapcar
                              #'(lambda (P)
                                  (cond ((mem P *skolem-free-suppositions*) 0)
                                        (t (incf length) (complexity P))))
                              sup))))
                  (t (max 1 (formula-complexity formula))))))
      ;  (when *display?*
      ;       (princ "The complexity of ") (print-sequent sequent) (princ " is ") (princ complexity) (terpri))
      (if (> length 2) (* complexity (expt 10 (* length length))) complexity))))
|#

#| When a priority-interest is encountered, it is placed at the front of the inference-queue. |#
(defun queue-interest (interest priority)
  ; (when (eq interest (interest 7)) (setf i interest p priority) (break))
  ;; (step (queue-interest i p))
  (let* ((complexity (sequent-complexity (interest-sequent interest)))
         (queue-node
           (make-inference-queue-node
             :queue-number (incf *queue-number*)
             :queue-item interest
             :queue-item-kind :interest
             :queue-item-complexity complexity
             :queue-discounted-strength priority
             :queue-degree-of-preference (interest-preference priority complexity))))
    (setf (interest-queue-node interest) queue-node)
    (let ((n (interest-number interest)))
      (cond ((member n *priority-interests*)
             (when *display?* (princ "Giving priority to interest ") (princ n) (terpri))
             (setf *inference-queue* (cons queue-node *inference-queue*))
             (when *display?* (display-inference-queue)))
            (t (setf *inference-queue*
                     (ordered-insert queue-node *inference-queue* #'i-preferred)))))
    ; (when *display?* (princ "                                        Preference = ")
    ;               (princ (float (/ (truncate (* 10000 (queue-degree-of-preference queue-node))) 10000)))
    ;               (terpri))
    ))

(defun discharged? (interest degree)
  (let ((discharged-degree (interest-discharged-degree interest)))
    (and discharged-degree
         (>= discharged-degree degree))))

(defun interest-link-priority (link interest-priority interest)
  (if (or (link-defeat-status link)
          (let ((rn (link-resultant-interest link)))
            (discharged? rn (interest-maximum-degree-of-interest rn)))
          (and interest (discharged? interest (interest-maximum-degree-of-interest interest))))
    *base-priority*
    interest-priority))

(defun re-queue-interest (link interest-priority interest degree)
  ; (when (eq interest (interest 7)) (setf l link p interest-priority i interest d degree) (break))
  ;;  (step (re-queue-interest l p i d))
  (let ((Q (interest-queue-node interest)))
    (cond (Q
            (let ((preference
                    (interest-preference
                      (interest-link-priority link interest-priority interest)
                      (sequent-complexity (interest-sequent interest)))))
              (when (> preference (queue-degree-of-preference Q))
                (setf *inference-queue*
                      (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))))
          (t
            (let ((old-degree (interest-last-processed-degree-of-interest interest)))
              (when (or (null old-degree) (< degree old-degree))
                (queue-interest interest (interest-link-priority link interest-priority interest))
                ))))))

(defun reason-code* (P variables descriptor)
  (cond ((listp P)
         (let ((description nil) (elt-num 1) (stop nil))
           (cond
             ;; This handles notational variants.
             ((or (eq (car p) 'all) (eq (car P) 'some))
              (setf P
                    (cons (car P) (subst (list 'q-var (incf *quantifier-number*)) (mem2 P) (cddr P)))))
             ((and (symbolp (car P))
                   (not (member (car P) *operators*))
                   (not (member (car P) '(~ & v -> <-> all some ? @ at throughout))))
              (setf P (list (car P)))))
           (block stop-here
                  (dolist (Q P)
                    (cond
                      ((member Q variables)
                       (setf stop t)
                       (return-from stop-here))
                      (t
                        (let ((Q-descriptor (cons elt-num descriptor)))
                          (cond ((not (listp Q))
                                 (push (cons (reverse Q-descriptor) Q) description))
                                (t
                                  (multiple-value-bind (d st) (reason-code* Q variables Q-descriptor)
                                    (setf description (append d description))
                                    (when st (setf stop t) (return-from stop-here))))))))
                    (incf elt-num)))
           (values description stop)))
        ((not (member P variables)) (values (list (cons descriptor P)) nil))))

#| This is like premise-code, but it stops producing code when it comes to the first variable. |#
(defun reason-code (P variables)
  (when P
    (setf *quantifier-number* 0)
    (reverse (reason-code* P variables nil))))

(defun rectify-binding (binding0 unifier ip)
  (let ((binding
          (mapcar
            #'(lambda (assoc)
                (cons (car assoc) (match-sublis (mem2 unifier) (cdr assoc))))
            (ip-binding ip))))
    (dolist (v (fp-variables (ip-premise ip)))
      (when (null (assoc v (ip-binding ip)))
        (push (cons v (match-sublis (mem1 unifier) (cdr (assoc v binding0)))) binding)))
    binding))

(defun reductio-supposition (node) (eq (hypernode-justification node) :reductio-supposition))

;(defun remove-double-negation (P)
;    (if (and (negationp P) (negationp (negand P))) (negand (negand P)) P))

(defun remove-double-negation (P)
  (cond
    ((listp P)
     (cond ((and (negationp P) (negationp (negand P))) (negand (negand P)))
           ((or (member (car P) *operators*)
                (member (car P) '(& v <-> ->))
                (and (listp (car P))
                     (or (eq (caar P) 'all)
                         (eq (caar P) 'some))))
            (mapcar #'remove-double-negation P))
           (t P)))
    (t P)))

(defun set-def-binding (def-instantiator var binding)
  (multiple-value-bind
    (val binding new-vars)
    (funcall def-instantiator binding)
    (values
      (cons (cons var val) (remove (assoc var binding) binding :test 'equal))
      new-vars (cons (e-assoc var binding) val))))

(defun display-instantiated-premise (ip)
  (terpri)
  (princ "  Constructing instantiated-premise #") (princ (ip-number ip)) (terpri)
  (princ "  next premise:  ")
  (prinp (match-sublis (ip-binding ip) (fp-formula (ip-premise ip))))
  (terpri) (princ "  by ")
  (princ (ip-reason ip)) (princ ",  basis = ")
  (print-list (mapcar #'hypernode-number (ip-basis ip)))
  (princ " with clues ") (print-list (mapcar #'hypernode-number (ip-clues ip)) nil)
  (terpri) (terpri))

#| (mem3 premise) will be a function which, when applied to a formua, returns a binding.
(mem4 premise) will be the list of premise-variables occurring therein. |#
(defun store-instantiated-premise-at-d-node
  (reason premise node c-list binding instantiations ip0 d-node remaining-premises)
  (when node (setf c-list (hypernode-c-list node)))
  (let* ((ip
           (make-instantiated-premise
             :reason reason
             :number (incf *ip-number*)
             :premise premise
             :binding binding
             :basis (if (and ip0 (not (fp-clue? (ip-premise ip0))))
                      (cons node (ip-basis ip0)))
             :remaining-premises remaining-premises
             :clues (when ip0
                      (if (fp-clue? (ip-premise ip0)) (cons node (ip-clues ip0)) (ip-clues ip0)))
             :d-node d-node
             :instantiations (if ip0 instantiations)
             :used-premise-variables
             (if ip0 (union (fp-variables premise) (ip-used-premise-variables ip0))
               (fp-variables premise))
             :used-variables (if ip0 (union (c-list-variables c-list) (ip-used-variables ip0)))
             :number (incf *ip-number*)
             )))
    (push ip (d-node-forwards-reasons d-node))
    (setf (ip-d-node ip) d-node)
    (push ip (c-list-generated-instantiated-premises c-list))
    (if ip0 (push ip (ip-derived-premises ip0)))
    (when *display?* (display-instantiated-premise ip))
    ip))

#| Test is the final member of the formula-profile for the hypernode-formula. |#
(defun store-instantiated-premise-at-new-d-node
  (reason premise node c-list binding instantiations ip d-node test remaining-premises)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push dn *discrimination-net*)
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (store-instantiated-premise-at-d-node
      reason premise node c-list binding instantiations ip dn remaining-premises)))

(defun index-instantiated-premise-at-new-nodes
  (reason premise profile node c-list binding instantiations ip d-node test remaining-premises)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (push dn *discrimination-net*)
    (let ((desc (cdr profile)))
      (cond (desc (index-instantiated-premise-at-new-nodes
                    reason premise desc node c-list binding instantiations
                    ip dn (car profile) remaining-premises))
            (t (store-instantiated-premise-at-new-d-node
                 reason premise node c-list binding instantiations ip
                 dn (car profile) remaining-premises))))))

(defun index-instantiated-premise
  (reason premise profile node c-list binding instantiations ip d-node remaining-premises)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node)))
        (new-profile (cdr profile)))
    (cond (dn
            (cond
              (new-profile
                (index-instantiated-premise
                  reason premise new-profile node c-list binding
                  instantiations ip dn remaining-premises))
              (t (store-instantiated-premise-at-d-node
                   reason premise node c-list binding instantiations
                   ip dn remaining-premises))))
          (new-profile
            (index-instantiated-premise-at-new-nodes
              reason premise new-profile node c-list binding instantiations
              ip d-node (car profile) remaining-premises))
          (t
            (store-instantiated-premise-at-new-d-node
              reason premise node c-list binding instantiations
              ip d-node (car profile) remaining-premises)))))

(defun store-interest-scheme-at-d-node (interest-scheme d-node)
  (push interest-scheme (d-node-interest-schemes d-node))
  (setf (is-d-node interest-scheme) d-node)
  interest-scheme)

#| Test is the final member of the formula-profile for the hypernode-formula. |#
(defun store-interest-scheme-at-new-d-node (interest-scheme  d-node test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push dn *discrimination-net*)
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (store-interest-scheme-at-d-node interest-scheme dn)))

(defun index-interest-scheme-at-new-nodes (interest-scheme d-node profile test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (push dn *discrimination-net*)
    (let ((desc (cdr profile)))
      (cond (desc (index-interest-scheme-at-new-nodes interest-scheme dn desc (car profile)))
            (t (store-interest-scheme-at-new-d-node interest-scheme dn (car profile)))))))

(defun index-interest-scheme (interest-scheme profile d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node)))
        (new-profile (cdr profile)))
    (cond (dn
            (cond
              (new-profile
                (index-interest-scheme interest-scheme new-profile dn))
              (t (store-interest-scheme-at-d-node interest-scheme  dn))))
          (new-profile
            (index-interest-scheme-at-new-nodes interest-scheme d-node new-profile (car profile)))
          (t (store-interest-scheme-at-new-d-node interest-scheme d-node (car profile))))))

#| This returns the ip at which the premise is stored. |#
(defun store-interest-scheme (interest-scheme profile d-node)
  (cond
    (profile (index-interest-scheme interest-scheme profile d-node))
    (t (store-interest-scheme-at-d-node interest-scheme d-node))))

(defun subsumed (node basis sequent NDA non-reductio-supposition rule binding d-node)
  ; (when (equal *hypernode-number* 9)
  ;      (setf n node b basis s sequent nd nda nr non-reductio-supposition r rule bi binding dn d-node)  (break))
  ;; (step (subsumed n b s nd nr r bi dn))
  (let ((defeasible? (and (not (keywordp rule)) (reason-defeasible-rule rule))))
    (when defeasible? (setf NDA (list (list node))))
    (cond
      (node
        (and
          (not defeasible?)
          (every #'(lambda (Y)
                     (some #'(lambda (X) (subsetp X Y)) (hypernode-nearest-defeasible-ancestors node)))
                 NDA)))
      (t
        (let ((formula (sequent-formula sequent)))
          (some
            #'(lambda (cl)
                (and
                  (c-list-nodes cl)
                  (let* ((P (c-list-formula cl))
                         (f-vars (c-list-variables cl))
                         (m (match P formula f-vars)))
                    (when (and m (equal formula (match-sublis m P)))
                      (let ((sup (sequent-supposition sequent)))
                        (some
                          #'(lambda (N)
                              ; (and
                              (let* ((N-sup (match-sublis m (hypernode-supposition N)))
                                     (vars
                                       (setdifference
                                         (unionmapcar= #'formula-hypernode-variables (hypernode-supposition N))
                                         f-vars))
                                     (sm (set-match N-sup sup vars)))
                                (and
                                  SM
                                  (let ((NR (match-sublis m (hypernode-non-reductio-supposition N))))
                                    (some
                                      #'(lambda (s)
                                          (subsetp= (match-sublis (mem2 s) NR) non-reductio-supposition))
                                      sm))
                                  (cond
                                    (defeasible?
                                      (let ((binding* (match-sublis m binding)))
                                        (some
                                          #'(lambda (L)
                                              (and
                                                (eq rule (hyperlink-rule L))
                                                (equal binding* (hyperlink-binding L))
                                                (== (unionmapcar+ #'hypernode-nearest-defeasible-ancestors
                                                                  basis)
                                                    (unionmapcar+ #'hypernode-nearest-defeasible-ancestors
                                                                  (hyperlink-basis L)))))
                                          (hypernode-hyperlinks N))))
                                    (t
                                      (every
                                        #'(lambda (Y)
                                            (some
                                              #'(lambda (X) (subsetp X Y)) (hypernode-nearest-defeasible-ancestors N)))
                                        NDA)))))
                              ; (or (progn (princ "*** ")
                              ;           (princ sequent) (princ " is subsumed by ") (princ N) (terpri))
                              ;       t))
                              )
                          (c-list-nodes cl)))))))
            (d-node-c-lists d-node)))))))

(defun subsuming-supposition (supposition)
  (let* ((sup
           (find-if
             #'(lambda (N)
                 (let* ((P (hypernode-formula N))
                        (f-vars (hypernode-variables N))
                        (m (match P supposition f-vars)))
                   (and m (equal supposition (match-sublis m P)))))
             *non-reductio-supposition-nodes*)))
    (when (null sup)
      (setf sup
            (find-if
              #'(lambda (N)
                  (let* ((P (hypernode-formula N))
                         (f-vars (hypernode-variables N))
                         (m (match P supposition f-vars)))
                    (and m (equal supposition (match-sublis m P)))))
              *reductio-supposition-nodes*)))
    sup))

(defun unifying-nodes (interest)
  (let ((nodes nil))
    (dolist (cl (i-list-corresponding-c-lists (interest-i-list interest)))
      (dolist (c (c-list-nodes (mem1 cl)))
        (push c nodes)))
    nodes))

#| This returns deductive-node. |#
(defun validating-deductive-node (S deductive-rule?)
  (let ((c-list (c-list-for (sequent-formula S))))
    (when c-list
      (let ((sup (sequent-supposition S)))
        (find-if
          #'(lambda (c)
              (and (deductive-node c)
                   (or (not (hypernode-deductive-only c)) deductive-rule?)
                   (subsetp= (hypernode-supposition c) sup)))
          (c-list-nodes c-list))))))

(defun display-interest-scheme (interest-scheme)
  (princ "  Constructing interest-scheme #") (princ (is-number interest-scheme))
  (princ " for ") (princ (is-target-interest interest-scheme)) (terpri)
  (princ "  next premise:  ")
  (prinp (match-sublis (is-binding interest-scheme) (fp-formula (is-premise interest-scheme))))
  (terpri) (princ "  by ")
  (princ (ip-reason interest-scheme)) (princ ",  basis = ")
  (print-list (mapcar #'hypernode-number (is-basis interest-scheme)))
  (princ " with clues ") (print-list (mapcar #'hypernode-number (is-clues interest-scheme)) nil)
  (terpri) (terpri))

(labels ()

  #| Rule is either a member of *forwards-reasons* or *backwards-reasons*,
  or keyword describing an inference (:given, :Q&I, or :supposition).  basis
  is a list of conclusions.  If supposition is not T, it is added to the supposition.  |#
  (defun DRAW-CONCLUSION
    (formula basis rule instantiations discount depth interests defeasible?
             &key interest motivators binding link (supposition t) clues)
    (when (and formula (not (some #'hypernode-cancelled-node basis))
               (not (inconsistent-supposition basis)))
      (setf basis (reverse basis))
      (setf instantiations (reverse instantiations))
      (let* ((NDA (compute-nearest-defeasible-ancestors basis rule))
             (discharge (if (backwards-reason-p rule)
                          (remove-double-negation (match-sublis binding (b-reason-discharge rule)))))
             (CD (conclusion-data basis instantiations discharge supposition)))
        (when CD
          (let* ((RA (mem1 CD))
                 (NR (mem2 CD))
                 (sup (mem3 CD))
                 (sequent (list sup formula))
                 (d-node (d-node-for formula))
                 (c-list (if d-node (fetch-c-list-for formula d-node)))
                 (proof-nodes (if c-list (c-list-nodes c-list)))
                 (node (find-if #'(lambda (c)
                                    (and (eq (hypernode-kind c) :inference)
                                         (== (hypernode-supposition c) sup)))
                                proof-nodes))
                 (new-node? (null node)))
            (when
              (and
                (not (some #'(lambda (f) (mem (neg f) sup)) sup))
                (or (null d-node)
                    (not (subsumed node basis sequent NDA NR rule binding d-node))))
              (let* ((deductive-only (and (not (eq rule :reductio))
                                          (some #'hypernode-deductive-only basis))))
                (when (and node (hypernode-deductive-only node) (not deductive-only))
                  (setf (hypernode-deductive-only node) nil))
                (when (null node)
                  (setf node (make-new-conclusion sequent deductive-only RA NR)))
                (let ((old-degree (current-maximal-degree-of-justification node))
                      (hyperlink
                        (build-hyperlink
                          basis clues rule discount node NDA binding link instantiations depth defeasible?)))
                  (cond
                    ((null hyperlink)
                     (decf *hyperlink-number*)
                     (when new-node? (decf *hypernode-number*)))
                    (t
                      (setf (hypernode-motivating-nodes node) (union clues motivators))
                      (when new-node?
                        (push node *hypergraph*)
                        (store-hypernode-with-c-list
                          node (sequent-formula sequent) c-list))
                      (when interest
                        (push interest (hypernode-enabling-interests node))
                        (push node (interest-enabled-nodes interest)))
                      (when *trace* (indent depth) (princ "DRAW CONCLUSION: ")
                        (princ node) (terpri))
                      (when (read-char-no-hang) (clear-input) (throw 'die nil))
                      (let* ((i-lists (c-list-corresponding-i-lists (hypernode-c-list node)))
                             (increased-justification?
                               (or new-node? (> (hypernode-maximal-degree-of-justification node) old-degree)))
                             (cancellations
                               (when increased-justification?
                                 (discharge-interest-in-defeaters node i-lists old-degree new-node?))))
                        (when *display?* (display-hyperlink hyperlink))
                        (adopt-interest-in-defeaters-for hyperlink instantiations binding)
                        (push hyperlink *new-links*)
                        ; (update-beliefs hyperlink node)
                        (dolist (node* cancellations) (cancel-node node* (if *trace* depth 0)))
                        (when (not (hypernode-cancelled-node node))
                          (when increased-justification?
                            (discharge-interest-in
                              node i-lists old-degree new-node? (1+ depth) interests :interest interest)
                            (cond (*use-reductio*
                                    (discharge-immediate-reductios
                                      node old-degree new-node? (1+ depth) interests interest))))
                          (when new-node? (invert-contradictions node instantiations (1+ depth)))
                          (cancel-subsumed-links hyperlink depth)))))))
              nil))))))

  (defun cancel-subsumed-links (link depth)
    ; (when (equal link (hyperlink 14)) (break))
    ;; (step (cancel-subsumed-links (hyperlink 14) 0))
    (when (not (hyperlink-defeasible? link))
      (let* ((node (hyperlink-target link))
             (formula (hypernode-formula node))
             (f-vars (hypernode-variables node)))
        (dolist (cl (d-node-c-lists (c-list-d-node (hypernode-c-list node))))
          (let* ((P (c-list-formula cl))
                 (m (match formula P f-vars)))
            (when (and m (equal P (match-sublis m formula)))
              (let* ((sup (match-sublis m (hypernode-supposition node)))
                     (vars (setdifference (unionmapcar #'formula-hypernode-variables sup) f-vars))
                     (NR (match-sublis m (hypernode-non-reductio-supposition node))))
                (dolist (M (c-list-nodes cl))
                  (cond
                    ((eq M node)
                     (let ((NDA (hyperlink-nearest-defeasible-ancestors link)))
                       (dolist (L (hypernode-hyperlinks M))
                         (when
                           (and (not (eq L link))
                                (not (hyperlink-defeasible? L)))
                           (let ((NDA* (hyperlink-nearest-defeasible-ancestors L)))
                             (when (every
                                     #'(lambda (Y)
                                         (some #'(lambda (X) (subsetp X Y)) NDA))
                                     NDA*)
                               (delete-arguments L M link depth)
                               (when *display?*
                                 (princ link) (princ " subsumes ") (princ L) (terpri))
                               ; (pull L (hypernode-hyperlinks M))
                               ))))))
                    ((<= (length (hypernode-supposition node)) (length (hypernode-supposition M)))
                     (let* ((M-sup (hypernode-supposition M))
                            (SM (set-match sup M-sup vars)))
                       (when
                         (and SM
                              (some
                                #'(lambda (s)
                                    (subsetp=
                                      (match-sublis (mem2 s) NR)
                                      (hypernode-non-reductio-supposition M)))
                                SM))
                         (let ((NDA (hyperlink-nearest-defeasible-ancestors link)))
                           (dolist (L (hypernode-hyperlinks M))
                             (when
                               (and (not (hypernode-cancelled-node (hyperlink-target L)))
                                    (not (link-ancestor L link))
                                    (let ((NDA* (hyperlink-nearest-defeasible-ancestors L)))
                                      (every
                                        #'(lambda (Y)
                                            (some #'(lambda (X) (subsetp X Y)) NDA))
                                        NDA*)))
                               (delete-arguments L M link depth)
                               (when *display?*
                                 (princ link) (princ " subsumes ") (princ L) (terpri))
                               )))))))))))))))

  #| L0 subsumes link which supports node. |#
  (defun delete-arguments (link node L0 depth)
    (declare (special *deleted-arguments*))
    ; (when (equal link (hyperlink 10)) (setf l link n node ll l0 d depth) (break))
    ;; (step (delete-arguments l n ll d t))
    (setf *deleted-arguments* nil)
    (when (and (not (member link *deleted-arguments*))
               (not (hypernode-cancelled-node node))
               (not (link-ancestor link L0)))
      (push link *deleted-arguments*)
      ; (princ "**** Deleting ") (princ link) (terpri)
      (pull link (hypernode-hyperlinks node))
      (cond ((null (hypernode-hyperlinks node)) (cancel-node node (if *trace* depth 0)))
            (t
              (dolist (L (hypernode-hyperlinks node))
                (let ((NDA
                        (cond ((hyperlink-defeasible? node)
                               (mapcar #'genunion
                                       (gencrossproduct
                                         (mapcar #'hypernode-nearest-defeasible-ancestors
                                                 (hyperlink-basis L)))))
                              (t (list (list node))))))
                  (dolist (X NDA)
                    (when
                      (not (some #'(lambda (Y) (subsetp= Y X))
                                 (hypernode-nearest-defeasible-ancestors node)))
                      (dolist (Y (hypernode-nearest-defeasible-ancestors node))
                        (when (subsetp= X Y) (pull Y (hypernode-nearest-defeasible-ancestors node))))
                      (push X (hypernode-nearest-defeasible-ancestors node))))
                  (recursively-compute-nearest-defeasible-ancestors node)))
              (let ((ancestors
                      (unionmapcar+
                        #'(lambda (L)
                            (union (hyperlink-basis L)
                                   (unionmapcar+ #'hypernode-ancestors (hyperlink-basis L))))
                        (hypernode-hyperlinks node))))
                (setf (hypernode-ancestors node) ancestors)
                (recursively-compute-hypernode-ancestors node ancestors)
                )))))

  (defun recursively-compute-nearest-defeasible-ancestors
    (node &optional nodes-done)
    (push node nodes-done)
    (dolist (L (hypernode-consequent-links node))
      (when (not (hyperlink-defeasible? L))
        (let ((NDA
                (mapcar #'genunion
                        (gencrossproduct
                          (mapcar #'hypernode-nearest-defeasible-ancestors (hyperlink-basis L)))))
              (target (hyperlink-target L)))
          (let ((old-NDA (hypernode-nearest-defeasible-ancestors node)))
            (dolist (X NDA)
              (when
                (not (some #'(lambda (Y) (subsetp Y X))
                           (hypernode-nearest-defeasible-ancestors target)))
                (dolist (Y (hypernode-nearest-defeasible-ancestors target))
                  (when (subsetp X Y) (pull Y (hypernode-nearest-defeasible-ancestors target))))
                (push X (hypernode-nearest-defeasible-ancestors target))
                (invert-contradictions-retrospectively node X old-NDA))))
          (when (not (member target nodes-done))
            (recursively-compute-nearest-defeasible-ancestors target nodes-done))))))

  (defun invert-contradictions-retrospectively (node NDA old-NDA)
    (let ((c-list (hypernode-c-list node)))
      (dolist (nl (c-list-contradictors c-list))
        (let ((unifier (reverse (mem2 nl))))
          (dolist (node* (c-list-nodes (mem1 nl)))
            (dolist (u (appropriately-related-node-suppositions node node* unifier))
              (dolist (N NDA)
                (when
                  (and (not (some #'(lambda (Y) (member N Y)) old-NDA))
                       (set-unifier
                         (match-sublis (mem2 u) (hypernode-supposition node*))
                         (hypernode-supposition N)
                         (append (hypernode-variables node) (hypernode-variables node*))
                         (hypernode-variables N)))
                  (dolist (L (hypernode-hyperlinks N))
                    (invert-contradiction L node node* NDA N u 0))))))))))

  (defun invert-contradiction  (L node node* D N instantiations depth)
    (let ((variables nil)
          (reverse-binding nil)
          (reverse-binding* nil)
          (binding* nil))
      (dolist (b (hyperlink-binding L))
        (cond ((or (and (listp (cdr b)) (skolem-function (mem1 (cdr b))))
                   (skolem-function (cdr b))
                   (conclusion-variable (cdr b)))
               (push (car b) variables)
               (push (cons (cdr b) (car b)) reverse-binding)
               (push (cons (cdr b) (make-interest-variable)) reverse-binding*))
              (t (push b binding*))))
      (let* ((S (hypernode-sequent (hyperlink-target L)))
             (B (hyperlink-basis L))
             (supposition
               (subset
                 #'(lambda (P)
                     (every #'(lambda (b) (not (occur (car b) P :test 'equal))) reverse-binding))
                 (sequent-supposition S)))
             (sup-remainder (setdifference (sequent-supposition S) supposition))
             (antecedent (match-sublis reverse-binding sup-remainder :test 'equal))
             (antecedent*
               (gen-conjunction
                 (match-sublis reverse-binding* sup-remainder :test 'equal)))
             (antecedent-variables
               (subset #'(lambda (v) (occur v antecedent)) variables))
             (sup
               (if sup-remainder
                 (generalized-e-gen antecedent-variables (gen-conjunction antecedent))))
             (new-sup (if sup (cons sup supposition) supposition))
             (formula (match-sublis reverse-binding* (sequent-formula S)))
             (base
               (mapcar
                 #'(lambda (c m)
                     (cond ((is-desire c)
                            (list 'I_desire_that
                                  (match-sublis reverse-binding*
                                                (match-sublis m (hypernode-formula c)))))
                           ((is-percept c)
                            (let ((time (percept-date (hypernode-justification c))))
                              (list 'it-appears-to-me-that
                                    (match-sublis reverse-binding*
                                                  (match-sublis m (mem2 (hypernode-formula c))))
                                    (list 'closed time time))))
                           (t (match-sublis reverse-binding*
                                            (match-sublis m (hypernode-formula c)) :test 'equal))))
                 B instantiations))
             (rebutting-defeater
               (cond (antecedent* (conj antecedent* (conj (gen-conjunction base) (neg formula))))
                     (variables (conj (gen-conjunction base) (neg formula)))
                     (t (neg formula)))))
        (draw-conclusion
          rebutting-defeater (adjoin node* (remove N D))
          (read-from-string
            (cat-list (list ":inversion_from_contradictory_nodes_"
                            (string-rep (hypernode-number node))
                            "_and_" (string-rep (hypernode-number node*)))))
          nil 1 (1+ depth) nil nil :motivators (list node) :supposition new-sup))))

  (defun invert-contradictions-from-new-hyperlink (link instantiations)
    (let ((target (hyperlink-target link)))
      (dolist (node (deductive-consequences target))
        (let ((c-list (hypernode-c-list node)))
          (dolist (nl (c-list-contradictors c-list))
            (let ((unifier (mem2 nl)))
              (dolist (node* (c-list-nodes (mem1 nl)))
                (when (not (deductive-node node*))
                  (dolist (u (appropriately-related-node-suppositions node* node unifier))
                    (when (set-unifier (match-sublis (mem2 u) (hypernode-supposition node))
                                       (hypernode-supposition target)
                                       (append (hypernode-variables node) (hypernode-variables node*))
                                       (hypernode-variables target))
                      (dolist (D (hypernode-nearest-defeasible-ancestors node))
                        (invert-contradiction link node node* D target instantiations 0))))))))))))

  (defun invert-contradictions (node instantiations depth)
    ; (when (eq node (node 43)) (break))
    ;; (step (invert-contradictions (node 43) 0))
    (let ((c-list (hypernode-c-list node)))
      (dolist (nl (c-list-contradictors c-list))
        (let* ((unifier (mem2 nl))
               (unifier* (reverse unifier)))
          (dolist (node* (c-list-nodes (mem1 nl)))
            (when (not (deductive-node node*))
              (dolist (u (appropriately-related-node-suppositions node* node unifier))
                (dolist (D (hypernode-nearest-defeasible-ancestors node))
                  (dolist (N D)
                    (when (set-unifier
                            (match-sublis (mem2 u) (hypernode-supposition node))
                            (hypernode-supposition N)
                            (append (hypernode-variables node) (hypernode-variables node*))
                            (hypernode-variables N))
                      (dolist (L (hypernode-hyperlinks N))
                        (invert-contradiction L node node* D N instantiations depth)))))))
            (when (not (deductive-node node))
              (dolist (u (appropriately-related-node-suppositions node node* unifier*))
                (dolist (D (hypernode-nearest-defeasible-ancestors node*))
                  (dolist (N D)
                    (when (set-unifier
                            (match-sublis (mem2 u) (hypernode-supposition node*))
                            (hypernode-supposition N)
                            (append (hypernode-variables node) (hypernode-variables node*))
                            (hypernode-variables N))
                      (dolist (L (hypernode-hyperlinks N))
                        (invert-contradiction L node* node D N instantiations depth))))))))))))

  (defun draw-reductio-conclusion (P node node* R Y Y* RA NR interest unifier depth d-interests)
    (when (and (not (hypernode-cancelled-node node))
               (not (hypernode-cancelled-node node*))
               (not (mem (neg P) Y)) (not (mem (neg P) Y*))
               (not (inconsistent-supposition (list node node*)))
               ;; This prevents a reductio-ancestor from being instantiated in two different ways
               (not (some
                      #'(lambda (R)
                          (some #'(lambda (R*)
                                    (and (not (eq R R*))
                                         (eq (cdr R) (cdr R*))
                                         (zerop (hypernode-readopted-supposition (cdr R)))))
                                RA))
                      RA))
               ;; This prevents a non-reductio-supposition from being instantiated in two different ways
               (not (some
                      #'(lambda (R)
                          (some
                            #'(lambda (R*)
                                (and (not (eq R R*))
                                     (eq (cdr R) (cdr R*))
                                     (zerop (hypernode-readopted-supposition (cdr R)))))
                            NR))
                      NR)))
      (let ((sup (remove-if-equal P (union= Y Y*))))
        (when (not (some #'(lambda (f) (mem (neg f) sup)) sup))
          ; (setf sup (order sup #'lessp))
          (let* ((P* (neg P))
                 (sequent (list sup P*))
                 (reductio-ancestors (remove-if-equal R RA))
                 (non-reductio-supposition
                   (subset #'(lambda (S) (not (equal P (car S)))) NR))
                 (NDA
                   (mapcar #'genunion
                           (crossproduct (hypernode-nearest-defeasible-ancestors node)
                                         (hypernode-nearest-defeasible-ancestors node*))))
                 (d-node (d-node-for P*))
                 (c-list (if d-node (fetch-c-list-for P* d-node)))
                 (nodes (if c-list (c-list-nodes c-list)))
                 (N-conclusion
                   (find-if #'(lambda (c)
                                (and (eq (hypernode-kind c) :inference)
                                     (== (hypernode-supposition c) sup)
                                     (== (hypernode-reductio-ancestors c) reductio-ancestors)
                                     (== (hypernode-non-reductio-supposition c) non-reductio-supposition)))
                            nodes))
                 (new-node? (null N-conclusion)))
            (when
              (or (null d-node)
                  (not (subsumed N-conclusion (list node node*) sequent NDA
                                 non-reductio-supposition :reductio nil d-node)))
              (pushnew node (interest-discharging-nodes interest))
              (when (null N-conclusion)
                (setf N-conclusion
                      (make-new-conclusion
                        sequent reductio-ancestors reductio-ancestors non-reductio-supposition)))
              (let ((old-degree (current-maximal-degree-of-justification N-conclusion))
                    (hyperlink
                      (build-hyperlink
                        (list node node*) nil :reductio 1.0 N-conclusion NDA nil nil unifier depth nil)))
                (cond
                  ((null hyperlink)
                   (decf *hyperlink-number*)
                   (when new-node? (decf *hypernode-number*)))
                  (t
                    (when new-node?
                      (push N-conclusion *hypergraph*)
                      (store-hypernode-with-c-list
                        N-conclusion (sequent-formula sequent) c-list))
                    ; (when R
                    ;      (setf (hypernode-enabling-interests N-conclusion)
                    ;               (union (hypernode-enabling-interests N-conclusion)
                    ;                          (hypernode-generating-interests (cdr R)))))
                    (when *trace* (indent depth)
                      (princ "draw-reductio-conclusion: ")
                      (princ N-conclusion) (terpri))
                    (when *display?* (display-hyperlink hyperlink))
                    (when (read-char-no-hang) (clear-input) (throw 'die nil))
                    (let ((i-lists (c-list-corresponding-i-lists (hypernode-c-list N-conclusion)))
                          (increased-justification?
                            (or new-node? (> (current-maximal-degree-of-justification node) old-degree))))
                      (when increased-justification?
                        (discharge-interest-in-defeaters
                          N-conclusion i-lists old-degree new-node?))
                      (push hyperlink *new-links*)
                      (when increased-justification?
                        (discharge-interest-in
                          N-conclusion i-lists old-degree new-node? (1+ depth) d-interests)
                        (when (not (hypernode-cancelled-node N-conclusion))
                          (discharge-immediate-reductios
                            N-conclusion old-degree new-node?
                            (1+ depth) d-interests interest)))
                      (when new-node? (invert-contradictions node unifier (1+ depth)))
                      (cancel-subsumed-links hyperlink depth)
                      ))))))))))

  #| This must recompute the set of hypernode-arguments for the hyperlink-target and its
  inference-descendants.  Node arguments are stored as triples (arg,strength,discounted-strength) |#
  (defun build-hyperlink (basis clues rule discount node NDA binding link instantiations depth defeasible?)
    ; (setf b basis r rule d discount n node nd nda bi binding de depth)
    ;; (when (eql *hyperlink-number* 20) (setf b basis cl clues r rule d discount n node nd nda bi binding li link in instantiations de depth def defeasible?) (break))
    ;; (step (build-hyperlink b cl r d n nd bi li in de def))
    ;; (princ "Building link ") (princ *hyperlink-number*) (terpri) (break)
    (incf *hyperlink-number*)
    (when (not (some #'(lambda (L)
                         (and (equal (hyperlink-basis L) basis)
                              (eq (hyperlink-rule L) rule)))
                     (hypernode-hyperlinks node)))
      (let* ((new? (null (hypernode-hyperlinks node)))
             (reason-strength
               (cond ((keywordp rule) 1.0)
                     ((numberp (reason-strength rule)) (reason-strength rule))
                     (t (let ((r (funcall (reason-strength rule) binding basis)))
                          (if (>= r 0) r 0)))))
             (link (make-hyperlink
                     :hyperlink-number *hyperlink-number*
                     :hyperlink-basis basis
                     :hyperlink-clues clues
                     :hyperlink-rule rule
                     :hyperlink-target node
                     :hyperlink-defeasible? defeasible?
                     :hyperlink-temporal
                     (if (or (and (not (keywordp rule)) (reason-temporal? rule))
                             (some #'hypernode-temporal-node basis)) *cycle*)
                     :hyperlink-reason-strength  reason-strength
                     :hyperlink-binding binding
                     :hyperlink-discount-factor
                     (cond (discount discount)
                           ((not (keywordp rule)) (reason-discount-factor rule))
                           (t 1.0))
                     :hyperlink-nearest-defeasible-ancestors
                     (if defeasible? (list (list node)) NDA)
                     :hyperlink-generating-interest-link link))
             (ancestors (union basis (unionmapcar+ #'hypernode-ancestors basis))))
        (when (or (not (member nil NDA))
                  (non-circular (hypernode-sequent node) ancestors))  ;; this is a circularity test
          (dolist (n basis) (push link (hypernode-consequent-links n)))
          (if (null (hypernode-temporal-node node)) (setf (hypernode-temporal-node node) (hyperlink-temporal link)))
          (push link *hyperlinks*)
          (add-hyperlink link node depth)
          (if *log-on* (push node *reasoning-log*))
          (when (and (not defeasible?) basis (every #'hypernode-background-knowledge basis))
            (setf (hypernode-background-knowledge node) t))
          (let ((old-NDA (hypernode-nearest-defeasible-ancestors node)))
            (cond (defeasible?
                    (pushnew (list node) (hypernode-nearest-defeasible-ancestors node) :test 'equal))
                  (t
                    (dolist (X NDA)
                      (when
                        (not (some #'(lambda (Y) (subsetp Y X))
                                   (hypernode-nearest-defeasible-ancestors node)))
                        (dolist (Y (hypernode-nearest-defeasible-ancestors node))
                          (when (subsetp X Y) (pull Y (hypernode-nearest-defeasible-ancestors node))))
                        (push X (hypernode-nearest-defeasible-ancestors node))))))
            (when (not new?)
              (dolist (X (hypernode-nearest-defeasible-ancestors node))
                (invert-contradictions-retrospectively node X old-NDA))))
          (recursively-compute-nearest-defeasible-ancestors node)
          (setf (hypernode-ancestors node) (union ancestors (hypernode-ancestors node)))
          (recursively-compute-hypernode-ancestors node ancestors)
          (when (not new?) (invert-contradictions-from-new-hyperlink link instantiations))
          link))))

  #| This returns the instantiated-premise. |#
  (defun store-instantiated-premise
    (reason node c-list binding instantiations ip remaining-premises &optional profile)
    (cond
      ((and (forwards-premise-p (car remaining-premises))
            (listp (fp-formula (car remaining-premises)))
            (equal (car (fp-formula (car remaining-premises))) 'define))
       (let* ((var (mem2 (fp-formula (car remaining-premises))))
              (def-instantiator (fp-instantiator (car remaining-premises)))
              (new-binding (set-def-binding def-instantiator var binding)))
         (cond ((cdr remaining-premises)
                (when (funcall** (fp-condition (car remaining-premises)) nil new-binding)
                  (store-instantiated-premise
                    reason node c-list new-binding instantiations ip (cdr remaining-premises))))
               ((funcall** (fp-condition (car remaining-premises)) nil new-binding)
                (make-forwards-inference
                  new-binding instantiations
                  (if (clue? (ip-premise ip)) (ip-basis ip) (cons node (ip-basis ip)))
                  (if (clue? (ip-premise ip)) (cons node (ip-clues ip)) (ip-clues ip))
                  0 ip)))))
      (t
        (let ((premise (mem1 remaining-premises)))
          (when (null profile)
            (setf profile (reason-code (funcall (fp-instantiator premise) binding) (fp-variables premise))))
          (cond (profile
                  (index-instantiated-premise
                    reason premise profile node c-list binding instantiations
                    ip *top-d-node* (cdr remaining-premises)))
                (t (store-instantiated-premise-at-d-node
                     reason premise node c-list binding instantiations
                     ip *top-d-node* (cdr remaining-premises))))))))

  (defun reason-substantively-from-first-instantiated-premise (node depth ip)
    (multiple-value-bind
      (binding instantiation)
      (funcall (fp-binding-function (ip-premise ip)) (hypernode-formula node) (hypernode-variables node))
      (let ((spec (premise-hypernode-specifier (ip-premise ip))))
        (when spec (push (cons spec node) binding)))
      (when (and instantiation (equal (fp-kind (ip-premise ip)) (hypernode-kind node))
                 (funcall** (fp-condition (ip-premise ip)) node binding))
        (cond
          ((ip-remaining-premises ip)
           (let* ((ip*
                    (store-instantiated-premise
                      (ip-reason ip) node nil binding (list instantiation) ip (ip-remaining-premises ip)))
                  (dn (ip-d-node ip*)))
             (reason-from-subsidiary-c-lists dn depth ip*)))
          (t (make-forwards-inference
               binding (if (not (clue? (ip-premise ip))) (list instantiation))
               (if (not (clue? (ip-premise ip))) (list node))
               (if (clue? (ip-premise ip)) (list node))
               depth ip))))))

  (defun reason-from-subsidiary-c-lists (d-node depth ip)
    (dolist (c-list (d-node-c-lists d-node))
      (when (c-list-processed-nodes c-list)
        (reason-substantively-from-non-initial-instantiated-premise c-list depth ip)))
    (dolist (test (d-node-discrimination-tests d-node))
      (reason-from-subsidiary-c-lists (cdr test) depth ip)))

  #| This can be blocked by a prior reductio-supposition, but this then converts it so that it is
  no longer deductive-only.  Any hypernode-descendants not inferred from other deductive-only
  nodes are made not deductive-only, and all defeasible forwards-rules are applied to them. |#
  (defun queue-supposition (supposition instance-supposition e-vars discount-factor interest)
    ; (when (eq interest (interest 36)) (setf s supposition i instance-supposition e e-vars d discount-factor in interest) (break))
    ;; (step (queue-supposition s i e d in))
    (let ((sup (find-if #'(lambda (N) (equal (hypernode-formula N) supposition))
                        *non-reductio-supposition-nodes*)))
      (cond (sup
              (incf (hypernode-readopted-supposition sup))
              (push interest (hypernode-generating-interests sup))
              (push sup (interest-generated-suppositions interest))
              (when (and (hypernode-deductive-only sup) (not (interest-deductive interest)))
                (let ((nodes (convert-from-deductive-only sup)))
                  (dolist (C nodes)
                    (apply-forwards-defeasible-reasons C))))
              (values sup nil))
            (t
              (setf sup (subsuming-supposition supposition))  ;; an hypernode
              (cond ((null sup)
                     (queue-non-reductio-supposition
                       supposition instance-supposition e-vars discount-factor interest))
                    ((reductio-supposition sup)
                     (incf (hypernode-readopted-supposition sup))
                     (push interest (hypernode-generating-interests sup))
                     (convert-reductio-supposition sup discount-factor)
                     (values sup t)))))))

  (defun queue-non-reductio-defeater-supposition (supposition)
    (when (skolem-free supposition) (push supposition *skolem-free-suppositions*))
    (let* ((sequent (list (list supposition) supposition))
           (complexity
             (max 1 (* 2 (formula-complexity supposition))))
           (node
             (make-hypernode
               :hypernode-number (incf *hypernode-number*)
               :hypernode-sequent sequent
               :hypernode-formula supposition
               :hypernode-supposition (list supposition)
               :hypernode-kind :inference
               :hypernode-nearest-defeasible-ancestors (list nil)
               :hypernode-justification :supposition
               :hypernode-maximal-degree-of-justification 1.0
               :hypernode-degree-of-justification 1.0
               :hypernode-discounted-node-strength 1.0
               :hypernode-non-reductio-supposition? t))
           (queue-node
             (make-inference-queue-node
               :queue-number (incf *queue-number*)
               :queue-item node
               :queue-item-kind :conclusion
               :queue-item-complexity complexity
               :queue-discounted-strength 1.0
               :queue-degree-of-preference (/ 1.0 complexity))))
      (setf (hypernode-non-reductio-supposition node) (list (cons supposition node)))
      (setf (hypernode-queue-node node) queue-node)
      (store-hypernode node supposition)
      (push node *hypergraph*)
      (push node *non-reductio-supposition-nodes*)
      (if *log-on* (push node *reasoning-log*))
      (when *display?* (display-unsupported-hypernode node))
      (discharge-interest-in node (c-list-corresponding-i-lists (hypernode-c-list node)) nil t 1 nil)
      (setf *inference-queue* (ordered-insert queue-node *inference-queue* #'i-preferred))
      (when (and *display?* *graphics-on*)
        (when *graphics-pause* (pause-graphics))
        (draw-n node *og* *nodes-displayed*) (push node *nodes-displayed*))
      node))

  (defun queue-non-reductio-supposition
    (supposition instance-supposition e-vars discount-factor interest)
    (let* ((sequent (list instance-supposition supposition))
           (deductive-only (interest-deductive interest)))
      (when (skolem-free supposition) (push supposition *skolem-free-suppositions*))
      (let* ((complexity
               (max 1 (* 2 (formula-complexity supposition))))
             (priority (* discount-factor (interest-priority interest)))
             (node
               (make-hypernode
                 :hypernode-number (incf *hypernode-number*)
                 :hypernode-sequent sequent
                 :hypernode-formula supposition
                 :hypernode-supposition instance-supposition
                 :hypernode-kind :inference
                 :hypernode-nearest-defeasible-ancestors (list nil)
                 :hypernode-justification :supposition
                 :hypernode-maximal-degree-of-justification 1.0
                 :hypernode-degree-of-justification 1.0
                 :hypernode-discounted-node-strength priority
                 :hypernode-deductive-only deductive-only
                 :hypernode-variables e-vars
                 :hypernode-supposition-variables e-vars
                 :hypernode-discount-factor discount-factor
                 :hypernode-generating-interests (list interest)
                 :hypernode-non-reductio-supposition? t))
             (queue-node
               (make-inference-queue-node
                 :queue-number (incf *queue-number*)
                 :queue-item node
                 :queue-item-kind :conclusion
                 :queue-discounted-strength priority
                 :queue-item-complexity complexity
                 :queue-degree-of-preference (/ discount-factor complexity))))
        (setf (hypernode-non-reductio-supposition node) (list (cons (mem1 instance-supposition) node)))
        (setf (hypernode-queue-node node) queue-node)
        (store-hypernode node (sequent-formula sequent))
        (push node (interest-generated-suppositions interest))
        (push node *hypergraph*)
        (push node *non-reductio-supposition-nodes*)
        (if *log-on* (push node *reasoning-log*))
        (when *display?* (display-unsupported-hypernode node))
        (discharge-interest-in node (c-list-corresponding-i-lists (hypernode-c-list node)) nil t 1 nil)
        (setf *inference-queue* (ordered-insert queue-node *inference-queue* #'i-preferred))
        (when (and *display?* *graphics-on*)
          (when *graphics-pause* (pause-graphics))
          (draw-n node *og* *nodes-displayed*) (push node *nodes-displayed*))
        (values node t))))

  #| This must recompute hypernode-reductio-ancestors, non-reductio-suppositions, deductive-only-status,
  and apply forwards defeasible reasons. |#
  (defun convert-reductio-supposition (sup discount-factor)
    (setf (hypernode-reductio-ancestors sup) (list (cons (hypernode-formula sup) sup)))
    ; (setf (hypernode-non-reductio-supposition sup) nil)
    (setf (hypernode-non-reductio-supposition? sup) t)
    (let ((Q (hypernode-queue-node sup)))
      (when Q
        (setf (queue-degree-of-preference Q) (* discount-factor (/ 1 (queue-item-complexity Q))))
        (setf *inference-queue*
              (ordered-insert Q (remove Q *inference-queue*) #'i-preferred))))
    (let ((nodes
            (convert-from-deductive-only sup)))
      (dolist (C nodes)
        (when (deductive-in C sup)
          (let ((nr (find-if #'(lambda (x) (equal (cdr x) sup)) (hypernode-non-reductio-supposition C))))
            (when nr
              (pull nr (hypernode-non-reductio-supposition C))
              (push nr (hypernode-reductio-ancestors C))))))
      (dolist (C nodes)
        (apply-forwards-defeasible-reasons C))))

  (defun make-forwards-inference (binding instantiations basis clues depth ip)
    ; (when (eql *hypernode-number* 284) (setf b binding in instantiations bs basis cl clues d depth i ip) (break))
    ;;  (step (make-forwards-inference b in bs cl d i))
    (when *trace* (indent depth) (princ "MAKE-FORWARDS-INFERENCE from instantiated-premise ")
      (princ (ip-number ip)) (terpri))
    (cond
      ((reason-backwards-premises (ip-reason ip))
       (let ((formulas (funcall (reason-conclusions-function (ip-reason ip)) binding))
             (sup nil)
             (instantiations+ instantiations)
             (variables (unionmapcar+ #'hypernode-variables basis))
             (new-vars nil))
         (dolist (b basis)
           (let ((b-sup (hypernode-supposition b))
                 (b-vars (setdifference (hypernode-supposition-variables b) (hypernode-variables b))))
             (dolist (var b-vars)
               (when (mem var variables)
                 (let ((new-var (make-interest-variable)))
                   (push new-var new-vars)
                   (setf b-sup (=subst new-var var b-sup)))))
             (setf sup (union= sup (match-sublis (mem1 instantiations+) b-sup)))
             (setf instantiations+ (cdr instantiations+))))
         (setf sup
               (remove-if
                 #'(lambda (s)
                     (some #'(lambda (b) (and (not (equal s b)) (match s b new-vars))) sup)) sup))
         (dolist (formula formulas)
           (let* ((sequent (list sup (car formula)))
                  (deductive-node (validating-deductive-node sequent (not (reason-defeasible-rule (ip-reason ip))))))
             (cond (deductive-node
                     (draw-conclusion
                       (car formula) (cons deductive-node basis) (ip-reason ip) (cons t instantiations) 1 depth
                       nil (cdr formula) :binding binding :clues clues))
                   (t
                     (let ((degree
                             (minimum
                               (cons (applied-forwards-reason-strength (ip-reason ip) binding basis)
                                     (append
                                       (mapcar #'hypernode-degree-of-justification (ip-basis ip))
                                       (mapcar #'hypernode-degree-of-justification (ip-clues ip))
                                       (mapcar #'query-strength *ultimate-epistemic-interests*))))))
                       (construct-initial-interest-link
                         basis instantiations (ip-reason ip) nil depth degree binding sup
                         :remaining-premises (reason-backwards-premises (ip-reason ip)) :clues clues))))))))
      (t
        (dolist (formula (funcall (reason-conclusions-function (ip-reason ip)) binding))
          (draw-conclusion
            (car formula) basis (ip-reason ip) instantiations (reason-discount-factor (ip-reason ip)) depth nil
            (cdr formula) :binding binding :clues clues)))))

  (defun reason-substantively-from-non-initial-instantiated-premise
    (c-list depth ip &optional node)
    ; (when (eq ip (ip 29)) (setf n node d depth p ip c c-list) (break))
    ;; (step (reason-substantively-from-non-initial-instantiated-premise c d p n))
    (let* ((vars (if node (hypernode-variables node) (c-list-variables c-list)))
           (formula (if node (hypernode-formula node) (c-list-formula c-list))))
      (multiple-value-bind
        (binding0 instantiation0)
        (funcall (fp-binding-function (ip-premise ip)) formula vars)
        (when instantiation0
          (let ((unifier
                  (binding-unifier
                    binding0 (ip-binding ip)
                    (ip-used-premise-variables ip) vars (ip-used-variables ip))))
            (when unifier
              (let
                ((binding
                   (rectify-binding binding0 unifier ip))
                 (instantiations
                   (cons (merge-matches* (mem1 unifier) instantiation0)
                         (mapcar #'(lambda (in) (merge-matches* (mem2 unifier) in))
                                 (ip-instantiations ip))))
                 (spec (premise-hypernode-specifier (ip-premise ip))))
                (let ((nodes nil))
                  (when
                    (or
                      (and node
                           (equal (fp-kind (ip-premise ip)) (hypernode-kind node))
                           (funcall** (fp-condition (ip-premise ip)) node
                                      (if spec (cons (cons spec node) binding) binding))
                           (setf nodes (list node)))
                      (and (null node)
                           (setf nodes
                                 (subset
                                   #'(lambda (c)
                                       (and (equal (fp-kind (ip-premise ip)) (hypernode-kind c))
                                            (funcall** (fp-condition (ip-premise ip)) c
                                                       (if spec (cons (cons spec c) binding) binding))))
                                   (c-list-processed-nodes c-list)))))
                    (cond
                      ((ip-remaining-premises ip)
                       (dolist (node nodes)
                         (let* ((ip*
                                  (store-instantiated-premise
                                    (ip-reason ip) node c-list
                                    (if spec (cons (cons spec node) binding) binding)
                                    instantiations ip (ip-remaining-premises ip))))
                           (when ip* (reason-from-subsidiary-c-lists (ip-d-node ip*) depth ip*)))))
                      (t
                        (dolist (node nodes)
                          (make-forwards-inference
                            binding instantiations
                            (if (clue? (ip-premise ip)) (ip-basis ip) (cons node (ip-basis ip)))
                            (if (clue? (ip-premise ip)) (cons node (ip-clues ip)))
                            depth ip)))))))))))))

  (defun reason-defeasibly-from-instantiated-premises (node d-node)
    (dolist (ip (d-node-forwards-reasons d-node))
      (let ((reason (ip-reason ip)))
        (when (reason-defeasible-rule reason)
          (let ((reason-function (and (null (ip-basis ip)) (reason-function reason))))
            (when (hypernode-cancelled-node node) (throw 'apply-forwards-reasons nil))
            (when (not (hypernode-deductive-only node))
              (cond
                (reason-function (funcall reason-function node 0 ip))
                ((ip-basis ip)
                 (reason-substantively-from-non-initial-instantiated-premise nil 0 ip node))
                (t (reason-substantively-from-first-instantiated-premise node 0 ip)))))))))

  (defun reason-defeasibly-from-dominant-premise-nodes (node d-node)
    (reason-defeasibly-from-instantiated-premises node d-node)
    (let ((pn (d-node-parent d-node)))
      (when pn (reason-defeasibly-from-dominant-premise-nodes node pn))))

  (defun apply-forwards-defeasible-reasons (node)
    (catch 'apply-forwards-defeasible-reasons
           (let* ((c-list (hypernode-c-list node))
                  (d-node (c-list-d-node c-list)))
             (reason-defeasibly-from-dominant-premise-nodes node d-node))))

  (defun queue-defeater-supposition (sup)
    (let ((sup-node (find-if #'(lambda (N) (equal (hypernode-formula N) sup))
                             *non-reductio-supposition-nodes*)))
      (cond (sup-node
              (incf (hypernode-readopted-supposition sup-node))
              (when (hypernode-deductive-only sup-node)
                (let ((nodes (convert-from-deductive-only sup-node)))
                  (dolist (C nodes)
                    (apply-forwards-defeasible-reasons C)))))
            (t
              (setf sup-node (subsuming-supposition sup))  ;; an hypernode
              (cond ((null sup-node)
                     (setf sup-node
                           (queue-non-reductio-defeater-supposition sup)))
                    ((reductio-supposition sup-node)
                     (incf (hypernode-readopted-supposition sup-node))
                     (convert-reductio-supposition sup-node 1.0)))))))

  (defun instantiate-defeater (undercutting-interest defeater antecedent* link reverse-binding)
    ;(setf u undercutting-interest d defeater a antecedent* l link r reverse-binding)
    ;; (step (instantiate-defeater u d a l r))
    (let ((binding (match-sublis reverse-binding (hyperlink-binding link) :test 'equal)))
      (cond
        (antecedent*
          (let*
            ((i-link
               (construct-initial-interest-link
                 nil nil adjunction undercutting-interest 0 *base-priority*
                 (list (cons 'p defeater) (cons 'q antecedent*)) (interest-supposition undercutting-interest)))
             (interest (link-interest i-link)))
            (dolist (reason (reason-undercutting-defeaters (hyperlink-rule link)))
              (when (and (member reason *backwards-reasons*) (funcall* (b-reason-condition reason) binding))
                (let ((supposition (interest-supposition interest)))
                  (cond
                    ((reason-forwards-premises reason)
                     (construct-interest-scheme
                       reason nil interest binding nil (reason-forwards-premises reason) nil 1
                       *base-priority* supposition))
                    (t (make-backwards-inference
                         reason binding interest 1 *base-priority* nil nil nil supposition))))))))
        (t
          (dolist (reason (reason-undercutting-defeaters (hyperlink-rule link)))
            (when (and (member reason *backwards-reasons*) (funcall* (b-reason-condition reason) binding))
              (let ((supposition (interest-supposition undercutting-interest)))
                (cond
                  ((reason-forwards-premises reason)
                   (construct-interest-scheme
                     reason nil undercutting-interest binding nil (reason-forwards-premises reason) nil 1
                     *base-priority* supposition))
                  (t (make-backwards-inference
                       reason binding undercutting-interest 1 *base-priority* nil nil nil supposition))))))))))

  (defun make-undercutting-defeater (base formula supposition antecedent* link reverse-binding)
    ; (when (eql link 2812) (setf b base f formula s supposition a antecedent* l link rb reverse-binding) (break))
    ;; (step (make-undercutting-defeater b f s a l rb))
    (let* ((defeater (make-@ (gen-conjunction base) formula))
           (undercutting-defeater
             (cond (antecedent* (conj defeater antecedent*))
                   (t defeater)))
           (undercutting-variables
             (formula-hypernode-variables undercutting-defeater)))
      (multiple-value-bind
        (undercutting-interest i-list)
        (interest-for (list supposition undercutting-defeater)
                      undercutting-variables nil nil)
        (cond ((null undercutting-interest)
               (setf undercutting-interest
                     (make-interest
                       :interest-number (incf *interest-number*)
                       :interest-sequent (list supposition undercutting-defeater)
                       :interest-formula undercutting-defeater
                       :interest-supposition supposition
                       :interest-variables undercutting-variables
                       :interest-supposition-variables (supposition-variables supposition)
                       :interest-defeatees (list link)
                       :interest-priority *base-priority*
                       :interest-defeater-binding (hyperlink-binding link)
                       :interest-generating-defeat-nodes (list (hyperlink-target link))))
               (store-interest undercutting-interest i-list)
               (pushnew undercutting-interest (hypernode-generated-defeat-interests (hyperlink-target link)))
               (when *display?*
                 (display-interest undercutting-interest)
                 (princ
                   "                                        Of interest as defeater for hyperlink ")
                 (princ (hyperlink-number link)) (terpri) (terpri))
               (when *log-on* (push undercutting-interest *reasoning-log*))
               (when (and *display?* *graphics-on* *graph-interests*)
                 (draw-i undercutting-interest *og*))
               (instantiate-defeater
                 undercutting-interest defeater antecedent* link reverse-binding))
              (t
                (readopt-interest undercutting-interest (list link))
                (push undercutting-interest (hypernode-generated-defeat-interests (hyperlink-target link)))
                (push (hyperlink-target link) (interest-generating-defeat-nodes undercutting-interest))
                (setf (interest-defeatees undercutting-interest)
                      (cons link (interest-defeatees undercutting-interest)))))
        (dolist (node (unifying-nodes undercutting-interest))
          (when (subsetp= (hypernode-supposition node) supposition)
            (when *display?*
              (princ "  Node # ") (princ (hypernode-number node))
              (princ " defeats link # ")
              (princ (hyperlink-number link)) (terpri))
            (let ((DL (build-hyper-defeat-link node link)))
              (pushnew DL (hyperlink-defeaters link))
              (pushnew node (interest-discharging-nodes undercutting-interest))
              (pushnew DL (hypernode-supported-hyper-defeat-links node))))))))

  (defun discharge-reductios (node old-degree depth d-interests)
    (when *trace* (indent depth) (princ "DISCHARGE-REDUCTIOS-FROM ")
      (princ node) (terpri))
    (when
      (not (some
             #'(lambda (il) (member (mem1 il) d-interests))
             (hypernode-discharged-interests node)))
      (setf (hypernode-reductios-discharged node) t)
      (let ((reductio-ancestors (hypernode-reductio-ancestors node))
            (Y0 (hypernode-supposition node)))
        (discharge-fortuitous-reductios node d-interests (1+ depth))
        (dolist (il (hypernode-discharged-interests node))
          (let* ((interest (mem1 il))
                 (direct-reductio-interest (interest-direct-reductio interest))
                 (unifier (mem2 il))
                 (unifiers (mem3 il))
                 ;; rewrite supposition-variables to avoid collision with formula-variables
                 (new-vars
                   (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                           (intersection (interest-variables interest)
                                         (set-difference (hypernode-supposition-variables node)
                                                         (hypernode-variables node)))))
                 (Y1 (remove-duplicates=
                       (match-sublis (mem1 unifier) (sublis new-vars Y0)))))
            ; (when new-vars (break))
            (when (and
                    (setdifference (interest-supposition interest)
                                   *skolem-free-suppositions*)
                    (> (interest-maximum-degree-of-interest interest) old-degree)
                    (<= (interest-degree-of-interest interest)
                        (current-maximal-degree-of-justification node)))
              (dolist (dr direct-reductio-interest)
                (let ((node* (car dr))
                      (match (cdr dr)))
                  (when (hypernode-cancelled-node node) (return-from discharge-reductios))
                  (let ((Y*0 (remove-duplicates=
                               (match-sublis
                                 (mem2 unifier)
                                 (match-sublis
                                   match (hypernode-supposition node*))))))
                    (dolist (u unifiers)
                      (let ((unifier* (merge-unifiers* unifier u))
                            (Y (remove-duplicates=
                                 (match-sublis (mem1 u) Y1)))
                            (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                        (let ((RA (union=
                                    (mapcar
                                      #'(lambda (x)
                                          (cons
                                            (match-sublis
                                              (mem1 unifier*)
                                              (car x)) (cdr x)))
                                      reductio-ancestors)
                                    (mapcar
                                      #'(lambda (x)
                                          (cons (match-sublis
                                                  (mem2 unifier*)
                                                  (match-sublis match (car x))) (cdr x)))
                                      (hypernode-reductio-ancestors node*))))
                              (NR (union=
                                    (mapcar
                                      #'(lambda (x)
                                          (cons
                                            (match-sublis
                                              (mem1 unifier*)
                                              (car x)) (cdr x)))
                                      (hypernode-non-reductio-supposition node))
                                    (mapcar
                                      #'(lambda (x)
                                          (cons (match-sublis
                                                  (mem2 unifier*)
                                                  (match-sublis match (car x))) (cdr x)))
                                      (hypernode-non-reductio-supposition node*)))))
                          (dolist (R RA)
                            (when (base-test R RA)
                              (let ((P (car R)))
                                (draw-reductio-conclusion
                                  P node node* R Y Y* RA NR interest unifier* (1+ depth)
                                  d-interests))))))))))))))))

  (defun reason-from-current-interest-scheme (node d-node old-degree depth)
    ; (when (eq node (node 28)) (setf n node dn d-node od old-degree d depth) (break))
    ;; (step (reason-from-current-interest-scheme n dn od d))
    (when *trace* (indent depth) (princ "REASON-FROM-CURRENT-INTEREST-SCHEME: ")
      (princ node) (princ " and ") (princ d-node) (terpri))
    (dolist (is (d-node-interest-schemes d-node))
      (let ((reason (is-reason is))
            (instance-function (is-instance-function is)))
        (when (hypernode-cancelled-node node) (throw 'discharge-interest-schemes nil))
        (when (and (or (not (hypernode-deductive-only node)) (not (reason-defeasible-rule reason)))
                   (or (not (interest-deductive (is-target-interest is))) (deductive-node node)))
          (let ((degree* (interest-degree-of-interest (is-target-interest is))))
            (when (and (>= (current-maximal-degree-of-justification node) degree*)
                       (> degree* old-degree))
              (cond
                (instance-function (funcall instance-function node (1+ depth) nil))
                (t (reason-from-interest-scheme
                     node (interest-priority (is-target-interest is)) (1+ depth) is)))))))))

  (defun reason-from-dominant-interest-schemes (node d-node old-degree depth)
    ; (when (and (eq node (node 6)) (eq d-node (d-node 19)))
    ;      (setf n node dn d-node od old-degree d depth) (break))
    ;; (step (reason-from-dominant-interest-schemes n dn od d))
    (reason-from-current-interest-scheme node d-node old-degree depth)
    (let ((pn (d-node-parent d-node)))
      (when pn (reason-from-dominant-interest-schemes node pn old-degree depth))))

  #| old-degree is the maximal-degree-of-justification for the node the last
  time discharge-interest-schemes was applied to it. |#
  (defun discharge-interest-schemes (node old-degree depth)
    ; (when (equal node (node 54)) (setf n node o old-degree d depth) (break))
    ;; (step (discharge-interest-schemes n o d))
    (catch 'discharge-interest-schemes
           (let* ((c-list (hypernode-c-list node))
                  (d-node (c-list-d-node c-list)))
             (reason-from-dominant-interest-schemes node d-node old-degree depth))))

  (defun discharge-interest-in-defeaters (node i-lists old-degree new?)
    ; (when (eq node (node 7)) (setf n node i i-lists o old-degree n? new?) (break))
    ;; (step (discharge-interest-in-defeaters n i o n?))
    (let ((degree (current-maximal-degree-of-justification node))
          (cancellations nil))
      (dolist (il i-lists)
        (let ((i-list (car il)))
          (dolist (N (i-list-interests i-list))
            (when (and  (interest-defeatees N)
                        (<= (interest-degree-of-interest N) degree)
                        (or new?
                            (> (interest-maximum-degree-of-interest N) old-degree))
                        (subsetp= (hypernode-supposition node)
                                  (interest-supposition N)))
              (pushnew N (hypernode-generating-defeat-interests node))
              (dolist (L (interest-defeatees N))
                (let ((DL (build-hyper-defeat-link node L)))
                  (pushnew DL (hyperlink-defeaters L))
                  (pushnew DL (hypernode-supported-hyper-defeat-links node)))
                (when (deductive-node node)
                  (let ((node* (hyperlink-target L)))
                    (setf (hyperlink-conclusive-defeat-status L) T)
                    (cond ((every #'hyperlink-conclusive-defeat-status (hypernode-hyperlinks node*))
                           (push node* cancellations))
                          (t
                            (dolist (L (hypernode-hyperlinks node*))
                              (let ((NDA
                                      (cond ((hyperlink-defeasible? L)
                                             (mapcar #'genunion
                                                     (gencrossproduct
                                                       (mapcar #'hypernode-nearest-defeasible-ancestors
                                                               (hyperlink-basis L)))))
                                            (t (list (list node*))))))
                                (dolist (X NDA)
                                  (when
                                    (not (some #'(lambda (Y) (subsetp= Y X))
                                               (hypernode-nearest-defeasible-ancestors node*)))
                                    (dolist (Y (hypernode-nearest-defeasible-ancestors node*))
                                      (when (subsetp= X Y) (pull Y (hypernode-nearest-defeasible-ancestors node*))))
                                    (push X (hypernode-nearest-defeasible-ancestors node*))))
                                (recursively-compute-nearest-defeasible-ancestors node*)))
                            (let ((ancestors
                                    (unionmapcar+
                                      #'(lambda (L)
                                          (union (hyperlink-basis L)
                                                 (unionmapcar+ #'hypernode-ancestors (hyperlink-basis L))))
                                      (hypernode-hyperlinks node*))))
                              (setf (hypernode-ancestors node*) ancestors)
                              (recursively-compute-hypernode-ancestors node* ancestors)
                              ))))))))))
      (if (and cancellations
               (every #'(lambda (L)
                          (and (not (keywordp (hyperlink-rule L)))
                               (backwards-reason-p (hyperlink-rule L))))
                      (hypernode-hyperlinks node)))
        (cons node cancellations) cancellations)))

  (defun discharge-appropriately-related-link (link u* degree new? old-degree N node depth interests)
    ; (when (eq link  (link 885)) (setf l link u u* d degree nw new? od old-degree n* n nd node dp depth in interests) (break))
    ;; (step (discharge-appropriately-related-link l u d nw od n* nd dp in))
    (when *trace* (indent depth) (princ "DISCHARGE-APPROPRIATELY-RELATED-LINK: ") (princ link) (terpri))
    (let* ((degree* (degree-of-interest* (link-resultant-interest link)))
           (spec (premise-hypernode-specifier (link-premise link)))
           (binding (if spec (cons (cons spec node) (link-binding link)) (link-binding link))))
      (when (and (<= degree* degree) (or new? (> (link-strength link) old-degree)))
        (setf (link-discharged link) t)
        (cond ((eq (link-rule link) :answer)
               (when (null (hypernode-supposition node))
                 (when (not (member node (link-supporting-nodes link)))
                   (push node (link-supporting-nodes link))
                   (push node (query-answers (link-resultant-interest link)))
                   (pushnew (link-resultant-interest link) (hypernode-answered-queries node))
                   (when (deductive-node node)
                     (when (and
                             (every
                               #'(lambda (query)
                                   (or (eq query (link-resultant-interest link))
                                       (some #'deductive-node (query-answers query))))
                               *ultimate-epistemic-interests*)
                             (not (some
                                    #'(lambda (Q) (eq (queue-item-kind Q) :query))
                                    *inference-queue*)))
                       (setf (hypernode-degree-of-justification node) 1.0)
                       (setf (query-answered? (link-resultant-interest link)) T)
                       (let ((deductive-links nil)
                             (deductive-nodes nil))
                         (dolist (L *new-links*)
                           (when (deductive-node (hyperlink-target L))
                             (push L deductive-links)
                             (push (hyperlink-target L) deductive-nodes)))
                         (dolist (N deductive-nodes) (setf (hypernode-degree-of-justification N) 1.0))
                         (dolist (L deductive-links) (setf (hyperlink-degree-of-justification L) 1.0))
                         (display-belief-changes
                           *new-links*
                           deductive-nodes
                           nil))
                       (dolist (instruction (query-positive-instructions (link-resultant-interest link)))
                         (funcall instruction node))
                       (when *display?*
                         (terpri)
                         (princ "             ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
                         (terpri))
                       ; (cancel-interest-in (link-interest link) 0)
                       (throw 'die nil)))
                   ; (record-query-answers link)
                   )))
              ((and (or (interest-non-reductio? (link-resultant-interest link)) (deductive-node node))
                    (funcall+ (interest-discharge-condition N) node u*
                              (match-sublis (link-interest-match link) binding)))
               ; (setf u* (convert-unifier-variables u* (hypernode-variables node)))
               (let
                 (;(match (link-interest-match link))
                  (match* (link-interest-reverse-match link)))
                 (setf u* (match-sublis match* u*))
                 (let* ((u1 (mem1 u*))
                        (u2 (mem2 u*))
                        (binding
                          (mapcar
                            #'(lambda (assoc)
                                (cons (car assoc) (match-sublis u2 (cdr assoc)))) binding))
                        (instantiations
                          (cons u1
                                (mapcar
                                  #'(lambda (in)
                                      (cond ((eq in t) u2)
                                            (t (cons (car in) (match-sublis u2 (cdr in))))))
                                  (link-instantiations link))))
                        (supposition (match-sublis u2 (link-supposition link))))
                   (cond
                     ((link-remaining-premises link)
                      (construct-interest-link
                        link node instantiations binding (link-remaining-premises link) supposition
                        (interest-degree-of-interest N) (interest-maximum-degree-of-interest N) (1+ depth)
                        (interest-priority (link-resultant-interest link)) interests))
                     ((or (null (interest-right-links (link-resultant-interest link)))
                          (some #'(lambda (L) (eq (link-rule L) ug))
                                (interest-right-links (link-resultant-interest link)))
                          (some #'(lambda (L)
                                    (funcall+ (interest-discharge-condition (link-resultant-interest link)) nil (list u1 u2)
                                              (match-sublis (link-interest-match link) (link-binding L))))
                                (interest-right-links (link-resultant-interest link))))
                      (cond
                        ((reason-conclusions-function (link-rule link))
                         (dolist (P (funcall (reason-conclusions-function (link-rule link)) binding))
                           (draw-conclusion
                             (car P) (cons node (link-supporting-nodes link)) (link-rule link) instantiations
                             (reason-discount-factor (link-rule link)) depth nil (cdr P) :binding binding :interest
                             (link-resultant-interest link) :link link :clues (link-clues link))))
                        (t
                          (draw-conclusion
                            (interest-formula (link-resultant-interest link)) (cons node (link-supporting-nodes link))
                            (link-rule link) instantiations (reason-discount-factor (link-rule link)) depth nil
                            (reason-defeasible-rule (link-rule link)) :binding binding :interest (link-resultant-interest link)
                            :link link :clues (link-clues link)))
                        ))))))))))

  #| new? indicates whether the node is newly-constructed.  Old-degree
  is the old maximal-degree-of-justification  |#
  (defun DISCHARGE-INTEREST-IN
    (node corresponding-i-lists old-degree new? depth interests &key interest reductio-only)
    (let ((degree (current-maximal-degree-of-justification node)))
      (when (or new? (> degree old-degree))
        (when
          (every
            #'(lambda (i-list)
                (not (some
                       #'(lambda (N) (member N interests))
                       (i-list-interests (mem1 i-list)))))
            corresponding-i-lists)
          (setf (hypernode-interests-discharged? node) t)
          (dolist (corresponding-i-list corresponding-i-lists)
            (let* ((i-list (mem1 corresponding-i-list))
                   (interest-candidates
                     (subset
                       #'(lambda (N)
                           (not (member node (interest-discharging-nodes N))))
                       (if (and interest (member interest (i-list-interests i-list)))
                         (cons interest (remove interest (i-list-interests i-list)))
                         (i-list-interests i-list)))))
              (let* ((unifier (mem2 corresponding-i-list))
                     (C-sup (match-sublis (mem1 unifier) (hypernode-supposition node))))
                (dolist (N interest-candidates)
                  (when
                    (and (or (null reductio-only) (interest-reductio N))
                         (not (hypernode-cancelled-node node))
                         (not (member N interests))
                         (or (eq N interest)
                             (and
                               (or new?
                                   (> (interest-maximum-degree-of-interest N) old-degree))
                               (or (deductive-node node) (not (interest-deductive N)))
                               (<= (interest-degree-of-interest N) degree)
                               (not (assoc N (hypernode-discharged-interests node))))))
                    (let ((unifiers
                            (if
                              (or (not (interest-direct-reductio N))
                                  (some #'(lambda (L)
                                            (or (eq (link-rule L) :answer)
                                                (not (interest-reductio (link-resultant-interest L)))))
                                        (interest-right-links N)))
                              (appropriately-related-non-reductio-suppositions node N unifier)))
                          (reductio-unifiers
                            (if
                              (or (interest-direct-reductio N)
                                  (some #'(lambda (L)
                                            (and (not (eq (link-rule L) :answer))
                                                 (interest-reductio (link-resultant-interest L))))
                                        (interest-right-links N)))
                              (appropriately-related-reductio-suppositions node N unifier))))
                      (when (or unifiers reductio-unifiers)
                        (dolist (u unifiers)
                          (let ((u* (merge-unifiers* unifier u)))
                            (dolist (link (interest-right-links N))
                              (let ((spec (premise-hypernode-specifier (link-premise link))))
                                (when (and (or (not (interest-direct-reductio N))
                                               (eq (link-rule link) :answer)
                                               (not (interest-reductio (link-resultant-interest link))))
                                           (funcall+
                                             (interest-discharge-condition N) node unifier
                                             (match-sublis
                                               (link-interest-match link)
                                               (if spec (cons (cons spec node) (link-binding link))
                                                 (link-binding link)))))
                                  (push (list N unifier (append unifiers reductio-unifiers)) (hypernode-discharged-interests node))
                                  (pushnew node (interest-discharging-nodes N))
                                  (when *display?* (princ "  Node ") (princ (hypernode-number node))
                                    (princ " discharges interest ") (princ (interest-number N)) (terpri) (terpri))
                                  (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-IN: ")
                                    (princ N) (princ " from ") (princ node) (terpri))
                                  (discharge-appropriately-related-link
                                    link u* degree new? old-degree N node depth (cons N interests)))))))
                        (when reductio-unifiers
                          (push (list N unifier (append unifiers reductio-unifiers))
                                (hypernode-discharged-interests node)))
                        (dolist (u reductio-unifiers)
                          (let ((u* (merge-unifiers* unifier u)))
                            (dolist (link (interest-right-links N))
                              (let ((spec (premise-hypernode-specifier (link-premise link))))
                                (when (and (not (eq (link-rule link) :answer))
                                           (interest-reductio (link-resultant-interest link))
                                           (funcall+
                                             (interest-discharge-condition N) node unifier
                                             (match-sublis
                                               (link-interest-match link)
                                               (if spec (cons (cons spec node) (link-binding link))
                                                 (link-binding link)))))
                                  (pushnew node (interest-discharging-nodes N))
                                  (when *display?* (princ "  Node ") (princ (hypernode-number node))
                                    (princ " discharges interest ") (princ (interest-number N)) (terpri) (terpri))
                                  (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-IN: ")
                                    (princ N) (princ " from ") (princ node) (terpri))
                                  (discharge-appropriately-related-link
                                    link u* degree new? old-degree N node depth (cons N interests)))))))
                        (when (and (not (interest-cancelled N))
                                   (eq (mem2 unifier) t)
                                   (subsetp= C-sup (interest-supposition N)))
                          (cond ((deductive-node node)
                                 (setf (interest-cancelling-node N) node)
                                 (cancel-interest-in N (if *trace* depth 0)))
                                (t
                                  (dolist (sup-node (interest-generated-suppositions N))
                                    (when
                                      (and
                                        (equal (hypernode-generating-interests sup-node) (list N))
                                        (deductive-in node sup-node))
                                      (cancel-node sup-node (if *trace* depth 0))))))
                          ))))))))))))

  ;(defun discharge-fortuitous-reductios (node d-interests depth)
  ;    ; (when (eq node (node 399)) (setf n node di d-interests d depth) (break))
  ;    ;; (step (discharge-fortuitous-reductios n di d))
  ;    (dolist (nl (c-list-contradictors (hypernode-c-list node)))
  ;        (let* ((unifier (mem2 nl))
  ;                  (unifier* (list (mem2 unifier) (mem1 unifier))))
  ;           (dolist (node* (c-list-nodes (mem1 nl)))
  ;               (when (and (null (hypernode-supposition node))
  ;                                     (null (hypernode-supposition node*))
  ;                                     (deductive-node node)
  ;                                     (deductive-node node*))
  ;                    (dolist (Q *ultimate-epistemic-interests*)
  ;                        (let ((in (query-interest Q)))
  ;                           (draw-conclusion
  ;                             (match-sublis (mem1 unifier) (interest-formula in))
  ;                             (list node node*) :fortuitous-reductio unifier 1 (1+ depth) d-interests))))
  ;               (when
  ;                    (and
  ;                      (some
  ;                        #'(lambda (sup)
  ;                              (some
  ;                                #'(lambda (in) (not (assoc in (hypernode-discharged-interests node))))
  ;                                (hypernode-generated-interests (cdr sup))))
  ;                        (hypernode-non-reductio-supposition node*))
  ;                      (appropriately-related-node-suppositions node node* unifier))
  ;                    (dolist (sup (hypernode-non-reductio-supposition node*))
  ;                        (let ((sup-node (cdr sup)))
  ;                           (when (deductive-in node* sup-node)
  ;                                (dolist (in (hypernode-generated-interests sup-node))
  ;                                    (when (appropriately-related-suppositions node in '(t t))
  ;                                         (draw-conclusion
  ;                                           (match-sublis (mem1 unifier) (interest-formula in))
  ;                                           (list node node*) :fortuitous-reductio unifier 1 (1+ depth) d-interests)))))))
  ;               (when
  ;                    (and
  ;                      (some
  ;                        #'(lambda (sup)
  ;                              (some
  ;                                #'(lambda (in) (not (assoc in (hypernode-discharged-interests node))))
  ;                                (hypernode-generated-interests (cdr sup))))
  ;                        (hypernode-non-reductio-supposition node))
  ;                      (appropriately-related-node-suppositions node* node unifier*))
  ;                    (dolist (sup (hypernode-non-reductio-supposition node))
  ;                        (let ((sup-node (cdr sup)))
  ;                           (when (deductive-in node sup-node)
  ;                                (dolist (in (hypernode-generated-interests sup-node))
  ;                                    (when (appropriately-related-suppositions node in '(t t))
  ;                                         (draw-conclusion
  ;                                           (match-sublis (mem1 unifier*) (interest-formula in))
  ;                                           (list node* node) :fortuitous-reductio unifier* 1 (1+ depth) d-interests)))))))
  ;               ))))

  (defun discharge-fortuitous-reductios (node d-interests depth)
    ; (when (eq node (node 4)) (setf n node di d-interests d depth) (break))
    ;; (step (discharge-fortuitous-reductios n di d))
    (dolist (nl (c-list-contradictors (hypernode-c-list node)))
      (let ((unifier (mem2 nl)))
        (dolist (node* (c-list-nodes (mem1 nl)))
          (when (and (null (hypernode-supposition node))
                     (null (hypernode-supposition node*))
                     (deductive-node node)
                     (deductive-node node*))
            (dolist (Q *ultimate-epistemic-interests*)
              (let ((in (query-interest Q)))
                (draw-conclusion
                  (match-sublis (mem1 unifier) (interest-formula in))
                  (list node node*) :fortuitous-reductio unifier 1 (1+ depth) d-interests nil))))
          (let ((nodes nil))
            (dolist (n (hypernode-reductio-ancestors node)) (pushnew (cdr n) nodes))
            (dolist (n (hypernode-non-reductio-supposition node)) (pushnew (cdr n) nodes))
            (dolist (n (hypernode-reductio-ancestors node*)) (pushnew (cdr n) nodes))
            (dolist (n (hypernode-non-reductio-supposition node*)) (pushnew (cdr n) nodes))
            (dolist (n nodes)
              (dolist (interest (hypernode-generated-interests n))
                (when (subsetp nodes (interest-supposition-nodes interest))
                  (draw-conclusion
                    (interest-formula interest) (list node node*) :discharge-fortuitous-reductios
                    unifier 1 (1+ depth) d-interests nil)))))))))

  (defun discharge-immediate-reductios
    (node old-degree new? depth d-interests d-interest)
    ; (when (eq node (node 6)) (setf c node o old-degree n new? d depth di d-interests di* d-interest) (break))
    ;(setf c node o old-degree n new? d depth di d-interests di* d-interest)
    ;; (step (discharge-immediate-reductios c o n d di di*))
    (when *trace* (indent depth) (princ "DISCHARGE-IMMEDIATE-REDUCTIOS-FROM ")
      (princ node) (terpri))
    (when
      (and
        (<= (length (setdifference (hypernode-supposition node) *skolem-free-suppositions*)) 1)
        (not (member d-interest d-interests)))
      (setf (hypernode-reductios-discharged node) t)
      (let ((reductio-ancestors (hypernode-reductio-ancestors node))
            (Y0 (hypernode-supposition node)))
        (discharge-fortuitous-reductios node d-interests (1+ depth))
        (dolist (il (hypernode-discharged-interests node))
          (let* ((interest (mem1 il))
                 (direct-reductio-interest (interest-direct-reductio interest))
                 (unifier (mem2 il))  ;; this unifies node with interest
                 (unifiers
                   (if (mem3 il)
                     (mem3 il)
                     (appropriately-related-suppositions node interest unifier)))
                 (Y1 (remove-duplicates= (match-sublis (mem1 unifier) Y0))))
            (when (or  (eq interest d-interest)
                       (and
                         (not (member interest d-interests))
                         (or new?
                             (> (interest-maximum-degree-of-interest interest) old-degree))
                         (<= (interest-degree-of-interest interest)
                             (current-maximal-degree-of-justification node))))
              (dolist (dr direct-reductio-interest)
                (let ((node* (car dr))
                      (match (cdr dr)))
                  (when (hypernode-cancelled-node node) (return-from discharge-immediate-reductios))
                  ;; to use unifier we must first transform node* to make it like interest
                  (let ((Y*0 (remove-duplicates=
                               (match-sublis
                                 (mem2 unifier)
                                 (match-sublis
                                   match (hypernode-supposition node*))))))
                    (dolist (u unifiers)
                      (let ((unifier* (merge-unifiers* unifier u))
                            (Y (remove-duplicates= (match-sublis (mem1 u) Y1)))
                            (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                        (let ((RA (union=
                                    (mapcar
                                      #'(lambda (x)
                                          (cons
                                            (match-sublis
                                              (mem1 unifier*)
                                              (car x)) (cdr x)))
                                      reductio-ancestors)
                                    (mapcar
                                      #'(lambda (x)
                                          (cons (match-sublis
                                                  (mem2 unifier*)
                                                  (match-sublis match (car x))) (cdr x)))
                                      (hypernode-reductio-ancestors node*))))
                              (NR (union=
                                    (mapcar
                                      #'(lambda (x)
                                          (cons
                                            (match-sublis
                                              (mem1 unifier*)
                                              (car x)) (cdr x)))
                                      (hypernode-non-reductio-supposition node))
                                    (mapcar
                                      #'(lambda (x)
                                          (cons (match-sublis
                                                  (mem2 unifier*)
                                                  (match-sublis match (car x))) (cdr x)))
                                      (hypernode-non-reductio-supposition node*)))))
                          (dolist (R RA)
                            (when (base-test R RA)
                              (let ((P (car R)))
                                (draw-reductio-conclusion
                                  P node node* R Y Y* RA NR interest unifier* (1+ depth)
                                  (cons d-interest d-interests)))))))))))))))))

  (defun adjust-support-for-consequences (node old-degree depth)
    ; (setf n node o old-degree d depth)
    ;; (step (adjust-support-for-consequences n o d))
    (when *trace* (indent depth) (princ "ADJUST-SUPPORT-FOR-CONSEQUENCES for ")
      (princ node) (terpri))
    (dolist (L (hypernode-consequent-links node))
      (let ((n (hyperlink-target L)))
        (cond ((hypernode-temporal-node node)
               (let* ((decay (expt *temporal-decay* (- *cycle* (hypernode-temporal-node n))))
                      (adjusted-old-degree (adjust-for-decay old-degree decay)))
                 (when (>< adjusted-old-degree (hypernode-maximal-degree-of-justification n))
                   (let* ((temp
                            (or (eq (hyperlink-rule L) *temporal-projection*)
                                (eq (hyperlink-rule L) *causal-implication*)
                                (and (not (keywordp (hyperlink-rule L)))
                                     (reason-temporal? (hyperlink-rule L)))))
                          (degree-of-justification
                            (if temp
                              (* (adjust-for-decay (hyperlink-reason-strength L) decay)
                                 (minimum
                                   (mapcar #'hypernode-maximal-degree-of-justification (hyperlink-basis L))))
                              (adjust-for-decay
                                (minimum
                                  (cons (hyperlink-reason-strength L)
                                        (mapcar #'hypernode-maximal-degree-of-justification (hyperlink-basis L))))
                                decay))))
                     (when (> degree-of-justification adjusted-old-degree)
                       (setf (hypernode-maximal-degree-of-justification n) degree-of-justification)
                       (dolist (L (hypernode-hyperlinks node))
                         (setf (hyperlink-degree-of-justification L) (adjust-for-decay (hyperlink-degree-of-justification L) decay))
                         (when (and (not (keywordp (hyperlink-rule L))) (reason-temporal? (hyperlink-rule L)))
                           (setf (hyperlink-reason-strength L)
                                 (adjust-for-decay (hyperlink-reason-strength L) decay)))
                         (setf (hyperlink-temporal L) *cycle*))
                       (setf (hypernode-temporal-node n) *cycle*)
                       (setf (hyperlink-temporal L) *cycle*)
                       (let ((i-lists (c-list-corresponding-i-lists (hypernode-c-list n))))
                         (discharge-interest-in-defeaters n i-lists old-degree nil)
                         (discharge-interest-in n i-lists old-degree (1+ depth) nil nil)
                         (when (hypernode-processed? N)
                           (discharge-interest-schemes N old-degree (1+ depth)))
                         (when *use-reductio*
                           (cond ((hypernode-queue-node n)
                                  (discharge-immediate-reductios n old-degree nil (1+ depth) nil nil))
                                 (t (discharge-reductios n old-degree (1+ depth) nil)))))
                       (adjust-support-for-consequences n old-degree depth))))))
              ((eql (hypernode-maximal-degree-of-justification n) old-degree)
               (let ((degree-of-justification
                       (maximum
                         (cons (hyperlink-reason-strength L)
                               (mapcar #'hypernode-maximal-degree-of-justification (hyperlink-basis L))))))
                 (when (> degree-of-justification old-degree)
                   (setf (hypernode-maximal-degree-of-justification node) degree-of-justification)
                   (let ((i-lists (c-list-corresponding-i-lists (hypernode-c-list n))))
                     (discharge-interest-in-defeaters n i-lists old-degree nil)
                     (discharge-interest-in n i-lists old-degree (1+ depth) nil nil)
                     (when (hypernode-processed? N)
                       (discharge-interest-schemes N old-degree (1+ depth)))
                     (when *use-reductio*
                       (cond ((hypernode-queue-node n)
                              (discharge-immediate-reductios n old-degree nil (1+ depth) nil nil))
                             (t (discharge-reductios n old-degree (1+ depth) nil)))))
                   (adjust-support-for-consequences n old-degree depth))))))))

  (defun add-hyperlink (link node depth)
    ; (setf l link n node d depth)
    ; (when (eq link (hyperlink 21)) (setf l link n node d depth) (break))
    ;; (step (add-hyperlink l n d))
    (push link (hypernode-hyperlinks node))
    (let ((degree-of-justification
            (minimum (cons (hyperlink-reason-strength link)
                           (mapcar #'current-maximal-degree-of-justification (hyperlink-basis link))))))
      (cond ((and (hyperlink-temporal link) (not (eql (hypernode-temporal-node node) *cycle*)))
             (let* ((decay (expt *temporal-decay* (- *cycle* (hypernode-temporal-node node))))
                    (old-degree (adjust-for-decay (hypernode-maximal-degree-of-justification node) decay)))
               (when (> degree-of-justification old-degree)
                 (setf (hypernode-maximal-degree-of-justification node) degree-of-justification)
                 (setf (hypernode-temporal-node node) *cycle*)
                 (adjust-support-for-consequences node old-degree depth))))
            (t
              (let ((old-degree (hypernode-maximal-degree-of-justification node)))
                (when (> degree-of-justification old-degree)
                  (setf (hypernode-maximal-degree-of-justification node) degree-of-justification)
                  (adjust-support-for-consequences node old-degree depth)))))))

  (defun make-rebutting-defeater (variables base formula supposition antecedent* link)
    (let ((rebutting-defeater
            (cond (antecedent* (conj antecedent* (conj (gen-conjunction base) (neg formula))))
                  (variables (conj (gen-conjunction base) (neg formula)))
                  (t (neg formula))))
          (rebutting-variables
            (hypernode-variables (hyperlink-target link))))
      (multiple-value-bind
        (rebutting-interest i-list)
        (interest-for (list supposition rebutting-defeater) rebutting-variables nil nil)
        (cond ((null rebutting-interest)
               (setf rebutting-interest
                     (make-interest
                       :interest-number (incf *interest-number*)
                       :interest-sequent (list supposition rebutting-defeater)
                       :interest-formula rebutting-defeater
                       :interest-supposition supposition
                       :interest-variables rebutting-variables
                       :interest-supposition-variables (supposition-variables supposition)
                       :interest-defeatees (list link)
                       :interest-priority *base-priority*
                       :interest-generating-defeat-nodes (list (hyperlink-target link))))
               (store-interest rebutting-interest i-list)
               (pushnew rebutting-interest (hypernode-generated-defeat-interests (hyperlink-target link)))
               (when *display?*
                 (display-interest rebutting-interest)
                 (princ
                   "                                        Of interest as defeater for hyperlink ")
                 (princ (hyperlink-number link)) (terpri) (terpri))
               (when *log-on* (push rebutting-interest *reasoning-log*))
               (when (and *display?* *graphics-on* *graph-interests*)
                 (draw-i rebutting-interest *og*))
               (let ((priority (defeater-priority rebutting-interest)))
                 (queue-interest
                   rebutting-interest priority)
                 (apply-degenerate-backwards-reasons rebutting-interest priority 0)))
              (t
                (readopt-interest rebutting-interest (list link))
                (push rebutting-interest (hypernode-generated-defeat-interests (hyperlink-target link)))
                (push (hyperlink-target link) (interest-generating-defeat-nodes rebutting-interest))
                (setf (interest-defeatees rebutting-interest)
                      (cons link (interest-defeatees rebutting-interest)))))
        (dolist (node (unifying-nodes rebutting-interest))
          (when (subsetp= (hypernode-supposition node) supposition)
            (when *display?*
              (princ "  Node # ") (princ (hypernode-number node))
              (princ " defeats link # ")
              (princ (hyperlink-number link)) (terpri))
            (let ((DL (build-hyper-defeat-link node link)))
              (pushnew DL (hyperlink-defeaters link))
              (pushnew node (interest-discharging-nodes rebutting-interest))
              (pushnew DL (hypernode-supported-hyper-defeat-links node))))))))

  #| The following assumes that the sequent and members of the basis share the same
  sequent-supposition.  Basis is a list of conclusions. |#
  (defun adopt-interest-in-defeaters-for (link instantiations &optional bindings)
    (cond ((hyperlink-defeasible? link)
           (let ((variables nil)
                 (reverse-binding nil)
                 (reverse-binding* nil)
                 (binding* nil))
             (dolist (b bindings)
               (cond ((or (and (listp (cdr b)) (skolem-function (mem1 (cdr b))))
                          (skolem-function (cdr b))
                          (conclusion-variable (cdr b))
                          )
                      (push (car b) variables)
                      (push (cons (cdr b) (car b)) reverse-binding)
                      (push (cons (cdr b) (make-interest-variable)) reverse-binding*))
                     (t (push b binding*))))
             (let* ((S (hypernode-sequent (hyperlink-target link)))
                    (B (hyperlink-basis link))
                    (supposition
                      (subset
                        #'(lambda (P)
                            (every #'(lambda (b) (not (occur (car b) P :test 'equal))) reverse-binding))
                        (sequent-supposition S)))
                    (sup-remainder (setdifference (sequent-supposition S) supposition))
                    (antecedent (match-sublis reverse-binding sup-remainder :test 'equal))
                    (antecedent*
                      (gen-conjunction
                        (match-sublis reverse-binding* sup-remainder :test 'equal)))
                    (antecedent-variables
                      (subset #'(lambda (v) (occur v antecedent)) variables))
                    (sup
                      (if sup-remainder
                        (generalized-e-gen antecedent-variables (gen-conjunction antecedent))))
                    (new-sup (if sup (cons sup supposition) supposition))
                    (formula (match-sublis reverse-binding* (sequent-formula S)))
                    (base
                      (mapcar
                        #'(lambda (c m)
                            (cond ((is-desire c)
                                   (list 'I_desire_that
                                         (match-sublis reverse-binding*
                                                       (match-sublis m (hypernode-formula c)))))
                                  ((is-percept c)
                                   (let ((time (percept-date (hypernode-justification c))))
                                     (list 'it-appears-to-me-that
                                           (match-sublis reverse-binding*
                                                         (match-sublis m (mem2 (hypernode-formula c))))
                                           (list 'closed time time))))
                                  (t (match-sublis reverse-binding*
                                                   (match-sublis m (hypernode-formula c)) :test 'equal))))
                        B instantiations)))
               (when sup (queue-defeater-supposition sup))
               (when base
                 (make-undercutting-defeater base formula new-sup antecedent* link reverse-binding*))
               (make-rebutting-defeater variables base formula new-sup antecedent* link))))
          ((eq (hyperlink-rule link) :Q&I)
           (adopt-interest-in-Q&I-defeaters-for (hypernode-sequent (hyperlink-target link))))))

  (defun construct-interest-link
    (link0 node instantiations binding remaining-premises supposition degree
           max-degree depth priority interests &key new-variables)
    (when *trace* (indent depth) (princ "CONSTRUCT-INTEREST-LINK for interest ")
      (princ (interest-number (link-resultant-interest link0))) (princ " using ") (princ (link-rule link0))
      (princ " and nodes ") (princ (mapcar #'hypernode-number (link-supporting-nodes link0)))
      (terpri))
    (cond
      ((and (backwards-premise-p (car remaining-premises))
            (listp (bp-formula (car remaining-premises)))
            (equal (car (bp-formula (car remaining-premises))) 'define))
       (let* ((var (mem2 (bp-formula (car remaining-premises))))
              (def-instantiator (bp-instantiator (car remaining-premises))))
         (multiple-value-bind
           (new-binding new-vars match)
           (set-def-binding def-instantiator var binding)
           (when (funcall** (bp-condition1 (car remaining-premises)) nil new-binding)
             (cond ((cdr remaining-premises)
                    (construct-interest-link
                      link0 node instantiations new-binding (cdr remaining-premises)
                      supposition degree max-degree depth priority interests
                      :new-variables (append new-vars new-variables)))
                   ((funcall+
                      (interest-discharge-condition (link-resultant-interest link0)) nil (list t t)
                      (subst (cdr match) (car match)
                             (link-binding (car (interest-right-links (link-resultant-interest link0))))))
                    (cond
                      ((reason-conclusions-function (link-rule link0))
                       (dolist (P (funcall (reason-conclusions-function (link-rule link0)) new-binding))
                         (draw-conclusion
                           (car P) (cons node (link-supporting-nodes link0)) (link-rule link0) instantiations
                           (reason-discount-factor (link-rule link0)) depth nil (cdr P) :binding new-binding :interest
                           (link-resultant-interest link0) :link link0 :clues (link-clues link0))))
                      (t (draw-conclusion
                           (interest-formula (link-resultant-interest link0)) (cons node (link-supporting-nodes link0))
                           (link-rule link0) instantiations (reason-discount-factor (link-rule link0)) depth nil
                           (reason-defeasible-rule (link-rule link0)) :binding new-binding
                           :interest (link-resultant-interest link0) :link link0 :clues (link-clues link0)))
                      )))))))
      (t
        (let* ((premise0 (car remaining-premises))
               (premise
                 (if (backwards-premise-p premise0) premise0
                   (funcall premise0 nil binding))))
          (multiple-value-bind
            (interest-formula new-vars new-binding)
            (funcall (bp-instantiator premise) binding)
            (let ((link
                    (make-interest-link
                      :link-number (incf *interest-link-number*)
                      :link-resultant-interest (link-resultant-interest link0)
                      :link-interest-formula (remove-double-negation interest-formula)
                      :link-interest-condition (bp-condition2 premise)
                      :link-rule (link-rule link0)
                      :link-premise premise
                      :link-remaining-premises (cdr remaining-premises)
                      :link-supporting-nodes
                      (if (bp-clue? (link-premise link0))
                        (link-supporting-nodes link0) (cons node (link-supporting-nodes link0)))
                      :link-clues
                      (if (bp-clue? (link-premise link0))
                        (cons node (link-clues link0)) (link-clues link0))
                      :link-instantiations instantiations
                      :link-supposition supposition
                      :link-strength
                      (cond ((eq (link-rule link0) :answer)
                             (interest-maximum-degree-of-interest (link-resultant-interest link0)))
                            ((numberp (reason-strength (link-rule link0))) (reason-strength (link-rule link0)))
                            (t (interest-maximum-degree-of-interest (link-resultant-interest link0))))
                      :link-generating-node (link-generating-node link0)
                      :link-binding new-binding
                      :link-generating link0
                      )))
              (push link *interest-links*)
              (push link (interest-left-links (link-resultant-interest link0)))
              (compute-link-interest
                link (bp-condition1 premise) (bp-condition2 premise)
                degree max-degree depth priority (append new-vars new-variables)
                (bp-text-condition premise))
              (discharge-link link (1+ depth) (interest-degree-of-interest (link-resultant-interest link0)) priority interests)
              (apply-degenerate-backwards-reasons (link-interest link) priority (1+ depth))
              ))))))

  #| The priority is the priority of the inference-queue node from which this link
  is derived, if this value is known.  This simplifies the computation of the interest-priority
  for the new interests produced by this operation.  degree is the degree of interest of
  the resultant-interest. |#
  (defun DISCHARGE-LINK (link depth degree priority interests)
    ; (when (eq link (link 159)) (setf l link d depth dg degree p priority in interests) (break))
    ; (setf l link d depth dg degree p priority in interests)
    ;; (step (discharge-link l d dg p in))
    (when *trace* (indent depth) (princ "DISCHARGE-LINK: ") (princ link) (terpri))
    (let ((deductive-rule? (not (reason-defeasible-rule (link-rule link))))
          (hypernode-list nil)
          (interest (link-interest link))
          (reason (link-rule link))
          (condition (link-interest-condition link))
          ; (match (link-interest-match link))
          (match* (link-interest-reverse-match link))
          (spec (premise-hypernode-specifier (link-premise link))))
      (block nodes
             (dolist  (cl (i-list-corresponding-c-lists (interest-i-list interest)))
               (let* ((c-list (car cl))
                      (unifier0 (mem2 cl))
                      (unifier
                        (match-sublis match* unifier0)))
                 (dolist (node (c-list-nodes c-list))
                   (when (and (funcall+
                                (interest-discharge-condition interest) node unifier
                                (if spec (cons (cons spec node) (link-binding link)) (link-binding link)))
                              (or (not (hypernode-deductive-only node)) deductive-rule?)
                              (or (interest-non-reductio? interest) (deductive-node node)))
                     (when (and (deductive-node node)
                                (null condition)
                                (eq (mem2 unifier) t)
                                (subsetp= (match-sublis (mem1 unifier) (hypernode-supposition node))
                                          (link-supposition link)))
                       (setf hypernode-list (list (cons node unifier)))
                       (setf (interest-cancelling-node interest) node)
                       (return-from nodes))
                     (when (>= (current-maximal-degree-of-justification node) degree)
                       (push (cons node unifier) hypernode-list))))))
             (re-queue-interest link priority (link-interest link) degree))
      (dolist (nl hypernode-list)
        (let* ((node (car nl))
               (unifier (cdr nl))
               (unifiers
                 (appropriately-related-supposition
                   node (link-interest link) (link-supposition link) (interest-supposition-variables interest) unifier)))
          (when unifiers (setf (link-discharged link) t))
          (dolist (u unifiers)
            (let ((u* (merge-unifiers* unifier u)))
              (when (interest-cancelled (link-interest link)) (return-from discharge-link))
              (when
                (constrained-assignment
                  u* (hypernode-supposition-variables node) (interest-variables (link-interest link)))
                (when *display?*
                  (princ "                                        ") (princ "Hypernode #") (princ (hypernode-number node))
                  (princ " discharges interest #") (princ (interest-number interest)) (terpri) (terpri))
                (pushnew node (interest-discharging-nodes interest))
                ; (setf u* (convert-unifier-variables u* (hypernode-variables node)))
                (let
                  ((binding
                     (mapcar
                       #'(lambda (assoc) (cons (car assoc) (match-sublis (mem2 u*) (cdr assoc))))
                       (if spec (cons (cons spec node) (link-binding link)) (link-binding link))))
                   (instantiations
                     (cons (mem1 u*)
                           (mapcar #'(lambda (in) (merge-matches* in (mem2 u*))) (link-instantiations link))))
                   (supposition (match-sublis (mem2 u*) (link-supposition link))))
                  (cond
                    ((eq (link-rule link) :answer)
                     (push node (query-answers (link-resultant-interest link)))
                     (pushnew (link-resultant-interest link) (hypernode-answered-queries node))
                     (when (deductive-node node)
                       (when (and
                               (every
                                 #'(lambda (query)
                                     (or (eq query (link-resultant-interest link))
                                         (some #'deductive-node (query-answers query))))
                                 *ultimate-epistemic-interests*)
                               (not (some
                                      #'(lambda (Q) (eq (queue-item-kind Q) :query))
                                      *inference-queue*)))
                         (setf (hypernode-degree-of-justification node) 1.0)
                         (setf (query-answered? (link-resultant-interest link)) T)
                         (let ((deductive-links nil)
                               (deductive-nodes nil))
                           (dolist (L *new-links*)
                             (when (deductive-node (hyperlink-target L))
                               (push L deductive-links)
                               (push (hyperlink-target L) deductive-nodes)))
                           (dolist (N deductive-nodes) (setf (hypernode-degree-of-justification N) 1.0))
                           (dolist (L deductive-links) (setf (hyperlink-degree-of-justification L) 1.0))
                           (display-belief-changes
                             *new-links*
                             deductive-nodes
                             nil))
                         (dolist (instruction (query-positive-instructions (link-resultant-interest link)))
                           (funcall instruction node))
                         (when *display?*
                           (terpri)
                           (princ "             ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
                           (terpri))
                         ; (cancel-interest-in (link-interest link) 0)
                         (throw 'die nil)))
                     ; (record-query-answers link)
                     )
                    ((link-remaining-premises link)
                     (construct-interest-link
                       link node instantiations binding (link-remaining-premises link) supposition
                       (interest-degree-of-interest (link-interest link))
                       (interest-maximum-degree-of-interest (link-interest link)) (1+ depth) priority interests))
                    ((or
                       (some #'(lambda (L) (eq (link-rule L) ug)) (interest-left-links (link-resultant-interest link)))
                       (funcall+ (interest-discharge-condition interest) nil u binding))
                     (cond
                       ((reason-conclusions-function reason)
                        (dolist (P (funcall (reason-conclusions-function reason) binding))
                          (draw-conclusion
                            (car P) (cons node (link-supporting-nodes link)) reason instantiations
                            (reason-discount-factor reason) depth nil (cdr P) :binding binding :interest
                            (link-resultant-interest link) :link link :clues (link-clues link))))
                       (t
                         (draw-conclusion
                           (interest-formula (link-resultant-interest link)) (cons node (link-supporting-nodes link)) reason
                           instantiations (reason-discount-factor reason) depth nil (reason-defeasible-rule reason)
                           :binding binding :interest (link-resultant-interest link) :link link :clues (link-clues link)))
                       )))))))
          (when (and (interest-cancelling-node interest) (every #'link-discharged (interest-right-links interest)))
            (cancel-interest-in interest (if *trace* depth 0)))
          (when (and
                  unifiers
                  (not (interest-cancelled interest))
                  (equal (hypernode-formula node) (interest-formula interest))
                  (subsetp= (hypernode-supposition node) (interest-supposition interest))
                  (dolist (sup-node (interest-generated-suppositions interest))
                    (when
                      (and
                        (equal (hypernode-generating-interests sup-node) (list interest))
                        (deductive-in node sup-node))
                      (cancel-node sup-node (if *trace* depth 0)))))))
        )))

  (defun reason-substantively-from-backwards-reason (reason interest depth priority)
    ; (when (eq interest (interest 133)) (setf r reason n interest d depth p priority) (break))
    ;; (step (reason-substantively-from-backwards-reason r n d p))
    (when *trace* (indent depth) (princ "REASON-SUBSTANTIVELY-FROM-BACKWARDS-REASON ")
      (princ reason) (terpri))
    (multiple-value-bind
      (binding instantiation)
      (funcall (b-reason-conclusions-binding-function reason)
               (interest-formula interest) (interest-variables interest))
      (when (and instantiation (funcall* (b-reason-condition reason) binding))
        (let ((supposition (match-sublis instantiation (interest-supposition interest))))
          (cond
            ((reason-forwards-premises reason)
             (construct-interest-scheme
               reason nil interest binding nil
               (reason-forwards-premises reason) nil (1+ depth) priority supposition))
            (t (make-backwards-inference
                 reason binding interest (1+ depth) priority nil nil nil supposition)))))))

  (defun reason-degenerately-backwards-from-reason-node (interest priority depth d-node)
    ; (when (and (eq interest (interest 24)) (eq d-node (d-node 27))) (setf i interest p priority d depth dn d-node) (break))
    ;; (step (reason-degenerately-backwards-from-reason-node i p d dn))
    (when *trace* (indent depth) (princ "REASON-DEGENERATELY-BACKWARDS-FROM-REASON-NODE ")
      (princ interest) (princ " and ") (princ d-node) (terpri))
    (dolist (reason (d-node-degenerate-backwards-reasons d-node))
      (when (interest-cancelled interest) (throw 'apply-backwards-reasons nil))
      (when (or (not (interest-deductive interest)) (not (reason-defeasible-rule reason)))
        (let ((strength (reason-strength reason)))
          (when
            (or (not (numberp strength))
                (and (>= strength (interest-degree-of-interest interest))
                     (or (null (interest-last-processed-degree-of-interest interest))
                         (< strength (interest-last-processed-degree-of-interest interest)))))
            (let ((reason-function (reason-function reason)))
              (cond
                (reason-function (funcall (reason-function reason) interest (1+ depth) priority))
                (t (reason-substantively-from-backwards-reason reason interest (1+ depth) priority)))))))))

  (defun reason-degenerately-backwards-from-dominant-reason-nodes
    (interest priority depth d-node)
    (when *trace* (indent depth)
      (princ "REASON-DEGENERATELY-BACKWARDS-FROM-DOMINANT-REASON-NODES ")
      (princ interest) (princ " and ") (princ d-node) (terpri))
    (reason-degenerately-backwards-from-reason-node interest priority (1+ depth) d-node)
    (let ((pn (d-node-parent d-node)))
      (when pn (reason-degenerately-backwards-from-dominant-reason-nodes interest priority (1+ depth) pn))))

  (defun apply-degenerate-backwards-reasons (interest priority depth)
    ; (when (eq interest (interest 97)) (setf i interest p priority d depth) (break))
    ;; (step (apply-degenerate-backwards-reasons i p d))
    (when *trace* (indent depth) (princ "APPLY-DEGENERATE-BACKWARDS-REASONS ") (princ interest) (terpri))
    (catch 'apply-backwards-reasons
           (let* ((i-list (interest-i-list interest))
                  (d-node (i-list-d-node i-list)))
             (reason-degenerately-backwards-from-dominant-reason-nodes interest priority (1+ depth) d-node))))

  (defun construct-initial-interest-link
    (supporting-nodes instantiations reason resultant-interest depth priority binding supposition
                      &key generating-node remaining-premises clues new-variables)
    ; (when (eq *cycle* 518) (setf sn supporting-nodes in instantiations r reason ri resultant-interest d depth p priority b binding s supposition gn generating-node rp remaining-premises cl clues nv new-variables) (break))
    ; (setf sn supporting-nodes in instantiations r reason ri resultant-interest d depth p priority b binding s supposition gn generating-node rp remaining-premises cl clues nv new-variables)
    ;; (step (construct-initial-interest-link sn in r ri d p b s :generating-node gn :remaining-premises rp :clues cl :new-variables nv))
    (when *trace* (indent depth) (princ "CONSTRUCT-INITIAL-INTEREST-LINK for interest ")
      (princ (interest-number resultant-interest)) (princ " using ") (princ reason) (terpri))
    (when (null remaining-premises) (setf remaining-premises (reason-backwards-premises reason)))
    (cond
      ((and (backwards-premise-p (car remaining-premises))
            (listp (bp-formula (car remaining-premises)))
            (equal (car (bp-formula (car remaining-premises))) 'define))
       (let* ((var (mem2 (bp-formula (car remaining-premises))))
              (def-instantiator (bp-instantiator (car remaining-premises))))
         (multiple-value-bind
           (new-binding new-vars)
           (set-def-binding def-instantiator var binding)
           (when (funcall** (bp-condition1 (car remaining-premises)) nil new-binding)
             (cond ((cdr remaining-premises)
                    (construct-initial-interest-link
                      supporting-nodes instantiations reason resultant-interest depth priority new-binding
                      supposition :generating-node generating-node :remaining-premises (cdr remaining-premises)
                      :clues clues :new-variables (append new-vars new-variables)))
                   ((reason-conclusions-function reason)
                    (dolist (P (funcall (reason-conclusions-function reason) new-binding))
                      (draw-conclusion
                        (car P) supporting-nodes
                        reason instantiations (reason-discount-factor reason) depth nil
                        (reason-defeasible-rule reason) :binding new-binding
                        :interest resultant-interest :clues clues)))
                   (t (draw-conclusion
                        (interest-formula resultant-interest) supporting-nodes
                        reason instantiations (reason-discount-factor reason) depth nil
                        (reason-defeasible-rule reason) :binding new-binding
                        :interest resultant-interest :clues clues)))))))
      (t
        (when (null resultant-interest)
          (multiple-value-bind
            (formulas vars)
            (funcall (reason-conclusions-function reason) binding)
            (multiple-value-bind
              (i-list match)
              (i-list-for (caar formulas) vars)
              (let ((sup (if i-list (match-sublis match supposition) supposition)))
                (setf resultant-interest
                      (if i-list
                        (find-if #'(lambda (i) (== (interest-supposition i) sup))
                                 (i-list-interests i-list))))))))
        (let* ((premise0 (car remaining-premises))
               (premise
                 (if (backwards-premise-p premise0) premise0
                   (funcall premise0
                            (interest-defeater-binding resultant-interest) binding)))
               (discharge (if (and (backwards-reason-p reason) (b-reason-discharge reason))
                            (remove-double-negation
                              (match-sublis binding (b-reason-discharge reason))))))
          (multiple-value-bind
            (generating-node new?)
            (if (and discharge (null supporting-nodes))
              (queue-supposition
                discharge (list discharge)
                (subset #'(lambda (v) (occur v discharge)) (interest-variables resultant-interest))
                (reason-discount-factor reason) resultant-interest)
              generating-node)
            (when (or generating-node new? (null discharge) supporting-nodes)
              (multiple-value-bind
                (interest-formula new-vars new-binding)
                (funcall (bp-instantiator premise) binding)
                (setf interest-formula (remove-double-negation interest-formula))
                (when (or (not (equal interest-formula (interest-formula resultant-interest)))
                          (not (mem discharge supposition)))
                  (let ((link
                          (make-interest-link
                            :link-number (incf *interest-link-number*)
                            :link-resultant-interest resultant-interest
                            :link-interest-formula interest-formula
                            :link-interest-condition (bp-condition2 premise)
                            :link-rule reason
                            :link-premise premise
                            :link-remaining-premises (cdr remaining-premises)
                            :link-supporting-nodes supporting-nodes
                            :link-clues clues
                            :link-instantiations instantiations
                            :link-supposition (if (and discharge (not (mem discharge supposition)))
                                                (cons discharge supposition) supposition)
                            :link-strength
                            (cond ((eq reason :answer)
                                   (interest-maximum-degree-of-interest resultant-interest))
                                  ((numberp (reason-strength reason)) (reason-strength reason))
                                  (t (interest-maximum-degree-of-interest resultant-interest)))
                            :link-generating-node generating-node
                            :link-binding new-binding
                            )))
                    (push link *interest-links*)
                    (push link (interest-left-links resultant-interest))
                    (compute-link-interest
                      link (bp-condition1 premise) (bp-condition2 premise)
                      (interest-degree-of-interest resultant-interest)
                      (interest-maximum-degree-of-interest resultant-interest) depth priority
                      (append new-vars new-variables) (bp-text-condition premise))
                    (discharge-link
                      link (1+ depth) (interest-degree-of-interest resultant-interest)
                      (interest-priority (link-interest link)) nil)
                    (apply-degenerate-backwards-reasons
                      (link-interest link) (interest-priority (link-interest link)) (1+ depth))
                    link)))))))))

  (defun make-backwards-inference
    (reason binding interest depth priority supporting-nodes clues instantiations supposition
            &optional generating-node)
    (cond
      ((or (reason-backwards-premises reason) (reason-backwards-premises-function reason))
       (construct-initial-interest-link
         supporting-nodes instantiations reason interest depth priority binding supposition
         :generating-node generating-node :remaining-premises (reason-backwards-premises reason) :clues clues))
      ((or (numberp (reason-strength reason))
           (>= (funcall (reason-strength reason) binding supporting-nodes) (interest-degree-of-interest interest)))
       (dolist (P (funcall (reason-conclusions-function reason) binding))
         (draw-conclusion
           (car P) supporting-nodes reason instantiations (reason-discount-factor reason) depth nil (cdr P)
           :binding binding :clues clues)))))

  (defun construct-interest-scheme
    (reason node interest binding instantiations remaining-premises is0
            depth priority supposition)
    (cond
      ((and (forwards-premise-p (car remaining-premises))
            (listp (fp-formula (car remaining-premises)))
            (equal (car (fp-formula (car remaining-premises))) 'define))
       (let* ((var (mem2 (fp-formula (car remaining-premises))))
              (def-instantiator (fp-instantiator (car remaining-premises)))
              (new-binding (set-def-binding def-instantiator var binding)))
         (when (funcall** (fp-condition (car remaining-premises)) nil new-binding)
           (cond ((cdr remaining-premises)
                  (construct-interest-scheme
                    reason node interest new-binding instantiations (cdr remaining-premises)
                    is0 depth priority supposition))
                 (is0
                   (make-backwards-inference
                     (is-reason is0) new-binding (is-target-interest is0) (1+ depth) priority
                     (if (fp-clue? (is-premise is0)) (is-basis is0) (cons node (is-basis is0)))
                     (if (fp-clue? (is-premise is0)) (cons node (is-clues is0)) (is-clues is0))
                     instantiations supposition (is-generating-node is0)))
                 (t
                   (make-backwards-inference
                     reason new-binding interest (1+ depth) priority nil nil instantiations supposition nil))))))
      (t
        (let* ((basis
                 (when is0
                   (cond ((fp-clue? (is-premise is0)) (is-basis is0))
                         (t (if node (cons node (is-basis is0)) (is-basis is0))))))
               (clues
                 (when is0
                   (cond ((fp-clue? (is-premise is0)) (if node (cons node (is-clues is0)) (is-clues is0)))
                         (t (is-clues is0)))))
               (discharge (if (and (null basis)
                                   (null (if is0 (is-generating-node is0)))
                                   (b-reason-discharge reason))
                            (remove-double-negation
                              (match-sublis binding (b-reason-discharge reason))))))
          (multiple-value-bind
            (generating-node new-sup?)
            (if discharge
              (queue-supposition
                discharge (list discharge)
                (subset #'(lambda (v) (occur v discharge)) (interest-variables interest))
                (reason-discount-factor reason) interest))
            (when (or new-sup? (null discharge))
              (let* ((premise (mem1 remaining-premises))
                     (profile (reason-code (fp-formula premise) (reason-variables reason)))
                     (d-node (pursue-d-node-for profile *top-d-node*))
                     (generating-node
                       (cond (new-sup? generating-node) (is0 (is-generating-node is0))))
                     (interest-scheme
                       (when d-node
                         (find-if
                           #'(lambda (is)
                               (and
                                 (eq (is-reason is) reason)
                                 (eq (is-premise is) premise)
                                 (eq (is-target-interest is) interest)
                                 (eq (is-basis is) basis)
                                 (eq (is-remaining-premises is) (cdr remaining-premises))
                                 (eq (is-binding is) binding)
                                 (eq (is-supposition is) supposition)
                                 (eq (is-generating-node is) generating-node)))
                           (d-node-interest-schemes d-node)))))
                (when (null interest-scheme)
                  (incf *interest-scheme-number*)
                  (setf interest-scheme
                        (make-interest-scheme
                          :reason reason
                          :premise premise
                          :number (incf *is-number*)
                          :target-interest interest
                          :basis basis
                          :clues clues
                          :remaining-premises (cdr remaining-premises)
                          :binding binding
                          :instantiations instantiations
                          :supposition supposition
                          :generating-node generating-node
                          :supposition-variables (supposition-variables supposition)
                          :used-premise-variables
                          (if is0 (union (fp-variables premise) (is-used-premise-variables is0))
                            (fp-variables premise))
                          :used-variables
                          (if is0 (union (hypernode-variables node) (is-used-variables is0))
                            (interest-variables interest))))
                  (if d-node
                    (store-interest-scheme-at-d-node interest-scheme d-node)
                    (store-interest-scheme interest-scheme profile *top-d-node*))
                  (when *display?* (display-interest-scheme interest-scheme))
                  (if node (pushnew interest-scheme (c-list-generated-instantiated-premises (hypernode-c-list node))))
                  (when is0 (pushnew interest-scheme (is-derived-premises is0)))
                  (discharge-interest-scheme
                    interest-scheme (is-d-node interest-scheme) priority depth))
                interest-scheme)))))))

  (defun reason-from-interest-scheme (node priority depth is)
    ; (when (and (eq node (node 56)) (eq is (interest-scheme 20))) (setf n node p priority d depth i is) (break))
    ;; (step (reason-from-interest-scheme n p d i))
    (when *trace* (indent depth) (princ "REASON-FROM-INTEREST-SCHEME ")
      (princ (is-number is)) (terpri))
    (cond
      ((is-instance-function is) (funcall (is-instance-function is) node (1+ depth) priority))
      (t
        (let* ((vars (if node (hypernode-variables node)))
               (formula (if node (hypernode-formula node))))
          (multiple-value-bind
            (binding0 instantiation0)
            (funcall (fp-binding-function (is-premise is)) formula vars)
            (when
              (and instantiation0 (equal (fp-kind (is-premise is)) (hypernode-kind node)))
              (let ((unifier
                      (binding-unifier
                        binding0 (is-binding is)
                        (is-used-premise-variables is) vars (is-used-variables is))))
                (when unifier
                  (let ((unifiers
                          (appropriately-related-supposition
                            node (is-target-interest is)
                            (if (b-reason-discharge (is-reason is))
                              (cons (remove-double-negation
                                      (match-sublis (is-binding is) (b-reason-discharge (is-reason is))))
                                    (is-supposition is))
                              (is-supposition is))
                            (is-supposition-variables is) unifier)))
                    (dolist (u unifiers)
                      (let ((u* (merge-unifiers* unifier u)))
                        (when (interest-cancelled (is-target-interest is))
                          (return-from reason-from-interest-scheme))
                        (when
                          (constrained-assignment
                            u* (hypernode-supposition-variables node)
                            (interest-variables (is-target-interest is)))
                          (let ((binding (rectify-binding binding0 u* is))
                                (spec (premise-hypernode-specifier (is-premise is))))
                            (when spec (push (cons spec node) binding))
                            (when (funcall** (fp-condition (is-premise is)) node binding)
                              (let
                                ((instantiations
                                   (if (fp-clue? (is-premise is))
                                     (mapcar #'(lambda (in) (merge-matches* (mem2 u*) in))
                                             (is-instantiations is))
                                     (cons (merge-matches* (mem1 u*) instantiation0)
                                           (mapcar #'(lambda (in) (merge-matches* (mem2 u*) in))
                                                   (is-instantiations is)))))
                                 (supposition (match-sublis (mem2 u) (is-supposition is))))
                                (cond
                                  ((is-remaining-premises is)
                                   (construct-interest-scheme
                                     (is-reason is) node (is-target-interest is) binding
                                     instantiations (is-remaining-premises is)
                                     is (1+ depth) priority supposition))
                                  (t
                                    (make-backwards-inference
                                      (is-reason is) binding (is-target-interest is) (1+ depth) priority
                                      (if (fp-clue? (is-premise is)) (is-basis is) (cons node (is-basis is)))
                                      (if (fp-clue? (is-premise is)) (cons node (is-clues is)) (is-clues is))
                                      instantiations supposition (is-generating-node is)))))
                              ))))))))))))))

  (defun discharge-interest-scheme (interest-scheme d-node priority depth)
    (when *trace* (indent depth) (princ "DISCHARGE-INTEREST-SCHEME ")
      (princ (is-number interest-scheme)) (terpri))
    (dolist (c-list (d-node-c-lists d-node))
      (dolist (node (c-list-processed-nodes c-list))
        (reason-from-interest-scheme node priority (1+ depth) interest-scheme)))
    (dolist (test (d-node-discrimination-tests d-node))
      (discharge-interest-scheme interest-scheme (cdr test) priority (1+ depth))))
  )

#| This is the default computation of degree-of-preference for premises.  Premises
are triples consisting of a formula, a supposition, and a degree-of-justification.
Premises are queued for immediate retrieval. |#
(defun premise-preference (premise)
  (/ (mem2 premise) (complexity (mem1 premise))))

(defstruct (goal
	    (:print-function
	     (lambda (goal stream depth)
	       (declare (ignore depth))
	       (princ "#<goal: " stream)
	       (princ (pretty (goal-formula goal)) stream)
	       (princ ">" stream)))
	    (:conc-name nil))
  (goal-number 0)
  (goal-formula nil)
  (goal-strength 1)
  (goal-supporting-node nil)  ;; the node supporting this as a suitable goal
  (goal-generating-desire nil)  ;; the desire, if there is on, that generates the goal
  ; (plans-for nil)  ;; the list of candidate plans that aim at the satisfaction of this goal
  ; (user-question-asked? nil)
  )

(defstruct (desire
	    (:print-function
	     (lambda (desire stream depth)
	       (declare (ignore depth))
	       (princ "#<desire: " stream)
	       (princ (pretty (desire-content desire)) stream)
	       (princ ">" stream)))
	    (:conc-name nil))
  (desire-number 0)
  (desire-content nil)
  (desire-object nil)  ;; the object of a desire will be a goal
  (desire-strength 0)
  (desire-generated-plans nil)
  (desire-generating-interest nil)  ;; for epistemic-desires
  (desire-hypernode nil))  ;; the hypernode recording the desire

(defun goal-generating-interest (goal)
  (let ((desire (goal-generating-desire goal)))
    (when desire (desire-generating-interest desire))))

#| This is the default computation of degree-of-preference for desires. |#
(defun desire-preference (desire)
  (/ (desire-strength desire) (complexity (desire-content desire))))

#| This is the default computation of degree-of-preference for percepts. |#
(defun percept-preference (percept)
  (/ (percept-clarity percept) (complexity (percept-content percept))))

#| This reverses the default computation of degree-of-preference to compute priority
from preference. |#
(defun retrieved-interest-priority (preference complexity)
  (* complexity preference))

#| The following is the default computation of interest-priority for an interest on
the inference-queue that is concluded. |#
(defun concluded-interest-priority (Q)
  (declare (ignore Q))
  *concluded-interest-priority*)

;======================================================
;------------------------------------------- REASONING ---------------------------------------

#| The following turn various displays on and off. |#
(defun trace-on () (setf *display?* t) (setf *trace* t))
(defun trace-off () (setf *trace* nil *start-trace* nil))
(defun trace-from (n) (setf *start-trace* n *display?* nil *trace* nil))
(defun display-on () (setf *display?* t))
(defun display-off () (setf *display?* nil *trace* nil *start-trace* nil *start-display* nil))
(defun display-from (n) (setf *display?* nil *trace* nil *start-trace* nil *start-display* n))
(defun proof-on () (setf *proofs?* t))
(defun proof-off () (setf *proofs?* nil))
(defun logic-on () (setf *use-logic* t) (setf *use-reductio* t))
(defun logic-off () (setf *use-logic* nil) (setf *use-reductio* nil))
(defun reductio-on () (setf *use-reductio* t) (setf *use-logic* t))
(defun reductio-off () (setf *use-reductio* nil))
(defun log-on () (setf *log-on* t))
(defun log-off () (setf *log-on* nil))
(defun IQ-on () (setf *display-inference-queue* t))
(defun IQ-off () (setf *display-inference-queue* nil))
(defun graph-log-on () (setf *graph-log* t))
(defun graph-log-off () (setf *graph-log* nil))

#| When graphics-pause is on, the reasoning-display pauses after printing the node display
and before graphing the node, and waits for a character (preferably a space) to be typed
in the Listener. |#
(defun graphics-pause-on () (setf *graphics-pause* t))
(defun graphics-pause-off () (setf *graphics-pause* nil))

(defun store-backwards-reason-at-d-node (reason d-node)
  ; (when (eq reason null-plan) (setf r reason d d-node) (break))
  (cond ((b-reason-immediate reason)
         (push reason (d-node-degenerate-backwards-reasons d-node)))
        ((reason-backwards-premises reason)
         (push reason (d-node-backwards-reasons d-node)))
        (t (push reason (d-node-degenerate-backwards-reasons d-node))))
  d-node)

#| Test is the final member of the formula-profile for the hypernode-formula. |#
(defun store-backwards-reason-at-new-d-node (reason d-node test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push dn *discrimination-net*)
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (store-backwards-reason-at-d-node reason dn)))

(defun index-backwards-reason-at-new-nodes (reason d-node profile test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (push dn *discrimination-net*)
    (let ((desc (cdr profile)))
      (cond (desc (index-backwards-reason-at-new-nodes reason dn desc (car profile)))
            (t (store-backwards-reason-at-new-d-node reason dn (car profile)))))))

(defun index-backwards-reason (reason profile d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node)))
        (new-profile (cdr profile)))
    (cond (dn
            (cond
              (new-profile (index-backwards-reason reason new-profile dn))
              (t (store-backwards-reason-at-d-node reason dn))))
          (new-profile
            (index-backwards-reason-at-new-nodes
              reason d-node new-profile (car profile)))
          (t
            (store-backwards-reason-at-new-d-node reason d-node (car profile))))))

#| This returns the d-node at which the premise is stored. |#
(defun store-backwards-reason (reason profile)
  (cond
    (profile (index-backwards-reason reason profile *top-d-node*))
    (t (store-backwards-reason-at-d-node reason *top-d-node*))))

(defun store-forwards-reason-at-d-node (reason premise d-node)
  (let ((ip
          (make-instantiated-premise
            :reason reason
            :premise premise
            :remaining-premises (cdr (reason-forwards-premises reason))
            :used-premise-variables (fp-variables premise)
            :d-node d-node
            :number (incf *ip-number*)
            :initial? t)))
    (push ip (d-node-forwards-reasons d-node))
    (setf (ip-d-node ip) d-node)
    ip))

#| Test is the final member of the formula-profile for the hypernode-formula. |#
(defun store-forwards-reason-at-new-d-node (reason premise d-node test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push dn *discrimination-net*)
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (store-forwards-reason-at-d-node reason premise dn)))

(defun index-forwards-reason-at-new-nodes
  (reason premise d-node profile test)
  (let ((dn (make-d-node
              :d-node-number (incf *d-node-number*)
              :d-node-description (cons test (d-node-description d-node))
              :d-node-parent d-node)))
    (push (cons test dn) (d-node-discrimination-tests d-node))
    (push dn *discrimination-net*)
    (let ((desc (cdr profile)))
      (cond (desc (index-forwards-reason-at-new-nodes reason premise dn desc (car profile)))
            (t (store-forwards-reason-at-new-d-node reason premise dn (car profile)))))))

(defun index-forwards-reason (reason premise profile d-node)
  (let ((dn (e-assoc (car profile) (d-node-discrimination-tests d-node)))
        (new-profile (cdr profile)))
    (cond (dn
            (cond
              (new-profile (index-forwards-reason reason premise new-profile dn))
              (t (store-forwards-reason-at-d-node reason premise dn))))
          (new-profile
            (index-forwards-reason-at-new-nodes
              reason premise d-node new-profile (car profile)))
          (t
            (store-forwards-reason-at-new-d-node reason premise d-node (car profile))))))

#| This returns the ip at which the premise is stored. |#
(defun store-forwards-reason (reason premise profile)
  (cond
    (profile (index-forwards-reason reason premise profile *top-d-node*))
    (t (store-forwards-reason-at-d-node reason premise *top-d-node*))))

(defun compute-forwards-reason-d-nodes ()
  (dolist (reason *forwards-reasons*)
    (let* ((premise (mem1 (reason-forwards-premises reason)))
           (profile (reason-code (fp-formula premise) (fp-variables premise)))
           (ip (store-forwards-reason reason premise profile)))
      (setf (reason-instantiated-premise reason) ip))))

(defun compute-backwards-reason-d-nodes ()
  (dolist (reason *backwards-reasons*)
    (when (reason-conclusions reason)
      (let ((profile (reason-code (mem1 (reason-conclusions reason)) (reason-variables reason))))
        (store-backwards-reason reason profile)))))

(defun initialize-discrimination-net ()
  (setf *top-d-node* (make-d-node :d-node-number (setf *d-node-number* 1)))
  (setf *conditional-node*
        (make-d-node :d-node-number (incf *d-node-number*) :d-node-parent *top-d-node*))
  (setf *undercutter-node*
        (make-d-node :d-node-number (incf *d-node-number*) :d-node-parent *top-d-node*))
  (setf *conjunctive-undercutter-node*
        (make-d-node :d-node-number (incf *d-node-number*) :d-node-parent *undercutter-node*))
  (setf (d-node-discrimination-tests *top-d-node*)
        (list (cons '((1) . ->) *conditional-node*)
              (cons '((1) . @) *undercutter-node*)))
  (setf *discrimination-net*
        (list *top-d-node* *conditional-node* *undercutter-node* *conjunctive-undercutter-node*))
  (setf (d-node-discrimination-tests *undercutter-node*)
        (list (cons '((2 1) . &) *conjunctive-undercutter-node*)))
  (compute-forwards-reason-d-nodes)
  (compute-backwards-reason-d-nodes))

(defun adopt-interest-in-premise-defeater (S node)
  (let* ((supposition (sequent-supposition S))
         (formula (sequent-formula S))
         (rebutting-interest
           (let ((interests (interests-for (neg formula) nil)))
             (when interests
               (find-if #'(lambda (i)
                            (and (null (interest-deductive i))
                                 (== (interest-supposition i) supposition)))
                        interests)))))
    (cond ((null rebutting-interest)
           (setf rebutting-interest
                 (make-interest
                   :interest-number (incf *interest-number*)
                   :interest-sequent (list supposition (neg formula))
                   :interest-formula (neg formula)
                   :interest-supposition supposition
                   :interest-priority *base-priority*
                   :interest-defeatees (hypernode-hyperlinks node)))
           (store-interest rebutting-interest)
           (when *display?*
             (display-interest rebutting-interest)
             (princ
               "                                        Of interest as defeater for hypernode ")
             (princ *hypernode-number*) (terpri))
           (when *log-on*
             (push rebutting-interest *reasoning-log*)
             (when (and *display?* *graphics-on* *graph-interests*) (draw-i rebutting-interest *og*)))
           (queue-interest rebutting-interest (defeater-priority rebutting-interest)))
          (t
            (readopt-interest rebutting-interest (list node))))))

#| Premises are pairs (formula, degree-of-justification). |#
(defun queue-premise (premise)
  ; (setf P premise)
  (let* ((formula (mem1 premise))
         (sequent (list nil formula))
         (node
           (make-hypernode
             :hypernode-number (incf *hypernode-number*)
             :hypernode-sequent sequent
             :hypernode-formula formula
             :hypernode-variables (formula-hypernode-variables formula)
             :hypernode-kind :inference
             :hypernode-justification :given
             :hypernode-maximal-degree-of-justification 1.0
             :hypernode-nearest-defeasible-ancestors (list nil)
             :hypernode-degree-of-justification (mem2 premise)
             :hypernode-old-degree-of-justification (mem2 premise)
             :hypernode-discounted-node-strength (mem2 premise)
             :hypernode-background-knowledge (mem4 premise)))
         (queue-node
           (make-inference-queue-node
             :queue-number (incf *queue-number*)
             :queue-item node
             :queue-item-kind :conclusion
             :queue-discounted-strength (mem2 premise)
             :queue-item-complexity (complexity sequent)))
         (link (make-hyperlink
                 :hyperlink-number (incf *hyperlink-number*)
                 :hyperlink-basis nil
                 :hyperlink-rule :given
                 :hyperlink-target node
                 :hyperlink-defeasible? t
                 :hyperlink-degree-of-justification (mem2 premise)
                 :hyperlink-nearest-defeasible-ancestors (list (list node)))))
    (setf (hypernode-queue-node node) queue-node)
    (setf (hypernode-hyperlinks node) (list link))
    (when (not (eql (mem2 premise) 1.0))
      (setf (hypernode-nearest-defeasible-ancestors node) (list (list node)))
      (when (not (mem4 premise))
        (adopt-interest-in-premise-defeater sequent node)))
    (setf (queue-degree-of-preference queue-node) (premise-preference premise))
    (push node *hypergraph*)
    (if *log-on* (push node *reasoning-log*))
    (when *display?* (display-unsupported-hypernode node))
    (store-hypernode node formula)
    (discharge-interest-in
      node (c-list-corresponding-i-lists (hypernode-c-list node)) nil t 1 nil)
    (setf *inference-queue*
          (ordered-insert queue-node *inference-queue* #'i-preferred))
    ))

(defun initialize-reasoner ()
  (setf *new-links* nil)
  (setf *hypergraph* nil)
  (setf *processed-desires* nil)
  (setf *desires* nil)
  (setf *percepts* nil)
  (setf *interest-links* nil)
  (setf *inference-queue* nil)
  (setf *hyperlinks* nil)
  (setf *interests* nil)
  (setf *interest-schemes* nil)
  (setf *hyper-defeat-links* nil)
  (setf *reductio-supposition-nodes* nil)
  (setf *non-reductio-supposition-nodes* nil)
  (setf *altered-nodes* nil)
  (setf *reasoning-log* nil)
  (setf *direct-reductio-interests* nil)
  (setf *Q&I-modules* nil)
  (setf *inherited-non-reductio-suppositions* nil)
  (setf *skolem-free-suppositions* nil)
  (setf *constructed-plans* nil)
  (setf *constructed-goals* nil)
  (setf *constructed-desires* nil)
  (setf pause-flag nil)
  (setf *cycle* 0)
  (setf *hypernode-number* 0)
  (setf *hyperlink-number* 0)
  (setf *interest-number* 0)
  (setf *interest-scheme-number* 0)
  (setf *queue-number* 0)
  (setf *interest-link-number* 0)
  (setf *hyper-defeat-link-number* 0)
  (setf *unused-suppositions* 0)
  (setf *gensym-counter* 0)
  (setf *ip-number* 0)
  (setf *is-number* 0)
  (setf *plan-number* 0)
  (setf *goal-number* 0)
  (setf *executable-operations* nil)
  (setf *deleted-arguments* nil)
  (setf *forwards-reasons*
        (if *use-logic*
          (append *forwards-logical-reasons* *forwards-substantive-reasons*)
          *forwards-substantive-reasons*))
  (setf *backwards-reasons*
        (if *use-logic*
          (append *backwards-logical-reasons* *backwards-substantive-reasons*)
          *backwards-substantive-reasons*))
  (initialize-discrimination-net)
  (when (and *display?* *graphics-on*) (make-oscar-window))
  (setf *query-number* (length *fixed-ultimate-epistemic-interests*))
  (dolist (query *fixed-ultimate-epistemic-interests*)
    (setf (query-answered? query) nil)
    (setf (query-answers query) nil)
    (setf (query-interest query) nil)
    (setf (query-negative-interest query) nil)
    (setf (query-queue-node query) nil))
  (dolist (premise *premises*)
    (when (null (mem3 premise)) (pull premise *premises*) (queue-premise premise)))
  (setf *ultimate-epistemic-interests* *fixed-ultimate-epistemic-interests*)
  (when (and *display?* *graphics-on*)
    (dolist (node (reverse *hypergraph*))
      (draw-n node *og* *nodes-displayed*) (push node *nodes-displayed*)))
  (if (not (boundp '*display?*)) (setf *display?* nil)))

(defun premise-code* (P variables descriptor)
  (cond ((listp P)
         (let ((description nil) (elt-num 1) (term-list nil))
           (cond
             ;; This handles notational variants.
             ((or (eq (car p) 'all) (eq (car P) 'some))
              (setf P
                    (cons (car P) (subst (list 'q-var (incf *quantifier-number*)) (mem2 P) (cddr P)))))
             ((and (symbolp (car P))
                   (not (member (car P) *operators*))
                   (not (member (car P) '(~ & v -> <-> all some ? @))))
              (setf term-list (cdr P))
              (setf P (list (car P)))))
           (dolist (Q P)
             (when (not (member Q variables))
               (let ((Q-descriptor (cons elt-num descriptor)))
                 (cond ((not (listp Q))
                        (when (not (member Q variables))
                          (push (cons (reverse Q-descriptor) Q) description)))
                       (t
                         (multiple-value-bind (d tl) (premise-code* Q variables Q-descriptor)
                           (setf term-list (append tl term-list))
                           (setf description (append d description))
                           )))))
             (incf elt-num))
           (values description term-list)))
        ((not (member P variables)) (values (list (cons descriptor P)) nil))))

(defun premise-code (P variables)
  (when P
    (setf *quantifier-number* 0)
    (multiple-value-bind (code term-list) (premise-code* P variables nil)
      (values (reverse code) term-list))))

#| The following introduces new nodes for a desire with a new content, resets the
desire-strength for a previous desire with an altered strength, and retracts desires
whose new desire-strengths are zero. |#
(defun queue-desire (desire)
  (let* ((formula (desire-content desire))
         (sequent (list nil formula))
         (node (find-if
                 #'(lambda (node)
                     (and (eq (hypernode-kind node) :desire)
                          (equal (hypernode-sequent node) sequent)))
                 *desires*)))
    (cond (node
            (let ((strength (hypernode-maximal-degree-of-justification node)))
              (cond ((zerop strength)
                     (pull node *desires*)
                     (pull node *processed-desires*)
                     (pull (cons formula (hypernode-c-list node)) *hypergraph*)
                     (let ((queue-node (hypernode-queue-node node)))
                       (when queue-node (pull queue-node *inference-queue*))))
                    (t
                      (let ((queue-node (hypernode-queue-node node)))
                        (when queue-node
                          (setf (queue-degree-of-preference queue-node)
                                (desire-preference desire))
                          (setf *inference-queue*
                                (ordered-insert queue-node
                                                (remove queue-node *inference-queue*)
                                                #'i-preferred))))))))
          (t
            (let* ((node
                     (make-hypernode
                       :hypernode-number (incf *hypernode-number*)
                       :hypernode-sequent sequent
                       :hypernode-formula formula
                       :hypernode-supposition nil
                       :hypernode-kind :desire
                       :hypernode-nearest-defeasible-ancestors (list nil)
                       :hypernode-maximal-degree-of-justification (desire-strength desire)
                       :hypernode-discounted-node-strength (desire-strength desire)))
                   (queue-node
                     (make-inference-queue-node
                       :queue-number (incf *queue-number*)
                       :queue-item node
                       :queue-item-kind :conclusion
                       :queue-discounted-strength 1.0
                       :queue-item-complexity (complexity sequent))))
              (setf (hypernode-queue-node node) queue-node)
              (setf (queue-degree-of-preference queue-node) (desire-preference desire))
              (push node *hypergraph*)
              (when *display?* (display-unsupported-hypernode node))
              (push node *desires*)
              (setf *inference-queue*
                    (ordered-insert queue-node *inference-queue* #'i-preferred)))))))

#| The following treats percepts as always new.  If they fade before they are retrieved
from the *inference-queue*, this has no effect.  They are left on the queue anyway
for subsequent processing. |#
(defun queue-percept (percept)
  (let* ((formula (list 'throughout (percept-content percept)
                        (list 'closed (percept-date percept) (percept-date percept))))
         (sequent (list nil formula))
         (node
           (make-hypernode
             :hypernode-number (incf *hypernode-number*)
             :hypernode-sequent sequent
             :hypernode-formula formula
             :hypernode-supposition nil
             :hypernode-kind :percept
             :hypernode-nearest-defeasible-ancestors (list nil)
             :hypernode-justification percept
             :hypernode-maximal-degree-of-justification (percept-clarity percept)
             :hypernode-degree-of-justification (percept-clarity percept)
             :hypernode-discounted-node-strength (percept-clarity percept)
             :hypernode-background-knowledge t))
         (queue-node
           (make-inference-queue-node
             :queue-number (incf *queue-number*)
             :queue-item node
             :queue-item-kind :conclusion
             :queue-discounted-strength 1.0
             :queue-item-complexity (sequent-complexity sequent))))
    (when *log-on* (push node *reasoning-log*))
    (setf (hypernode-queue-node node) queue-node)
    (setf (queue-degree-of-preference queue-node) (percept-preference percept))
    (push node *hypergraph*)
    (store-hypernode node (hypernode-formula node))
    (when *display?* (display-unsupported-hypernode node))
    (setf *inference-queue*
          (ordered-insert queue-node *inference-queue* #'i-preferred))))

(defun pause-on () (setf *pause* t))
(defun pause-off () (setf *pause* nil))

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

(defun display-test-log ()
  (princ "=========================== TEST RESULTS ===========================")
  (terpri) (terpri)
  (princ "                                                                                ") (princ (mem1 *test-log*))
  (when *comparison-log*
    (princ "                        ") (princ (mem1 *comparison-log*))
    (princ "                   ratio of run times"))
  (terpri)
  (princ "          *reductio-discount*:                                 ") (princ (mem2 *test-log*))
  (when *comparison-log*
    (princ "                                      ") (princ (mem2 *comparison-log*)))
  (terpri)
  (princ "          *reductio-interest*:                                   ") (princ (mem3 *test-log*))
  (when *comparison-log*
    (princ "                                    ") (princ (mem3 *comparison-log*)))
  (terpri)
  (princ "          *skolem-multiplier*:                                   ") (princ (mem4 *test-log*))
  (when *comparison-log*
    (princ "                                    ") (princ (mem4 *comparison-log*)))
  (terpri)
  (princ "          *quantifier-discount*:                                   ") (princ (mem5 *test-log*))
  (when (and *comparison-log* (numberp (mem5 *comparison-log*)))
    (princ "                                    ") (princ (mem5 *comparison-log*)))
  (terpri) (terpri)
  (let ((ratios nil))
    (dolist (L (reverse (mem6 *test-log*)))
      (let* ((n (mem1 L))
             (L* (assoc
                   n (if (numberp (mem5 *comparison-log*))
                       (mem6 *comparison-log*) (mem5 *comparison-log*)) :test 'equal)))
        (princ "#") (princ n) (princ "                                                                          ")
        (display-run-time-in-seconds (mem2 L))
        (when L* (princ "                            ") (display-run-time-in-seconds (mem2 L*))
          (cond ((and (not (zerop (mem3 L))) (not (zerop (mem3 L*))))
                 (let ((ratio (/ (mem3 L) (mem3 L*))))
                   (push ratio ratios)
                   (princ "                            ")
                   (princ
                     (if (< (abs (- (mem2 L) (mem2 L*))) 1) 1.0
                       (float (/ (truncate (* 1000 ratio)) 1000))))))
                ; (let ((ratio
                ;           (if (< (abs (- (mem2 L) (mem2 L*))) 15) 1.0
                ;                (/ (mem2 L) (mem2 L*)))))
                ;    (push ratio ratios)
                ;    (princ "                            ")
                ;    (princ (float (/ (truncate (* 100 ratio)) 100)))))
                (t (princ "                            ##"))))
        (terpri)
        (princ "           cumulative  argument length:                 ") (princ (mem3 L))
        (when L* (princ "                                           ") (princ (mem3 L*))
          (cond ((and (not (zerop (mem3 L))) (not (zerop (mem3 L*))))
                 (princ "                                      ")
                 (let ((d (- (mem3 L) (mem3 L*))))
                   (cond ((> d 0) (princ "+") (princ d))
                         ((< d 0) (princ d))
                         (t (princ "  --")))))
                (t (princ "                            --"))))
        (terpri)
        (princ "           total number of inferences:                     ") (princ (mem4 L))
        (when L* (princ "                                          ") (princ (mem4 L*))
          (cond ((and (not (zerop (mem3 L))) (not (zerop (mem3 L*))))
                 (princ "                                      ")
                 (let ((d (- (mem4 L) (mem4 L*))))
                   (cond ((> d 0) (princ "+") (princ d))
                         ((< d 0) (princ d))
                         (t (princ "  --")))))
                (t (princ "                            --"))))
        (terpri) (terpri))
      (terpri))
    ; (when ratios
    ;      (princ "                                                                               average ratio of run times = ")
    ;      (let ((average (/ (apply '+ ratios) (length ratios))))
    ;         (princ (float (/ (truncate (* 10000 average)) 10000))))
    ;      (terpri))
    (when ratios
      (princ "geometric average ratio of run times = ")
      (setf ratios (remove 0 ratios))
      (let ((average (expt (apply '* ratios) (/ 1 (length ratios)))))
        (princ (float (/ (truncate (* 10000 average)) 10000))))
      (terpri))))

;................................................. BACKWARDS REASONING ........................................

(defun reason-backwards-from-reason-node (interest priority depth d-node)
  ; (when (eq interest (interest 5)) (setf i interest p priority d depth dn d-node) (break))
  ;; (step (reason-backwards-from-reason-node i p d dn))
  (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-REASON-NODE ")
    (princ interest) (princ " and ") (princ d-node) (terpri))
  (dolist (reason (d-node-backwards-reasons d-node))
    (when (interest-cancelled interest) (throw 'apply-backwards-reasons nil))
    (when (or (not (interest-deductive interest)) (not (reason-defeasible-rule reason)))
      (let ((strength (reason-strength reason)))
        (when
          (or (not (numberp strength))
              (and (>= strength (interest-degree-of-interest interest))
                   (or (null (interest-last-processed-degree-of-interest interest))
                       (< strength (interest-last-processed-degree-of-interest interest)))))
          (let ((reason-function (reason-function reason)))
            (cond
              (reason-function (funcall (reason-function reason) interest (1+ depth) priority))
              (t (reason-substantively-from-backwards-reason reason interest (1+ depth) priority)))))))))

(defun reason-backwards-from-dominant-reason-nodes (interest priority depth d-node)
  (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-DOMINANT-REASON-NODES ")
    (princ interest) (princ " and ") (princ d-node) (terpri))
  (reason-backwards-from-reason-node interest priority (1+ depth) d-node)
  (let ((pn (d-node-parent d-node)))
    (when pn (reason-backwards-from-dominant-reason-nodes interest priority (1+ depth) pn))))

(defun apply-backwards-reasons (interest priority depth)
  ; (when (eq interest (interest 9)) (setf i interest p priority d depth) (break))
  ; (setf i interest p priority d depth)
  ;; (step (apply-backwards-reasons i p d))
  (when *trace* (indent depth) (princ "APPLY-BACKWARDS-REASONS ") (princ interest) (terpri))
  (catch 'apply-backwards-reasons
         (let* ((i-list (interest-i-list interest))
                (d-node (i-list-d-node i-list)))
           (reason-backwards-from-dominant-reason-nodes interest priority (1+ depth) d-node)))
  (setf (interest-last-processed-degree-of-interest interest) (interest-degree-of-interest interest)))

(defun discharge-fortuitous-reductio-interests (interest depth)
  ; (when (eq interest (interest 88)) (setf i interest d depth) (break))
  ;; (step (discharge-fortuitous-reductio-interests i d))
  (when *trace* (indent depth) (princ "DISCHARGE-FORTUITOUS-REDUCTIO-INTERESTS: ")
    (princ interest) (terpri))
  (when (interest-reductio interest)
    (dolist (n (interest-supposition-nodes interest))
      (when (deductive-node n)
        (dolist (c (c-list-contradictors (hypernode-c-list n)))
          (let ((cl (car c))
                (u (cadr c)))
            (dolist (n* (c-list-nodes cl))
              (when (eq (hypernode-justification n*) :reductio-supposition)
                (draw-conclusion
                  (interest-formula interest) (list n* n) :fortuitous-reductio u 1.0 depth nil nil)))))))))

#| node* is the node that generates interest, whose interest-formula is the
negation of the hypernode-formula of node*.  This is called by GENERATE-REDUCTIO-INTERESTS. |#
(defun DISCHARGE-RETROSPECTIVE-REDUCTIOS (node match interest depth)
  ; (when (eq interest (interest 37)) (setf n node m match i interest d depth) (break))
  ;; (step (discharge-retrospective-reductios n m i d))
  (when *trace* (indent depth) (princ "DISCHARGE-RETROSPECTIVE-REDUCTIOS-FROM ")
    (princ node) (princ " and ") (princ interest) (terpri))
  (let* ((Y0 (match-sublis match (hypernode-supposition node)))
         (reductio-ancestors* (hypernode-reductio-ancestors node)))
    (dolist (cl (i-list-corresponding-c-lists (interest-i-list interest)))
      (let* ((c-list (mem1 cl))
             (nodes (c-list-nodes c-list))
             (unifier (mem2 cl))
             (new-vars
               (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                       (intersection (c-list-variables c-list)
                                     (set-difference (hypernode-supposition-variables node)
                                                     (hypernode-variables node)))))
             (Y*0 (remove-duplicates=
                    (match-sublis (mem2 unifier) (sublis new-vars Y0)))))
        (dolist (C nodes)
          (when (interest-cancelled interest)
            (return-from discharge-retrospective-reductios))
          (when (<= (interest-degree-of-interest interest) (current-maximal-degree-of-justification C))
            (let* ((unifiers (appropriately-related-suppositions C interest unifier))
                   (reductio-ancestors (hypernode-reductio-ancestors C))
                   (new-vars
                     (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                             (intersection (hypernode-variables node)
                                           (set-difference
                                             (hypernode-supposition-variables C)
                                             (hypernode-variables C)))))
                   (Y1 (remove-duplicates=
                         (match-sublis
                           (mem1 unifier) (sublis new-vars (hypernode-supposition C))))))
              (dolist (u unifiers)
                (let ((unifier* (merge-unifiers* unifier u))
                      (Y (remove-duplicates=
                           (match-sublis (mem1 u) Y1)))
                      (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                  ; (when (and
                  ;                 (not (some #'(lambda (f) (mem (neg f) Y)) Y))
                  ;                 (not (some #'(lambda (f) (mem (neg f) Y*)) Y*))
                  ;                 (not (some #'(lambda (f) (mem (neg f) Y)) Y*)))
                  (let ((RA (union=
                              (mapcar
                                #'(lambda (x)
                                    (cons
                                      (match-sublis
                                        (mem1 unifier*)
                                        (car x)) (cdr x)))
                                reductio-ancestors)
                              (mapcar
                                #'(lambda (x)
                                    (cons
                                      (match-sublis
                                        (mem2 unifier*)
                                        (match-sublis match (car x))) (cdr x)))
                                reductio-ancestors*)))
                        (NR (union=
                              (mapcar
                                #'(lambda (x)
                                    (cons
                                      (match-sublis
                                        (mem1 unifier*)
                                        (car x)) (cdr x)))
                                (hypernode-non-reductio-supposition C))
                              (mapcar
                                #'(lambda (x)
                                    (cons
                                      (match-sublis
                                        (mem2 unifier*)
                                        (match-sublis match (car x))) (cdr x)))
                                (hypernode-non-reductio-supposition node)))))
                    (dolist (R RA)
                      (when (base-test R RA)
                        (let ((P (car R)))
                          (draw-reductio-conclusion
                            P C node R Y Y* RA NR interest unifier* (1+ depth) nil))))))))))))))

(defun non-reductio-interest-supposition (interest &optional nodes interests)
  (let ((sup nil))
    (dolist (node (interest-generating-nodes interest))
      (when (not (member node nodes))
        (push node nodes)
        (dolist (R (hypernode-non-reductio-supposition node))
          (pushnew (cdr R) sup))))
    (dolist (dr (interest-direct-reductio interest))
      (let ((node (car dr)))
        (when (not (member node nodes))
          (push node nodes)
          (dolist (R (hypernode-non-reductio-supposition node))
            (pushnew (cdr R) sup)))))
    (dolist (L (interest-right-links interest))
      (let ((in (link-resultant-interest L)))
        (when (and (not (query-p in))
                   (not (member in interests)))
          (push in interests)
          (setf sup (union= sup (non-reductio-interest-supposition in nodes interests))))))
    sup))

(defun augment-inherited-non-reductio-suppositions (interest &optional nodes interests)
  (dolist (node (interest-generating-nodes interest))
    (when (not (member node nodes))
      (push node nodes)
      (dolist (R (hypernode-non-reductio-supposition node))
        (pushnew (cdr R) *inherited-non-reductio-suppositions*))
      (dolist (in (hypernode-generating-interests node))
        (when (and (not (member in interests))
                   (not (interest-direct-reductio interest)))
          (push in interests)
          (dolist (R (non-reductio-interest-supposition in nodes interests))
            (pushnew R *inherited-non-reductio-suppositions*))))))
  (dolist (L (interest-right-links interest))
    (let ((in (link-resultant-interest L)))
      (when (and (not (query-p in))
                 (not (member in interests)))
        (push in interests)
        (dolist (R (non-reductio-interest-supposition in nodes interests))
          (pushnew R *inherited-non-reductio-suppositions*))))))

(defun recompute-reductio-ancestors (node sup)
  (let ((assoc (rassoc sup (hypernode-non-reductio-supposition node))))
    (when assoc
      (pull assoc (hypernode-non-reductio-supposition node))
      (push assoc (hypernode-reductio-ancestors node))
      (discharge-interest-in node (c-list-corresponding-i-lists (hypernode-c-list node)) 0 t 1 nil :interest nil :reductio-only t)
      (dolist (L (hypernode-consequent-links node))
        (recompute-reductio-ancestors (hyperlink-target L) sup)))))

(defun discharge-new-reductio-interest (interest depth d-interests)
  (when *trace* (indent depth) (princ "DISCHARGE-NEW-REDUCTIO-INTEREST from ")
    (princ interest) (terpri))
  ; (when (equal interest (interest 6)) (break))
  (dolist (corresponding-c-list (i-list-corresponding-c-lists (interest-i-list interest)))
    (let* ((c-list (mem1 corresponding-c-list))
           (unifier (mem2 corresponding-c-list))
           (i-sup (match-sublis (mem2 unifier) (interest-supposition interest))))
      (dolist (node (c-list-nodes c-list))
        (let ((degree (current-maximal-degree-of-justification node))
              (deductive? (deductive-node node)))
          (when (and
                  (or deductive? (not (interest-deductive interest)))
                  (<= (interest-degree-of-interest interest) degree)
                  (not (subsetp=
                         (match-sublis (mem1 unifier) (hypernode-supposition node))
                         i-sup)))
            (let* ((unifiers (appropriately-related-suppositions node interest unifier))
                   (new-vars
                     (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                             (intersection (c-list-variables c-list)
                                           (set-difference (hypernode-supposition-variables node)
                                                           (hypernode-variables node)))))
                   (Y1 (remove-duplicates=
                         (match-sublis
                           (mem1 unifier) (sublis new-vars (hypernode-supposition node))))))
              (dolist (dr (interest-direct-reductio interest))
                (let ((node* (car dr))
                      (match (cdr dr)))
                  (when (interest-cancelled interest)
                    (return-from discharge-new-reductio-interest))
                  (let* ((new-vars
                           (mapcar #'(lambda (v) (cons v (make-interest-variable)))
                                   (intersection (hypernode-variables node)
                                                 (set-difference (hypernode-supposition-variables node*)
                                                                 (hypernode-variables node*)))))
                         (Y*0 (remove-duplicates=
                                (match-sublis
                                  (mem2 unifier)
                                  (match-sublis
                                    match
                                    (sublis new-vars (hypernode-supposition node*)))))))
                    (dolist (u unifiers)
                      (let ((unifier* (merge-unifiers* unifier u))
                            (Y (remove-duplicates=
                                 (match-sublis (mem1 u) Y1)))
                            (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                        (let ((RA (union=
                                    (mapcar
                                      #'(lambda (x)
                                          (cons
                                            (match-sublis
                                              (mem1 unifier*)
                                              (car x)) (cdr x)))
                                      (hypernode-reductio-ancestors node))
                                    (mapcar
                                      #'(lambda (x)
                                          (cons (match-sublis
                                                  (mem2 unifier*)
                                                  (match-sublis match (car x))) (cdr x)))
                                      (hypernode-reductio-ancestors node*))))
                              (NR (union=
                                    (mapcar
                                      #'(lambda (x)
                                          (cons
                                            (match-sublis
                                              (mem1 unifier*)
                                              (car x)) (cdr x)))
                                      (hypernode-non-reductio-supposition node))
                                    (mapcar
                                      #'(lambda (x)
                                          (cons (match-sublis
                                                  (mem2 unifier*)
                                                  (match-sublis match (car x))) (cdr x)))
                                      (hypernode-non-reductio-supposition node*)))))
                          (dolist (R RA)
                            (when (base-test R RA)
                              (let ((P (car R)))
                                (draw-reductio-conclusion
                                  P node node* R Y Y* RA NR interest unifier*
                                  (1+ depth) (cons interest d-interests)))))
                          )))))))))))))

(defun change-to-reductio-interest (interest depth d-interests)
  ; (when (equal interest (interest 6)) (break))
  (when (not (interest-reductio interest))
    (setf (interest-reductio interest) t)
    (discharge-new-reductio-interest interest (1+ depth) d-interests)
    (dolist (L (interest-left-links interest))
      (change-to-reductio-interest (link-interest L) depth d-interests))))

(defun generate-reductio-interests (node depth d-interests)
  ; (setf n node d depth di d-interests)
  ; (when (eq node (node 54)) (setf n node d depth di d-interests) (break))
  ;; (step (generate-reductio-interests n d di))
  (multiple-value-bind
    (sequent vars substitution)
    (convert-conclusion-variables
      (list (domain (hypernode-non-reductio-supposition node)) (neg (hypernode-formula node))) (hypernode-variables node))
    (let ((P (sequent-formula sequent))
          (sup (sequent-supposition sequent)))
      (multiple-value-bind
        (interest i-list match)
        (interest-for sequent vars nil nil)
        (let* ((interests (unionmapcar #'hypernode-generating-interests *reductio-supposition-nodes*))
               (degree (maximum (mapcar #'interest-degree-of-interest interests)))
               (priority
                 (* *reductio-interest*
                    (maximum
                      (mapcar #'compute-discounted-node-strength *reductio-supposition-nodes*)))))
          (cond ((null interest)
                 (setf interest
                       (make-interest
                         :interest-number (incf *interest-number*)
                         :interest-sequent sequent
                         :interest-formula P
                         :interest-supposition sup
                         :interest-variables vars
                         :interest-supposition-variables (supposition-variables sup)
                         :interest-degree-of-interest degree
                         :interest-priority priority
                         :interest-maximum-degree-of-interest degree
                         :interest-reductio t
                         :interest-direct-reductio (list (cons node substitution))
                         :interest-non-reductio? nil
                         ))
                 (push interest (hypernode-generated-direct-reductio-interests node))
                 (if i-list
                   (store-interest interest i-list)
                   (let ((c-lists (c-list-contradictors (hypernode-c-list node))))
                     (setf c-lists
                           (mapcar
                             #'(lambda (cl)
                                 (cons (car cl) (match-sublis substitution (cdr cl))))
                             c-lists))
                     (store-interest-with-c-lists interest c-lists)))
                 (when *display?*
                   (display-interest interest) (princ "                                        ")
                   (princ "using node ") (princ (hypernode-number node)) (terpri))
                 (when *log-on* (push interest *reasoning-log*))
                 (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
                 (queue-interest interest priority)
                 (push interest *direct-reductio-interests*))
                (t
                  (let ((direct-reductio-interest (interest-direct-reductio interest)))
                    (pushnew (cons node (merge-matches* substitution match))
                             (interest-direct-reductio interest))
                    (pushnew interest (hypernode-generated-direct-reductio-interests node))
                    (when (not direct-reductio-interest)
                      (push interest *direct-reductio-interests*)
                      (setf (interest-priority interest) (max (interest-priority interest) priority))
                      (change-to-reductio-interest interest depth d-interests)
                      (setf (interest-degree-of-interest interest) (max (interest-degree-of-interest interest) degree))))
                  (readopt-interest interest nil))))))))

#| Reductio-interests are started when the first reductio-supposition is made, and
reductio-interests in the negations of reductio-suppositions are adopted when the
suppositions are made.  Other direct-reductio-interests are adopted when the
generating nodes are retrieved from the inference-queue. |#
(defun START-REDUCTIO-INTERESTS (node depth interests)
  ; (when (equal node (node 7)) (setf c node d depth i interests) (break))
  ;; (step (start-reductio-interests c d i))
  (when *trace* (indent depth) (princ "ADOPT-REDUCTIO-INTEREST-FROM: ")
    (princ node) (terpri))
  (let ((start-interests (null *reductio-supposition-nodes*)))
    (push node *reductio-supposition-nodes*)
    (when start-interests
      (when *trace* (indent (1+ depth)) (princ "INITIATING-REDUCTIO-INTERESTS") (terpri))
      (dolist (dn *discrimination-net*)
        (dolist (cl (d-node-c-lists dn))
          (when  (c-list-reductio-interests cl)
            (dolist (C (c-list-processed-nodes cl))
              (when
                (and (deductive-node C)
                     (or
                       (null (hypernode-enabling-interests C))
                       (some #'(lambda (in) (not (interest-cancelled in))) (hypernode-enabling-interests C))))
                (generate-reductio-interests C (1+ depth) interests)))))))
    (when (c-list-reductio-interests (hypernode-c-list node))
      (generate-reductio-interests node depth interests))))

#| When a hypernode-non-reductio-supposition is readopted as a reductio-supposition, for all
of its inclusive-hypernode-descendants that are deductive in it, it is moved from the
hypernode-non-reductio-supposition to the list of hypernode-reductio-ancestors.  For all of those altered
nodes that are not still on the inference-queue, we discharge-interest-in them and
reason-forwards-from them. |#
(defun convert-non-reductio-sup (sup)
  (when *display?* (princ "Converting node ") (princ (hypernode-number sup))
    (princ " to a reductio supposition") (terpri))
  (pull sup *non-reductio-supposition-nodes*)
  (when (not (member sup *reductio-supposition-nodes*))
    (setf (hypernode-justification sup) :reductio-supposition)
    (when (null *reductio-supposition-nodes*) (start-reductio-interests sup 0 nil))
    (when *reductio-supposition-nodes* (push sup *reductio-supposition-nodes*))
    (recompute-reductio-ancestors sup sup)))

(defun queue-for-inference (node)
  ; (when (equal node (node 13)) (break))
  (when (not (hypernode-cancelled-node node))
    (cond ((mem (hypernode-number node) *blocked-conclusions*)
           (when *display?* (princ "Hypernode #") (princ (hypernode-number node))
             (princ " is a blocked node and so is not being queued.") (terpri)))
          (t
            (let* ((complexity (sequent-complexity (hypernode-sequent node)))
                   (strength (compute-discounted-node-strength node))
                   (degree
                     (if (numberp strength) (/ strength complexity)))
                   (queue-node
                     (make-inference-queue-node
                       :queue-number (incf *queue-number*)
                       :queue-item node
                       :queue-item-kind :conclusion
                       :queue-item-complexity complexity
                       :queue-discounted-strength (hypernode-discounted-node-strength node)
                       :queue-degree-of-preference degree)))
              (setf (hypernode-queue-node node) queue-node)
              (when degree
                (setf *inference-queue*
                      (ordered-insert queue-node *inference-queue* #'i-preferred)))
              ; (when *display?* (princ "  Preference = ")
              ;               (princ (float (/ (truncate (* 10000 (queue-degree-of-preference queue-node))) 10000)))
              ;               (terpri))
              )))))

(defun make-new-reductio-supposition (interest X i-list P c-vars depth)
  (let ((c-list (c-list-for P)))
    (cond
      ((or (null c-list)
           (not (some #'(lambda (c) (subsetp= (hypernode-supposition c) X))
                      (c-list-nodes c-list))))
       (augment-inherited-non-reductio-suppositions interest)
       (let* ((new-sup (list P))
              (sequent (list new-sup P))
              (N (make-hypernode
                   :hypernode-number (incf *hypernode-number*)
                   :hypernode-sequent sequent
                   :hypernode-formula P
                   :hypernode-supposition new-sup
                   :hypernode-kind :inference
                   :hypernode-nearest-defeasible-ancestors (list nil)
                   :hypernode-justification :reductio-supposition
                   :hypernode-degree-of-justification 1.0
                   :hypernode-maximal-degree-of-justification 1.0
                   :hypernode-deductive-only t
                   :hypernode-discounted-node-strength
                   (* *reductio-discount* (interest-priority interest))
                   :hypernode-generating-interests (list interest)
                   :hypernode-variables c-vars
                   :hypernode-supposition-variables c-vars
                   )))
         (when *trace* (indent depth)
           (princ "DRAW CONCLUSION: ")
           (princ N) (terpri))
         (incf *unused-suppositions*)
         (setf (i-list-reductio-supposition i-list) N)
         (setf (hypernode-reductio-ancestors N) (list (cons P N)))
         (push N *hypergraph*)
         (store-hypernode-with-c-list N P c-list)
         (if *log-on* (push N *reasoning-log*))
         (push N (interest-generated-suppositions interest))
         (when *display?* (display-unsupported-hypernode N))
         (queue-for-inference N)
         (when (and *display?* *graphics-on*) (when *graphics-pause* (pause-graphics))
           (draw-n N *og* *nodes-displayed*) (push N *nodes-displayed*))
         (start-reductio-interests N (1+ depth) nil)
         ))
      (t (setf (i-list-reductio-trigger i-list) t)))))

#| When an interest is retrieved from the inference-queue, check to see the value of
reductio-trigger for its i-list.  If it is T, make a reductio-supposition for the negation
of the interest-formula,  and reset reductio-trigger to NIL. |#
(defun MAKE-REDUCTIO-SUPPOSITION (interest depth)
  ; (when (equal interest (interest 9)) (break))
  ;; (step (make-reductio-supposition (interest 9) 0))
  (when
    (not (interest-cancelled interest))
    (let ((q (interest-formula interest))
          (X (interest-supposition interest))
          (i-list (interest-i-list interest)))
      (when (not (mem q X))
        (cond ((i-list-reductio-trigger i-list)
               (setf (i-list-reductio-trigger i-list) nil)
               (multiple-value-bind
                 (P c-vars)
                 (convert-interest-variables (neg q) (interest-variables interest))
                 (let ((sup (find-if #'(lambda (N) (equal (hypernode-formula N) P))
                                     *reductio-supposition-nodes*)))
                   (when (null sup)
                     (setf sup
                           (find-if
                             #'(lambda (R)
                                 (let* ((vars (hypernode-variables R))
                                        (R-formula (hypernode-formula R))
                                        (m (match R-formula P vars)))
                                   (and m (equal (match-sublis m R-formula) P))))
                             *reductio-supposition-nodes*))
                     (when (null sup)
                       (setf sup
                             (find-if
                               #'(lambda (R)
                                   (let ((vars (hypernode-variables R))
                                         (R-formula (hypernode-formula R)))
                                     (match R-formula P vars)))
                               *non-reductio-supposition-nodes*))))
                   (cond (sup
                           (incf (hypernode-readopted-supposition sup))
                           (setf (hypernode-justification sup) :reductio-supposition)
                           (push interest (hypernode-generating-interests sup))
                           (convert-non-reductio-sup sup))
                         (t (make-new-reductio-supposition interest X i-list P c-vars depth))))))
              (t (augment-inherited-non-reductio-suppositions interest)))))))

#| Carrying along the priority of the inference-queue node from which
backwards reasoning proceeds simplifies the computation of interest-priorities in
discharge-link. |#
(defun reason-backwards-from (interest priority depth)
  ; (when (equal interest (interest 1)) (setf i interest p priority d depth) (break))
  ;; (step (reason-backwards-from i p d))
  (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM: ") (princ interest) (terpri))
  (apply-backwards-reasons interest priority depth)
  (when (and *use-reductio* (not (interest-cancelled interest)))
    (make-reductio-supposition interest depth)
    (dolist (dr (interest-direct-reductio interest))
      (let ((node (car dr))
            (match (cdr dr)))
        (discharge-retrospective-reductios node match interest 1)))
    (discharge-fortuitous-reductio-interests interest depth))
  (dolist (rule *auxiliary-backwards-rules*)
    (funcall rule interest)))

#| The following function is left undefined pending further specification of the form
of epistemic desires. |#
(defun form-epistemic-desires-for (interest)
  (declare (ignore interest))
  T)

(defun record-query-answers (link)
  ; (when (eq link (link 1)) (break))
  (let* ((C (mem1 (link-supporting-nodes link)))
         (degree (current-degree-of-justification C))
         (Q (link-resultant-interest link)))
    (pushnew C (query-answers Q))
    (pull C (link-supporting-nodes link))
    (pushnew Q (hypernode-answered-queries C))
    (when (and *display?* *graphics-on*)
      (draw-just-node (hypernode-position C *og*) *og* C (hypernode-color C *og*)))
    (cond ((and (not (zerop degree))
                (>= degree (query-strength Q))
                (or (null (hypernode-old-degree-of-justification C))
                    (zerop (hypernode-old-degree-of-justification C))
                    (< (hypernode-old-degree-of-justification C) (query-strength Q))))
           (when *log-on* (push (list :answer-query C Q degree) *reasoning-log*))
           (when *display?*
             (princ "               ")
             (princ "=========================================") (terpri)
             (princ "               ") (princ "Justified belief in ")
             (prinp (hypernode-formula C)) (terpri)
             (princ "               with degree-of-justification ")
             (princ (current-degree-of-justification C)) (terpri)
             (princ "               ") (princ "answers ") (princ Q)
             (terpri) (princ "               ")
             (princ "=========================================") (terpri))
           (dolist (instruction (query-positive-instructions Q))
             (funcall instruction C))
           (setf (query-answered? Q) t))
          (*display?*
            (princ "               ----------------------------------------") (terpri)
            (princ "               ") (princ C)
            (princ " answers ") (princ Q) (terpri)
            (princ "               ----------------------------------------") (terpri)))
    (when (deductive-node C)
      (when (and
              (every
                #'(lambda (query)
                    (or (eq query Q)
                        (some #'deductive-node (query-answers query))))
                *ultimate-epistemic-interests*)
              (not (some
                     #'(lambda (Q) (eq (queue-item-kind Q) :query))
                     *inference-queue*)))
        (setf (hypernode-degree-of-justification C) 1.0)
        (setf (query-answered? Q) T)
        (when *display?*
          (princ "             ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
          (terpri))
        (cancel-interest-in (link-interest link) 0)
        (throw 'die nil)))))

(defun reason-backwards-from-whether-query (query priority depth)
  ; (when (equal query (query 1)) (setf q query p priority d depth) (break))
  (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-QUERY") (terpri))
  (let* ((formula (mem2 (query-formula query)))
         (sequent (list nil formula))
         (link
           (make-interest-link
             :link-number (incf *interest-link-number*)
             :link-resultant-interest query
             :link-strength (query-strength query)
             :link-rule :answer))
         (positive-interest
           (let ((interests (interests-for formula nil)))
             (when interests
               (find-if #'(lambda (i)
                            (and (null (interest-supposition i))
                                 (eq (interest-deductive i) (query-deductive query))))
                        interests))))
         (negative-interest
           (let ((interests (interests-for (neg formula) nil)))
             (when interests
               (find-if #'(lambda (i)
                            (and (null (interest-supposition i))
                                 (eq (interest-deductive i) (query-deductive query))))
                        interests)))))
    (cond (positive-interest
            (setf (interest-degree-of-interest positive-interest)
                  (min (query-strength query) (interest-degree-of-interest positive-interest)))
            (setf (interest-maximum-degree-of-interest positive-interest)
                  (max (query-strength query) (interest-maximum-degree-of-interest positive-interest)))
            (setf (interest-priority positive-interest) (interest-maximum-degree-of-interest positive-interest))
            (readopt-interest positive-interest nil)
            (setf (link-interest link) positive-interest)
            (push link (interest-right-links positive-interest))
            (push link *interest-links*)
            (when (and *display?* *graphics-on* *graph-interests*)
              (draw-interest positive-interest (interest-position positive-interest *og*) *og*))
            (let ((Q (interest-queue-node positive-interest)))
              (when Q
                (setf (queue-degree-of-preference Q)
                      (maximum
                        (list (queue-degree-of-preference Q)
                              (interest-preference
                                (query-strength query)
                                (sequent-complexity sequent)))))
                (setf *inference-queue*
                      (ordered-insert Q (remove Q *inference-queue*)
                                      #'i-preferred)))))
          (t
            (setf positive-interest
                  (make-interest
                    :interest-number (incf *interest-number*)
                    :interest-sequent sequent
                    :interest-formula formula
                    :interest-supposition nil
                    :interest-right-links (list link)
                    :interest-degree-of-interest (query-strength query)
                    :interest-maximum-degree-of-interest (query-strength query)
                    :interest-priority (query-strength query)
                    :interest-deductive (query-deductive query)))
            (store-interest positive-interest)
            (when *display?* (display-interest positive-interest))
            (when *log-on* (push positive-interest *reasoning-log*))
            (when (and *display?* *graphics-on* *graph-interests*) (draw-i positive-interest *og*))
            (setf (link-interest link) positive-interest)
            (push link *interest-links*)
            (apply-degenerate-backwards-reasons positive-interest priority (1+ depth))
            (reason-backwards-from positive-interest priority (1+ depth))
            (form-epistemic-desires-for positive-interest)))
    (setf (query-interest query) positive-interest)
    (dolist (cl (i-list-corresponding-c-lists (interest-i-list positive-interest)))
      (let ((conclusion
              (find-if
                #'(lambda (c)
                    (and (null (hypernode-supposition c))
                         (>= (current-maximal-degree-of-justification c)
                             (query-strength query))))
                (c-list-nodes  (mem1 cl)))))
        (when (and conclusion (not (member conclusion (link-supporting-nodes link))))
          (push conclusion (link-supporting-nodes link))
          (record-query-answers link))))
    (cond (negative-interest
            (setf (interest-degree-of-interest negative-interest)
                  (min (query-strength query) (interest-degree-of-interest negative-interest)))
            (setf (interest-maximum-degree-of-interest negative-interest)
                  (max (query-strength query) (interest-maximum-degree-of-interest negative-interest)))
            (setf (interest-priority negative-interest) (interest-maximum-degree-of-interest negative-interest))
            (readopt-interest negative-interest nil)
            (setf (link-interest link) negative-interest)
            (push link (interest-right-links negative-interest))
            (push link *interest-links*)
            (when (and *display?* *graphics-on* *graph-interests*)
              (draw-interest negative-interest (interest-position negative-interest *og*) *og*))
            (let ((Q (interest-queue-node negative-interest)))
              (when Q
                (setf (queue-degree-of-preference Q)
                      (maximum
                        (list (queue-degree-of-preference Q)
                              (interest-preference
                                (query-strength query)
                                (sequent-complexity sequent)))))
                (setf *inference-queue*
                      (ordered-insert Q (remove Q *inference-queue*)
                                      #'i-preferred)))))
          (t
            (setf negative-interest
                  (make-interest
                    :interest-number (incf *interest-number*)
                    :interest-sequent (list (sequent-supposition sequent) (neg formula))
                    :interest-formula (neg formula)
                    :interest-supposition nil
                    :interest-right-links (list link)
                    :interest-degree-of-interest (query-strength query)
                    :interest-maximum-degree-of-interest (query-strength query)
                    :interest-priority (query-strength query)
                    :interest-deductive (query-deductive query)))
            (store-interest negative-interest)
            (when *display?* (display-interest negative-interest))
            (when *log-on* (push negative-interest *reasoning-log*))
            (when (and *display?* *graphics-on* *graph-interests*) (draw-i negative-interest *og*))
            (setf (link-interest link) negative-interest)
            (push link *interest-links*)
            (apply-degenerate-backwards-reasons negative-interest priority (1+ depth))
            (reason-backwards-from negative-interest priority (1+ depth))
            (form-epistemic-desires-for negative-interest)))
    (setf (query-negative-interest query) negative-interest)
    (dolist (cl (i-list-corresponding-c-lists (interest-i-list negative-interest)))
      (let ((conclusion
              (find-if
                #'(lambda (c)
                    (and (null (hypernode-supposition c))
                         (>= (current-maximal-degree-of-justification c)
                             (query-strength query))))
                (c-list-nodes  (mem1 cl)))))
        (when (and conclusion (not (member conclusion (link-supporting-nodes link))))
          (push conclusion (link-supporting-nodes link))
          (record-query-answers link))))
    (when (not (member query *permanent-ultimate-epistemic-interests*))
      (push #'(lambda (C)
                (when (deductive-node C)
                  (cancel-interest-in (query-interest query) 0)
                  (cancel-interest-in (query-negative-interest query) 0)))
            (query-positive-instructions query)))
    ))

(defun reason-backwards-from-simple-query (query priority depth)
  ; (when (equal query (query 3)) (setf q query p priority d depth) (break))
  (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-QUERY") (terpri))
  (let* ((formula (query-formula query))
         (sequent (list nil formula))
         (link
           (make-interest-link
             :link-number (incf *interest-link-number*)
             :link-resultant-interest query
             :link-strength (query-strength query)
             :link-rule :answer))
         (interest
           (let ((interests (interests-for formula nil)))
             (when interests
               (find-if #'(lambda (i)
                            (and (null (interest-supposition i))
                                 (eq (interest-deductive i) (query-deductive query))))
                        interests)))))
    (cond (interest
            (setf (interest-degree-of-interest interest)
                  (min (query-strength query) (interest-degree-of-interest interest)))
            (setf (interest-maximum-degree-of-interest interest)
                  (max (query-strength query) (interest-maximum-degree-of-interest interest)))
            (setf (interest-priority interest) (interest-maximum-degree-of-interest interest))
            (readopt-interest interest nil)
            (setf (link-interest link) interest)
            (push link (interest-right-links interest))
            (push link *interest-links*)
            (when (and *display?* *graphics-on* *graph-interests*)
              (draw-interest interest (interest-position interest *og*) *og*))
            (let ((Q (interest-queue-node interest)))
              (when Q
                (setf (queue-degree-of-preference Q)
                      (maximum
                        (list (queue-degree-of-preference Q)
                              (interest-preference
                                (query-strength query)
                                (sequent-complexity sequent)))))
                (setf *inference-queue*
                      (ordered-insert Q (remove Q *inference-queue*)
                                      #'i-preferred)))))
          (t
            (setf interest
                  (make-interest
                    :interest-number (incf *interest-number*)
                    :interest-sequent sequent
                    :interest-formula formula
                    :interest-supposition nil
                    :interest-right-links (list link)
                    :interest-degree-of-interest (query-strength query)
                    :interest-maximum-degree-of-interest (query-strength query)
                    :interest-priority (query-strength query)
                    :interest-deductive (query-deductive query)))
            (store-interest interest)
            (when *display?* (display-interest interest))
            (when *log-on* (push interest *reasoning-log*))
            (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
            (setf (link-interest link) interest)
            (push link *interest-links*)
            (apply-degenerate-backwards-reasons interest priority (1+ depth))
            (reason-backwards-from interest priority (1+ depth))
            (form-epistemic-desires-for interest)))
    (setf (query-interest query) interest)
    (dolist (cl (i-list-corresponding-c-lists (interest-i-list interest)))
      (let ((conclusion
              (find-if
                #'(lambda (c)
                    (and (null (hypernode-supposition c))
                         (>= (current-maximal-degree-of-justification c)
                             (query-strength query))))
                (c-list-nodes  (mem1 cl)))))
        (when (and conclusion (not (member conclusion (link-supporting-nodes link))))
          (push conclusion (link-supporting-nodes link))
          (record-query-answers link))))))

(defun ?-positive-instruction (query)
  #'(lambda (C)
      (when (deductive-node C)
        (cancel-interest-in (query-interest query) 0))))

(defun reason-backwards-from-?-query (query priority depth)
  ; (when (equal query (query 3)) (setf q query p priority d depth) (break))
  ;; (step (reason-backwards-from-?-query q p d))
  (when *trace* (indent depth) (princ "REASON-BACKWARDS-FROM-QUERY") (terpri))
  (let ((p (query-formula query)))
    (multiple-value-bind
      (formula ?-vars) (?-matrix p)
      (let ((vars nil))
        (dolist (v ?-vars)
          (let ((var (make-interest-variable)))
            (setf formula (subst var v formula))
            (push var vars)))
        (let* ((sequent (list nil formula))
               (link
                 (make-interest-link
                   :link-number (incf *interest-link-number*)
                   :link-resultant-interest query
                   :link-strength (query-strength query)
                   :link-rule :answer))
               (interest
                 (make-interest
                   :interest-number (incf *interest-number*)
                   :interest-sequent sequent
                   :interest-formula formula
                   :interest-variables vars
                   :interest-right-links (list link)
                   :interest-degree-of-interest (query-strength query)
                   :interest-maximum-degree-of-interest (query-strength query)
                   :interest-priority (query-strength query)
                   :interest-discharge-condition
                   (if (query-?-constraint query) (funcall (query-?-constraint query) vars))
                   :interest-deductive (query-deductive query))))
          (store-interest interest)
          (when *display?* (display-interest interest))
          (when *log-on* (push interest *reasoning-log*))
          (when (and *display?* *graphics-on* *graph-interests*) (draw-i interest *og*))
          (setf (link-interest link) interest)
          (push link *interest-links*)
          (apply-degenerate-backwards-reasons interest priority (1+ depth))
          (reason-backwards-from interest priority (1+ depth))
          (form-epistemic-desires-for interest)
          (setf (query-interest query) interest)
          (dolist (cl (i-list-corresponding-c-lists (interest-i-list interest)))
            (let ((conclusion
                    (find-if
                      #'(lambda (c)
                          (and (null (hypernode-supposition c))
                               (>= (current-maximal-degree-of-justification c)
                                   (query-strength query))))
                      (c-list-nodes  (mem1 cl)))))
              (when (and conclusion (not (member conclusion (link-supporting-nodes link))))
                (push conclusion (link-supporting-nodes link))
                (record-query-answers link))))
          (when (not (member query *permanent-ultimate-epistemic-interests*))
            (pushnew (?-positive-instruction query) (query-positive-instructions query)))
          )))))

#| This introduces ?P queries and whether-queries. |#
(defun reason-backwards-from-query (query priority  depth)
  ; (when (equal query (query 3)) (setf q query p priority d depth) (break))
  ;; (step (reason-backwards-from-query q p d))
  (let ((formula (query-formula query)))
    (cond
      ((whether-formula formula)
       (reason-backwards-from-whether-query query priority depth))
      ((?-genp formula)
       (reason-backwards-from-?-query query priority depth))
      (t
       (reason-backwards-from-simple-query query priority depth)))))

(defun menu-item-disable (x) (declare (ignore x)))
(defun menu-item-enable (x) (declare (ignore x)))
(defun oscar-menu-item (x) (declare (ignore x)))

;................................................. FORWARDS REASONING ........................................
#|  In the following functions, the depth variable is used in printing the trace. |#

(defun ADOPT-REDUCTIO-INTEREST (node depth d-interests)
  (let ((enabling-interests (hypernode-enabling-interests node)))
    (when
      (and
        *reductio-supposition-nodes*
        (deductive-node node)
        (not (eq (hypernode-justification node) :reductio-supposition))
        (c-list-reductio-interests (hypernode-c-list node))
        (or (null enabling-interests)
            (some #'(lambda (in) (not (interest-cancelled in))) enabling-interests)))
      (generate-reductio-interests node depth d-interests))))

(defun reason-from-instantiated-premises (node d-node depth)
  ; (when (and (eq node (node 252)) (eq d-node (d-node 10))) (setf n node dn d-node d depth) (break))
  ;; (step (reason-from-instantiated-premises n dn d))
  (dolist (ip (d-node-forwards-reasons d-node))
    (let* ((reason (ip-reason ip))
           (reason-function (reason-function reason)))
      ;(and (null (ip-basis ip)) (reason-function reason))))
      (when (hypernode-cancelled-node node) (throw 'apply-forwards-reasons nil))
      (when (or (not (hypernode-deductive-only node)) (not (reason-defeasible-rule reason)))
        (cond
          (reason-function (funcall reason-function node depth ip))
          ((ip-initial? ip) (reason-substantively-from-first-instantiated-premise node depth ip))
          (t (reason-substantively-from-non-initial-instantiated-premise nil depth ip node)))))))

(defun reason-from-dominant-premise-nodes (node d-node depth)
  ; (when (and (eq node (node 252)) (eq d-node (d-node 68))) (setf n node dn d-node d depth) (break))
  ;; (step (reason-from-dominant-premise-nodes n dn d))
  (reason-from-instantiated-premises node d-node depth)
  (let ((pn (d-node-parent d-node)))
    (when pn (reason-from-dominant-premise-nodes node pn depth))))

(defun apply-forwards-reasons (node depth)
  ; (when (equal node (node 10)) (setf n node) (break))
  ;; (step (apply-forwards-reasons n 0))
  (catch 'apply-forwards-reasons
         (let* ((c-list (hypernode-c-list node))
                (d-node (c-list-d-node c-list)))
           (reason-from-dominant-premise-nodes node d-node depth))))

(defun discharge-delayed-reductios (node depth d-interests)
  (when *trace* (indent depth) (princ "DISCHARGE-DELAYED-REDUCTIOS-FROM ")
    (princ node) (terpri))
  ; (when (eq node (node 3)) (setf n node d depth di d-interests) (break))
  ;; (step (discharge-delayed-reductios n d di))
  (when
    (not (hypernode-reductios-discharged node))
    (setf (hypernode-reductios-discharged node) t)
    (let ((reductio-ancestors (hypernode-reductio-ancestors node))
          (Y0 (hypernode-supposition node)))
      (discharge-fortuitous-reductios node d-interests (1+ depth))
      (dolist (il (hypernode-discharged-interests node))
        (let* ((interest (mem1 il))
               (direct-reductio-interest (interest-direct-reductio interest))
               (unifier (mem2 il))
               (unifiers
                 (if (mem3 il)
                   (mem3 il)
                   (appropriately-related-suppositions node interest unifier)))
               (Y1 (remove-duplicates= (match-sublis (mem1 unifier) Y0))))
          (when (<= (interest-degree-of-interest interest)
                    (current-maximal-degree-of-justification node))
            (dolist (dr direct-reductio-interest)
              (let ((node* (car dr))
                    (match (cdr dr)))
                (when (hypernode-cancelled-node node) (return-from discharge-delayed-reductios))
                (let ((Y*0 (remove-duplicates=
                             (match-sublis
                               (mem2 unifier)
                               (match-sublis
                                 match (hypernode-supposition node*))))))
                  (dolist (u unifiers)
                    (let ((unifier* (merge-unifiers* unifier u))
                          (Y (remove-duplicates=
                               (match-sublis (mem1 u) Y1)))
                          (Y* (remove-duplicates= (match-sublis (mem2 u) Y*0))))
                      ; (when (and
                      ;               (not (some #'(lambda (f) (mem (neg f) Y)) Y))
                      ;               (not (some #'(lambda (f) (mem (neg f) Y*)) Y*))
                      ;               (not (some #'(lambda (f) (mem (neg f) Y)) Y*)))
                      (let ((RA (union=
                                  (mapcar
                                    #'(lambda (x)
                                        (cons
                                          (match-sublis
                                            (mem1 unifier*)
                                            (car x)) (cdr x)))
                                    reductio-ancestors)
                                  (mapcar
                                    #'(lambda (x)
                                        (cons (match-sublis
                                                (mem2 unifier*)
                                                (match-sublis match (car x))) (cdr x)))
                                    (hypernode-reductio-ancestors node*))))
                            (NR (union=
                                  (mapcar
                                    #'(lambda (x)
                                        (cons
                                          (match-sublis
                                            (mem1 unifier*)
                                            (car x)) (cdr x)))
                                    (hypernode-non-reductio-supposition node))
                                  (mapcar
                                    #'(lambda (x)
                                        (cons (match-sublis
                                                (mem2 unifier*)
                                                (match-sublis match (car x))) (cdr x)))
                                    (hypernode-non-reductio-supposition node*)))))
                        (dolist (R RA)
                          (when (base-test R RA)
                            (let ((P (car R)))
                              (draw-reductio-conclusion
                                P node node* R Y Y* RA NR interest unifier* (1+ depth)
                                d-interests))))))))))))))))

(defun reason-forwards-from (node depth)
  (when *trace* (indent depth) (princ "REASON-FORWARDS-FROM: ")
    (princ node) (terpri))
  ; (when (equal node (node 21)) (break))
  (when (eq (hypernode-justification node) :reductio-supposition) (decf *unused-suppositions*))
  (discharge-interest-schemes node 0 (1+ depth))
  (when (not (hypernode-cancelled-node node)) (apply-forwards-reasons node depth))
  (when (eq (hypernode-kind node) :inference)
    (let ((i-lists (c-list-corresponding-i-lists (hypernode-c-list node))))
      (when (null (hypernode-interests-discharged? node)) (discharge-interest-in node i-lists 0 t depth nil))
      (when *use-reductio*
        (when (not (hypernode-cancelled-node node)) (adopt-reductio-interest node (1+ depth) nil))
        (discharge-delayed-reductios node depth nil)))  )
  (dolist (rule *auxiliary-forwards-rules*) (funcall rule node)))
;; Definitions for inference hypergraphs.  This is based on OSCAR_3-33.lisp.
;; It implements the theory in the paper of 5/28/02

(proclaim '(special *j-trace* *s-trace* *safe-trace* *new-beliefs* *new-retractions*))

(defvar *j-trace* nil)
;; setting *j-trace* to T traces the justification calculation.

;; (setf *j-trace* t)

(defvar *s-trace* nil)
;; setting *s-trace* to T traces splitting of the hypergraph.

;; (setf *s-trace* t)

(defvar *safe-trace* nil)
;; setting *safe-trace* to T traces the computation of minimal-safe-partial-arguments

;; (setf *safe-trace* t)
;; (setf *safe-trace* nil)

;; ================ defeat-loops and critical-links ==================

(defun ultimate-target (link)
  (cond ((hyper-defeat-link-p link) (hyperlink-target (hyper-defeat-link-target link)))
        ((hyperlink-p link) (hyperlink-target link))))

;; This returns the list of non-circular non-bypassed defeat-paths between links
(defun defeat-paths (link1 link2 &optional used-links)
  (let ((d-paths nil)
        (target1 (hyperlink-target link1)))
    (dolist (link (hypernode-consequent-links target1))
      ;; defeat-paths from the targets of hypernode-consequent-links of link1 are defeat-paths
      ;; provided link1 does not have the same target as the links used in constructing
      ;; the defeat-path or introduce a bypass.
      (when (and (not (eq link link2)) (not (member link used-links)))
        (let ((target (hyperlink-target link)))
          (dolist (d-path (defeat-paths link link2 (cons link used-links)))
            (when
              (not
                (some
                  #'(lambda (DL)
                      (or (eq target (hyperlink-target (hyper-defeat-link-target DL)))  ;; circularity check
                          (member target1 (hypernode-ancestors (hyper-defeat-link-root DL)))))  ;; bypass check
                  (cdr d-path)))
              (pushnew d-path d-paths :test 'equal))))))
    (dolist (d-link (hypernode-supported-hyper-defeat-links target1))
      (let* ((link (hyper-defeat-link-target d-link))
             (target (hyperlink-target link)))
        (cond ((eq link link2) (push (list d-link) d-paths))   ;; one-step defeat-path
              ((not (member link used-links))
               ;; if link1 supports the hyper-defeat-link d-link, adding d-link to the front of a defeat-path
               ;; from its target to link2 is a defeat-path provided that does not introduce a bypass
               ;; or a circularity.
               (dolist (d-path (defeat-paths link link2 (cons link used-links)))
                 (when
                   (not
                     (some
                       #'(lambda (DL)
                           (or (eq target (hyperlink-target (hyper-defeat-link-target DL)))  ;; circularity check
                               (member target1 (hypernode-ancestors (hyper-defeat-link-root DL)))))  ;; bypass check
                       (cdr d-path)))
                   (pushnew (cons d-link d-path) d-paths :test 'equal)))))))
    d-paths))

;; defeat-loops are remembered
(defun defeat-loops (link)
  (cond ((eq (hyperlink-defeat-loops link) T)
         (setf (hyperlink-defeat-loops link) (defeat-paths link link nil)))
        (t (hyperlink-defeat-loops link))))

(defun clear-hyperlink-defeat-loops ()
  (dolist (link *hyperlinks*) (setf (hyperlink-defeat-loops link) T)))

(defun clear-criticalities ()
  (dolist (DL *hyper-defeat-links*) (setf (hyper-defeat-link-critical? DL) nil)))

;; d-loop is a defeat-loop
(defun sigma-defeat-loop (d-loop sigma)
  (or (null (cdr sigma)) (every #'(lambda (L) (mem (cdr sigma) (hyper-defeat-link-in L))) d-loop)))

;; DL is a hyper-defeat-link and sigma a list of hyperlinks and unit sets of hyperlinks.
(defun critical-link (DL sigma)
  ;  (when (eq dl (hyper-defeat-link 1)) (setf d dl x1 sigma) (break))
  (when sigma
    (let ((L (car sigma)))
      (when (hyperlink-p L)
        (let ((critical (assoc sigma (hyper-defeat-link-critical? DL) :test 'equal)))
          (cond
            (critical (cdr critical))
            (t
              (setf critical
                    (some       ;; (defeat-loops L)
                      #'(lambda (d-loop)
                          (and (member DL d-loop) (sigma-defeat-loop d-loop sigma)))
                      (defeat-loops L)))
              (push (cons sigma critical) (hyper-defeat-link-critical? DL))
              critical)))))))

;; DL is a hyper-defeat-link and sigma a list of hyperlinks and unit sets of hyperlinks.
(defun hereditarily-critical-link (DL sigma)
  (and sigma (or (critical-link DL sigma) (hereditarily-critical-link DL (cdr sigma)))))

;; ================ splitting hypergraphs  ==================

;; link is an sigma-critical-hyperlink for DL.
(defun critical-hyperlinks (DL sigma)
  (let ((L (car sigma))
        (critical-links nil))
    (when (hyperlink-p L)
      (dolist (d-loop (defeat-loops L))
        (when (sigma-defeat-loop d-loop sigma)
          (let ((d-link (car d-loop))
                (d-links d-loop)
                (last-d-link nil)
                (link nil)
                (node nil))
            ;; if DL is the first member of d-loop, let link be L, node be (hyperlink-target L).
            ;; If DL is a later member of d-loop, let last-d-link be the previous member and
            ;; let link be its target and node its ultimate-target.
            (loop
              (when (eq d-link DL)
                (cond ((null last-d-link) (setf node (hyperlink-target L)) (setf link L))
                      (t (setf link (hyper-defeat-link-target last-d-link)) (setf node (hyperlink-target link))))
                (return))
              (setf d-links (cdr d-links))
              (when (null d-links) (return))
              (setf last-d-link d-link)
              (setf d-link (car d-links)))
            (when node
              (let* ((links (cdr (hypernode-hyperlinks (hyper-defeat-link-root DL))))
                     (s-link (car (hypernode-hyperlinks (hyper-defeat-link-root DL)))))
                ;; collect the critical hyperlinks
                (when (eq s-link link) (pushnew s-link critical-links))
                (loop
                  (dolist (B (hyperlink-basis s-link))
                    (when (or (eq node B) (member node (hypernode-ancestors B)))
                      (pushnew s-link critical-links)
                      (setf links (append links (hypernode-hyperlinks B)))))
                  (when (null links) (return))
                  (setf s-link (car links))
                  (setf links (cdr links)))))))))
    critical-links))

;; path is an sigma-convergent support-path for (hyper-defeat-link-root DL)
(defun convergent-support-path (path sigma DL)
  (let ((L (car sigma)))
    (and (hyperlink-p L)
         (some     ;; (defeat-loops L)
           #'(lambda (d-loop)
               (and (sigma-defeat-loop d-loop sigma)
                    (let ((d-link (car d-loop))
                          (d-links d-loop)
                          (last-d-link nil))
                      ;; if DL is the first member of d-loop, L is in path. If DL is a later member of
                      ;; d-loop, and last-d-link is the previous member, (hyper-defeat-link-target last-d-link) is in path.
                      (loop
                        (when (eq DL d-link)
                          (cond ((null last-d-link) (return (member L path)))
                                (t (return (member (hyper-defeat-link-target last-d-link) path)))))
                        (setf d-links (cdr d-links))
                        (when (null d-links) (return))
                        (setf last-d-link d-link)
                        (setf d-link (car d-links))))))
           (defeat-loops L)))))

;; path is an sigma-safe support-path for (hyper-defeat-link-root DL)
(defun safe-support-path (path sigma DL)
  (let ((L (car sigma)))
    (and (hyperlink-p L)
         (every     ;; (defeat-loops L)
           #'(lambda (d-loop)
               (and (sigma-defeat-loop d-loop sigma)
                    (let ((d-link (car d-loop))
                          (d-links d-loop)
                          (last-d-link nil))
                      ;; if DL is the first member of d-loop, L is not in path and (hyperlink-target L)
                      ;; is not a hypernode-ancestor of the first member of path. If DL is a later member
                      ;;of d-loop, and last-d-link is the previous member, (hyperlink-target last-d-link)
                      ;;  is not in path and (ultimate-target last-d-link)is not a hypernode-ancestor of the
                      ;; first member of path.
                      (loop
                        (when (eq DL d-link)
                          (cond ((null last-d-link)
                                 (return
                                   (and (not (member L path))
                                        (not
                                          (some
                                            #'(lambda (b)
                                                (or (eq (hyperlink-target L) b)
                                                    (member (hyperlink-target L) (hypernode-ancestors b))))
                                            (hyperlink-basis (car path)))))))
                                (t (return
                                     (and (not (member (hyper-defeat-link-target last-d-link) path))
                                          (not
                                            (some
                                              #'(lambda (b)
                                                  (or (eq (ultimate-target last-d-link) b)
                                                      (member (ultimate-target last-d-link) (hypernode-ancestors b))))
                                              (hyperlink-basis (car path)))))))))
                        (setf d-links (cdr d-links))
                        (when (null d-links) (return t))
                        (setf last-d-link d-link)
                        (setf d-link (car d-links))))))
           (defeat-loops L)))))

(defun princ-sigma (sigma)
  (cond ((null sigma) (princ nil))
        ((hyperlink-p sigma)  (princ "<hyperlink #") (princ (hyperlink-number sigma)) (princ ">"))
        ((hyper-defeat-link-p sigma)  (princ "hyper-defeat-link #") (princ (hyper-defeat-link-number sigma)) (princ ">"))
        ((listp sigma)
         (princ "(")
         (dolist (x sigma)
           (cond ((hyperlink-p x) (princ "<hyperlink #") (princ (hyperlink-number x)) (princ ">"))
                 (t (princ "[<hyperlink #") (princ (hyperlink-number (car x))) (princ ">]"))))
         (princ ")"))))

(defun link-descendant (L link)
  (or (member (hyperlink-target link) (hyperlink-basis L))
      (some #'(lambda (b)   ;; (hyperlink-basis L)
                (member (hyperlink-target link) (hypernode-ancestors b)))
            (hyperlink-basis L))))

;; Where link has a previously computed value, link is sigma-independent and hence that value
;; can be reused in computing the degree of justification of the first member of sigma. This returns
;; the previously computed value.
(defun independent-link-value (link sigma)
  (and (not (link-descendant link (car sigma)))
       (not (member sigma (hyperlink-dependencies link) :test 'equal))
       (assoc (cdr sigma) (hyperlink-justifications link) :test 'equal)))

;; Where node has a previously computed-value, node is sigma-independent and hence that value
;; can be reused in computing the degree of justification of the first member of sigma. This returns
;; the previously computed-value.
(defun independent-hypernode-value (node sigma)
  (and (not (member (hyperlink-target (car sigma)) (hypernode-ancestors node)))
       (not (member sigma (hypernode-dependencies node) :test 'equal))
       (assoc (cdr sigma) (hypernode-justifications node) :test 'equal)))

;; Where dl has a previously computed-value, dl is L-independent and hence that value
;; can be reused in computing the degree of justification of the first member of sigma. This returns
;; the previously computed-value.
(defun independent-hyper-defeat-link-value (dl sigma)
  (independent-hypernode-value (hyper-defeat-link-root dl) sigma))

;; This assumes that (car sigma) is a hyperlink.
(defun initial-node (node sigma)
  (or (and (member node (hyperlink-basis (car sigma)))
           (assoc sigma (hypernode-justifications node) :test 'equal))
      (independent-hypernode-value node sigma)))

;;; This assumes that (car sigma) is a hyperlink.
;(defun initial-node (node sigma)
;     (or (member node (hyperlink-basis (car sigma)))
;            (independent-hypernode-value node sigma)))

(labels ()

  ;; set of sigma-subsidiary-hyperlinks for node relative to path, where path is an sigma-support-path
  ;; for (hyper-defeat-link-root DL). This returns the two values links and unsecured-links
  (defun subsidiary-hyperlinks-for-node (node sigma path DL indent)
    (when (and *display?* *safe-trace*)
      (indent indent) (princ "want subsidiary-hyperlinks-for ") (princ node)
      (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
      (princ-sigma path) (terpri))
    (let ((links nil) (unsecured-links nil))
      (when (not (initial-node node sigma))
        (dolist (L (hypernode-hyperlinks node))
          (multiple-value-bind
            (L-links L-unsecured-links)
            (subsidiary-hyperlinks-for-link L sigma path DL (1+ indent))
            (dolist (L-link L-links)
              (when (and (not (member L-link path))
                         (not (convergent-support-path (cons L-link path) sigma DL)))
                (push L-link links)
                (when (member L-link L-unsecured-links) (push L-link unsecured-links))))))
        (when (and *display?* *safe-trace*)
          (indent indent) (princ "the set of subsidiary-hyperlinks-for ") (princ node)
          (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
          (princ-sigma path) (princ " = ") (princ-sigma links) (terpri))
        (values links unsecured-links))))

  ;; set of sigma-subsidiary-hyperlinks for link relative to path, where path is an sigma-support-path
  ;; for (hyper-defeat-link-root DL). This returns the two values links and unsecured-links. It assumes
  ;; (not (safe-support-path path sigma DL)), because the recursion would have stopped before
  ;; getting to such a path.
  (defun subsidiary-hyperlinks-for-link (link sigma path DL indent)
    (when (and *display?* *safe-trace*)
      (indent indent) (princ "want subsidiary-hyperlinks-for ") (princ link)
      (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
      (princ-sigma path) (terpri))
    (when (not (member link path))
      (let ((new-path (cons link path)))
        (cond ((or
                 (cond ((and *display?* *safe-trace*)
                        (let ((ind (independent-link-value link sigma)))
                          (when ind
                            (indent indent) (princ-sigma link) (princ " is ") (princ-sigma sigma)
                            (princ "-independent, so") (terpri)
                            (indent indent) (princ "the set of subsidiary-hyperlinks-for ") (princ link)
                            (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
                            (princ-sigma path) (princ " = ") (princ-sigma (list link)) (terpri))
                          ind))
                       (t (independent-link-value link sigma)))
                 (cond ((and *display?* *safe-trace*)
                        (let ((safe (safe-support-path new-path sigma DL)))
                          (when safe
                            (indent indent) (princ-sigma new-path) (princ " is a ") (princ-sigma sigma)
                            (princ "-safe support-path, so") (terpri)
                            (indent indent) (princ "the set of subsidiary-hyperlinks-for ") (princ link)
                            (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
                            (princ-sigma path) (princ " = ") (princ-sigma (list link)) (terpri))
                          safe))
                       (t (safe-support-path new-path sigma DL))))
               (values (list link) (list link)))
              ((not (convergent-support-path new-path sigma DL))
               (let ((links nil) (unsecured-links nil))
                 (dolist (B (hyperlink-basis link))
                   (when (not (initial-node B sigma))
                     (multiple-value-bind
                       (B-links B-unsecured-links)
                       (subsidiary-hyperlinks-for-node B sigma (cons link path) DL (1+ indent))
                       (when (null B-links) (return-from subsidiary-hyperlinks-for-link))
                       (setf links (cons link (append B-links links)))
                       (setf unsecured-links (append B-unsecured-links unsecured-links)))))
                 (when (and *display?* *safe-trace*)
                   (indent indent) (princ "the set of subsidiary-hyperlinks-for ") (princ link)
                   (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
                   (princ-sigma path) (princ " = ") (princ-sigma links) (terpri))
                 (values links unsecured-links)))
              ((and *display?* *safe-trace*)
               (indent indent) (princ-sigma new-path) (princ " is ") (princ-sigma sigma)
               (princ "-convergent, so") (terpri)
               (indent indent) (princ "the set of subsidiary-hyperlinks-for ") (princ link)
               (princ " in ") (princ-sigma sigma) (princ " for ") (princ DL) (princ " relative to path ")
               (princ-sigma path) (princ " = nil") (terpri)
               nil)
              ))))
  )

;; This returns the lists of links and unsecured links in the minimal sigma-safe arguments for the root of DL.
(defun minimal-safe-arguments (sigma  DL indent)
  ; (when (and (equal sigma (list (hyperlink 11))) (eq dl (hyper-defeat-link 2))) (setf s sigma d dl i indent) (break))
  ;; (step (minimal-safe-arguments s d i))
  (cond ((and *display?* *safe-trace*)
         (terpri) (terpri) (indent indent) (princ "Computing minimal ") (princ-sigma sigma)
         (princ "-safe-arguments for ") (princ DL) (terpri)
         (multiple-value-bind
           (links unsecured-links)
           (subsidiary-hyperlinks-for-node (hyper-defeat-link-root DL) sigma nil DL (1+ indent))
           (indent indent) (princ "The set of hyperlinks in minimal ") (princ-sigma sigma)
           (princ "-safe-arguments for ") (princ DL) (princ " = ") (princ-sigma links) (terpri)
           (values links unsecured-links)))
        (t (subsidiary-hyperlinks-for-node (hyper-defeat-link-root DL) sigma nil DL (1+ indent)))))

(defun clear-graph-memories ()
  (dolist (node *hypergraph*) (setf (hypernode-in node) nil))
  (dolist (link *hyperlinks*) (setf (hyperlink-in link) nil))
  (dolist (DL *hyper-defeat-links*) (setf (hyper-defeat-link-in DL) nil)))

(labels ()

  ;; This adds link to the critical-graph sigma, and closes it under the closure conditions
  (defun add-link-to-critical-graph (link sigma1 sigma2 &optional (indent 0))
    ;  (when (and (eq link (hyperlink 6)) (equal sigma1 (list (hyperlink 11)))) (setf l link s1 sigma1 s2 sigma2 i indent) (break))
    ;  (step (add-link-to-critical-graph l s1 s2 i))
    (when (not (mem sigma1 (hyperlink-in link)))
      (when (and *display?* *s-trace*)
        (terpri) (indent indent) (princ "Inserting ") (princ link) (princ " in ") (princ-sigma sigma1))
      (push sigma1 (hyperlink-in link))
      ;; if a hyperlink is in sigma1 then all members of its basis are in sigma1
      (dolist (B (hyperlink-basis link))
        (add-node-to-critical-graph B sigma1 sigma2 (1+ indent)))
      (dolist (dl (hyperlink-defeaters link))
        (when (and (mem (cdr sigma1) (hyper-defeat-link-in dl)) (not (mem sigma1 (hyper-defeat-link-in dl))))
          ;; if a hyperlink is in sigma1 all of its sigma1-noncritical hyper-defeat-links and their roots are in sigma1
          (cond ((not (critical-link dl sigma1))
                 (push sigma1 (hyper-defeat-link-in dl))
                 (when (and *display?* *s-trace*)
                   (terpri) (indent (1+ indent)) (princ "Inserting ") (princ dl) (princ " in ") (princ-sigma sigma1))
                 (add-node-to-critical-graph (hyper-defeat-link-root dl) sigma1 sigma2 (1+ indent)))
                ;; if a sigma1-critical hyper-defeat-link has minimal sigma1-safe arguments, it is in sigma1
                ;; and all hyperlinks and their targets in the minimal sigma1-safe arguments
                ;; are in the noncritical-graph sigma2. If one of these hyperlinks is (cdr sigma1)-
                ;; unsecured and it is not sigma1-independent, it is also in the critical-graph sigma1.
                (t  (multiple-value-bind
                      (links unsecured-links)
                      (minimal-safe-arguments sigma1 dl indent)
                      (when links
                        (when (and *display?* *s-trace*)
                          (terpri) (indent (1+ indent)) (princ "Inserting ") (princ dl) (princ " in ") (princ-sigma sigma1))
                        (pushnew sigma1 (hyper-defeat-link-in dl)))
                      (dolist (L links)
                        (when (not (mem sigma2 (hypernode-in (hyperlink-target L))))
                          (when (and *display?* *s-trace*)
                            (terpri) (indent (1+ indent)) (princ "Inserting ") (princ (hyperlink-target L))
                            (princ " in noncritical graph  ") (princ-sigma sigma2))
                          (push sigma2 (hypernode-in (hyperlink-target L)))
                          )
                        (when (not (mem sigma2 (hyperlink-in L)))
                          (when (and *display?* *s-trace*)
                            (terpri) (indent (1+ indent)) (princ "Inserting ") (princ L)
                            (princ " in noncritical graph ") (princ-sigma sigma2))
                          (push sigma2 (hyperlink-in L))
                          ))
                      (dolist (L unsecured-links)
                        (push sigma2 (hyperlink-unsecured? L))
                        (when (not (independent-link-value L sigma1))
                          (add-link-to-critical-graph L sigma1 sigma2 (1+ indent)))))))))))

  ;; This adds node to the critical-graph sigma1, and closes it under the closure conditions
  (defun add-node-to-critical-graph (node sigma1 sigma2 &optional (indent 0))
    (when (not (member sigma1 (hypernode-in node)))
      (when (and *display?* *s-trace*)
        (terpri) (indent indent) (princ "Inserting ") (princ node) (princ " in ") (princ-sigma sigma1))
      (push sigma1 (hypernode-in node))
      ;; if a node is in sigma1, it is not  sigma1-initial, all of its hyperlinks are in sigma1
      (when (not (initial-node node sigma1))
        (dolist (L (hypernode-hyperlinks node))
          (add-link-to-critical-graph L sigma1 sigma2 (1+ indent))))))
  )

(labels ()

  (defun display-hypergraphs (link)
    (compute-new-hypergraphs link)
    (terpri)  (princ "When sigma = ") (princ-sigma (list link)) (princ ":")
    (dolist (N *hypergraph*)
      (when (mem (list link) (hypernode-in  N)) (terpri) (princ N) (princ " is in")))
    (dolist (L *hyperlinks*)
      (when (mem (list link) (hyperlink-in L)) (terpri) (princ L) (princ " is in")))
    (dolist (L *hyper-defeat-links*)
      (when (mem (list link) (hyper-defeat-link-in L)) (terpri) (princ L) (princ " is in")))
    (terpri)
    (terpri) (princ "When sigma = ") (princ-sigma (list (list link))) (princ ":")
    (dolist (N *hypergraph*)
      (when (mem (list (list link)) (hypernode-in N)) (terpri) (princ N) (princ " is in")))
    (dolist (L *hyperlinks*)
      (when  (mem (list (list link)) (hyperlink-in L)) (terpri) (princ L) (princ " is in")))
    (dolist (L *hyper-defeat-links*)
      (when  (mem (list (list link)) (hyper-defeat-link-in L)) (terpri) (princ L) (princ " is in"))))


  #| On HG14:

  ? (display-hypergraphs (hyperlink 7))

  When sigma = (#<hyperlink #7 for node 8>):
  #<Node 9> is in
  #<Node 8> is in
  #<Node 7> is in
  #<Node 6> is in
  #<hyperlink #10 for node 9> is in
  #<hyperlink #7 for node 8> is in
  #<hyperlink #6 for node 7> is in
  #<hyperlink #5 for node 6> is in
  #<hyper-defeat-link #2 for hyperlink 5 for node 6> is in
  #<hyper-defeat-link #1 for hyperlink 7 for node 8> is in

  When sigma = ((#<hyperlink #7 for node 8>)):
  #<Node 9> is in
  #<Node 7> is in
  #<hyperlink #9 for node 9> is in
  #<hyperlink #8 for node 7> is in

  |#

  (defun display-hypergraph ()
    (terpri) (princ "(") (terpri)
    (dolist (node (reverse *hypergraph*)) (princ node)
      (princ "  --  ") (princ "justification = ") (princ (hypernode-degree-of-justification node)) (terpri)
      (when (hypernode-hyperlinks node)
        (princ "     hyperlinkS:") (terpri)
        (dolist (link (reverse (hypernode-hyperlinks node)))
          (princ "          ") (princ link) (princ " from ") (princ (hyperlink-basis link)) (terpri)
          (when (hyperlink-defeaters link)
            (princ "               hyper-defeat-linkS-FOR:") (terpri)
            (dolist (dl (reverse (hyperlink-defeaters link)))
              (princ "                    ") (princ dl) (princ " from ") (princ (hyper-defeat-link-root dl)) (terpri)))))
      (when (hypernode-consequent-links node)
        (princ "     CONSEQUENT-LINKS:") (terpri)
        (dolist (link (reverse (hypernode-consequent-links node)))
          (princ "          ") (princ link) (terpri)
          (when (hyperlink-defeaters link)
            (princ "               hyper-defeat-linkS-FOR:") (terpri)
            (dolist (dl (reverse (hyperlink-defeaters link)))
              (princ "                    ") (princ dl) (princ " from ") (princ (hyper-defeat-link-root dl)) (terpri)))))
      (when (hypernode-supported-hyper-defeat-links node)
        (princ "     SUPPORTED-hyper-defeat-linkS:") (terpri)
        (dolist (dl (reverse (hypernode-supported-hyper-defeat-links node)))
          (princ "          ") (princ dl) (terpri))))
    (princ ")") (terpri))

  (defun display-split (link sigma indent)
    (terpri)
    (let ((S (cons link sigma)))
      (terpri) (indent indent)  (princ "When sigma = ") (princ-sigma S) (princ ":")
      (when (mem S (hyperlink-in link))
        (terpri) (indent (+ 2 indent)) (princ link) (princ " is in")
        (dolist (DL (reverse (hyperlink-defeaters link)))
          (when (mem S (hyper-defeat-link-in DL))
            (terpri)  (indent (+ 4 indent)) (princ DL) (princ " is in"))))
      (dolist (N (reverse *hypergraph*))
        (when (mem S (hypernode-in  N))  (terpri)
          (indent indent) (princ N) (princ " is in")
          (dolist (L (reverse (hypernode-hyperlinks N)))
            (when (mem S (hyperlink-in L))
              (terpri) (indent (+ 2 indent)) (princ L) (princ " is in")
              (dolist (DL (reverse (hyperlink-defeaters L)))
                (when (mem S (hyper-defeat-link-in DL))
                  (terpri)  (indent (+ 4 indent)) (princ DL) (princ " is in")))))))
      (dolist (L (reverse *hyperlinks*))
        (when (and (not (eq L link)) (mem S (hyperlink-in L)) (not (mem S (hypernode-in (hyperlink-target L)))))
          (terpri) (indent (+ 2 indent)) (princ L) (princ " is in")
          (dolist (DL (reverse (hyperlink-defeaters L)))
            (when (mem S (hyper-defeat-link-in DL))
              (terpri)  (indent (+ 4 indent)) (princ DL) (princ " is in"))))))
    (terpri)
    (let ((S (cons (list link) sigma)) (empty? t))
      (terpri) (indent indent)  (princ "When sigma = ") (princ-sigma S) (princ ":")
      (dolist (N (reverse *hypergraph*))
        (when (mem S (hypernode-in  N))  (terpri)
          (indent indent) (princ N) (princ " is in") (setf empty? nil)
          (dolist (L (reverse (hypernode-hyperlinks N)))
            (when (mem S (hyperlink-in L))
              (terpri) (indent (+ 2 indent)) (princ L) (princ " is in") (setf empty? nil)
              (dolist (DL (reverse (hyperlink-defeaters L)))
                (when (mem S (hyper-defeat-link-in DL))
                  (terpri) (indent (+ 4 indent)) (princ DL) (princ " is in") (setf empty? nil)))))))
      (when empty? (princ "   This hypergraph is empty.")))
    (terpri) (terpri))
  ;  (when (eq link (hyperlink 11)) (break)))

  (defun split-hypergraph (link &optional sigma (indent 0))
    ;  (when (equal *cycle* 5) (setf l link s sigma i indent) (break))
    ;; (split-hypergraph l s i)
    ;; (step (split-hypergraph l s i))
    (when (and *display?* *s-trace*)
      (terpri) (princ "------The current hypergraph is-------") (terpri)
      (display-hypergraph)
      (princ "-----------------------------------") (terpri)
      (terpri) (indent indent) (princ "Splitting the hypergraph ")
      (princ-sigma sigma) (princ " relative to ") (princ link) (terpri))
    (let ((sigma1 (cons link sigma))             ;; the link-critical graph
          (sigma2 (cons (list link) sigma)))      ;; the link-noncritical graph
      ;; add link to the critical-graph and close under the closure conditions
      (add-link-to-critical-graph link sigma1 sigma2 indent)
      ;; for each hyperlink that is sigma1-critical for the hyper-defeat-link-root of a link-defeater of link, add it and
      ;; its target to the critical-graph, and close under the closure conditions.
      (dolist (dl (hyperlink-defeaters link))
        (dolist (L (critical-hyperlinks dl sigma1))
          (when (not  (member sigma1 (hypernode-in (hyperlink-target L)) :test 'equal))
            (when (and *display?* *s-trace*)
              (terpri) (indent indent) (princ "Inserting ") (princ (hyperlink-target L))
              (princ " in ") (princ-sigma sigma1))
            (push sigma1 (hypernode-in (hyperlink-target L))))
          (add-link-to-critical-graph L sigma1 sigma2 (1+ indent))))
      (when (and *display?* *j-trace*) (display-split link sigma indent))))

  (defun compute-new-hypergraphs (link &optional sigma (indent 0))
    (clear-graph-memories)
    (split-hypergraph link sigma indent))

  )

#|
;; This adds the hyper-defeat-link dl to the critical-graph sigma and closes it under the closure conditions
(defun add-hyper-defeat-link-to-critical-graph (dl sigma1 sigma2 &optional (indent 0))
  (when (not (mem sigma1 (hyper-defeat-link-in dl)))
    (when (and *display?* *s-trace*)
      (terpri) (indent indent) (princ "Inserting ") (princ dl) (princ " in ") (princ-sigma sigma1))
    (push sigma1 (hyper-defeat-link-in dl))
    ;; if a hyper-defeat-link is in sigma1 and it is not sigma1-critical then its root is in sigma1. If it is
    ;; sigma1-critical, then for every hyperlink L in a minimal sigma1-safe argument for the
    ;; root of dl , L and its target are in the noncritical-graph sigma2. If L is (cdr sigma1)-unsecured,
    ;; it is also in the critical-graph sigma1.
    (cond ((critical-link dl sigma1)
           (multiple-value-bind
             (links unsecured-links)
             (minimal-safe-arguments sigma1 dl)
             (dolist (L links)
               (when (not (mem sigma2 (hyperlink-in L)))
                 (push sigma2 (hyperlink-in L))
                 (when (and *display?* *s-trace*)
                   (terpri) (indent indent) (princ "Inserting ") (princ L) (princ " in ") (princ-sigma sigma2)))
               (when (not (mem sigma2 (hyperlink-in (hyperlink-target L))))
                 (push sigma2 (hypernode-in (hyperlink-target L)))
                 (when (and *display?* *s-trace*)
                   (terpri) (indent indent) (princ "Inserting ") (princ (hyperlink-target L))
                   (princ " in ") (princ-sigma sigma2))))
             (dolist (L unsecured-links)
               (add-link-to-critical-graph L sigma1 sigma2 (1+ indent)))))
          (t
            (add-node-to-critical-graph (hyper-defeat-link-root dl) sigma1 sigma2 (1+ indent))))))
|#

;; ================ computing degrees of justification  ==================

#|
(defun update-beliefs ()
  ; (when (equal *cycle* 2) (break))
  ; (step (update-beliefs))
  (cond
    (*deductive-only*
      (dolist (link *new-links*)
        (let ((node (hyperlink-target link)))
          (setf (hypernode-old-degree-of-justification node) (hypernode-degree-of-justification node))
          (setf (hypernode-degree-of-justification node) 1.0)
          (setf (hyperlink-degree-of-justification link) 1.0)
          (setf (hypernode-discounted-node-strength node) (hyperlink-discount-factor link))
          (when (null (hypernode-old-degree-of-justification node))
            (queue-for-inference node))
          ; (display-belief-changes (list link) (list node) nil)
          (discharge-ultimate-epistemic-interests (list node) nil))))
    (t
      (setf *new-beliefs* nil)
      (setf *new-retractions* nil)
      (compute-hypernode-degrees-of-justification)
      (display-belief-changes *new-links* *new-beliefs* *new-retractions*)
      (dolist (node *new-beliefs*)
        (apply-optative-dispositions-to node)
        (apply-Q&I-modules-to node))
      (let ((altered-queries
              (discharge-ultimate-epistemic-interests *new-beliefs* *new-retractions*))
            (altered-interests
              (compute-interest-graph-defeat-statuses *new-beliefs* *new-retractions*)))
        (recompute-priorities *new-beliefs* *new-retractions* altered-interests altered-queries))
      )))
|#

;; This finds the hyperlink in values that occurs after all other hyperlinks in values in path
(defun last-link (values path)
  (let ((last-link nil)
        (remainder path))
    (dolist (value values)
      (when (hyperlink-p value)
        (let ((new-remainder (member value remainder)))
          (when new-remainder
            (setf remainder new-remainder)
            (setf last-link value)))))
    last-link))

;; This records node and hyperlink-dependencies discovered during the computation of
;; degrees of justification. It is called by COMPUTE-LINK-JUSTIFICATION. It records the fact
;; that link has been found to be sigma-dependent.
(defun record-dependencies (link sigma indent)
  (when (and *display?* *j-trace*)
    (indent indent) (princ "RECORDING: ") (princ link) (princ " is ") (princ-sigma sigma)
    (princ "-dependent") (terpri) (indent indent) (princ "RECORDING: ") (princ (hyperlink-target link))
    (princ " is ") (princ-sigma sigma) (princ "-dependent") (terpri))
  (when (not (member sigma (hyperlink-dependencies link) :test 'equal))
    (push sigma (hyperlink-dependencies link))
    (when (not (member sigma (hypernode-dependencies (hyperlink-target link)) :test 'equal))
      (push sigma (hypernode-dependencies (hyperlink-target link)))
      (dolist (c-link (hypernode-consequent-links (hyperlink-target link)))
        (record-dependencies c-link sigma indent)))))

(defun ~ (x y)
  (if (>= y x) 0.0 (- x y)))

(labels ()

  ;; path is the reverse of the  list of hyperlinks the recursion has traversed before getting to link.
  ;; Link0 is the hyperlink initiating the recursive computation leading to node.
  ;; This returns a hyperlink or numerical value.
  (defun compute-hyper-defeat-link-justification (DL sigma link0 &optional (indent 0) path)
    ;  (when (eq dl (hyper-defeat-link 2)) (setf d dl   l0 link0 s sigma i indent p path) (break))
    ;; (step (compute-hyper-defeat-link-justification d  s l0 i p))
    (when (> indent 100) (break))
    (when (and *display?* *j-trace*)
      (cond ((zerop indent) (terpri) (princ "want justification of ") (princ DL))
            (t
              (indent indent) (princ "need justification of ") (princ DL)
              (when sigma (princ " relative to ") (princ-sigma sigma))
              (when path (princ " and path ") (princ-sigma path))))
      (terpri))
    (let ((value nil))
      (cond
        ;; If the value has already been computed and either link0 = NIL or the value is link0-independent, use it
        ((or
           (and (null link0) (setf value (cdr (assoc sigma (hyper-defeat-link-justifications DL) :test 'equal))))
           (and link0 (setf value (cdr (independent-hyper-defeat-link-value DL (cons link0 sigma))))))
         (when (and *display?* *j-trace*) (indent indent) (princ "This value has already been computed.") (terpri))
         t)
        ;; If the value has been computed in (cdr sigma) and either link0 = NIL or it is link0-independent, use it
        ((and sigma
              (or
                (and (null link0) (setf value (assoc (cdr sigma) (hyper-defeat-link-justifications DL) :test 'equal)))
                (and link0 (setf value (independent-hyper-defeat-link-value DL (cons  link0 (cdr sigma)))))))
         (when (and *display?* *j-trace*)
           (indent indent)  (princ "This hyper-defeat-link is ") (princ sigma)
           (princ "-independent. It inherits its value from ") (princ-sigma (cdr sigma)) (terpri))
         (setf value (cdr value))
         (push (cons sigma value) (hyper-defeat-link-justifications DL)))
        (t
          (let ((root (hyper-defeat-link-root DL)))
            (setf value
                  (cond ((critical-link DL sigma)
                         ;; critical-hyper-defeat-links inherit their value from the noncritical hypergraph
                         (let ((sigma+ (cons (list (car sigma)) (cdr sigma))))
                           (when (and *display?* *j-trace*)
                             (indent (1+ indent)) (princ "This hyper-defeat-link was imported from ")
                             (princ-sigma sigma+) (terpri))
                           (compute-hypernode-justification root sigma+ link0 (1+ indent) :dep path)))
                        ;; noncritical-hyper-defeat-links have the value of their root
                        (t (compute-hypernode-justification root sigma link0 (1+ indent) :ind path))))
            (when (numberp value) (push (cons sigma value) (hyper-defeat-link-justifications DL))))))
      (when (and *display?* *j-trace*)
        (indent indent)
        (princ "(justification ") (princ DL) (princ " ") (princ-sigma sigma) (princ ") = ") (princ value)
        (when path (princ ", path = ") (princ-sigma path)) (terpri))
      value))

  ;; path is the reverse of the  list of hyperlinks the recursion has traversed before getting to link.
  ;; Link0 is the hyperlink initiating the recursive computation leading to node.
  ;; This returns a hyperlink or a numerical value.
  (defun compute-link-justification (link sigma link0 &optional (indent 0) path)
    ;  (setf l link l0 link0 s sigma  i indent p path)
    ; (when (eq link (hyperlink 3)) (setf l link l0 link0 s sigma  i indent p path) (break))
    ;; (step (compute-link-justification l s l0 i p))
    (when (> indent 100) (break))
    (when (and *display?* *j-trace*)
      (cond ((zerop indent) (terpri) (princ "want justification of ") (princ link))
            (t
              (indent indent) (princ "need justification of  ") (princ link)
              (when sigma (princ " relative to ") (princ-sigma sigma))
              (when path (princ " and path ") (princ-sigma path))))
      (terpri))
    (let ((value nil))
      (cond
        ;; If the value has already been computed and either link0 = NIL or the value is link0-independent, use it
        ((or
           (and (null link0) (setf value (cdr (assoc sigma (hyperlink-justifications link) :test 'equal))))
           (and link0 (setf value  (cdr (independent-link-value link (cons link0 sigma))))))
         (when (and *display?* *j-trace*) (indent indent) (princ "This value has already been computed.") (terpri))
         t)
        ;; if path contains link, return link
        ((member link path)
         (when (and *display?* *j-trace*)
           (indent indent) (princ "This path of computation is circular.") (terpri))
         (setf value link))
        ;;  If the value has been computed in (cdr sigma) and either link0 = NIL or it is link0-independent, use it
        ((and sigma
              (or
                (and (null link0) (setf value (assoc (cdr sigma) (hyperlink-justifications link) :test 'equal)))
                (and link0 (setf value (independent-link-value link (cons link0 (cdr sigma)))))))
         (when (and *display?* *j-trace*)
           (indent indent)  (princ "This hyperlink is ") (princ sigma)
           (princ "-independent. It inherits its value from ") (princ-sigma (cdr sigma)) (terpri))
         (setf value (cdr value))
         (push (cons sigma value) (hyperlink-justifications link)))
        ;; if (car sigma) is a bracketed-hyperlink and link is sigma-unsecured, compute the link-justification
        ;; in the critical hypergraph.
        ((and sigma (not (hyperlink-p (car sigma))) (mem sigma (hyperlink-unsecured? link)))
         (let ((sigma-  (cons (caar sigma) (cdr sigma))))
           (when (and *display?* *j-trace*)
             (indent indent)  (princ "This hyperlink was imported from ") (princ-sigma sigma-) (terpri))
           (setf value (compute-link-justification link sigma- link0 (1+ indent) path))
           (push (cons sigma value) (hyperlink-justifications link))))
        ;; if link is not sigma-unsecured, and all defeaters have numerical-values
        ;; then value is the min of the reason-strength and the degrees of justification of elements of
        ;; the basis, less the degree of justification of the undercutting defeater if there is one. The
        ;; defeaters having numerical values signifies that the link is not self-dependent.
        (t
          (block compute-value
                 (let ((basis (hyperlink-basis link)))
                   (cond
                     (basis
                       (let ((D nil) (B nil))
                         (cond ((null link0)
                                ;; if link0 = NIL, compute the degrees of justification for the members of the basis
                                ;; without requiring independence, and compute the degrees of justification of
                                ;; the hyper-defeat-links requiring hyperlink-independence.
                                (dolist (bs basis)
                                  (let ((bs-value (compute-hypernode-justification bs sigma nil (1+ indent) :basis path)))
                                    (when (eq bs-value 0.0)
                                      (setf value 0.0)
                                      (push (cons sigma 0.0) (hyperlink-justifications link))
                                      (return-from compute-value))
                                    (push bs-value B)))
                                (dolist (dl (hyperlink-defeaters link))
                                  (when (member sigma (hyper-defeat-link-in dl) :test 'equal)
                                    (push (compute-hyper-defeat-link-justification dl sigma link (1+ indent)  (cons link path)) D)))
                                ; (when (not (and (every #'numberp D)
                                ;                                     (every #'(lambda (dl) (independent-hyper-defeat-link-value dl (cons link sigma)))
                                ;                                                    (hyperlink-defeaters link))))
                                (when (not (every #'numberp D))
                                  (setf link0 link)))
                               (t
                                 ;; if link0 is not NIL, compute the degrees of justification for the members of the basis
                                 ;;and  the hyper-defeat-links requiring link0-independence.
                                 (dolist (bs basis)
                                   (let ((bs-value (compute-hypernode-justification bs sigma link0 (1+ indent) :basis path)))
                                     (when (eq bs-value 0.0)
                                       (setf value 0.0)
                                       (push (cons sigma 0.0) (hyperlink-justifications link))
                                       (return-from compute-value))
                                     (push bs-value B)))
                                 (dolist (dl (hyperlink-defeaters link))
                                   (when (member sigma (hyper-defeat-link-in dl) :test 'equal)
                                     (push (compute-hyper-defeat-link-justification dl sigma link0 (1+ indent)  (cons link path)) D)))))
                         (cond ((and (every #'numberp B) (every #'numberp D))
                                (setf value (~ (min (hyperlink-reason-strength link) (minimum B)) (maximum0 D)))
                                (push (cons sigma value) (hyperlink-justifications link)))
                               ;; if some defeater is assigned a hyperlink, and the path is either empty or contains
                               ;; no hyperlinks assigned as values to defeaters of link, then then link is self-dependent
                               ;; and its value is of use in computing the degree of justification of link0. So we split the
                               ;; hypergraph and compute its value accordingly.
                               ((and (every #'(lambda (sl) (and (not (member sl B)) (not (member sl D)))) path))
                                (when (and *display?* *j-trace*)
                                  (indent indent) (princ link) (princ " is self-dependent") (terpri))
                                (let ((independent-defeaters nil)
                                      (dependent-defeaters nil)
                                      (sigma1 (cons link sigma))
                                      (sigma2 (cons (list link) sigma))
                                      (D1 nil) (D2 nil))
                                  (split-hypergraph link sigma (1+ indent))
                                  (dolist (DL (hyperlink-defeaters link))
                                    (when (mem sigma (hyper-defeat-link-in DL))
                                      (let ((root (hyper-defeat-link-root DL)))
                                        (cond ((mem sigma1 (hypernode-in root))
                                               (push root dependent-defeaters)
                                               (when (mem sigma2 (hypernode-in root)) (push root independent-defeaters)))
                                              ((mem sigma2 (hypernode-in root)) (push root independent-defeaters))))))
                                  (when (not (every #'numberp B))
                                    (setf B nil)
                                    (dolist (bs basis)
                                      (let ((bs-value (compute-hypernode-justification bs sigma link0 (1+ indent) :basis)))
                                        (when (eq bs-value 0.0)
                                          (setf value 0.0)
                                          (push (cons sigma 0.0) (hyperlink-justifications link))
                                          (return-from compute-value))
                                        (push bs-value B))))
                                  (dolist (d independent-defeaters)
                                    (push (compute-hypernode-justification D sigma2 link0 (1+ indent) :ind) D1))
                                  (dolist (d dependent-defeaters)
                                    (push (compute-hypernode-justification D sigma1 link0 (1+ indent) :dep) D2))
                                  (setf
                                    value
                                    (~ (min (hyperlink-reason-strength link) (minimum B))
                                       (+ (maximum0 D1) (maximum0 D2))))
                                  (push (cons sigma value) (hyperlink-justifications link))))
                               ;; otherwise, its value is last-link.
                               (t (setf value (last-link (append B D) path))
                                  (record-dependencies value (cons link sigma) indent)))))
                     (t (setf value (hypernode-degree-of-justification (hyperlink-target link)))
                        (push (cons sigma value) (hyperlink-justifications link))))))))
      (when (and (null sigma) (numberp value)) (setf (hyperlink-degree-of-justification link) value))
      (when (and *display?* *j-trace*)
        (indent indent)
        (princ "(justification ") (princ link) (princ " ") (princ-sigma sigma) (princ ") = ") (princ value)
        (when path (princ ", path = ") (princ-sigma path)) (terpri))
      value))

  ;; path is the reverse of the  list of hyperlinks through whose defeaters the recursion has
  ;;  traversed before getting to node. Link0 is the hyperlink initiating the recursive computation
  ;; leading to node. This returns a hyperlink or numerical value.
  (defun compute-hypernode-justification (node sigma &optional link0 (indent 0) case path)
    ;  (when (and (equal sigma (list (list (hyperlink 3)))) (eq node (node 5))) (setf n node l link0 s sigma  i indent c case p path) (break))
    ;; (step (compute-hypernode-justification n l s i c p))
    (when (> indent 100) (break))
    (when (and *display?* *j-trace*)
      (cond ((zerop indent) (terpri) (princ "want justification of ") (princ node))
            (t
              (indent indent)
              (cond ((eq case :basis) (princ "need justification of basis element ") (princ node))
                    ((eq case :ind) (princ "need justification of ") (princ node)
                                    (princ " as the root of an independent hyper-defeat-link"))
                    ((eq case :dep) (princ "need justification of ") (princ node)
                                    (princ " as the root of a dependent hyper-defeat-link")))
              (when sigma (princ " relative to ") (princ-sigma sigma))
              (when path (princ " and path ") (princ-sigma path))))
      (terpri))
    (let ((value nil))
      (cond
        ;; If the value has already been computed and either link0 = NIL or node is in the hyperlink-basis
        ;; of link0 or the value is link0-independent, use it
        ((or
           (and
             (or (null link0) (member node (hyperlink-basis link0)))
             (setf value (cdr (assoc sigma (hypernode-justifications node) :test 'equal))))
           (and link0 (setf value (cdr (independent-hypernode-value node (cons link0 sigma))))))
         (when (and *display?* *j-trace*) (indent indent) (princ "This value has already been computed.") (terpri))
         t)
        ;; Initial nodes get their assigned degrees of justification
        ((eq (hypernode-justification node) :given)
         (when (and *display?* *j-trace*) (indent indent) (princ "This is an initial node.") (terpri))
         (setf value (hypernode-degree-of-justification node))
         (push (cons sigma value) (hypernode-justifications node)))
        ;;  If the value has been computed in (cdr sigma) and either link0 = NIL or it is link0-independent, use it
        ((and sigma
              (or
                (and (or (null link0) (member node (hyperlink-basis link0)))
                     (setf value (assoc (cdr sigma) (hypernode-justifications node) :test 'equal)))
                (and link0 (setf value (independent-hypernode-value node (cons link0 (cdr sigma)))))))
         (when (and *display?* *j-trace*) (indent indent) (princ "This node is ") (princ sigma)
           (princ "-independent. It inherits its value from ") (princ-sigma (cdr sigma)) (terpri))
         (setf value (cdr value))
         (push (cons sigma value) (hypernode-justifications node)))
        (t
          (let ((values nil))
            (dolist (link  (subset #'(lambda (link) (mem sigma (hyperlink-in link))) (hypernode-hyperlinks node)))
              (push (compute-link-justification link sigma link0 (1+ indent) path) values))
            ;;  it receives the maximum value of its sigma-hyperlinks if they all have numerical values.
            (cond ((every #'numberp values)
                   (setf value (maximum0 values))
                   (push (cons sigma value) (hypernode-justifications node))
                   ;; The following is standard stuff from OSCAR_3.33
                   (when (null sigma)
                     (let ((old-value (hypernode-degree-of-justification node)))
                       (setf (hypernode-degree-of-justification node) value)
                       (setf (hypernode-discounted-node-strength node)
                             (if (hypernode-hyperlinks node)
                               (* (hyperlink-discount-factor (car (hypernode-hyperlinks node))) value)
                               value))
                       (when (null old-value) (queue-for-inference node))
                       (setf (hypernode-old-degree-of-justification node) old-value)
                       (cond
                         ((null old-value)
                          (cond ((not (zerop value)) (push node *new-beliefs*))
                                ((not (member nil (hypernode-nearest-defeasible-ancestors node)))
                                 (push node *new-retractions*))))
                         ((> value old-value) (push node *new-beliefs*))
                         ((< value old-value) (push node *new-retractions*)))
                       )))
                  ;;  If any of them are assigned hyperlinks (signifying circularity in the computation)
                  ;; then it receives as its value the latest of those hyperlinks in the path.
                  (t (setf value (last-link values path)))))))
      (when (and *display?* *j-trace*)
        (indent indent)
        (princ "(justification ") (princ node) (princ " ") (princ-sigma sigma) (princ ") = ") (princ value)
        (when path (princ ", path = ") (princ-sigma path)) (terpri))
      value))

  )

(defun compute-affected-justifications (link)
  ; (when (eq link (hyperlink 4)) (break))
  (let ((node (hyperlink-target link)))
    (unless (assoc nil (hypernode-justifications node))
      (compute-hypernode-justification node nil)
      (dolist (L (hypernode-consequent-links node))
        (unless (assoc nil (hyperlink-justifications L))
          (compute-affected-justifications L)))
      (dolist (DL (hypernode-supported-hyper-defeat-links node))
        (let ((L (hyper-defeat-link-target DL)))
          (unless (assoc nil (hyperlink-justifications L))
            (compute-affected-justifications L)))))))

(defun reset-memories (link)
  (setf (hyperlink-justifications link) nil)
  (setf (hyperlink-defeat-loops link) T)
  (setf (hyperlink-unsecured? link) nil)
  (setf (hyperlink-in link) (list nil))
  (setf (hyperlink-dependencies link) nil)
  (let ((node (hyperlink-target link)))
    (setf (hypernode-justifications node) nil)
    (setf (hypernode-in node) (list nil))
    (setf (hypernode-dependencies node) nil)
    (dolist (L (hypernode-consequent-links node))
      (when (hyperlink-justifications L) (reset-memories L)))
    (dolist (dl (hypernode-supported-hyper-defeat-links node))
      (setf (hyper-defeat-link-justifications dl) nil)
      (setf (hyper-defeat-link-critical? dl) nil)
      (setf (hyper-defeat-link-in dl) (list nil))
      (let ((target (hyper-defeat-link-target dl)))
        (when (hyperlink-justifications target) (reset-memories target))))))

(defun compute-hypernode-degrees-of-justification ()
  ;  (when (equal *cycle* 3) (break))
  ; (step (compute-hypernode-degrees-of-justification))
  (dolist (link *new-links*) (reset-memories link))
  (dolist (link *new-links*) (compute-affected-justifications link)))

#|
(defun display-belief-changes  (links new-beliefs new-retractions)
  ; (when (member (hyperlink 12) links) (setf l links nb new-beliefs nr new-retractions) (break))
  ;; (step (display-belief-changes l  nb nr))
  (when (or *display?* *log-on*)
    (cond
      ((and (not *deductive-only*) (or new-beliefs new-retractions))
       (when (and *display?* *graphics-on*)
         (when *graphics-pause* (pause-graphics))
         (dolist (link links) (draw-n (hyperlink-target link) *og* *nodes-displayed*)))
       (when
         (or new-retractions
             (some
               #'(lambda (N)
                   (or (not (some #'(lambda (L) (eq N (hyperlink-target L))) links))
                       (set-difference (hypernode-hyperlinks N) links)
                       (not (eql (hypernode-degree-of-justification N) 1.0))))
               new-beliefs))
         (when *log-on*
           (push "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" *reasoning-log*))
         (when *display?* (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))
       (dolist (N new-beliefs)
         (cond ((or (not (some #'(lambda (L) (eq N (hyperlink-target L))) links))
                    (set-difference (hypernode-hyperlinks N) links))
                (when *log-on*
                  (push (list :increased-support N (hypernode-degree-of-justification N))
                        *reasoning-log*))
                (when *display?*
                  (princ "               The degree-of-justification of ") (princ N)
                  (princ " has increased to ") (princ (hypernode-degree-of-justification N)) (terpri)
                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                (when (and *display?* *graphics-on*)
                  (let ((posi (hypernode-position N *og*)))
                    (when posi
                      (when (and (boundp '*speak*) *speak*)
                        (speak-text "The degree-of-support of N ")
                        (speak-text (write-to-string (hypernode-number N)))
                        (speak-text "has increased to")
                        (speak-text (write-to-string (hypernode-degree-of-justification N))))
                      (draw-just-undefeated-node posi *og* N)))))
               ((not (eql (hypernode-degree-of-justification N) 1.0))
                (when *log-on*
                  (push (list :new-support N (hypernode-degree-of-justification N)) *reasoning-log*))
                (when *display?*
                  (princ "               The degree-of-justification of ") (princ N)
                  (princ " is ") (princ (hypernode-degree-of-justification N)) (terpri)
                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                (when (and *display?* *graphics-on*)
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "The degree-of-support of N ")
                    (speak-text (write-to-string (hypernode-number N)))
                    (speak-text "is")
                    (speak-text (write-to-string (hypernode-degree-of-justification N))))
                  (let ((posi (hypernode-position n *og*)))
                    (cond (posi (draw-just-undefeated-node posi *og* n))
                          (t
                            (draw-n n *og* *nodes-displayed*)
                            (push n *nodes-displayed*)
                            (setf posi (hypernode-position n *og*))
                            (draw-just-undefeated-node posi *og* n))))))))
       (dolist (N new-retractions)
         (cond ((or (not (some #'(lambda (L) (eq N (hyperlink-target L))) links))
                    (> (length (hypernode-hyperlinks N)) 1))
                (cond
                  ((zerop (hypernode-degree-of-justification N))
                   (when *log-on*
                     (push (list :defeated N) *reasoning-log*))
                   (when *display?*
                     (princ "               ") (princ N) (princ " has become defeated.") (terpri)
                     (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                   (when (and *display?* *graphics-on*)
                     (let ((posi (hypernode-position N *og*)))
                       (when posi
                         (when (and (boundp '*speak*) *speak*)
                           (speak-text "Node ")
                           (speak-text (write-to-string (hypernode-number N)))
                           (speak-text "has become defeated."))
                         (draw-just-defeated-node posi *og* N)))))
                  (t
                    (when *log-on*
                      (push (list :decreased-support N (hypernode-degree-of-justification N))
                            *reasoning-log*))
                    (when *display?*
                      (princ "               The degree-of-justification of ") (princ N)
                      (princ " has decreased to ") (princ (hypernode-degree-of-justification N)) (terpri)
                      (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)))))
               ((zerop (hypernode-degree-of-justification N))
                (when *log-on*
                  (push (list :defeated N) *reasoning-log*))
                (when *display?*
                  (princ "               ") (princ N) (princ " is defeated.") (terpri)
                  (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
                (when (and *display?* *graphics-on*)
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "Node ")
                    (speak-text (write-to-string (hypernode-number N)))
                    (speak-text "is defeated."))
                  (let ((posi (hypernode-position n *og*)))
                    (cond (posi (draw-just-defeated-node posi *og* n))
                          (t
                            (draw-n n *og* *nodes-displayed*)
                            (push n *nodes-displayed*)
                            (setf posi (hypernode-position n *og*))
                            (draw-just-defeated-node posi *og* n)))))))
         ))
      ((and *display?* *graphics-on*)
       (when *graphics-pause* (pause-graphics))
       (dolist (link links) (draw-n (hyperlink-target link) *og* *nodes-displayed*)))))
  (when (and *display?* *graphics-on*)
    (setf *nodes-displayed* (union (mapcar #'hyperlink-target links) *nodes-displayed*))))
|#

(defun critical-set (links paths)
  (every #'(lambda (p) (some #'(lambda (L) (member L p)) links)) paths)
  (not (some
         #'(lambda (link)
             (let ((links0 (remove link links)))
               (every #'(lambda (p) (some #'(lambda (L) (member L p)) links0)) paths)))
         links)))

; (critical-set (list (hyper-defeat-link 4)) (hyperlink-defeat-loops (hyperlink 8)))

; (critical-set (list (hyper-defeat-link 1) (hyper-defeat-link 2) (hyper-defeat-link 3)) (hyperlink-defeat-loops (hyperlink 8)))

;................................................. COMPUTING BELIEFS ........................................

(defun apply-optative-dispositions-to (conclusion)
  (dolist (O *doxastic-optative-dispositions*)
    (funcall O conclusion)))

#| A Q&I-module is a function which, when applied to an appropriate conclusion, returns
the sequent concluded. |#
(defun apply-Q&I-modules-to (conclusion)
  (when (not (hypernode-deductive-only conclusion))
    (dolist (Q&I *Q&I-modules*)
      (let ((S (funcall Q&I conclusion)))
        (when S (draw-conclusion S nil :Q&I nil 1 0 nil nil))))))

#| This computes defeat-statuses for interest-links and interests, and returns the list
of all interests whose defeat-statuses change as a result of the computation.  |#
(defun compute-interest-graph-defeat-statuses (new-beliefs new-retractions)
  (let ((altered-interests nil)
        (altered-links nil))
    (dolist (c new-beliefs)
      (dolist (L (c-list-link-defeatees (hypernode-c-list c)))
        (when (not (member L altered-links))
          (push L altered-links)
          (let ((defeated?
                  (and
                    (link-defeaters L)
                    (or (some
                          #'(lambda (D)
                              (and (>= (current-degree-of-justification D)
                                       (interest-degree-of-interest (link-resultant-interest L)))
                                   (subsetp= (hypernode-supposition D)
                                             (interest-supposition (link-resultant-interest L)))))
                          (c-list-nodes (mem1 (link-defeaters L))))
                        (some
                          #'(lambda (D)
                              (and (>= (current-degree-of-justification D)
                                       (interest-degree-of-interest (link-resultant-interest L)))
                                   (subsetp= (hypernode-supposition D)
                                             (interest-supposition (link-resultant-interest L)))))
                          (c-list-nodes (mem2 (link-defeaters L))))))))
            (when (not (eq defeated? (link-defeat-status L)))
              (setf (link-defeat-status L) defeated?)
              (pushnew (link-interest L) altered-interests))))))
    (dolist (c new-retractions)
      (dolist (L (c-list-link-defeatees (hypernode-c-list c)))
        (when (and (not (member L altered-links))
                   (subsetp= (hypernode-supposition c)
                             (interest-supposition (link-resultant-interest L))))
          (push L altered-links)
          (let ((defeated?
                  (and
                    (link-defeaters L)
                    (or (some
                          #'(lambda (D)
                              (>= (current-degree-of-justification D)
                                  (interest-degree-of-interest (link-resultant-interest L))))
                          (c-list-nodes (mem1 (link-defeaters L))))
                        (some
                          #'(lambda (D)
                              (>= (current-degree-of-justification D)
                                  (interest-degree-of-interest (link-resultant-interest L))))
                          (c-list-nodes (mem1 (link-defeaters L))))))))
            (when (not (eq defeated? (link-defeat-status L)))
              (setf (link-defeat-status L) defeated?)
              (pushnew (link-interest L) altered-interests))))))
    altered-interests))

(defun discharge-ultimate-epistemic-interests (new-beliefs new-retractions)
  ;(when (eql *cycle* 19) (setf nb new-beliefs nr new-retractions) (break))
  ; (setf nb new-beliefs nr new-retractions)
  ;; (step (discharge-ultimate-epistemic-interests nb nr))
  (let ((altered-queries nil))
    (dolist (C new-beliefs)
      (when (hypernode-answered-queries C)
        (let ((degree (current-degree-of-justification C)))
          (dolist (Q (hypernode-answered-queries C))
            (when (and (not (zerop (hypernode-degree-of-justification C)))
                       (>= degree (query-strength Q))
                       (or (null (hypernode-old-degree-of-justification C))
                           (zerop (hypernode-old-degree-of-justification C))
                           (< (hypernode-old-degree-of-justification C) (query-strength Q))))
              (when *log-on* (push (list :answer-query C Q degree) *reasoning-log*))
              (when *display?*
                (princ "               ")
                (princ "=========================================") (terpri)
                (princ "               ") (princ "Justified belief in ")
                (prinp (hypernode-formula C)) (terpri)
                (princ "               with degree-of-justification ")
                (princ (current-degree-of-justification C)) (terpri)
                (princ "               ") (princ "answers ") (princ Q)
                (terpri) (princ "               ")
                (princ "=========================================") (terpri))
              (dolist (instruction (query-positive-instructions Q))
                (funcall instruction C))
              (setf (query-answered? Q) t)
              (when (not (member Q *permanent-ultimate-epistemic-interests*))
                (push Q altered-queries)))))))
    (dolist (C new-retractions)
      (dolist (Q (hypernode-answered-queries C))
        (when (and (hypernode-old-degree-of-justification C)
                   (>= (hypernode-old-degree-of-justification C) (query-strength Q))
                   (or (zerop (hypernode-degree-of-justification C))
                       (not (>= (hypernode-degree-of-justification C) (query-strength Q)))))
          (when *log-on* (push (list :retract-answer C Q) *reasoning-log*))
          (when *display?*
            (princ "               ")
            (princ "=========================================") (terpri)
            (princ "               ") (princ "Lowering the degree-of-justification of ")
            (prinp (hypernode-formula C)) (terpri)
            (princ "               ") (princ "retracts the previous answer to ")
            (princ Q) (terpri) (princ "               ")
            (princ "=========================================") (terpri))
          (dolist (instruction (query-negative-instructions Q))
            (funcall instruction C))
          (when
            (every
              #'(lambda (A) (not (>= (current-degree-of-justification A) (query-strength Q))))
              (query-answers Q))
            (setf (query-answered? Q) nil)
            (when (not (member Q *permanent-ultimate-epistemic-interests*))
              (push Q altered-queries))))))
    altered-queries))

(defun affected-items (new-beliefs new-retractions altered-interests altered-queries)
  (let ((affected-nodes (append new-beliefs new-retractions))
        (affected-interests altered-interests))
    (dolist (query altered-queries)
      (pushnew (query-interest query) affected-interests))
    (loop
      (let ((changed? nil))
        (dolist (node affected-nodes)
          (dolist (n (hypernode-consequences node))
            (when (not (member n affected-nodes))
              (push n affected-nodes)
              (setf changed? t)))
          (dolist (in (hypernode-generated-interests node))
            (when (not (member in affected-interests))
              (push in affected-interests)
              (setf changed? t)))
          (when (eq (hypernode-justification node) :reductio-supposition)
            (dolist (in *direct-reductio-interests*)
              (when (not (member in affected-interests))
                (push in affected-interests)
                (setf changed? t)))))
        (dolist (interest affected-interests)
          (dolist (L (interest-left-links interest))
            (let ((in (link-interest L)))
              (when (not (member in affected-interests))
                (push in affected-interests)
                (setf changed? t))))
          (dolist (n (interest-generated-suppositions interest))
            (when (not (member n affected-nodes))
              (push n affected-nodes)
              (setf changed? t))))
        (when (null changed?)
          (return (list affected-nodes affected-interests)))))))

(defun broadly-generating-nodes (interest)
  (if (interest-direct-reductio interest)
    (union= *reductio-supposition-nodes* (interest-generating-nodes interest))
    (interest-generating-nodes interest)))

(defun generating-reductio-interests (N)
  (subset #'(lambda (in) (equal (hypernode-formula N) (neg (interest-formula in))))
          (hypernode-generating-interests N)))

(defun generating-non-reductio-interests (N)
  (subset #'(lambda (in) (not (equal (hypernode-formula N) (neg (interest-formula in)))))
          (hypernode-generating-interests N)))

(defun recompute-priorities (new-beliefs new-retractions altered-interests altered-queries)
  (let* ((affected-items
           (affected-items new-beliefs new-retractions altered-interests altered-queries))
         (affected-nodes (mem1 affected-items))
         (affected-interests (mem2 affected-items))
         (altered-queue nil))
    (dolist (query altered-queries)
      (let ((interest (query-interest query)))
        (pull interest affected-interests)
        (cond ((and (query-answered? query)
                    (not (member query *permanent-ultimate-epistemic-interests*)))
               (setf (interest-priority interest) (* (interest-degree-of-interest interest) *answered-discount*)))
              (t (setf (interest-priority interest) (interest-degree-of-interest interest))))))
    (dolist (node affected-nodes)
      (cond ((zerop (hypernode-degree-of-justification node))
             ;; If a node is defeated, its discounted-node-strength is *base-priority*.
             (pull node affected-nodes)
             (setf (hypernode-discounted-node-strength node) *base-priority*)
             (let ((Q (hypernode-queue-node node)))
               (when Q (pushnew Q altered-queue))))
            ((null (hypernode-generating-interests node))
             ;; If an undefeated node has an empty list of generating-interests, its
             ;; discounted-node-strength is the maximum  (over its hypernode-arguments)
             ;; of the product of the discount-factor of the hyperlink-rule of the last
             ;; hyperlink in the argument and the strength of the argument.
             ;; (This case includes all non-suppositional nodes.)
             (pull node affected-nodes)
             (let ((Q (hypernode-queue-node node)))
               (when Q (pushnew Q altered-queue))))))
    ;---------------------------------
    (loop
      (when (and (null affected-nodes) (null affected-interests)) (return))
      (let ((changes? nil))
        ; ===============
        ;; For each altered-node or altered-interest whose discounted-node-strength
        ;; or interest-priority can be computed without appealing to any other altered-nodes
        ;; or altered-interests, we do so and remove them from the lists of altered-nodes
        ;; and altered-interests.  Repeat this step until no further nodes or interests can be
        ;; removed.  If there are no generation-cycles, this will get them all, but if there are
        ;; cycles, some may remain.
        (loop
          (setf changes? nil)
          (dolist (node affected-nodes)
            (let ((reductio-interests (generating-reductio-interests node))
                  (non-reductio-interests (generating-non-reductio-interests node)))
              (when (and (not (some #'(lambda (in) (member in affected-interests))
                                    reductio-interests))
                         (not (some #'(lambda (in) (member in affected-interests))
                                    non-reductio-interests)))
                (setf changes? t)
                (pull node affected-nodes)
                ;; If a node is a supposition, its discounted-node-strength is the maximum of:
                ;;  (1)  the product of *reductio-discount* and the maximum of the
                ;;  interest-priorities of the generating-interests for which it is a
                ;;  reductio-supposition; and
                ;;  (2)  the interest-priorities of the generating-interests for which it is
                ;;  not a reductio-supposition.
                (setf (hypernode-discounted-node-strength node)
                      (max
                        (* *reductio-discount*
                           (maximum0 (mapcar #'interest-priority reductio-interests)))
                        (maximum0 (mapcar #'interest-priority non-reductio-interests))))
                (let ((Q (hypernode-queue-node node)))
                  (when Q (pushnew Q altered-queue))))))
          (dolist (interest affected-interests)
            (let ((GN (broadly-generating-nodes interest))
                  (links (subset #'(lambda (L) (null (link-defeat-status L))) (interest-right-links interest))))
              (cond ((and (null GN) (null links))
                     ;; If an interest has neither generating-nodes nor undefeated right-links,
                     ;;  its interest-priority is a0.  (This includes interest in defeaters.)
                     (setf changes? t)
                     (pull interest affected-interests)
                     (setf (interest-priority interest) *base-priority*)
                     (let ((Q (interest-queue-node interest)))
                       (when Q (pushnew Q altered-queue))))
                    ((and (not (some #'(lambda (n) (member n affected-nodes)) GN))
                          (not (some #'(lambda (in) (member in affected-interests)) links)))
                     ;; Otherwise, the interest-priority is the maximum of:
                     ;;  (1)  the discounted-node-strengths of its generating-nodes that are
                     ;;  not reductio-suppositions;
                     ;;  (2)  the product of *reductio-interest* and the maximum of the
                     ;;  discounted-node-strengths of its generating-nodes that are
                     ;;  reductio-suppositions;
                     ;;  (3)  for each of its right-links, the product
                     ;;  of the discount-factor of the link-rule and the interest-priority of the
                     ;;  resultant-interest.
                     (setf changes? t)
                     (pull interest affected-interests)
                     (setf (interest-priority interest)
                           (maximum
                             (append
                               (mapcar
                                 #'(lambda (n)
                                     (if (eq (hypernode-justification n) :reductio-supposition)
                                       (* *reductio-interest* (compute-discounted-node-strength n))
                                       (compute-discounted-node-strength n)))
                                 GN)
                               (mapcar
                                 #'(lambda (L)
                                     (if (eq (link-rule L) :answer)
                                       (query-strength (link-resultant-interest L))
                                       (* (reason-discount-factor (link-rule L))
                                          (interest-priority (link-resultant-interest L)))))
                                 links))))
                     (let ((Q (interest-queue-node interest)))
                       (when Q (pushnew Q altered-queue)))))))
          (when (and (null affected-nodes) (null affected-interests)) (return))
          (when (null changes?) (return)))
        ; ===============
        (when (and (null affected-nodes) (null affected-interests)) (return))
        ;; For any remaining nodes or interests, we want to compute their discounted-
        ;; nodes-strengths and interest-priorities just in terms of the nodes and interests
        ;; not involved in the cycles.  Cycles arise from direct-reductio-interests that also
        ;; have other sources and reductio-suppositions that are also non-reductio-
        ;; suppositions.  So for any such interests and suppositions, compute their
        ;; interest-priorities and discounted-node-strengths just in terms of those of their
        ;; sources that are no longer contained in the lists of altered-nodes or altered-interests.
        (dolist (node affected-nodes)
          (let ((reductio-interests (generating-reductio-interests node))
                (non-reductio-interests (generating-non-reductio-interests node)))
            (when (not (some #'(lambda (in) (member in affected-interests))
                             non-reductio-interests))
              (setf changes? t)
              (pull node affected-nodes)
              ;; If a node is a supposition, its discounted-node-strength is the maximum of:
              ;;  (1)  the product of *reductio-discount* and the maximum of the
              ;;  interest-priorities of the generating-interests for which it is a
              ;;  reductio-supposition; and
              ;;  (2)  the interest-priorities of the generating-interests for which it is
              ;;  not a reductio-supposition.
              (setf (hypernode-discounted-node-strength node)
                    (max
                      (* *reductio-discount*
                         (maximum0
                           (mapcar #'interest-priority
                                   (subset #'(lambda (in) (not (member in affected-interests)))
                                           reductio-interests))))
                      (maximum0 (mapcar #'interest-priority non-reductio-interests))))
              (let ((Q (hypernode-queue-node node)))
                (when Q (pushnew Q altered-queue))))))
        (dolist (interest affected-interests)
          (let ((GN (broadly-generating-nodes interest))
                (links (subset #'(lambda (L) (null (link-defeat-status L))) (interest-right-links interest))))
            (when (and (interest-direct-reductio interest)
                       (not (some #'(lambda (n)
                                      (and (not (eq (hypernode-justification n) :reductio-supposition))
                                           (member n affected-nodes))) GN))
                       (not (some #'(lambda (in) (member in affected-interests)) links)))
              (setf changes? t)
              (pull interest affected-interests)
              ;; If an interest has either generating-nodes or undefeated right-links
              ;;  the interest-priority is the maximum of:
              ;;  (1)  the discounted-node-strengths of its generating-nodes that are
              ;;  not reductio-suppositions;
              ;;  (2)  the product of *reductio-interest* and the maximum of the
              ;;  discounted-node-strengths of its generating-nodes that are
              ;;  reductio-suppositions;
              ;;  (3)  for each of its right-links, the product
              ;;  of the discount-factor of the link-rule and the interest-priority of the
              ;;  resultant-interest.
              (setf (interest-priority interest)
                    (maximum
                      (cons
                        (* *reductio-interest*
                           (maximum0
                             (mapcar #'compute-discounted-node-strength
                                     (subset
                                       #'(lambda (n)
                                           (and (eq (hypernode-justification n) :reductio-supposition)
                                                (not (member n affected-nodes)))) GN))))
                        (append
                          (mapcar #'compute-discounted-node-strength
                                  (subset
                                    #'(lambda (n)
                                        (not (eq (hypernode-justification n) :reductio-supposition)))
                                    GN))
                          (mapcar
                            #'(lambda (L)
                                (if (eq (link-rule L) :answer)
                                  (query-strength (link-resultant-interest L))
                                  (* (reason-discount-factor (link-rule L))
                                     (interest-priority (link-resultant-interest L)))))
                            links)))))
              (let ((Q (interest-queue-node interest)))
                (when Q (pushnew Q altered-queue))))))))
    ;---------------------------------
    (dolist (Q altered-queue)
      (cond ((eq (queue-item-kind Q) :conclusion)
             (setf (queue-discounted-strength Q)
                   (compute-discounted-node-strength (queue-item Q)))
             (setf (queue-degree-of-preference Q)
                   (/ (queue-discounted-strength Q) (queue-item-complexity Q)))
             (setf *inference-queue*
                   (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))
            ((not (interest-cancelled (queue-item Q)))
             (setf (queue-discounted-strength Q) (interest-priority (queue-item Q)))
             (setf (queue-degree-of-preference Q)
                   (/ (queue-discounted-strength Q) (queue-item-complexity Q)))
             (setf *inference-queue*
                   (ordered-insert Q (remove Q *inference-queue*) #'i-preferred)))))))

(defun update-beliefs ()
  ; (when (equal *cycle* 2) (break))
  ; (step (update-beliefs))
  (cond
    (*deductive-only*
      (dolist (link *new-links*)
        (let ((node (hyperlink-target link)))
          (setf (hypernode-old-degree-of-justification node) (hypernode-degree-of-justification node))
          (setf (hypernode-degree-of-justification node) 1.0)
          (setf (hyperlink-degree-of-justification link) 1.0)
          (setf (hypernode-discounted-node-strength node) (hyperlink-discount-factor link))
          (when (null (hypernode-old-degree-of-justification node))
            (queue-for-inference node))
          ; (display-belief-changes (list link) (list node) nil)
          (discharge-ultimate-epistemic-interests (list node) nil))))
    (t
      (setf *new-beliefs* nil)
      (setf *new-retractions* nil)
      (compute-hypernode-degrees-of-justification)
      (display-belief-changes *new-links* *new-beliefs* *new-retractions*)
      (dolist (node *new-beliefs*)
        (apply-optative-dispositions-to node)
        (apply-Q&I-modules-to node))
      (let ((altered-queries
              (discharge-ultimate-epistemic-interests *new-beliefs* *new-retractions*))
            (altered-interests
              (compute-interest-graph-defeat-statuses *new-beliefs* *new-retractions*)))
        (recompute-priorities *new-beliefs* *new-retractions* altered-interests altered-queries))
      )))

(defun think ()
  ; (when (read-char-no-hang) (clear-input) (throw 'die nil))
  (when (and *display-inference-queue* *display?*) (display-inference-queue))
  (when (eq *cycle* *start-trace*)
    (trace-on)
    (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
      (menu-item-disable (oscar-menu-item "Trace on"))
      (menu-item-enable (oscar-menu-item "Trace off"))
      (menu-item-enable (oscar-menu-item "Trace from"))
      (menu-item-disable (oscar-menu-item "Display on"))
      (menu-item-enable (oscar-menu-item "Display off"))
      (menu-item-enable (oscar-menu-item "Display from"))))
  (when (eq *cycle* *start-display*)
    (display-on)
    (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
      (menu-item-disable (oscar-menu-item "Display on"))
      (menu-item-enable (oscar-menu-item "Display off"))
      (menu-item-enable (oscar-menu-item "Display from"))))
  (when *inference-queue*
    (let ((Q (mem1 *inference-queue*)))
      (setf *inference-queue* (cdr *inference-queue*))
      (when *display?*
        (princ "---------------------------------------------------------------------------") (terpri)
        (princ *cycle*) (princ ":    ")
        (princ "Retrieving ") (princ (queue-item Q))
        (princ " from the inference-queue.")
        (terpri) (terpri))
      (pause)
      (cond ((eq (queue-item-kind Q) :conclusion)
             (let ((node (queue-item Q)))
               (when (eq (hypernode-kind node) :inference)
                 (store-processed-node node)
                 (setf (hypernode-queue-node node) nil))
               (reason-forwards-from node 0)))
            (t
              (let ((priority
                      (retrieved-interest-priority
                        (queue-degree-of-preference Q) (queue-item-complexity Q))))
                (cond ((eq (queue-item-kind Q) :query)
                       (let ((query (queue-item Q)))
                         (setf (query-queue-node query) nil)
                         (reason-backwards-from-query query priority 0)))
                      ((eq (queue-item-kind Q) :interest)
                       (let ((interest (queue-item Q)))
                         (setf (interest-queue-node interest) nil)
                         (reason-backwards-from interest priority 0)
                         (form-epistemic-desires-for interest)))))))))
  (when *new-links*
    (update-beliefs)
    (setf *new-links* nil)))

(defun try-to-perform (act)
  (let ((executor (e-assoc (mem1 act) *act-executors*)))
    (when executor (apply executor (cdr act)))))

(defun initiate-actions ()
  (let ((act (find-if
               #'(lambda (x)
                   (every #'(lambda (y) (>= (cdr x) (cdr y))) *executable-operations*))
               *executable-operations*)))
    (pull act *executable-operations*)
    (try-to-perform act)
    (let ((query
            (make-query
              :query-number (incf *query-number*)
              :query-formula (list "was-not-performed-when-tried" (mem1 act))
              :query-strength (mem2 act)
              :query-positive-instructions (list #'(lambda (x) (push x *executable-operations*)))
              :query-negative-instructions (list #'(lambda (x) (pull x *executable-operations*))))))
      (adopt-ultimate-interest query))))

(defun update-environmental-input ()
  T)

#| This is based on Perception-causes_3.31, but loads the problems into the list *simulation-problems*,
which can then be run individually using the function (simulate-oscar n). |#

(proclaim '(special *cycle* *inputs* *substantive-interests* *empty-inference-queue* *msg* **percepts**
                    *start-time* **premises** *temporal-reason-decay* *simulation-problems*))

(setf *pretty-list* nil *string-symbols* nil)

;; *temporal-reason-decay* is the reason-strength and *temporal-decay* is the
;; corresponding probability.
(setf *temporal-reason-decay* (1- (* *temporal-decay* 2)))

(defvar **percepts** nil)

#| *inputs* is a list of conses (cycle . input) where input is a list of pairs (formula clarity). |#

(defun form-percept (P clarity &optional source)
  (let* ((percept (make-percept
                    :percept-content P
                    :percept-clarity clarity
                    :percept-date *cycle*)))
    (push percept *percepts*)
    (push percept **percepts**)
    (when *display?*
      (cond
        ((eq source :user-report)
         (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
         (terpri) (princ "It is reported by the user that ") (prinp P) (princ " at ")
         (princ (percept-date percept)) (terpri)
         (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
         (terpri))
        (t
          (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
          (terpri) (princ "It appears to me that ") (prinp P) (princ " at ")
          (princ (percept-date percept)) (terpri)
          (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
          (terpri))))))

;this is defined in perception-cause.lisp
;(defun update-percepts ()
;  T)

;;;; removed b/c redefined below
;;;;(defun update-percepts ()
;;;;    (dolist (input (e-assoc *cycle* *inputs*)) (apply #'form-percept input)))

(defun update-percepts ()
  (dolist (input *inputs*)
    (when (eq (car input) *cycle*) (apply #'form-percept (cdr input)))))

#| The following does not perform the operations in parallel as it should, because
this program is designed to run in serial LISP.  The functions update-environmental-
input and update-percepts are extrinsic to the reasoner,
and are supplied by the operating environment of the reasoner.
Optative dispositions are functions from inputs to desires.  This code allows
us to have premises supplied artificially rather than by perception.
Premises are triples (formula, supposition, degree-of-justification).
Premises can be defeated by rebutting defeaters, but there is no way
to have an undercutting defeater.  |#
(defun OSCAR ()
  (initialize-reasoner)
  (dolist (query *ultimate-epistemic-interests*)
    (reason-backwards-from-query query (query-strength query) 0))
  (loop
    (update-environmental-input)
    (update-percepts)
    (dolist (input *environmental-input*)
      (dolist (disposition *optative-dispositions*)
        (pull input *environmental-input*)
        (queue-desire (funcall disposition input))))
    (dolist (percept *percepts*)
      (pull percept *percepts*)
      (queue-percept percept))
    (dolist (premise *premises*)
      (when (eql (mem3 premise) *cycle*)
        (pull premise *premises*)
        (queue-premise (list (mem1 premise) nil (mem2 premise)))))
    (think)
    (initiate-actions)))

(defun add-relevant-nodes (node)
  (when (not (member node *relevant-nodes*))
    (push node *relevant-nodes*)
    (dolist (m (hypernode-motivating-nodes node)) (add-relevant-nodes m))
    (dolist (L (hypernode-hyperlinks node))
      (dolist (b (hyperlink-basis L)) (add-relevant-nodes b))
      (dolist (d (hyperlink-defeaters L)) (add-relevant-nodes (hyper-defeat-link-root d))))))

(defun compute-relevant-nodes (nodes)
  (setf *relevant-nodes* nil)
  (dolist (node nodes) (add-relevant-nodes node))
  *relevant-nodes*)

(defun display-peripherals (x boundary nodes-used)
  (cond
    ((equal x "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (setf boundary t))
    ((listp x)
     (cond ((and (equal (mem1 x) :increased-support) (member (mem2 x) nodes-used))
            (when (equal boundary t)
              (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
              (setf boundary nil))
            (princ "               The degree-of-justification of ") (princ (mem2 x))
            (princ " has increased to ") (princ (mem3 x))
            (terpri) (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
            (when *graph-log*
              (let ((posi (hypernode-position (mem2 x) *og*)))
                (when posi
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "The undefeeted-degree-of-justification of node ")
                    (speak-text (write-to-string (hypernode-number (mem2 x))))
                    (speak-text "has increased to")
                    (speak-text (write-to-string (mem3 x))))
                  (draw-just-undefeated-node posi *og* (mem2 x))))))
           ((and (equal (mem1 x) :new-support) (member (mem2 x) nodes-used)
                 (not (eql (mem3 x) 1.0)))
            (when (equal boundary t)
              (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
              (setf boundary nil))
            (princ "               The degree-of-justification of ") (princ (mem2 x))
            (princ " is ") (princ (mem3 x))
            (terpri) (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
            (when *graph-log*
              (let ((posi (hypernode-position (mem2 x) *og*)))
                (when posi
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "The degree-of-justification of node ")
                    (speak-text (write-to-string (hypernode-number (mem2 x))))
                    (speak-text "is")
                    (speak-text (write-to-string (mem3 x))))
                  (draw-just-undefeated-node posi *og* (mem2 x))))))
           ((and (equal (mem1 x) :defeated) (member (mem2 x) nodes-used))
            (when (equal boundary t)
              (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
              (setf boundary nil))
            (princ "               ") (princ (mem2 x)) (princ " has become defeated.") (terpri)
            (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
            (when *graph-log*
              (let ((posi (hypernode-position (mem2 x) *og*)))
                (when posi
                  (when (and (boundp '*speak*) *speak*)
                    (speak-text "Hypernode ")
                    (speak-text (write-to-string (hypernode-number (mem2 x))))
                    (speak-text "has become defeated."))
                  (draw-just-defeated-node posi *og* (mem2 x))))))
           ((and (equal (mem1 x) :decreased-support) (member (mem2 x) nodes-used))
            (when (equal boundary t)
              (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri)
              (setf boundary nil))
            (princ "               The degree-of-justification of ") (princ (mem2 x))
            (princ " has decreased to ") (princ (mem3 x))
            (terpri) (princ "               vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv") (terpri))
           ((and (equal (mem1 x) :answer-query) (member (mem2 x) nodes-used))
            (princ "               ")
            (princ "=========================================") (terpri)
            (princ "               ") (princ "Justified belief in ")
            (prinp (hypernode-formula (mem2 x))) (terpri)
            (princ "               with degree-of-justification ") (princ (mem4 x)) (terpri)
            (princ "               ") (princ "answers ") (princ (mem3 x))
            (terpri) (princ "               ")
            (princ "=========================================") (terpri)
            (when (and (boundp '*speak*) *speak*)
              (speak-text "Hypernode ")
              (speak-text (write-to-string (hypernode-number (mem2 x))))
              (speak-text "answers query ")
              (speak-text (write-to-string (query-number (mem3 x))))))
           ((and (equal (mem1 x) :retract-answer) (member (mem2 x) nodes-used))
            (princ "               ")
            (princ "=========================================") (terpri)
            (princ "               ") (princ "Lowering the degree-of-justification of ")
            (prinp (hypernode-formula (mem2 x))) (terpri)
            (princ "               ") (princ "retracts the previous answer to ")
            (princ (mem3 x)) (terpri) (princ "               ")
            (princ "=========================================") (terpri)
            (when (and (boundp '*speak*) *speak*)
              (speak-text "Hypernode ")
              (speak-text (write-to-string (hypernode-number (mem2 x))))
              (speak-text "no longer answers query ")
              (speak-text (write-to-string (query-number (mem3 x)))))))))
  boundary)

(defun strongly-discharging-node (dn interest proof-nodes enabling-interests)
  (or
    (some
      #'(lambda (dr)
          (some
            #'(lambda (pn)
                (some
                  #'(lambda (SL)
                      (and (equal (hyperlink-rule SL) :reductio)
                           (member dn (hyperlink-basis SL))
                           (member (car dr) (hyperlink-basis SL))))
                  (hypernode-hyperlinks pn)))
            proof-nodes))
      (interest-direct-reductio interest))
    (some #'(lambda (L)
              (and
                (link-discharged L)
                (member (link-resultant-interest L) enabling-interests)
                (some
                  #'(lambda (pn)
                      (and
                        (member (link-resultant-interest L) (hypernode-enabling-interests pn))
                        (some
                          #'(lambda (SL)
                              (member dn (hyperlink-basis SL)))
                          (hypernode-hyperlinks pn))))
                  proof-nodes)))
          (interest-right-links interest))))

(defun display-node
    (n proof-nodes nodes-used interests-used interests-discharged nodes-displayed)
  (when (eq (hypernode-kind n) :percept)
    (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
    (terpri) (princ "It appears to me that ") (prinp (hypernode-formula n)) (terpri)
    (princ "|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
    (terpri))
  (princ "  # ") (princ (hypernode-number n))
  (when (member n *not-strictly-relevant-nodes*) (princ "   NOT STRICTLY RELEVANT"))
  (terpri)
  (princ "  ") (when (eq (hypernode-kind n) :percept) (princ "It appears to me that "))
  (prinp (hypernode-formula n))
  (when (hypernode-supposition n)
    (princ "    supposition: ") (set-prinp (hypernode-supposition n)))
  (if (zerop (hypernode-degree-of-justification n)) (princ "                  DEFEATED"))
  (when (and (member n nodes-used)
	     (not (member n proof-nodes)))
    (princ "   --  NOT USED IN PROOF"))
  (terpri)
  (cond ((keywordp (hypernode-justification n)) (princ "  ") (princ (hypernode-justification n)) (terpri))
	((hypernode-hyperlinks n)
	 (princ "  Inferred by:") (terpri)
	 (dolist (L* (hypernode-hyperlinks n))
	   (when (subsetp (hyperlink-basis L*) nodes-displayed)
	     (princ "                hyperlink #") (princ (hyperlink-number L*))
	     (princ " from ") (princ-set (mapcar #'hypernode-number (hyperlink-basis L*)))
	     (princ " by ") (princ (hyperlink-rule L*))
	     (when (hyperlink-clues L*)
	       (princ " with clues ")
	       (princ-set (mapcar #'hypernode-number (hyperlink-clues L*))))
	     (when (hyperlink-defeaters L*)
	       (princ "  defeaters: ")
	       (princ-set (mapcar #'hypernode-number
				  (mapcar #'hyper-defeat-link-root (hyperlink-defeaters L*)))))
	     (when (= (hyperlink-degree-of-justification L*) 0.0) (princ "   DEFEATED"))
	     (terpri)))))
  (when (hypernode-supported-hyper-defeat-links n)
    (princ "  defeatees: ")
    (princ "{ ")
    (let ((L (car (hypernode-supported-hyper-defeat-links n))))
      (if (hyperlink-p L)
	  (progn
	    (princ "link ")
	    (princ (hyperlink-number L)) (princ " for node ")
	    (princ (hypernode-number (hyperlink-target L))))
	(princ "NOT-A-LINK"))) ; TODO why not?
    (dolist (L (cdr (hypernode-supported-hyper-defeat-links n)))
      (setf L (hyper-defeat-link-target L))
      (princ " , ")
      (if (hyperlink-p L)
	  (progn
	    (princ "link ")
	    (princ (hyperlink-number L)) (princ " for node ")
	    (princ (hypernode-number (hyperlink-target L))))
	(princ "NOT-A-LINK"))) ; TODO why not?
    (princ " }") (terpri))
					; (princ " by ") (princ (hypernode-justification n))
  (let ((generating-interests (intersection (hypernode-generating-interests n) interests-used)))
    (cond ((> (length generating-interests) 1)
	   (princ " generated by interests ")
	   (print-list (mapcar #'interest-number generating-interests) 40))
	  ((eq (length generating-interests) 1)
	   (princ "  generated by interest ")
	   (princ (interest-number (mem1 generating-interests)))))
    (when generating-interests (terpri)))
  (let ((DI (hypernode-enabling-interests n)))
    (cond
     ((> (length DI) 1)
      (princ "  This node is inferred by discharging links to interests ")
      (princ (mapcar #'interest-number DI)) (terpri))
     (DI
      (princ "  This node is inferred by discharging a link to interest #")
      (princ (interest-number (car DI)))
      (let ((SL (find-if #'(lambda (SL) (equal (hyperlink-rule SL) :reductio)) (hypernode-hyperlinks n))))
	(when SL
	  (let* ((node* (mem1 (hyperlink-basis SL)))
		 (rs (find-if
		      #'(lambda (sup)
			  (and
			   (member (car DI) (hypernode-generating-interests sup))
			   ;;
			   (mem sup (a-range (hypernode-reductio-ancestors node*)))
			   (not (mem sup (a-range (hypernode-reductio-ancestors n))))))
		      (a-range (hypernode-reductio-ancestors node*)))))
	    ;; (interest-generated-suppositions (car DI)))))
	    (when rs
	      (princ " as a result of inferring node #") (princ (hypernode-number node*))
	      (princ " from") (terpri) (princ "  reductio-supposition #")
	      (princ (hypernode-number rs)) (princ ", which was generated by interest #")
	      (princ (interest-number (car DI)))))))
      (terpri)))
    (let ((interests
	   (subset
	    #'(lambda (in)
		(and
		 (member n (interest-discharging-nodes in))
		 (or
		  (some
		   #'(lambda (dr)
		       (some
			#'(lambda (pn)
			    (some
			     #'(lambda (SL)
				 (and (equal (hyperlink-rule SL) :reductio)
				      (member n (hyperlink-basis SL))
				      (member (car dr) (hyperlink-basis SL))))
			     (hypernode-hyperlinks pn)))
			proof-nodes))
		   (interest-direct-reductio in))
		  (some #'(lambda (L)
			    (and
			     (link-discharged L)
			     (or
			      (equal (link-rule L) :answer)
			      (some
			       #'(lambda (pn)
				   (and
				    (member (link-resultant-interest L) (hypernode-enabling-interests pn))
				    (some
				     #'(lambda (SL)
					 (member n (hyperlink-basis SL)))
				     (hypernode-hyperlinks pn))))
			       proof-nodes))))
			(interest-right-links in)))))
	    (set-difference interests-used DI))))
      (cond ((> (length interests) 1)
	     (princ "  This discharges interests ") (print-list (mapcar #'interest-number interests) 40))
	    ((eq (length interests) 1)
	     (princ "  This discharges interest ") (princ (interest-number (mem1 interests))))
	    (t
	     (setf interests
		   (subset
		    #'(lambda (in)
			(and
			 (member n (interest-discharging-nodes in))
			 (not
			  (some
			   #'(lambda (dn)
			       (strongly-discharging-node dn in proof-nodes interests-discharged))
			   (interest-discharging-nodes in)))))
		    (set-difference interests-used DI)))
	     (cond
	      ((> (length interests) 1)
	       (princ "  This discharges interests ") (print-list (mapcar #'interest-number interests) 40)
	       (princ " but no inference made by discharging these interests is used in the solution."))
	      ((eq (length interests) 1)
	       (princ "  This discharges interest ") (princ (interest-number (mem1 interests)))
	       (princ " but no inference made by discharging this interest is used in the solution.")))))
      (when interests (terpri))))
  (when *graphics-pause* (pause-graphics))  ;; wait for a character to be typed in the Listener
  (when (and *graph-log* (member n proof-nodes))
    (push n *nodes-displayed*)
    (draw-n n *og* nodes-displayed)))

(defun display-used-interest
  (interest proof-nodes used-nodes used-interests enabling-interests interests-used-in-proof)
  ; (when (eq interest (interest 6)) (setf i interest pn proof-nodes un used-nodes ui used-interests ein enabling-interests iun interests-used-in-proof) (break))
  ;; (step (display-used-interest i pn un ui ein iun))
  (princ "                                        # ") (princ (interest-number interest))
  (when (not (member interest interests-used-in-proof))
    (princ "               NOT USED IN PROOF"))
  (terpri)
  (princ "                                        ")
  (when (interest-deductive interest) (princ "deductive "))
  (when (interest-reductio interest) (princ "reductio "))
  (princ "interest: ") (prinp (interest-formula interest))
  (when (interest-supposition interest)
    (princ "    supposition: ")
    (set-prinp (interest-supposition interest)))
  (terpri)
  (when
    (some #'(lambda (L) (query-p (link-resultant-interest L)))
          (interest-right-links interest))
    (princ "                                        This is of ultimate interest") (terpri))
  (dolist (L (interest-right-links interest))
    (when (and (not (query-p (link-resultant-interest L))) (link-discharged L)
               (member (link-resultant-interest L) used-interests))
      (princ "                                        For ")
      (when (interest-reductio (link-resultant-interest L)) (princ "reductio "))
      (princ "interest ")
      (princ (interest-number (link-resultant-interest L)))
      (princ " by ") (princ (link-rule L))
      (let ((nodes (link-supporting-nodes L)))
        (when nodes
          (cond ((equal (length nodes) 1)
                 (princ " using node ")
                 (princ (hypernode-number (mem1 nodes))))
                (t
                  (princ " using nodes ")
                  (print-list (mapcar
                                #'(lambda (conclusion)
                                    (hypernode-number conclusion))
                                nodes) 40)))))
      (let ((nodes (link-clues L)))
        (when nodes
          (cond ((equal (length nodes) 1)
                 (princ " with clue ")
                 (princ (hypernode-number (mem1 nodes))))
                (t
                  (princ " with clues ")
                  (print-list (mapcar
                                #'(lambda (conclusion)
                                    (hypernode-number conclusion))
                                nodes) 40)))))
      (terpri)))
  (let ((direct-reductio-interest
          (subset #'(lambda (n) (assoc n (interest-direct-reductio interest)))
                  used-nodes)))
    (cond ((> (length direct-reductio-interest) 1)
           (princ "                                        Reductio interest generated by nodes ")
           (print-list (mapcar #'(lambda (n) (hypernode-number n))
                               direct-reductio-interest) 40) (terpri))
          ((= (length direct-reductio-interest) 1)
           (princ "                                        Reductio interest generated by node ")
           (princ (hypernode-number (mem1 direct-reductio-interest))) (terpri))))
  (let ((discharging-nodes
          (subset
            #'(lambda (dn)
                (strongly-discharging-node dn interest proof-nodes enabling-interests))
            (intersection (interest-discharging-nodes interest) used-nodes)))
        (defeatees
          (subset #'(lambda (L)
                      (member (hyperlink-target L) proof-nodes))
                  (interest-defeatees interest))))
    (when defeatees
      (princ "                                        Of interest as a defeater for ")
      (cond ((cdr defeatees)
             (princ "hyperlinks: ")
             (princ "{ ")
             (let ((L (car defeatees)))
               (princ "link ")
               (princ (hyperlink-number L)) (princ " for node ")
               (princ (hypernode-number (hyperlink-target L))))
             (dolist (L (cdr defeatees))
               (princ " , ")
               (princ "link ")
               (princ (hyperlink-number L)) (princ " for node ")
               (princ (hypernode-number (hyperlink-target L))))
             (princ " }"))
            (t
              (princ "hyperlink ")
              (let ((L (car defeatees)))
                (princ (hyperlink-number L)) (princ " for node ")
                (princ (hypernode-number (hyperlink-target L))))))
      (terpri))
    (cond
      (discharging-nodes
        (princ "                                        This interest is discharged by")
        (cond ((> (length discharging-nodes) 1) (princ " nodes ")
                                                (princ (mapcar #'hypernode-number discharging-nodes)))
              (t (princ " node ") (princ (hypernode-number (mem1 discharging-nodes)))))
        (terpri))
      ((not (some #'(lambda (L) (and (query-p (link-resultant-interest L)) (link-discharged L)))
                  (interest-right-links interest)))
       (setf discharging-nodes
             (intersection (interest-discharging-nodes interest) used-nodes))
       (cond
         (discharging-nodes
           (princ "                                        This interest is discharged by")
           (cond ((> (length discharging-nodes) 1) (princ " nodes ")
                                                   (princ (mapcar #'hypernode-number discharging-nodes)))
                 (t (princ " node ") (princ (hypernode-number (mem1 discharging-nodes)))))
           (terpri)
           (when
             (and (null defeatees) (member interest interests-used-in-proof))
             (princ "                                        but no inference made by discharging this interest is used in the solution.")
             (terpri)))
         ((and (null defeatees) (member interest interests-used-in-proof))
          (princ "                                        No inference made by discharging this interest is used in the solution.") (terpri)))
       )))
  (when (and *graph-interests* *graph-log*)
    (when *graphics-pause* (pause-graphics))  ;; wait for a character to be typed in the Listener
    (draw-i interest *og*)))

#| This precedes the line of nodes by || . |#
(defun full-display-node (n proof-nodes)
  (princ "||  # ") (princ (hypernode-number n))
  (terpri)
  (princ "||  ") (prinp (hypernode-formula n))
  (when (hypernode-supposition n)
    (princ "    supposition: ") (set-prinp (hypernode-supposition n)))
  (when (not (member n proof-nodes)) (princ "   --  NOT USED IN PROOF"))
  (terpri)
  (when (hypernode-justification n) (princ "||  by ") (princ (hypernode-justification n)) (terpri))
  (when (hypernode-hyperlinks n)
    (princ "||  Inferred by:") (terpri)
    (dolist (L* (hypernode-hyperlinks n))
      (princ "||                hyperlink #") (princ (hyperlink-number L*))
      (princ " from ") (princ-set (mapcar #'hypernode-number (hyperlink-basis L*)))
      (princ " by ") (princ (hyperlink-rule L*))
      (when (hyperlink-defeaters L*)
        (princ "  defeaters: ")
        (princ-set (mapcar #'hypernode-number
                           (mapcar #'hyper-defeat-link-root (hyperlink-defeaters L*)))))
      (terpri)))
  ; (princ " by ") (princ (hypernode-justification n))
  (let ((generating-interests (hypernode-generating-interests n)))
    (cond ((> (length generating-interests) 1)
           (princ "||  generated by interests ")
           (print-list (mapcar #'interest-number generating-interests) 40))
          ((equal (length generating-interests) 1)
           (princ "||  generated by interest ")
           (princ (interest-number (mem1 generating-interests)))))
    (when generating-interests (terpri)))
  (let ((interests (remove-duplicates (hypernode-discharged-interests n))))
    (cond ((> (length interests) 1)
           (princ "||  This discharges interests ") (print-list (mapcar #'interest-number interests) 40))
          ((equal (length interests) 1)
           (princ "||  This discharges interest ") (princ (interest-number (mem1 interests)))))
    (when interests (terpri))))

#| This precedes the line of interests by || . |#
(defun full-display-used-interest (interest)
  (princ "                                        || # ") (princ (interest-number interest)) (terpri)
  (princ "                                        || ")
  (when (interest-deductive interest) (princ "deductive "))
  (when (interest-reductio interest) (princ "reductio "))
  (princ "interest: ") (prinp (interest-formula interest))
  (when (interest-supposition interest)
    (princ "    supposition: ")
    (set-prinp (interest-supposition interest)))
  (terpri)
  (when
    (some #'(lambda (L) (and (query-p (link-resultant-interest L)) (link-discharged L)))
          (interest-right-links interest))
    (princ "                                        || This is of ultimate interest") (terpri))
  (dolist (L (interest-right-links interest))
    (when (and (link-discharged L) (not (query-p (link-resultant-interest L))))
      (princ "                                        || For ")
      (when (interest-reductio (link-resultant-interest L)) (princ "reductio "))
      (princ "interest ")
      (princ (interest-number (link-resultant-interest L)))
      (princ " by ") (princ (link-rule L))
      (terpri)))
  (let ((direct-reductio-interest (interest-direct-reductio interest)))
    (cond ((> (length direct-reductio-interest) 1)
           (princ "                                        || Reductio interest generated by nodes ")
           (print-list (mapcar #'hypernode-number direct-reductio-interest) 40) (terpri))
          ((= (length direct-reductio-interest) 1)
           (princ "                                        || Reductio interest generated by node ")
           (princ (hypernode-number (mem1 direct-reductio-interest))) (terpri)))))

(defun link-interests (link)
  (cond
    ((null (link-generating link)) (list (link-interest link)))
    (t (cons (link-interest link) (link-interests (link-generating link))))))

(defun list-interest-schemes (&optional d-node)
  (when (null d-node) (setf d-node (d-node 1)))
  (append (d-node-interest-schemes d-node)
          (unionmapcar #'(lambda (d) (list-interest-schemes (cdr d)))
                       (d-node-discrimination-tests d-node))))

(defun process-unprocessed-node (node proof-nodes enabling-interests)
  ; (princ "process-unprocessed-node ") (princ node) (terpri)
  (pull node *unprocessed-nodes*)
  (dolist (L (hypernode-hyperlinks node))
    (dolist (b (hyperlink-basis L))
      (when (not (member b *used-nodes*))
        (push b *used-nodes*) (push b *unprocessed-nodes*)))
    (dolist (b (hyperlink-clues L))
      (when (not (member b *used-nodes*))
        (push b *used-nodes*) (push b *unprocessed-nodes*)))
    (let ((link (hyperlink-generating-interest-link L)))
      (when link
        (push (link-resultant-interest link) *used-interests*)
        (pull (link-resultant-interest link) *unprocessed-interests*)
        (dolist (interest (link-interests link))
          (when (member node proof-nodes) (push interest *interests-used-in-proof*))
          (when (not (member interest *used-interests*))
            (push interest *used-interests*)
            (push interest *unprocessed-interests*))))))
  (when (and (eq (hypernode-justification node) :reduction-supposition)
             (not (some #'(lambda (N)
                            (and (member N *used-interests*)
                                 (equal (interest-formula N) (neg (hypernode-formula node)))))
                        enabling-interests))
             (not (some #'(lambda (N)
                            (and (member N *used-interests*)
                                 (equal (interest-formula N) (neg (hypernode-formula node)))))
                        (hypernode-generating-interests node))))
    (let ((N (find-if #'(lambda (N) (equal (interest-formula N) (neg (hypernode-formula node))))
                      (hypernode-generating-interests node))))
      (push N *used-interests*) (push N *unprocessed-interests*)))
  (when (and (eq (hypernode-justification node) :supposition)
             (not (some #'(lambda (N) (member N *used-interests*)) enabling-interests))
             (not (some #'(lambda (N) (member N *used-interests*)) (hypernode-generating-interests node))))
    (push (car (hypernode-generating-interests node)) *used-interests*)
    (push (car (hypernode-generating-interests node)) *unprocessed-interests*)))

(defun process-unprocessed-interest (interest)
  ; (princ "process-unprocessed-interest ") (princ interest) (terpri)
  ; (when (eq interest (interest 8)) (break))
  (pull interest *unprocessed-interests*)
  (cond
    ((and (interest-direct-reductio interest)
          (not (some #'(lambda (N)  (member (car N) *used-nodes*)) (interest-direct-reductio interest))))
     (let ((N (caar (interest-direct-reductio interest))))
       (push N *used-nodes*) (push N *unprocessed-nodes*)))
    ((not (some #'(lambda (N) (member N *used-nodes*)) (interest-discharging-nodes interest)))
     (let ((link (find-if #'(lambda (L) (every #'(lambda (N) (member N *used-interests*)) (link-interests L)))
                          (interest-left-links interest))))
       (when (null link)
         (setf link (find-if #'(lambda (L) (every #'(lambda (N) (member N *used-interests*)) (link-interests L)))
                             (interest-cancelled-left-links interest))))
       (when (null link) (setf link (car (interest-left-links interest))))
       (when (null link) (setf link (car (interest-cancelled-left-links interest))))
       (when link
         (dolist (N (link-interests link))
           (when (not (member N *used-interests*))
             (push N *used-interests*) (push N *unprocessed-interests*))))))))

(defun generated-nodes-and-interests (proof-nodes enabling-interests ultimate-interests)
  ; (p-princ enabling-interests)
  (setf *interests-used-in-proof* enabling-interests)
  (setf *used-nodes* proof-nodes)
  (setf *unprocessed-nodes* proof-nodes)
  (setf *used-interests* ultimate-interests)
  (setf *unprocessed-interests* nil)
  (loop
    (cond ((and (null *unprocessed-nodes*) (null *unprocessed-interests*))
           (return (list *used-nodes* *used-interests* *interests-used-in-proof*)))
          (*unprocessed-nodes*
            (process-unprocessed-node (car *unprocessed-nodes*) proof-nodes enabling-interests))
          (t (process-unprocessed-interest (car *unprocessed-interests*))))))

(defun display-reasoning-fully ()
  (progn
    (princ "===========================================================================")
    (terpri) (princ "THE FOLLOWING IS THE REASONING INVOLVED IN THE SOLUTION") (terpri)
    (princ "Hypernodes marked DEFEATED have that status at the end of the reasoning.")
    (terpri)(terpri))
  (let ((nodes nil))
    (dolist (query *ultimate-epistemic-interests*)
      (dolist (N (query-answers query)) (pushnew N nodes)))
    (let* ((ultimate-interests (mapcar #'query-interest *ultimate-epistemic-interests*))
           (enabling-interests (unionmapcar+ #'hypernode-enabling-interests
                                             *relevant-nodes*))
           (closure (generated-nodes-and-interests
                      *relevant-nodes* (union ultimate-interests enabling-interests) ultimate-interests))
           (nodes-used (mem1 closure))
           (interests-used (mem2 closure))
           (interests-used-in-proof (mem3 closure))
           (previous-item nil)
           (log (reverse *reasoning-log*))
           (boundary nil)
           (nodes-displayed nil))
      (when *graph-log* (make-oscar-window))
      (dolist (x log)
        (cond
          ((hypernode-p x)
           (when (and previous-item (member previous-item interests-used))
             (princ "                                        ")
             (princ "==========================================================")
             (terpri) (terpri))
           (cond ((member x nodes-used)
                  (when (or (null previous-item)
                            (not (member previous-item nodes-used)))
                    (terpri)
                    (princ "====================== NODES USED ==========================")
                    (terpri))
                  (full-display-node x *relevant-nodes*))
                 (t (when (and previous-item (member previous-item nodes-used))
                      (princ "============================================================")
                      (terpri) (terpri))
                    (display-node
                      x *relevant-nodes* nodes-used interests-used enabling-interests nodes-displayed)
                    (push x nodes-displayed))))
          ((interest-p x)
           (when (and previous-item (member previous-item nodes-used))
             (princ "============================================================")
             (terpri) (terpri))
           (cond ((member x interests-used)
                  (when (or (null previous-item)
                            (not (member previous-item interests-used)))
                    (terpri) (princ "                                        ")
                    (princ "=================== INTERESTS USED =======================")
                    (terpri))
                  (full-display-used-interest x))
                 (t (when (and previous-item (member previous-item interests-used))
                      (princ "                                        ")
                      (princ "==========================================================")
                      (terpri) (terpri))
                    (display-used-interest
                      x *relevant-nodes* nodes-used interests-used
                      enabling-interests interests-used-in-proof))))
          (t (setf boundary (display-peripherals x boundary nodes-used))))
        (setf previous-item x))
      (when *graph-log* (invalidate-view *og*))
      (princ "============================================================")
      (terpri) (terpri))))

(defun add-strictly-relevant-nodes (node)
  (when (not (member node *strictly-relevant-nodes*))
    (push node *strictly-relevant-nodes*)
    (dolist (m (hypernode-motivating-nodes node)) (add-strictly-relevant-nodes m))
    (dolist (L (hypernode-hyperlinks node))
      (dolist (b (hyperlink-basis L)) (add-strictly-relevant-nodes b)))))

(defun compute-strictly-relevant-nodes (nodes)
  (setf *strictly-relevant-nodes* nil)
  (dolist (node nodes) (add-strictly-relevant-nodes node))
  *strictly-relevant-nodes*)

(defun strictly-relevant-nodes ()
  (let ((nodes nil))
    (dolist (query *ultimate-epistemic-interests*)
      (dolist (N (query-answers query)) (pushnew N nodes)))
    (compute-strictly-relevant-nodes nodes)))

(defun not-strictly-relevant-nodes ()
  (order (set-difference *relevant-nodes* (strictly-relevant-nodes))
         #'(lambda (x y) (< (hypernode-number x) (hypernode-number y)))))

(defun display-reasoning (&optional full-display)
  (cond
    (full-display (display-reasoning-fully))
    (t
      (progn
        (princ "===========================================================================")
        (terpri) (princ "THE FOLLOWING IS THE REASONING INVOLVED IN THE SOLUTION") (terpri)
        (princ "Hypernodes marked DEFEATED have that status at the end of the reasoning.")
        (terpri)(terpri))
      (let ((nodes nil))
        (dolist (query *ultimate-epistemic-interests*)
          (dolist (N (query-answers query)) (pushnew N nodes)))
        (compute-relevant-nodes nodes)
        (setf *not-strictly-relevant-nodes* (not-strictly-relevant-nodes))
        (let* ((ultimate-interests (mapcar #'query-interest *ultimate-epistemic-interests*))
               (enabling-interests
                 (union (unionmapcar+ #'hypernode-enabling-interests *relevant-nodes*)
                        (unionmapcar+ #'hypernode-generating-defeat-interests *relevant-nodes*)))
               (closure (generated-nodes-and-interests
                          *relevant-nodes* (union ultimate-interests enabling-interests) ultimate-interests))
               (nodes-used (remove-duplicates (mem1 closure)))
               (interests-used (remove-duplicates (mem2 closure)))
               (interests-used-in-proof (remove-duplicates (mem3 closure)))
               (log (reverse *reasoning-log*))
               (boundary nil)
               (nodes-displayed nil))
          (when *graph-log* (make-oscar-window))
          (dolist (x log)
            (cond ((hypernode-p x)
                   (when (member x nodes-used)
                     (display-node
                       x *relevant-nodes* nodes-used interests-used enabling-interests nodes-displayed)
                     (push x nodes-displayed)))
                  ((interest-p x)
                   (when (member x interests-used)
                     (display-used-interest
                       x *relevant-nodes* nodes-used interests-used
                       enabling-interests interests-used-in-proof)))
                  (t (setf boundary (display-peripherals x boundary nodes-used)))))
          (when (and *graph-log* (boundp '*speak*) *speak*)
            (setf nodes
                  (subset
                    #'(lambda (n)
                        (some #'(lambda (q) (>= (current-degree-of-justification n) (query-strength q)))
                              (hypernode-answered-queries n)))
                    nodes))
            (when nodes
              (speak-text
                (cond
                  ((cdr nodes)
                   (cat-list
                     (list "In conclusion, " (pranc-to-string (pretty (hypernode-formula (car nodes))))
                           (mapcar #'(lambda (n) (cat ", " (pranc-to-string (pretty (hypernode-formula n)))))
                                   (cdr nodes)))))
                  (t (cat "In conclusion, " (pranc-to-string (pretty (hypernode-formula (car nodes))))))))))
          (when *graph-log* (invalidate-view *og*))
          (princ "============================================================")
          (terpri) (terpri))))))
(proclaim '(special *arguments* *nodes-done* *arg-number* *nodes-used*))

(defstruct (argument
	    (:print-function
	     (lambda (x stream depth)
	       (declare (ignore depth))
	       (princ "#<" stream) (princ "argument " stream)
	       (princ (argument-number x) stream)
	       (princ " for node " stream) (princ (argument-node x) stream)
	       (princ ">" stream)))
	    (:conc-name nil))
  (argument-number 0)
  (argument-links nil)
  (argument-node nil)
  (argument-defeaters nil)
  (argument-defeatees nil)
  (argument-strength 0)
  (argument-ultimate-interest nil)
  (argument-inclusive-nodes nil))

(defun deductive-argument (arg)
  (every #'(lambda (L) (not (hyperlink-defeasible? L))) (argument-links arg)))

(defun hypernode-basis-in-arg (node arg)
  (let ((link (find-if #'(lambda (L) (eq (hyperlink-target L) node)) (argument-links arg))))
    ; (union (hypernode-motivating-nodes node)
    (if link (hyperlink-basis link)))) ;)

(defun clear-indent (n &optional fw)
  (dotimes (x n) (princ "        " fw))
  (if (not (zerop n)) (princ "|" fw)))

(defun print-supposition (sup indent-value &optional fw)
  (cond (sup
          (terpri fw)
          (clear-indent indent-value fw)
          (princ "----------------------------------------------------------" fw)
          (terpri fw) (clear-indent indent-value fw)
          (princ " Suppose:  " fw)
          (set-prinp sup fw)
          (terpri fw)
          (clear-indent indent-value fw)
          (princ "----------------------------------------------------------" fw)
          )))

(defun print-formatted-argument (nodes arg &optional fw)
  (let ((nodes-left nodes)
        (current-sup nil)
        (depth-list (list (cons 0 nil)))
        (indent-value 0))
    (loop
      (let* ((n (mem1 nodes-left))
             (sup (hypernode-supposition n))
             (depth (length sup)))
        (cond ((not (equal sup current-sup))
               (cond ((or (<= indent-value depth)
                          (not (equal sup (e-assoc depth depth-list))))
                      (setq depth-list (cons (cons depth sup) depth-list))
                      (print-supposition sup depth fw)))
               (setq indent-value depth)
               (setq current-sup sup)))
        (terpri fw)
        (clear-indent indent-value fw) (princ " " fw) (princ (hypernode-number n) fw) (princ ".  " fw)
        (when (equal (hypernode-kind n) :percept) (princ "It appears that " fw))
        (prinp (hypernode-formula n) fw)
        (princ "     " fw)
        (let ((link (find-if #'(lambda (L) (eq (hyperlink-target L) n)) (argument-links arg))))
          (cond ((equal (hypernode-kind n) :percept) (princ "given" fw))
                ((hypernode-justification n) (princ (hypernode-justification n) fw))
                (link
                  (princ (hyperlink-rule link) fw)
                  (princ " from " fw)
                  (princ-set (mapcar #'hypernode-number (hyperlink-basis link)) fw))
                (t (let ((args (subset #'(lambda (A) (eq (argument-node A) n)) *arguments*)))
                     (cond ((eql (length args) 1)
                            (princ "by argument #" fw) (princ (argument-number (mem1 args)) fw))
                           ((> (length args) 1)
                            (princ "by arguments #" fw) (princ (argument-number (mem1 args)) fw)
                            (dolist (A (cdr args))
                              (princ ", #" fw) (princ (argument-number A) fw))))))))
        (setq nodes-left (cdr nodes-left))
        (if (null nodes-left) (return))))
    (terpri fw)))

#| Choose the first node all of whose ancestors are already in lines and whose
supposition is the same as the last one, if there is one.  Otherwise, choose the
first node all of whose ancestors are already in lines and whose supposition is
such that every node having that supposition is such that all of its ancestors are
either already in a line or have that same supposition.    Otherwise, choose the
first node all of whose ancestors are already in lines and whose supposition
is already used, if there is one.  Otherwise, choose the first line all of whose
ancestors are already in lines, and put its supposition in sups-used. |#
(defun format-argument (arg  &optional fw)
  (let* ((nodes (order (argument-inclusive-nodes arg) 'sup-order))
         (sups-used (list nil))
         (sup nil)
         (nodes-done nil))
    (loop
      ; (princ nodes) (terpri)
      ; (princ nodes-done) (terpri)
      (let ((next
              (find-if
                #'(lambda (x)
                    (and
                      (equal (hypernode-supposition x) sup)
                      (subsetp (hypernode-basis-in-arg x arg) nodes-done)))
                nodes)))
        (when (null next)
          (setq next
                (find-if
                  #'(lambda (x)
                      (and (subsetp (hypernode-basis-in-arg x arg) nodes-done)
                           (let ((sup (hypernode-supposition x)))
                             (every
                               #'(lambda (n)
                                   (or (member n nodes-done)
                                       (not (subsetp= sup (hypernode-supposition n)))
                                       (every
                                         #'(lambda (anc)
                                             (or (member anc nodes-done)
                                                 (equal (hypernode-supposition anc) sup)))
                                         (hypernode-basis-in-arg x arg))))
                               nodes))))
                  nodes))
          (when (null next)
            (setq next
                  (find-if
                    #'(lambda (x)
                        (and (mem (hypernode-supposition x) sups-used)
                             (subsetp (hypernode-basis-in-arg x arg) nodes-done)))
                    nodes))
            (when (null next)
              (setq next
                    (find-if
                      #'(lambda (x)
                          (subsetp (hypernode-basis-in-arg x arg) nodes-done))
                      nodes)))))
        (pushnew (hypernode-supposition next) sups-used)
        (setq sup (hypernode-supposition next))
        (pull next nodes)
        (push next nodes-done))
      (when (null nodes) (return)))
    (print-formatted-argument (reverse nodes-done) arg fw)))

(defun display-argument (arg &optional fw)
  (let ((n (argument-node arg)))
    (princ "===========================================================================" fw)
    (terpri fw) (princ "ARGUMENT #" fw) (princ (argument-number arg) fw)
    (terpri fw) (princ "This is " fw)
    (cond ((deductive-argument arg) (princ "a deductive argument for:" fw))
          ((zerop (argument-strength arg)) (princ "a defeated argument for:" fw))
          (t (princ "an undefeated argument of strength " fw) (princ (argument-strength arg) fw)
             (princ " for:" fw)))
    (terpri fw) (princ "      " fw)
    (if (hypernode-supposition n) (prinp-sequent (hypernode-sequent n) fw) (prinp (hypernode-formula n) fw)) (terpri fw)
    (when (argument-ultimate-interest arg)
      (princ " which is of ultimate interest." fw) (terpri fw))
    (format-argument arg fw) (terpri fw)
    (let ((d-args
            (order (mapcar #'argument-number (argument-defeaters arg)) #'<)))
      (when d-args
        (cond ((> (length d-args) 1)
               (princ "Arguments " fw))
              (t (princ "Argument " fw)))
        (princ "#" fw) (princ (car d-args) fw)
        (dolist (d-arg (cdr d-args)) (princ ", #" fw) (princ d-arg fw))
        (princ " support defeaters for this argument." fw) (terpri fw)))
    (when (and (argument-defeaters arg) (argument-defeatees arg)) (terpri fw))
    (let ((d-args
            (order (mapcar #'argument-number (argument-defeatees arg)) #'<)))
      (when d-args
        (princ "This argument supports defeaters for " fw)
        (princ "{ " fw)
        (let ((L (car (hypernode-defeatees n))))
          (princ "link " fw)
          (princ (hyperlink-number L) fw) (princ " for node " fw)
          (princ (hypernode-number (hyperlink-target L)) fw))
        (dolist (L (cdr (hypernode-defeatees n)))
          (princ " , " fw)
          (princ "link " fw)
          (princ (hyperlink-number L)) (princ " for node " fw)
          (princ (hypernode-number (hyperlink-target L)) fw))
        (princ " }" fw)
        (princ " thereby providing defeaters for " fw)
        (cond ((> (length d-args) 1)
               (princ "arguments " fw))
              (t (princ "argument " fw)))
        (princ "#" fw) (princ (car d-args) fw)
        (dolist (d-arg (cdr d-args)) (princ ", #" fw) (princ d-arg fw))
        (terpri fw)))
    ))

(defun hypernode-arguments (node &optional used-sequents)
  (when (hypernode-p node)
    (if (hypernode-hyperlinks node)
	(let ((S (hypernode-sequent node)))
					; (union=
	  (unionmapcar=
	   #'(lambda (L)
	       (if (hyperlink-basis L)
		   (when
		       (and
			(not (some #'(lambda (b)
				       (and (is-inference b) (subsumes (hypernode-sequent b) S)))
				   (hyperlink-basis L)))
			(not (some #'(lambda (S)
				       (some #'(lambda (b)
						 (and (is-inference b) (subsumes (hypernode-sequent b) S)))
					     (hyperlink-basis L)))
				   used-sequents)))
		     (mapcar
		      #'(lambda (arg) (cons L arg))
		      (mapcar
		       #'genunion
		       (gencrossproduct
			(append
			 (mapcar
                          #'(lambda (b) (hypernode-arguments b (cons S used-sequents)))
                          (hypernode-motivating-nodes node))
			 (mapcar
                          #'(lambda (b) (hypernode-arguments b (cons S used-sequents)))
                          (hyperlink-basis L)))))))
		 (list (list L))))
	   (hypernode-hyperlinks node)))
      (list nil))))

(defun find-defeating-arguments (argument)
  (dolist (L (argument-links argument))
    (when (hyperlink-defeasible? L)
      (dolist (d (hyperlink-defeaters L))
        (cond ((member d *nodes-done*)
               (dolist (arg *arguments*)
                 (when (eq (argument-node arg) d)
                   (pushnew arg (argument-defeaters argument))
                   (pushnew argument (argument-defeatees arg)))))
              (t
                (push d *nodes-done*)
                (push d *nodes-used*)
                (dolist (d-arg (hypernode-arguments d))
                  (when
                    (not
                      (some
                        #'(lambda (a2)
                            (and
                              (eq d (argument-node a2))
                              (subsetp (argument-links a2) d-arg)))
                        *arguments*))
                    (dolist (a2 *arguments*)
                      (when
                        (and
                          (eq d (argument-node a2))
                          (subsetp d-arg (argument-links a2)))
                        (pull a2 *arguments*)))
                    (let ((d-argument
                            (make-argument
                              :argument-number (incf *arg-number*)
                              :argument-links d-arg
                              :argument-node d
                              :argument-strength
                              (minimum0 (mapcar #'hyperlink-degree-of-justification d-arg))
                              :argument-inclusive-nodes (list d))))
                      (push d-argument *arguments*)
                      (dolist (m (hypernode-motivating-nodes d))
                        (pushnew m (argument-inclusive-nodes d-argument))
                        (pushnew m *nodes-used*))
                      (pushnew d-argument (argument-defeaters argument))
                      (pushnew argument (argument-defeatees d-argument))
                      (dolist (L (argument-links d-argument))
                        (dolist (b (hyperlink-basis L))
                          (pushnew b (argument-inclusive-nodes d-argument))
                          (pushnew b *nodes-used*)
                          (dolist (m (hypernode-motivating-nodes b))
                            (pushnew m (argument-inclusive-nodes d-argument))
                            (pushnew m *nodes-used*))))
                      (find-defeating-arguments d-argument))))))))))

(defun hyperlink-strength+ (L)
  (or (hyperlink-degree-of-justification L)
      (if (not (reason-defeasible-rule (hyperlink-rule L))) 1.0 0)))

#| If nodes is nonempty, this constructs all arguments relevant to nodes.  Otherwise, it
constructs all arguments relevant to ultimate-epistemic-interests. |#
(defun show-arguments (&optional nodes)
  (setf *arg-number* 0 *nodes-used* nil *arguments* nil *nodes-done* nil)
  (when (null nodes)
    (setf nodes (unionmapcar+ #'query-answers *ultimate-epistemic-interests*)))
  (dolist (n nodes)
    (push n *nodes-done*)
    (push n *nodes-used*)
    (dolist (arg (hypernode-arguments n))
      (when
        (not
          (some
            #'(lambda (a2)
                (and
                  (eq n (argument-node a2))
                  (subsetp (argument-links a2) arg)))
            *arguments*))
        (dolist (a2 *arguments*)
          (when
            (and
              (eq n (argument-node a2))
              (subsetp arg (argument-links a2)))
            (pull a2 *arguments*)))
        (let ((argument
                (make-argument
                  :argument-number (incf *arg-number*)
                  :argument-links arg
                  :argument-node n
                  :argument-strength
                  (minimum0 (mapcar #'hyperlink-strength+ arg))
                  ; (if (every #'(lambda (L) (null (defeating-assignment-trees L))) arg)
                  ;    (minimum0 (mapcar #'hyperlink-strength+ arg)) 0)
                  :argument-ultimate-interest (mem1 (hypernode-answered-queries n))
                  :argument-inclusive-nodes (list n))))
          (push argument *arguments*)
          (dolist (m (hypernode-motivating-nodes n))
            (pushnew m (argument-inclusive-nodes argument))
            (pushnew m *nodes-used*))
          (dolist (L (argument-links argument))
            (dolist (b (hyperlink-basis L))
              (pushnew b (argument-inclusive-nodes argument))
              (pushnew b *nodes-used*)
              (dolist (m (hypernode-motivating-nodes b))
                (pushnew m (argument-inclusive-nodes argument))
                (pushnew m *nodes-used*))))))))
  (dolist (argument *arguments*)
    (find-defeating-arguments argument))
  (dolist (argument (reverse *arguments*))
    (display-argument argument))
  (let ((argument-length (length *nodes-used*))
        (graph-size *hypernode-number*))
    (princ "===========================================================================")
    (terpri)
    (terpri) (terpri)
    (princ "Cumulative size of arguments = ") (princ argument-length) (terpri)
    (princ "Size of inference-graph = ") (princ graph-size)
    (princ " of which ") (princ *unused-suppositions*)
    (princ " were unused suppositions.") (terpri)
    (princ (truncate (* argument-length 100) graph-size))
    (princ "% of the inference-graph was used in the argument.") (terpri)))

#| This is the same as think, but it aborts when the *inference-queue* is empty. |#
(defun think-or-die ()
  ; (when (eql *cycle* 82) (break))
  (when (null *inference-queue*) (throw 'die nil))
  (when (read-char-no-hang) (clear-input) (throw 'die nil))
  ; (when (and (node 3) (not (zerop (hypernode-readopted-supposition (node 3))))) (break))
  (when (eq *cycle* *start-trace*)
    (trace-on)
    (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
      (menu-item-disable (oscar-menu-item "Trace on"))
      (menu-item-enable (oscar-menu-item "Trace off"))
      (menu-item-enable (oscar-menu-item "Trace from"))
      (menu-item-disable (oscar-menu-item "Display on"))
      (menu-item-enable (oscar-menu-item "Display off"))
      (menu-item-enable (oscar-menu-item "Display from"))))
  (when (eq *cycle* *start-display*)
    (display-on)
    (when (equal (lisp-implementation-type) "Macintosh Common Lisp")
      (menu-item-disable (oscar-menu-item "Display on"))
      (menu-item-enable (oscar-menu-item "Display off"))
      (menu-item-enable (oscar-menu-item "Display from"))))
  ; (display-assignment-tree)
  (when (and *display-inference-queue* *display?*) (display-inference-queue))
  (let ((Q (mem1 *inference-queue*)))
    (when *display?*
      (princ "---------------------------------------------------------------------------") (terpri)
      (princ *cycle*) (princ ":    ")
      (princ "Retrieving ") (princ (queue-item Q))
      (princ " from the inference-queue.  Preference = ")
      (princ (float (/ (truncate (* 10000 (queue-degree-of-preference Q))) 10000)))
      (terpri) (terpri))
    (pause)
    (setf *inference-queue* (cdr *inference-queue*))
    ; (display-inference-queue)
    (cond ((eq (queue-item-kind Q) :conclusion)
           (let ((node (queue-item Q)))
             (store-processed-node node)
             (setf (hypernode-queue-node node) nil)
             (reason-forwards-from node 0)))
          (t
            (let ((priority (retrieved-interest-priority (queue-degree-of-preference Q) (queue-item-complexity Q))))
              (cond ((eq (queue-item-kind Q) :query)
                     (let ((query (queue-item Q)))
                       (setf (query-queue-node query) nil)
                       (reason-backwards-from-query query priority 0)))
                    ((eq (queue-item-kind Q) :interest)
                     (let ((interest (queue-item Q)))
                       ; (when (equal interest (interest 58)) (trace-on))
                       (setf (interest-queue-node interest) nil)
                       (reason-backwards-from interest priority 0)
                       (form-epistemic-desires-for interest))))))))
  (when *new-links*
    (update-beliefs)
    (setf *new-links* nil)))

#|  COGITATE is used in place of OSCAR in TEST.  COGITATE does all reasoning
from premises, ignoring environmental-input (desires) and percepts.
Premises are triples (formula, supposition, degree-of-justification).
Premises can be defeated by rebutting defeaters, but there is no way
to have an undercutting defeater.  |#
(defun COGITATE ()
  (let ((deductive-only *deductive-only*)
        (time nil))
    (unwind-protect
      (progn
        (when
          (and
            (not *deductive-only*)
            (every #'(lambda (p) (eql (mem2 p) 1.0)) *premises*)
            (every #'(lambda (r) (not (reason-defeasible-rule r))) *forwards-logical-reasons*)
            (every #'(lambda (r) (not (reason-defeasible-rule r))) *forwards-substantive-reasons*)
            (every #'(lambda (r) (not (reason-defeasible-rule r))) *backwards-logical-reasons*)
            (every #'(lambda (r) (not (reason-defeasible-rule r))) *backwards-substantive-reasons*))
          (setf *deductive-only* t))
        ; (initialize-reasoner)
        (setf *cycle* 0)
        ; (gc)
        (setf time (get-internal-run-time))
        (let ((abort-time
                (if *time-limit* (+ (* *time-limit* internal-time-units-per-second 60) time))))
          (catch 'die
                 (initialize-reasoner)
                 (dolist (query *ultimate-epistemic-interests*)
                   (reason-backwards-from-query query (query-strength query) 0))
                 (loop
                   (incf *cycle*)
                   (dolist (premise *premises*)
                     (when (eql (mem3 premise) *cycle*)
                       (pull premise *premises*)
                       (queue-premise (list (mem1 premise) nil (mem2 premise)))))
                   (think-or-die)
                   (when (and abort-time (> (get-internal-run-time) abort-time))
                     (princ "NO PROOF WAS FOUND WITHIN ") (princ *time-limit*) (princ " MINUTES.")
                     (throw 'die nil))))
          (setf time (- (get-internal-run-time) time))))
      (setf *deductive-only* deductive-only))
    (terpri)
    (display-queries) (terpri)
    (princ "Elapsed time = ") (display-run-time-in-seconds time) (terpri)
    (let ((nodes nil))
      (dolist (query *ultimate-epistemic-interests*)
        (dolist (N (query-answers query))
          (pushnew N nodes)))
      (compute-relevant-nodes nodes)
      (let ((argument-length (length *relevant-nodes*)))
        (cond (*proofs?* (terpri) (show-arguments))
              (t        (princ "Cumulative size of arguments = ") (princ argument-length) (terpri)
                        (princ "Size of inference-graph = ") (princ *hypernode-number*)
                        (princ " of which ") (princ *unused-suppositions*)
                        (princ " were unused suppositions.") (terpri)
                        (princ (truncate (* argument-length 100) *hypernode-number*))
                        (princ "% of the inference-graph was used in the argument.") (terpri)))
        (princ *interest-number*) (princ " interests were adopted.") (terpri)
        (let ((nodes
                (subset #'(lambda (n)
                            (or (equal (hypernode-justification n) :reductio-supposition)
                                (equal (hypernode-justification n) :supposition)))
                        *hypergraph*)))
          (princ (length nodes)) (princ " suppositions were made.") (terpri))
        (when *display?*
          (princ "The following nodes were used in the arguments:") (terpri)
          (print-list (order (mapcar #'hypernode-number *relevant-nodes*) #'<) 40))
        (push (list *problem-number* time argument-length
                    (- *hypernode-number* *unused-suppositions*)) *test-log*)
        (when *log-on* (terpri) (display-reasoning))
        ))))

(defvar *display?* nil)
(defvar *proofs?* nil)

#| A problem is a list of the following:
     1.  problem-number
     2.  a list of premises, which are pairs (formula, degree-of-justification)
     3.  a list of desired conclusions, which are pairs (formula, degree-of-interest)
     4.  a list of forwards prima facie reasons, which are quintuples
           (name,premises,conclusion,variables,strength)
     5.  a list of forwards conclusive reasons, which are quadruples
           (name,premises,conclusion,variables)
     6.  a list of backwards prima facie reasons, which are sextuples
           (name,forwards-premises,backwards-premises,conclusion,variables,strength)
     7.  a list of backwards conclusive reasons, which are quintuples
           (name,forwards-premises,backwards-premises,conclusion,variables)
     8.  an optional string describing the problem.
All formulas can be entered as pretty formulas instead.

Lines can be commented out, and comments are allowed at ends of lines,
by inserting semicolons in the standard way.

The listing of strengths in reasons is optional, the default being 1.0.
|#

;===================== DISPLAYING PROBLEMS =========================

(defun print-premise (P)
  (let ((kind (fp-kind P))
        (formula (fp-formula P)))
    (cond ((equal kind :inference) (prinp formula))
          ((equal kind :desire) (princ "< ") (prinp formula) (princ " , desire>"))
          ((equal kind :percept) (princ "< ") (prinp formula) (princ " , percept>")))))

(defun display-forwards-reason (R)
  (princ "      ") (princ (reason-name R))
  (princ ":   {") (print-premise (mem1 (reason-forwards-premises R)))
  (for-all (cdr (reason-forwards-premises R)) #'(lambda (p) (princ " , ") (print-premise p))) (princ "}")
  (princ " ||=> ") (prinp (reason-conclusions R))
  (cond ((reason-variables R)
         (princ "  variables = {") (princ (mem1 (reason-variables R)))
         (for-all (cdr (reason-variables R)) #'(lambda (x)
                                                 (princ ",") (princ x)))
         (princ "}")))
  (princ "   strength = ") (princ (reason-strength R)) (terpri))

(defun display-backwards-reason (R)
  (princ "      ") (princ (reason-name R)) (princ ":   {")
  (when (mem1 (reason-forwards-premises R)) (prinp (fp-formula (mem1 (reason-forwards-premises R)))))
  (for-all (cdr (reason-forwards-premises R)) #'(lambda (p) (princ " , ") (prinp (fp-formula p)))) (princ "} ")
  (princ "{") (prinp (bp-formula (mem1 (reason-backwards-premises R))))
  (for-all (cdr (reason-backwards-premises R)) #'(lambda (p) (princ " , ") (prinp (bp-formula p)))) (princ "}")
  (princ " ||=> ") (prinp (reason-conclusions R))
  (cond ((reason-variables R)
         (princ "  variables = {") (princ (mem1 (reason-variables R)))
         (for-all (cdr (reason-variables R)) #'(lambda (x)
                                                 (princ ",") (princ x)))
         (princ "}")))
  (princ "   strength = ") (princ (reason-strength R)) (terpri))

(defun display-reasons ()
  (when (some #'reason-defeasible-rule *forwards-substantive-reasons*)
    (terpri) (princ "    FORWARDS PRIMA FACIE REASONS") (terpri)
    (dolist (R *forwards-substantive-reasons*)
      (when (reason-defeasible-rule R) (display-forwards-reason R))))
  (when (some #'(lambda (R) (not (reason-defeasible-rule R))) *forwards-substantive-reasons*)
    (terpri) (princ "    FORWARDS CONCLUSIVE REASONS") (terpri)
    (dolist (R *forwards-substantive-reasons*)
      (when (not (reason-defeasible-rule R)) (display-forwards-reason R))))
  (when (some #'reason-defeasible-rule *backwards-substantive-reasons*)
    (terpri) (princ "    BACKWARDS PRIMA FACIE REASONS") (terpri)
    (dolist (R *backwards-substantive-reasons*)
      (when (reason-defeasible-rule R) (display-backwards-reason R))))
  (when (some #'(lambda (R) (not (reason-defeasible-rule R))) *backwards-substantive-reasons*)
    (terpri) (princ "    BACKWARDS CONCLUSIVE REASONS") (terpri)
    (dolist (R *backwards-substantive-reasons*)
      (when (not (reason-defeasible-rule R)) (display-backwards-reason R))))
  (terpri))

(defun display-problem (P)
  (princ "Problem #") (princ (mem1 P)) (terpri)
  (when (mem8 P) (princ (mem8 P)) (terpri))
  (setf *premises* (mem2 P))
  (princ "Given premises:") (terpri)
  (dolist (premise *premises*)
    (princ "     ")
    (prinp (reform-if-string (mem1 premise)))
    (princ "    justification = ") (princ (mem2 premise))
    (terpri))
  (setf *fixed-ultimate-epistemic-interests* nil)
  (setf *ultimate-epistemic-interests* nil)
  (setf *query-number* 0)
  (princ "Ultimate epistemic interests:") (terpri)
  (dolist (interest (mem3 P))
    (let ((query
            (make-query
              :query-number (incf *query-number*)
              :query-formula (reform-if-string (mem1 interest))
              :query-strength (mem2 interest))))
      (push query *fixed-ultimate-epistemic-interests*)
      (princ "     ")
      (prinp (query-formula query)) (princ "    interest = ") (princ (mem2 interest))
      (terpri)))
  (setf *forwards-substantive-reasons* (append (mem4 P) (mem5 P)))
  (setf *backwards-substantive-reasons* (append (mem6 P) (mem7 P)))
  (display-reasons)
  )

(defun run-reasoning-problem (P)
  (setf *problem-number* (car P))
  (setf *pretty-list* nil *string-symbols* nil)
  (terpri)
  (princ
    "******************************************************************************************")
  (terpri)
  (princ
    "******************************************************************************************")
  (terpri)
  (display-problem P)
  ; (gc)
  (COGITATE)
  (when *display?* (display-hypergraph))
  (terpri))

#| The following runs individual problems or lists of problems from the list *problems*.
(test) runs the entire set.  (test n) runs just problem n.  (test n t) starts with problem n
and runs the rest of the set.  (test n m) runs problems n through m.  (test n :skip '(i j k))
starts with problem n and runs the rest of the set except for i, j, and k.  (test n m :skip '(i j k))
runs problems n through m, skipping i, j, and k.  (test :skip i j k) runs all the problems
except i, j, k. |#
(defun test (&rest rest)
  (terpri) (princ "(") (princ "                                 ") (princ *version*) (princ "          ")
  (let ((time (multiple-value-list (get-decoded-time))))
    (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
    (princ (mem6 time)) (princ "          ") (princ (mem3 time))
    (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
    (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
    (terpri) (terpri))
  (princ "*reductio-discount* = ") (princ *reductio-discount*) (terpri)
  (princ "*reductio-interest* = ") (princ *reductio-interest*) (terpri)
  (princ "*skolem-multiplier* = ") (princ *skolem-multiplier*) (terpri)
  (princ "*quantifier-discount* = ") (princ *quantifier-discount*) (terpri)
  (setf *test-log* nil)
  (cond ((null rest)
         ;; (test)
         (dolist (P *problems*)
           (run-reasoning-problem P)
           (when *pause*
             (terpri) (princ "Type any key to continue.") (terpri) (terpri)
             (read-char))))
        ((equal (mem1 rest) :skip)
         ;; (test :skip i j k)
         (dolist (P *problems*)
           (when (not (mem (car P) (cdr rest)))
             (run-reasoning-problem P)
             (when *pause*
               (terpri) (princ "Type any key to continue.") (terpri) (terpri)
               (read-char)))))
        (t (let ((start (mem1 rest)))
             (cond
               ((null (cdr rest))
                ;; (test n)
                (run-reasoning-problem (assoc start *problems*)))
               ((eq (mem2 rest) t)
                ;; (test n t)
                (dolist (P (mem (assoc start *problems*) *problems*))
                  (run-reasoning-problem P)
                  (when *pause*
                    (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                    (read-char))))
               ((equal (mem2 rest) :skip)
                ;; (test n :skip i j k)
                (dolist (P (mem (assoc start *problems*) *problems*))
                  (when (not (mem (car P) (cdr rest)))
                    (run-reasoning-problem P)
                    (when *pause*
                      (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                      (read-char)))))
               ((numberp (mem2 rest))
                ;; (test n m) and (test n m :skip i j k)
                (dolist (P (mem (assoc start *problems*) *problems*))
                  (when (and (not (mem (car P) (cdddr rest))) (not (> (car P) (mem2 rest))))
                    (run-reasoning-problem P)
                    (when (and *pause* (not (= (car P) (mem2 rest))))
                      (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                      (read-char)))))))))
  (setf *test-log*
        (list *version* *reductio-discount* *reductio-interest* *skolem-multiplier*
              *quantifier-discount* *test-log*))
  (when (not *display?*) (display-test-log))
  (terpri)
  (princ *test-log*)
  (terpri) (princ ")")
  (terpri))

;===================== MAKING PROBLEM LISTS =========================

(defvar *forwards-logical-reasons* nil)

(defvar *backwards-logical-reasons* nil)

#| This recombines logical formulas containing whitespace that were taken apart by
string-list. |#
(defun collapse-strings (strings)
  (cond ((< (length strings) 2) strings)
        ((mem (mem2 strings) '("v" "->" "<->" "&" "@"))
         (let ((cs (collapse-strings (cddr strings))))
           (cons (concatenate 'string (mem1 strings) " " (mem2 strings) " " (mem1 cs))
                 (cdr cs))))
        (t (cons (mem1 strings) (collapse-strings (cdr strings))))))

#| Where string contains spaces, this returns the list of words separated by spaces.
Words can be separated by commas, provided there is whitespace between commas
and adjoining words.  The commas are then removed. |#
(defun string-list (string)
  (let ((string* (string-trim '(#\Space #\Tab #\Newline) string))
        (words nil))
    (when (not (eql (length string*) 0))
      (loop
        (let ((pos (search " " string*)))
          (when (null pos)
            (push string* words)
            (setf words (reverse (remove-if-equal "," words)))
            (return nil))
          (push (subseq string* 0 pos) words)
          (setf string* (string-left-trim '(#\Space) (subseq string* pos))))))
    (collapse-strings words)))

#| Where string is a string of pretty-formulas separated by commas (and whitespace on
                                                                        either side of the commas, if desired), this returns the list of formulas. |#
(defun reform-list (string)
  (let ((formulas nil)
        (string-remainder string))
    (loop
      (let ((pos (position #\, string-remainder)))
        (when (null pos)
          (let ((formula-string (string-trim '(#\Space) string-remainder)))
            (when (not (equal formula-string ""))
              (push formula-string formulas)))
          (return nil))
        (push (string-trim '(#\Space) (subseq string-remainder 0 pos)) formulas)
        (setf string-remainder (subseq string-remainder (1+ pos)))))
    (mapcar #'reform (reverse formulas))))

(defun find-backwards-con-reasons (string problem-number)
  (let ((reasons nil))
    (let ((reason-string string))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos10 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos10))))
            (setf reason-string (subseq reason-string pos10))
            (let* ((pos11 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos11)))
                   (reason-forwards-premises
                     (mapcar #'(lambda (p) (list p nil)) (reform-list premise-string))))
              (setf reason-string (subseq reason-string pos11))
              (let* ((pos2 (position #\{ reason-string)))
                (setf reason-string (subseq reason-string pos2))
                (let* ((pos4 (position #\} reason-string))
                       (premise-string
                         (string-trim
                           '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                       (reason-backwards-premises
                         (mapcar #'(lambda (p) (list p nil))  (reform-list premise-string))))
                  (setf reason-string (subseq reason-string pos4))
                  (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                    (setf reason-string (subseq reason-string pos5))
                    (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                          (variables nil)
                          (conclusion nil))
                      (when pos6
                        (setf conclusion
                              (list
                                (reform
                                  (string-trim
                                    '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6)))
                                nil))
                        (let ((pos7 (position #\} reason-string)))
                          (setf variables
                                (string-list (subseq reason-string (+ 13 pos6) pos7)))
                          (setf reason-string (subseq reason-string pos7))))
                      (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                        (when (null pos6)
                          (setf conclusion
                                (list
                                  (reform
                                    (string-trim
                                      '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8)))
                                  nil)))
                        (let* ((pos9 (position #\Newline reason-string)))
                          (setf reason-string (subseq reason-string pos9))
                          (push
                            (eval `(define-backwards-reason
                                     ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                     :reason-forwards-premises ',(mapcar #'(lambda (premise)
                                                                      (if (stringp premise)
                                                                        (list (reform premise) nil)
                                                                        (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                  reason-forwards-premises)
                                     :reason-backwards-premises ',(mapcar #'(lambda (premise)
                                                                       (if (stringp premise)
                                                                         (list (reform premise) nil)
                                                                         (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                   reason-backwards-premises)
                                     :conclusion ',(if (stringp conclusion)
                                                     (reform conclusion)
                                                     (reform-if-string (mem1 conclusion)))
                                     :condition ',(if (stringp conclusion)
                                                    nil
                                                    (mem2 conclusion))
                                     :variables ',variables))
                            reasons))))))))))))))

(defun find-backwards-pf-reasons (string problem-number)
  (let ((reasons nil)
        (pos (search "backwards conclusive reasons" string :test 'string-equal)))
    (let ((reason-string (subseq string 0 pos)))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos10 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos10))))
            (setf reason-string (subseq reason-string pos10))
            (let* ((pos11 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos11)))
                   (reason-forwards-premises
                     (mapcar #'(lambda (p) (list p nil)) (reform-list premise-string))))
              (setf reason-string (subseq reason-string pos11))
              (let* ((pos2 (position #\{ reason-string)))
                (setf reason-string (subseq reason-string pos2))
                (let* ((pos4 (position #\} reason-string))
                       (premise-string
                         (string-trim
                           '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                       (reason-backwards-premises
                         (mapcar #'(lambda (p) (list p nil))  (reform-list premise-string))))
                  (setf reason-string (subseq reason-string pos4))
                  (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                    (setf reason-string (subseq reason-string pos5))
                    (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                          (variables nil)
                          (conclusion nil))
                      (when pos6
                        (setf conclusion
                              (list
                                (reform
                                  (string-trim
                                    '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6)))
                                nil))
                        (let ((pos7 (position #\} reason-string)))
                          (setf variables
                                (string-list (subseq reason-string (+ 13 pos6) pos7)))
                          (setf reason-string (subseq reason-string pos7))))
                      (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                        (when (null pos6)
                          (setf conclusion
                                (list
                                  (reform
                                    (string-trim
                                      '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8)))
                                  nil)))
                        (let* ((pos9 (position #\Newline reason-string))
                               (strength
                                 (if (null pos8) 1.0
                                   (named-decimal-number
                                     (string-trim
                                       '(#\Space #\Tab) (subseq reason-string (+ 10 pos8) pos9))))))
                          (setf reason-string (subseq reason-string pos9))
                          (push
                            (eval `(define-backwards-reason
                                     ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                     :reason-forwards-premises ',(mapcar #'(lambda (premise)
                                                                      (if (stringp premise)
                                                                        (list (reform premise) nil)
                                                                        (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                  reason-forwards-premises)
                                     :reason-backwards-premises ',(mapcar #'(lambda (premise)
                                                                       (if (stringp premise)
                                                                         (list (reform premise) nil)
                                                                         (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                   reason-backwards-premises)
                                     :conclusion ',(if (stringp conclusion)
                                                     (reform conclusion)
                                                     (reform-if-string (mem1 conclusion)))
                                     :condition ',(if (stringp conclusion)
                                                    nil
                                                    (mem2 conclusion))
                                     :variables ',variables
                                     :defeasible? t
                                     :strength ',strength))
                            reasons))))))))))))))

(defun find-conclusions-from-string (string)
  (let ((conclusions nil)
        (subseq string))
    (loop
      (let ((pos (search "interest =" subseq :test 'string-equal)))
        (when (null pos) (return conclusions))
        (let ((conclusion (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 0 pos))))
          (setf subseq (subseq subseq pos))
          (setf pos (position #\Newline subseq))
          (let ((degree
                  (named-decimal-number (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 10 pos)))))
            (setf subseq (subseq subseq pos))
            (push (list (reform conclusion) degree) conclusions)))))))

#| This allows the premises of a forwards-reason to be entered either as a single
formula, or as a pair <formula , condition> where condition is either "inference",
"desire", or "percept" (entered without quotes).  If a formula is entered alone,
the default condition NIL is used. |#
(defun reform-forwards-premise-list (string)
  ; (setf s string) (break)
  (let ((premises nil)
        (string-remainder (string-trim '(#\Space) string)))
    (loop
      (cond ((equal (length string-remainder) 0) (return nil))
            ((equal (subseq string-remainder 0 1) "<")
             (let* ((pos (position #\> string-remainder))
                    (premise-string (subseq string-remainder 1 pos))
                    (pos1 (position #\, premise-string))
                    (formula-string (string-trim '(#\Space) (subseq premise-string 0 pos1)))
                    (condition-string (string-trim '(#\Space) (subseq premise-string (1+ pos1))))
                    (condition
                      (cond ((equal condition-string "inference") is-inference)
                            ((equal condition-string "desire") is-desire)
                            ((equal condition-string "percept") is-percept))))
               (setf string-remainder
                     (string-trim '(#\Space #\,) (subseq string-remainder (1+ pos))))
               (push (list (reform formula-string) condition) premises)))
            (t
              (let ((pos (position #\, string-remainder)))
                (when (null pos)
                  (let ((formula-string (string-trim '(#\Space) string-remainder)))
                    (when (not (equal formula-string ""))
                      (push (list (reform formula-string) NIL) premises)))
                  (return nil))
                (push
                  (list (reform (string-trim '(#\Space) (subseq string-remainder 0 pos)))
                        is-inference)
                  premises)
                (setf string-remainder
                      (string-trim '(#\Space) (subseq string-remainder (1+ pos))))))))
    (reverse premises)))

(defun find-forwards-con-reasons (string problem-number)
  (let ((reasons nil)
        (pos (search "backwards prima facie reasons" string :test 'string-equal)))
    (when (null pos)
      (setf pos (search "backwards conclusive reasons" string :test 'string-equal)))
    (let ((reason-string (subseq string 0 pos)))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos2 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos2))))
            (setf reason-string (subseq reason-string pos2))
            (let* ((pos4 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                   (premises (reform-forwards-premise-list premise-string)))
              (setf reason-string (subseq reason-string pos4))
              (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                (setf reason-string (subseq reason-string pos5))
                (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                      (variables nil)
                      (conclusion nil))
                  (when pos6
                    (setf conclusion
                          (reform
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6))))
                    (let ((pos7 (position #\} reason-string)))
                      (setf variables
                            (string-list (subseq reason-string (+ 13 pos6) pos7)))
                      (setf reason-string (subseq reason-string pos7))))
                  (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                    (when (null pos6)
                      (setf conclusion
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8))))
                    (let* ((pos9 (position #\Newline reason-string)))
                      (setf reason-string (subseq reason-string pos9))
                      (push
                        (eval `(define-forwards-reason
                                 ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                 :reason-forwards-premises ',(mapcar #'(lambda (premise)
                                                                  (if (stringp premise)
                                                                    (list (reform premise) nil)
                                                                    (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                              premises)
                                 :conclusion ',(reform-if-string conclusion)
                                 :variables ',variables))
                        reasons))))))))))))

#| If a strength is not listed, it is taken to be 1.0. |#
(defun find-forwards-pf-reasons (string problem-number)
  (let ((reasons nil)
        (pos (search "forwards conclusive reasons" string :test 'string-equal)))
    (when (null pos)
      (setf pos (search "backwards prima facie reasons" string :test 'string-equal)))
    (when (null pos)
      (setf pos (search "backwards conclusive reasons" string :test 'string-equal)))
    (let ((reason-string (subseq string 0 pos)))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos2 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos2))))
            (setf reason-string (subseq reason-string pos2))
            (let* ((pos4 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                   (premises (reform-forwards-premise-list premise-string)))
              (setf reason-string (subseq reason-string pos4))
              (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                (setf reason-string (subseq reason-string pos5))
                (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                      (variables nil)
                      (conclusion nil))
                  (when pos6
                    (setf conclusion
                          (reform
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6))))
                    (let ((pos7 (position #\} reason-string)))
                      (setf variables
                            (string-list (subseq reason-string (+ 13 pos6) pos7)))
                      (setf reason-string (subseq reason-string pos7))))
                  (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                    (when (null pos6)
                      (setf conclusion
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8))))
                    (let* ((pos9 (position #\Newline reason-string))
                           (strength
                             (if (null pos8) 1.0
                               (named-decimal-number
                                 (string-trim
                                   '(#\Space #\Tab) (subseq reason-string (+ 10 pos8) pos9))))))
                      (setf reason-string (subseq reason-string pos9))
                      (push
                        (eval `(define-forwards-reason
                                 ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                 :reason-forwards-premises
                                 ',(mapcar #'(lambda (premise)
                                               (if (stringp premise)
                                                 (list (reform premise) nil)
                                                 (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                           premises)
                                 :conclusion ',(reform-if-string conclusion)
                                 :variables ',variables
                                 :defeasible? t
                                 :strength ',strength))
                        reasons))))))))))))

(defun find-premises-from-string (string)
  (let ((premises nil)
        (subseq string))
    (loop
      (let ((pos (search "justification =" subseq :test 'string-equal)))
        (when (null pos) (return premises))
        (let ((premise (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 0 pos))))
          (setf subseq (subseq subseq pos))
          (setf pos (position #\Newline subseq))
          (let ((degree
                  (named-decimal-number
                    (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 15 pos)))))
            (setf subseq (subseq subseq pos))
            (push (list (reform premise) degree) premises)))))))

(defun make-problem-from-string (problem-string)
  (let* ((string (subseq problem-string 9))
         (pos1 (position #\Newline string))
         (problem-number (named-integer (string-trim '(#\Space #\Tab) (subseq string 0 pos1)))))
    (setf string (subseq string (1+ pos1)))
    (let* ((pos2 (search "Given premises:" string :test 'string-equal))
           (problem-description
             (string-trim '(#\Space #\Tab #\Newline) (subseq string 0 pos2))))
      (setf string
            (string-left-trim '(#\Space #\Tab #\Newline)
                              (subseq string (+ 16 pos2))))
      (let ((premises (find-premises-from-string string)))
        (setf string
              (string-left-trim '(#\Space #\Tab #\Newline)
                                (subseq string
                                        (+ 29 (search "ultimate epistemic interests:" string :test 'string-equal)))))
        (let ((conclusions (find-conclusions-from-string string)))
          (let ((pos3 (search "forwards prima facie reasons" string :test 'string-equal))
                (forwards-pf-reasons nil))
            (when pos3
              (setf string
                    (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 29 pos3))))
              (setf forwards-pf-reasons (find-forwards-pf-reasons string problem-number)))
            (let ((pos4 (search "forwards conclusive reasons" string :test 'string-equal))
                  (forwards-con-reasons nil))
              (when pos4
                (setf string
                      (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 28 pos4))))
                (setf forwards-con-reasons (find-forwards-con-reasons string problem-number)))
              (let ((pos5 (search "backwards prima facie reasons" string :test 'string-equal))
                    (backwards-pf-reasons nil))
                (when pos5
                  (setf string
                        (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 30 pos5))))
                  (setf backwards-pf-reasons (find-backwards-pf-reasons string problem-number)))
                (let ((pos6 (search "backwards conclusive reasons" string :test 'string-equal))
                      (backwards-con-reasons nil))
                  (when pos6
                    (setf string
                          (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 29 pos6))))
                    (setf backwards-con-reasons (find-backwards-con-reasons string problem-number)))
                  (list problem-number
                        (reverse premises)
                        (reverse conclusions)
                        (reverse forwards-pf-reasons)
                        (reverse forwards-con-reasons)
                        (reverse backwards-pf-reasons)
                        (reverse backwards-con-reasons)
                        problem-description))))))))))

#| This removes comment-lines or comments from ends of lines. |#
(defun trim-comments (string)
  (let ((pos (position #\; string)))
    (if pos
      (let ((pos2 (position #\Newline string :start pos)))
        (trim-comments
          (cat (subseq string 0 pos)
               (if (char= (char string (1- pos)) #\Newline)
                 (subseq string (1+ pos2))
                 (subseq string pos2)))))
      string)))

#| Given a string set-string describing a set of problems, this returns the list of strings
describing the individual problems. |#
(defun problem-strings (set-string)
  (setf set-string (trim-comments set-string))
  (let ((start (search "Problem #" set-string :test 'string-equal))
        (strings nil))
    (loop
      (let ((end (search "Problem #" set-string :start2 (1+ start) :test 'string-equal)))
        (cond (end
                (push (subseq set-string start end) strings)
                (setf start end))
              (t
                (push (subseq set-string start) strings)
                (return (reverse strings))))))))

#| Given a string describing a problem-set, this returns the list of problems. |#
(defun make-problem-list (set-string)
  (mapcar #'make-problem-from-string (problem-strings set-string)))

(defun default-problem-list ()
  (make-problem-list
          "
Problem #1008
Zombie problem 8 from Semantics for Defeasible Reasoning (2009)
Given premises:
     A    justification = 1.0
     C    justification = 1.0
     G    justification = 1.0
     H    justification = 1.0
Ultimate epistemic interests:
     B    interest = 1.0
     P    interest = 1.0
     Q    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> B   strength = 1.0
      pf-reason_2:   {C} ||=> D   strength = 1.0
      pf-reason_3:   {G} ||=> P   strength = 1.0
      pf-reason_4:   {H} ||=> Q   strength = 1.0
      pf-reason_5:   {B} ||=> (C @ D)   strength = 1.0
      pf-reason_6:   {D} ||=> (A @ B)   strength = 1.0
      pf-reason_7:   {B} ||=> (G @ P)   strength = 1.0
      pf-reason_8:   {D} ||=> (G @ P)   strength = 1.0
      pf-reason_9:   {P} ||=> (H @ Q)   strength = 1.0

Problem #1009
Zombie problem 9 from Semantics for Defeasible Reasoning (2009)
Given premises:
     A    justification = 1.0
     C    justification = 1.0
     E    justification = 1.0
     G    justification = 1.0
     H    justification = 1.0
Ultimate epistemic interests:
     B    interest = 1.0
     P    interest = 1.0
     Q    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> B   strength = 1.0
      pf-reason_2:   {C} ||=> D   strength = 1.0
      pf-reason_3:   {E} ||=> F   strength = 1.0
      pf-reason_4:   {G} ||=> P   strength = 1.0
      pf-reason_5:   {H} ||=> Q   strength = 1.0
      pf-reason_6:   {B} ||=> (C @ D)   strength = 1.0
      pf-reason_7:   {D} ||=> (E @ F)   strength = 1.0
      pf-reason_8:   {F} ||=> (A @ B)   strength = 1.0
      pf-reason_9:   {B} ||=> (G @ P)   strength = 1.0
      pf-reason_10:  {D} ||=> (G @ P)   strength = 1.0
      pf-reason_11:  {F} ||=> (G @ P)   strength = 1.0
      pf-reason_12:  {P} ||=> (H @ Q)   strength = 1.0

Problem #1
This is a case of collective rebutting defeat
Given premises:
     P    justification = 1.0
     A    justification = 1.0
Ultimate epistemic interests:
     R    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> Q   strength = 1.0
      pf-reason_2:   {Q} ||=> R   strength = 1.0
      pf-reason_3:   {C} ||=> ~R   strength = 1.0
      pf-reason_4:   {B} ||=> C   strength = 1.0
      pf-reason_5:   {A} ||=> B   strength = 1.0

Problem #2
This is the same as #1 except that some reasons are backwards.
Given premises:
     P    justification = 1.0
     A    justification = 1.0
Ultimate epistemic interests:
     R    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> Q   strength = 1.0
      pf-reason_2:   {Q} ||=> R   strength = 1.0
      pf-reason_3:   {A} ||=> B   strength = 1.0

    BACKWARDS PRIMA FACIE REASONS
      pf-reason_4:   {} {C} ||=> ~R   strength = 1.0
      pf-reason_5:   {} {B} ||=> C   strength = 1.0

Problem #3
Figure 2
Given premises:
     A    justification = 1.0
     B    justification = 1.0
     C    justification = 1.0
Ultimate epistemic interests:
     J    interest = 1.0
     K    interest = 1.0
     L    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> D   strength = 1.0
      pf-reason_2:   {D} ||=> G   strength = 1.0
      pf-reason_3:   {B} ||=> E   strength = 1.0
      pf-reason_4:   {C} ||=> F   strength = 1.0
      pf-reason_5:   {I} ||=> L   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {G} ||=> J   strength = 1.0
      con-reason_2:   {E} ||=> H   strength = 1.0
      con-reason_3:   {H} ||=> K   strength = 1.0
      con-reason_4:   {F} ||=> I   strength = 1.0
      con-reason_5:   {F} ||=> (B @ E)   strength = 1.0
      con-reason_6:   {H} ||=> (D @ G)   strength = 1.0

Problem #4
Figure 3
Given premises:
     A    justification = 1.0
     B    justification = 1.0
Ultimate epistemic interests:
     J    interest = 1.0
     K    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> D   strength = 1.0
      pf-reason_2:   {D} ||=> G   strength = 1.0
      pf-reason_3:   {B} ||=> ~D   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {G} ||=> J   strength = 1.0
      con-reason_2:   {~D} ||=> H   strength = 1.0
      con-reason_3:   {H} ||=> K   strength = 1.0

Problem #5
Figure 4
Given premises:
     A    justification = 1.0
     B    justification = 1.0
     C    justification = 1.0
Ultimate epistemic interests:
     J    interest = 1.0
     K    interest = 1.0
     L    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> D   strength = 1.0
      pf-reason_2:   {D} ||=> G   strength = 1.0
      pf-reason_3:   {B} ||=> ~D   strength = 1.0
      pf-reason_4:   {C} ||=> D   strength = 1.0
      pf-reason_5:   {I} ||=> L   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {G} ||=> J   strength = 1.0
      con-reason_2:   {~D} ||=> H   strength = 1.0
      con-reason_3:   {H} ||=> K   strength = 1.0
      con-reason_4:   {D} ||=> I   strength = 1.0

Problem #6
Figure 5
Given premises:
     A    justification = 1.0
     B    justification = 1.0
     C    justification = 1.0
Ultimate epistemic interests:
     J    interest = 1.0
     K    interest = 1.0
     L    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> D   strength = 1.0
      pf-reason_2:   {D} ||=> G   strength = 1.0
      pf-reason_3:   {B} ||=> ~D   strength = 1.0
      pf-reason_4:   {C} ||=> F   strength = 1.0
      pf-reason_5:   {I} ||=> L   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {G} ||=> J   strength = 1.0
      con-reason_2:   {~D} ||=> H   strength = 1.0
      con-reason_3:   {H} ||=> K   strength = 1.0
      con-reason_4:   {F} ||=> I   strength = 1.0
      con-reason_5:   {~D} ||=> M   strength = 1.0
      con-reason_6:   {M} ||=> N   strength = 1.0
      con-reason_7:   {N} ||=> (C @ F)   strength = 1.0
      con-reason_8:   {F} ||=> (B @ ~D)   strength = 1.0

Problem #7
Figure 7 -- self-defeat
Given premises:
     P    justification = 1.0
     Q    justification = 1.0
     S    justification = 1.0
Ultimate epistemic interests:
     T    interest = 1.0
     (R v ~T)    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> R   strength = 1.0
      pf-reason_2:   {Q} ||=> ~R   strength = 1.0
      pf-reason_3:   {S} ||=> T   strength = 1.0

Problem #8
Figure 8 -- the lottery paradox paradox
Given premises:
     P    justification = 1.0
Ultimate epistemic interests:
     ~T1    interest = 1.0
     ~T2    interest = 1.0
     ~T3    interest = 1.0
     R    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {R} ||=> ~T1   strength = 1.0
      pf-reason_2:   {R} ||=> ~T2   strength = 1.0
      pf-reason_3:   {R} ||=> ~T3   strength = 1.0
      pf-reason_4:   {P} ||=> R   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {R , ~T1 , ~T2} ||=> T3   strength = 1.0
      con-reason_2:   {R , ~T2 , ~T3} ||=> T1   strength = 1.0
      con-reason_3:   {R , ~T1 , ~T3} ||=> T2   strength = 1.0
      con-reason_4:   {~T1 , ~T2 , ~T3} ||=> ~R   strength = 1.0

Problem #9
Figure 8 -- the lottery paradox paradox using logic
Given premises:
     P    justification = 1.0
Ultimate epistemic interests:
     ~T1    interest = 1.0
     ~T2    interest = 1.0
     ~T3    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {R} ||=> ~T1   strength = 1.0
      pf-reason_2:   {R} ||=> ~T2   strength = 1.0
      pf-reason_3:   {R} ||=> ~T3   strength = 1.0
      pf-reason_4:   {P} ||=> R   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {R} ||=> (T1 v (T2 v T3))   strength = 1.0

Problem #10
Figure 9 -- No nearest defeasible ancestor is defeated.
Given premises:
     P    justification = 1.0
Ultimate epistemic interests:
     R    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> Q   strength = 1.0
      pf-reason_2:   {Q} ||=> R   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {R} ||=> (P @ Q)   strength = 1.0

Problem #11
figure 10 -- Robert and the pink elephant.
Given premises:
     P    justification = 1.0
     Q    justification = 1.0
     R    justification = 1.0
Ultimate epistemic interests:
     U    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P , Q} ||=> S   strength = 1.0
      pf-reason_2:   {R} ||=> T   strength = 1.0
      pf-reason_3:   {S} ||=> U   strength = 1.0
      pf-reason_4:   {V} ||=> ((P & Q) @ S)   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {T , U} ||=> V   strength = 1.0

Problem #12
figure 11 -- a simple case of ancestor defeat.
Given premises:
     P    justification = 1.0
     Q    justification = 1.0
     R    justification = 1.0
Ultimate epistemic interests:
     W    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> S   strength = 1.0
      pf-reason_2:   {S} ||=> U   strength = 1.0
      pf-reason_3:   {Q} ||=> T   strength = 1.0
      pf-reason_4:   {R} ||=> W   strength = 1.0
      pf-reason_5:   {V} ||=> (S @ U)   strength = 1.0
      pf-reason_6:   {U} ||=> (R @ W)   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {S , T} ||=> V   strength = 1.0

Problem #13
figure 12 -- a more complicated case of ancestor defeat.
Given premises:
     P    justification = 1.0
     Q    justification = 1.0
     R    justification = 1.0
     X    justification = 1.0
Ultimate epistemic interests:
     W    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> S   strength = 1.0
      pf-reason_2:   {S} ||=> U   strength = 1.0
      pf-reason_3:   {Q} ||=> T   strength = 1.0
      pf-reason_4:   {R} ||=> W   strength = 1.0
      pf-reason_5:   {X} ||=> ~S   strength = 1.0
      pf-reason_6:   {V} ||=> (S @ U)   strength = 1.0
      pf-reason_7:   {U} ||=> (R @ W)   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {S , T} ||=> V   strength = 1.0

Problem #14
figure 13 -- a still more complicated case of ancestor defeat.
Given premises:
     P    justification = 1.0
     Q    justification = 1.0
     R    justification = 1.0
     X    justification = 1.0
Ultimate epistemic interests:
     W    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P} ||=> S   strength = 1.0
      pf-reason_2:   {S} ||=> U   strength = 1.0
      pf-reason_3:   {Q} ||=> T   strength = 1.0
      pf-reason_4:   {R} ||=> W   strength = 1.0
      pf-reason_5:   {S} ||=> Y   strength = 1.0
      pf-reason_6:   {X} ||=> ~S   strength = 1.0
      pf-reason_7:   {V} ||=> (S @ U)   strength = 1.0
      pf-reason_8:   {U} ||=> (R @ W)   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {Y , T} ||=> V   strength = 1.0

Problem #15
figure 14 -- a three-membered defeat cycle.
Given premises:
     A    justification = 1.0
     P    justification = 1.0
     R    justification = 1.0
     T    justification = 1.0
Ultimate epistemic interests:
     B    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> B   strength = 1.0
      pf-reason_2:   {P} ||=> Q   strength = 1.0
      pf-reason_3:   {R} ||=> S   strength = 1.0
      pf-reason_4:   {T} ||=> U   strength = 1.0
      pf-reason_5:   {Q} ||=> (R @ S)   strength = 1.0
      pf-reason_6:   {S} ||=> (T @ U)   strength = 1.0
      pf-reason_7:   {U} ||=> (P @ Q)   strength = 1.0
      pf-reason_8:   {Q} ||=> (A @ B)   strength = 1.0

Problem #16
figure 18 -- the paradox of the preface.
Given premises:
     P1    justification = 1.0
     P2    justification = 1.0
     P3    justification = 1.0
     S    justification = 1.0
     T    justification = 1.0
Ultimate epistemic interests:
     (Q1 & (Q2 & Q3))    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P1} ||=> Q1   strength = 1.0
      pf-reason_2:   {P2} ||=> Q2   strength = 1.0
      pf-reason_3:   {P3} ||=> Q3   strength = 1.0
      pf-reason_4:   {S} ||=> R   strength = 1.0
      pf-reason_5:   {T} ||=> ~(Q1 & (Q2 & Q3))   strength = 1.0
      pf-reason_6:   {S1} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0
      pf-reason_7:   {S2} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0
      pf-reason_8:   {S3} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {Q1 , Q2} ||=> (Q1 & Q2)   strength = 1.0
      con-reason_2:   {Q2 , Q3} ||=> (Q2 & Q3)   strength = 1.0
      con-reason_3:   {Q1 , Q3} ||=> (Q1 & Q3)   strength = 1.0
      con-reason_4:   {R , (Q1 & Q3)} ||=> S2   strength = 1.0
      con-reason_5:   {R , (Q2 & Q3)} ||=> S1   strength = 1.0
      con-reason_6:   {R , (Q1 & Q2)} ||=> S3   strength = 1.0
      con-reason_7:   {(Q1 & Q2) , ~(Q1 & (Q2 & Q3))} ||=> ~Q3   strength = 1.0
      con-reason_8:   {(Q2 & Q3) , ~(Q1 & (Q2 & Q3))} ||=> ~Q1   strength = 1.0
      con-reason_9:   {(Q1 & Q3) , ~(Q1 & (Q2 & Q3))} ||=> ~Q2   strength = 1.0

    BACKWARDS CONCLUSIVE REASONS
      con-reason_11:   {} {Q1 , Q2 , Q3} ||=> (Q1 & (Q2 & Q3))   strength = 1.0

Problem #17
figure 18 -- the paradox of the preface, using logic.
Given premises:
     P1    justification = 1.0
     P2    justification = 1.0
     P3    justification = 1.0
     S    justification = 1.0
     T    justification = 1.0
Ultimate epistemic interests:
     (Q1 & (Q2 & Q3))    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {P1} ||=> Q1   strength = 1.0
      pf-reason_2:   {P2} ||=> Q2   strength = 1.0
      pf-reason_3:   {P3} ||=> Q3   strength = 1.0
      pf-reason_4:   {S} ||=> R   strength = 1.0
      pf-reason_5:   {T} ||=> ~(Q1 & (Q2 & Q3))   strength = 1.0
      pf-reason_6:   {S1} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0
      pf-reason_7:   {S2} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0
      pf-reason_8:   {S3} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_4:   {R , Q1 , Q3} ||=> S2   strength = 1.0
      con-reason_5:   {R , Q2 , Q3} ||=> S1   strength = 1.0
      con-reason_6:   {R , Q1 , Q2} ||=> S3   strength = 1.0

Problem #18
This uses contradiction-inversion.
Given premises:
     B    justification = 1
     A    justification = 1
     C    justification = 1
Ultimate epistemic interests:
     Q    interest = .7

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A , B} ||=> P   strength = .7
      pf-reason_2:   {C} ||=> ~Q   strength = .8

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {P} ||=> Q   strength = 1.0

Problem #19
Four-way collective defeat.
Given premises:
     A1    justification = 1
     B1    justification = 1
     C1    justification = 1
     D1    justification = 1
Ultimate epistemic interests:
     P1    interest = .7
     Q1    interest = .7
     R1    interest = .7
     S1    interest = .7

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A1} ||=> P1   strength = .7
      pf-reason_2:   {B1} ||=> Q1   strength = .7
      pf-reason_3:   {C1} ||=> R1   strength = .7
      pf-reason_4:   {D1} ||=> S1   strength = .7

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {P1,Q1,R1} ||=> ~S1   strength = 1.0
      con-reason_2:   {P1,Q1,S1} ||=> ~R1   strength = 1.0
      con-reason_3:   {S1,Q1,R1} ||=> ~P1   strength = 1.0
      con-reason_4:   {P1,S1,R1} ||=> ~Q1   strength = 1.0

Problem #20
Two copies of four-way collective defeat.
Given premises:
     A1    justification = 1
     B1    justification = 1
     C1    justification = 1
     D1    justification = 1
     A2    justification = 1
     B2    justification = 1
     C2    justification = 1
     D2    justification = 1
Ultimate epistemic interests:
     P1    interest = .7
     Q1    interest = .7
     R1    interest = .7
     S1    interest = .7
     P2    interest = .7
     Q2    interest = .7
     R2    interest = .7
     S2    interest = .7

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A1} ||=> P1   strength = .7
      pf-reason_2:   {B1} ||=> Q1   strength = .7
      pf-reason_3:   {C1} ||=> R1   strength = .7
      pf-reason_4:   {D1} ||=> S1   strength = .7
      pf-reason_5:   {A2} ||=> P2   strength = .7
      pf-reason_6:   {B2} ||=> Q2   strength = .7
      pf-reason_7:   {C2} ||=> R2   strength = .7
      pf-reason_8:   {D2} ||=> S2   strength = .7

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {P1,Q1,R1} ||=> ~S1   strength = 1.0
      con-reason_2:   {P1,Q1,S1} ||=> ~R1   strength = 1.0
      con-reason_3:   {S1,Q1,R1} ||=> ~P1   strength = 1.0
      con-reason_4:   {P1,S1,R1} ||=> ~Q1   strength = 1.0
      con-reason_5:   {P2,Q2,R2} ||=> ~S2   strength = 1.0
      con-reason_6:   {P2,Q2,S2} ||=> ~R2   strength = 1.0
      con-reason_7:   {S2,Q2,R2} ||=> ~P2   strength = 1.0
      con-reason_8:   {P2,S2,R2} ||=> ~Q2   strength = 1.0

Problem #21

Given premises:
Ultimate epistemic interests:
     ((p -> q) <-> (~q -> ~p))    interest = 1.0

Problem #22

Given premises:
Ultimate epistemic interests:
     (~~p <-> p)    interest = 1.0

Problem #23

Given premises:
Ultimate epistemic interests:
     (~(p -> q) -> (q -> p))    interest = 1.0

Problem #24

Given premises:
Ultimate epistemic interests:
     ((~p -> q) <-> (~q -> p))    interest = 1.0

Problem #25

Given premises:
Ultimate epistemic interests:
     (((p v q) -> (p v r)) -> (p v (q -> r)))    interest = 1.0

Problem #26

Given premises:
Ultimate epistemic interests:
     (p v ~p)    interest = 1.0

Problem #27

Given premises:
Ultimate epistemic interests:
     (p v ~~~p)    interest = 1.0

Problem #28

Given premises:
Ultimate epistemic interests:
     (((p -> q) -> p) -> p)    interest = 1.0

Problem #29

Given premises:
Ultimate epistemic interests:
     (((p v q) & ((~p v q) & (p v ~q))) -> ~(~p v ~q))    interest = 1.0

Problem #30

Given premises:
     (q -> r)    justification = 1.0
     (r -> (p & q))    justification = 1.0
     (p -> (q v r))    justification = 1.0
Ultimate epistemic interests:
     (p <-> q)    interest = 1.0

Problem #31

Given premises:
Ultimate epistemic interests:
     (p <-> p)    interest = 1.0

Problem #32

Given premises:
Ultimate epistemic interests:
     (((p <-> q) <-> r) <-> (p <-> (q <-> r)))    interest = 1.0

Problem #33

Given premises:
Ultimate epistemic interests:
     ((p v (q & r)) <-> ((p v q) & (p v r)))    interest = 1.0

Problem #34

Given premises:
Ultimate epistemic interests:
     ((p <-> q) <-> ((q v ~p) & (~q v p)))    interest = 1.0

Problem #35

Given premises:
Ultimate epistemic interests:
     ((p <-> q) -> (~p v q))    interest = 1.0

Problem #36

Given premises:
Ultimate epistemic interests:
     ((p -> q) v (q -> p))    interest = 1.0

Problem #37

Given premises:
Ultimate epistemic interests:
     (((p & (q -> r)) -> s) <-> ((~p v (q v s)) & (~p v (~r v s))))    interest = 1.0

Problem #41
Given premises:
    (all x)(F x)    justification = 1.0

Ultimate epistemic interests:
    (some x)(F x)    interest = 1.0

Problem #42
Given premises:
    (some x)(all y)(F x y)    justification = 1.0

Ultimate epistemic interests:
    (all y)(some x)(F x y)    interest = 1.0

Problem #43
Given premises:
    (all x)((P x) -> ~(P x))    justification = 1.0

Ultimate epistemic interests:
    ~(P a)    interest = 1.0

Problem #44
Given premises:
    (all x)[(F x) -> ((H x) & ~(G x))]    justification = 1.0

Ultimate epistemic interests:
    ((G a) -> ~(F a))    interest = 1.0

Problem #45
Given premises:
    (all x)((H x) -> (G x))    justification = 1.0

Ultimate epistemic interests:
    [((H a) -> (G a)) & ~(~(G b) & (H b))]    interest = 1.0

Problem #46
Given premises:
    (all x)[(P x) <-> ((H x) & ~(P x))]    justification = 1.0

Ultimate epistemic interests:
    (all x)~(H x)    interest = 1.0

Problem #47
Given premises:
    (all x)(F x)    justification = 1.0
    (all x)((F x) -> (G x))    justification = 1.0

Ultimate epistemic interests:
    (all x)(G x)    interest = 1.0

Problem #48
Given premises:
    (F a)    justification = 1.0

Ultimate epistemic interests:
    (some x)((F x) v (G x))    interest = 1.0

Problem #49
Given premises:
    (some x)(F x)    justification = 1.0

Ultimate epistemic interests:
    (some x)((F x) v (G x))    interest = 1.0

Problem #50
Given premises:
    (some x)((F x) v (G x))    justification = 1.0
    ~(some x)(F x)    justification = 1.0

Ultimate epistemic interests:
    (some x)(G x)    interest = 1.0

Problem #51
Given premises:
    [(some x)(F x) -> (all y)(G y)]    justification = 1.0

Ultimate epistemic interests:
    (all x)(all y)[(F x) -> (G y)]    interest = 1.0

Problem #52
Given premises:
    (all x)[(F x) -> ((G x) -> (H x))]    justification = 1.0

Ultimate epistemic interests:
    [(all x)((F x) -> (G x)) -> (all x)((F x) -> (H x))]    interest = 1.0

Problem #53
Given premises:
    (all x)[(F x) -> (some y)((F y) & (G x y))]    justification = 1.0

Ultimate epistemic interests:
    (all x)[(F x) -> (some y)(some z)((G x y) & (G y z))]    interest = 1.0

Problem #54
Given premises:
    (all x)(some y)(R x y)    justification = 1.0
    (all x)(all y)((R x y) -> (R y x))    justification = 1.0
    (all x)(all y)(all z)([(R x y) & (R y z)] -> (R x z))    justification = 1.0

Ultimate epistemic interests:
    (all x)(R x x)    interest = 1.0

Problem #55
Given premises:

Ultimate epistemic interests:
    [(all x)(F x) -> (some x)(F x)]    interest = 1.0

Problem #56
Given premises:

Ultimate epistemic interests:
    (some x)[(F x) -> (all y)(F y)]    interest = 1.0

Problem #57
Given premises:

Ultimate epistemic interests:
    [(all x)(all y)((R x y) -> ~(R y x)) -> ~(some x)(R x x)]    interest = 1.0

Problem #58
Given premises:

Ultimate epistemic interests:
    ~(some x)(all y)((R x y) <-> ~(R y y))    interest = 1.0

Problem #59
Given premises:

Ultimate epistemic interests:
    ~(all x)[((F x) v ~(F x)) -> ~((F x) v ~(F x))]    interest = 1.0

Problem #60
Given premises:

Ultimate epistemic interests:
    [(some x)((F x) v (G x)) <-> [(some x)(F x) v (some x)(G x)]]    interest = 1.0

Problem #61
Given premises:

Ultimate epistemic interests:
    [(all x)((F x) & (G x)) <-> [(all x)(F x) & (all x)(G x)]]    interest = 1.0

Problem #62
Given premises:

Ultimate epistemic interests:
    [(all x)((F x) -> (G x)) -> ((all x)(F x) -> (all x)(G x))]    interest = 1.0

Problem #63
Given premises:

Ultimate epistemic interests:
    [(P -> (all x)(F x)) <-> (all x)(P -> (F x))]    interest = 1.0

Problem #64
Given premises:

Ultimate epistemic interests:
    [(P -> (some x)(F x)) <-> (some x)(P -> (F x))]    interest = 1.0

Problem #65
Given premises:

Ultimate epistemic interests:
    [((all x)(F x) -> P) <-> (some x)((F x) -> P)]    interest = 1.0

Problem #66
Given premises:

Ultimate epistemic interests:
    (all x)((F x) v ~(F x))    interest = 1.0

Problem #67
Given premises:

Ultimate epistemic interests:
    (some x)((F x) v ~(F x))    interest = 1.0

Problem #68
Given premises:

Ultimate epistemic interests:
    (some y)((F a y) <-> (F y y))    interest = 1.0

Problem #69
Given premises:

Ultimate epistemic interests:
    (all x)(some y)((F x y) <-> (F y y))    interest = 1.0

Problem #70
     Pelletier's problem 18
Given premises:

Ultimate epistemic interests:
    (some y)(all x)((F y) -> (F x))    interest = 1.0

Problem #71
     Pelletier's problem 19
Given premises:

Ultimate epistemic interests:
    (some x)(all y)(all z)(((P y) -> (Q z)) -> ((P x) -> (Q x)))    interest = 1.0

Problem #72
     Pelletier's problem 20
Given premises:

Ultimate epistemic interests:
    [(all x)(all y)(some z)(all w)(((P x) & (Q y)) -> ((R z) & (S w)))
                  -> ((some v1)(some u)((P v1) & (Q u)) -> (some s)(R s))]    interest = 1.0

Problem #73
     Pelletier's problem 21
Given premises:
    (some x)(p -> (F x))    justification = 1.0
    (some x)((F x) -> p)    justification = 1.0

Ultimate epistemic interests:
    (some x)(p <-> (F x))    interest = 1.0

Problem #74
     Pelletier's problem 22
Given premises:

Ultimate epistemic interests:
    [(all x)(p <-> (F x)) -> (p <-> (all y)(F y))]    interest = 1.0

Problem #75
     Pelletier's problem 23
Given premises:

Ultimate epistemic interests:
    [(all x)(p v (F x)) <-> (p v (all y)(F y))]    interest = 1.0

Problem #76
     Pelletier's problem 24
Given premises:
    ~(some x)((S x) & (Q x))    justification = 1.0
    (all x)((P x) -> ((Q x) v (R x)))    justification = 1.0
    [~(some x)(P x) -> (some y)(Q y)]    justification = 1.0
    (all x)(((Q x) v (R x)) -> (S x))    justification = 1.0

Ultimate epistemic interests:
    (some x)((P x) & (R x))    interest = 1.0

Problem #77
     Pelletier's problem 25
Given premises:
    (some x)(P x)    justification = 1.0
    (all x)((F x) -> (~(G x) & (R x)))    justification = 1.0
    (all x)((P x) -> ((G x) & (F x)))    justification = 1.0
    [(all x)((P x) -> (Q x)) v (some y)((P y) & (R y))]    justification = 1.0

Ultimate epistemic interests:
    (some x)((Q x) & (P x))    interest = 1.0

Problem #78
     Pelletier's problem 26
Given premises:
    [(some x)(P x) <-> (some y)(Q y)]    justification = 1.0
    (all x)(all y)(((P x) & (Q y)) -> ((R x) <-> (S y)))    justification = 1.0

Ultimate epistemic interests:
    [(all x)((P x) -> (R x)) <-> (all y)((Q y) -> (S y))]    interest = 1.0

Problem #79
     Pelletier's problem 27
Given premises:
    (some x)((F x) & ~(G x))    justification = 1.0
    (all x)((F x) -> (H x))    justification = 1.0
    (all x)(((J x) & (I x)) -> (F x))    justification = 1.0
    [(some x)((H x) & ~(G x)) -> (all y)((I y) -> ~(H y))]    justification = 1.0

Ultimate epistemic interests:
    (all x)((J x) -> ~(I x))    interest = 1.0

Problem #80
     Pelletier's problem 28
Given premises:
    (all x)[(P x) -> (all x)(Q x)]    justification = 1.0
    [(all x)((Q x) v (R x)) -> (some y)((Q y) & (S y))]    justification = 1.0
    [(some x)(S x) -> (all x)((F x) -> (G x))]    justification = 1.0

Ultimate epistemic interests:
    (all x)[((P x) & (F x)) -> (G x)]    interest = 1.0

Problem #81
     Pelletier's problem 29
Given premises:
    [(some x)(F x) & (some y)(G y)]    justification = 1.0

Ultimate epistemic interests:
    ([(all x)((F x) -> (H x)) & (all y)((G y) -> (J y))] <->
          (all z)(all w)(((F z) & (G w)) -> ((H z) & (J w))))    interest = 1.0

Problem #82
     Pelletier's problem 30
Given premises:
    (all x)(((F x) v (G x)) -> ~(H x))    justification = 1.0
    (all x)(((G x) -> ~(I x)) -> ((F x) & (H x)))    justification = 1.0

Ultimate epistemic interests:
    (all x)(I x)    interest = 1.0

Problem #83
     Pelletier's problem 31
Given premises:
    ~(some x)((F x) & ((G x) v (H x)))    justification = 1.0
    (some x)((I x) & (F x))    justification = 1.0
    (all x)(~(H x) -> (J x))    justification = 1.0

Ultimate epistemic interests:
    (some x)((I x) & (J x))    interest = 1.0

Problem #84
     Pelletier's problem 32
Given premises:
    (all x)(((F x) & ((G x) v (H x))) -> (I x))    justification = 1.0
    (all x)(((I x) & (H x)) -> (J x))    justification = 1.0
    (all x)((K x) -> (H x))    justification = 1.0

Ultimate epistemic interests:
    (all x)(((F x) & (K x)) -> (J x))    interest = 1.0

Problem #85
     Pelletier's problem 33
Given premises:

Ultimate epistemic interests:
    [(all x)[((P a) & ((P x) -> (P b))) -> (P c)] <->
                  (all x)((~(P a) v ((P x) v (P c))) & (~(P a) v (~(P b) v (P c))))]    interest = 1.0

Problem #86
     Half of Pelletier's problem 34
     TODO this *may* be buggy in OSCAR
Given premises:

Ultimate epistemic interests:
    [[(some x)(all y)((P x) <-> (P y)) <-> ((some z)(Q z) <-> (all w)(Q w))] ->
              [(some u)(all v1)((Q u) <-> (Q v1)) <-> ((some r)(P r) <-> (all s)(P s))]]    interest = 1.0

Problem #87
     Pelletier's problem 35
Given premises:

Ultimate epistemic interests:
    (some u)(some v1)[(P u v1) -> (all x)(all y)(P x y)]    interest = 1.0

Problem #88
     Pelletier's problem 36
Given premises:
    (all x)(some y)(F x y)    justification = 1.0
    (all x)(some z)(G x z)    justification = 1.0
    (all x)(all y)[((F x y) v (G x y)) -> (all z)(((F y z) v (G y z)) -> (H x z))]    justification = 1.0

Ultimate epistemic interests:
    (all x)(some y)(H x y)    interest = 1.0

Problem #89
     Pelletier's problem 37
Given premises:
    (all z)(some w)(all x)(some y)[[((P x z) -> (P y w)) & (P y z)] &
               [(P y w) -> (some u)(Q u w)]]    justification = 1.0
    (all x)(all z)[~(P x z) -> (some v1)(Q v1 z)]    justification = 1.0
    [(some y)(some s)(Q y s) -> (all x)(R x x)]    justification = 1.0

Ultimate epistemic interests:
    (all x)(some y)(R x y)    interest = 1.0

Problem #90
     Pelletier's problem 38
Given premises:

Ultimate epistemic interests:
    [(all x)[[(P a) & ((P x) -> (some y)((P y) & (R x y)))] ->
                  (some z)(some w)[(P z) & ((R x w) & (R w z))]] <->
                     (all x)[[(~(P a) v (P x)) v (some z)(some w)((P z) & ((R x w) & (R w z)))] &
                    [~(P a) v (~(some y)((P y) & (R x y)) v
                     (some z)(some w)((P z) & ((R x w) & (R w z))))]]]    interest = 1.0

Problem #91
     Pelletier's problem 39
Given premises:

Ultimate epistemic interests:
    ~(some x)(all y)((F y x) <-> ~(F y y))    interest = 1.0

Problem #92
     Pelletier's problem 40
Given premises:

Ultimate epistemic interests:
    [(some y)(all x)((F x y) <-> (F x x)) -> ~(all z)(some w)(all v1)((F v1 w) <-> ~(F v1 z))]    interest = 1.0

Problem #93
     Pelletier's problem 41
Given premises:
    (all z)(some y)(all x)[(F x y) <-> ((F x z) & ~(F x x))]    justification = 1.0

Ultimate epistemic interests:
    ~(some z)(all x)(F x z)    interest = 1.0

Problem #94
     Pelletier's problem 42
Given premises:

Ultimate epistemic interests:
    ~(some y)(all x)[(F x y) <-> ~(some z)((F x z) & (F z x))]    interest = 1.0

Problem #95
     Pelletier's problem 43
Given premises:
    (all x)(all y)[(Q x y) <-> (all z)((F z x) <-> (F z y))]    justification = 1.0

Ultimate epistemic interests:
    (all x)(all y)[(Q x y) <-> (Q y x)]    interest = 1.0

Problem #96
     Pelletier's problem 44
Given premises:
    (all x)[[(F x) -> (some y)((G y) & (H x y))] & (some y)((G y) & ~(H x y))]    justification = 1.0
    (some x)[(J x) & (all y)[(G y) -> (H x y)]]    justification = 1.0

Ultimate epistemic interests:
    (some x)((J x) & ~(F x))    interest = 1.0

Problem #97
     Pelletier's problem 45
Given premises:
    (all x)[[(F x) & (all y)[((G y) & (H x y)) -> (J x y)]] ->
                (all y)[((G y) & (H x y)) -> (K y)]]    justification = 1.0
    ~(some y)((L y) & (K y))    justification = 1.0
    (some x)[[(F x) & (all y)((H x y) -> (L y))] &
             (all y)(((G y) & (H x y)) -> (J x y))]    justification = 1.0

Ultimate epistemic interests:
    (some x)((F x) & ~(some y)((G y) & (H x y)))    interest = 1.0

Problem #98
     Pelletier's problem 46
Given premises:
    (all x)([(F x) & (all y)[((F y) & (H y x)) -> (G y)]] -> (G x))    justification = 1.0
    [(some x)((F x) & ~(G x)) ->
             (some x)(((F x) & ~(G x)) & (all y)(((F y) & ~(G y)) -> (J x y)))]    justification = 1.0
    (all x)(all y)[[((F x) & (F y)) & (H x y)] -> ~(J y x)]    justification = 1.0

Ultimate epistemic interests:
    (all x)((F x) -> (G x))    interest = 1.0

Problem #99
     Pelletier's problem 47
Given premises:
    (all x)((W x) -> (A x))    justification = 1.0
    (all x)((F x) -> (A x))    justification = 1.0
    (all x)((B x) -> (A x))    justification = 1.0
    (all x)((C x) -> (A x))    justification = 1.0
    (all x)((S x) -> (A x))    justification = 1.0
    (some w0)(W w0)    justification = 1.0
    (some f0)(F f0)    justification = 1.0
    (some b0)(B b0)    justification = 1.0
    (some c0)(C c0)    justification = 1.0
    (some s0)(S s0)    justification = 1.0
    (some g0)(G g0)    justification = 1.0
    (all x)((G x) -> (P x))    justification = 1.0
    (all x)[(A x) -> [(all w)((P w) -> (E x w)) v
             (all y)(((A y) & ((M y x) & (some z)((P z) & (E y z)))) -> (E x y))]]    justification = 1.0
    (all x)(all y)[((C x) & (B y)) -> (M x y)]    justification = 1.0
    (all x)(all y)[((S x) & (B y)) -> (M x y)]    justification = 1.0
    (all x)(all y)[((B x) & (F y)) -> (M x y)]    justification = 1.0
    (all x)(all y)[((F x) & (W y)) -> (M x y)]    justification = 1.0
    (all x)(all y)[((W x) & (F y)) -> ~(E x y)]    justification = 1.0
    (all x)(all y)[((W x) & (G y)) -> ~(E x y)]    justification = 1.0
    (all x)(all y)[((B x) & (C y)) -> (E x y)]    justification = 1.0
    (all x)(all y)[((B x) & (S y)) -> ~(E x y)]    justification = 1.0
    (all x)[(C x) -> (some y)((P y) & (E x y))]    justification = 1.0
    (all x)[(S x) -> (some y)((P y) & (E x y))]    justification = 1.0

Ultimate epistemic interests:
    (some x)(some y)[[(A x) & (A y)] & (some z)[(E x y) & ((G z) & (E y z))]]    interest = 1.0

Problem #100
     Pelletier's problem 57
Given premises:
    (F (g a b) (g b c))    justification = 1.0
    (F (g b c) (g a c))    justification = 1.0
    (all x)(all y)(all z)[[(F x y) & (F y z)] -> (F x z)]    justification = 1.0

Ultimate epistemic interests:
    (F (g a b) (g a c))    interest = 1.0

Problem #102
Given premises:

Ultimate epistemic interests:
    [(all x)[((F a) & ((F x) -> (F (g x)))) -> (F (g (g x)))] ->
          (all x)[[(~(F a) v (F x)) v (F (g (g x)))] &
               [(~(F a) v ~(F (g x))) v (F (g (g x)))]]]    interest = 1.0

Problem #103
     The unintuitive problem
Given premises:
    (all x)(all y)(all z)([(P x y) & (P y z)] -> (P x z))    justification = 1.0
    (all x)(all y)(all z)([(Q x y) & (Q y z)] -> (Q x z))    justification = 1.0
    (all x)(all y)((Q x y) -> (Q y x))    justification = 1.0
    (all x)(all y)(~(P x y) -> (Q x y))    justification = 1.0
    ~(P a b)    justification = 1.0

Ultimate epistemic interests:
    (Q c d)    interest = 1.0

Problem #104
     Chang and Lee problem 3
Given premises:
    (all x)(P x e x)    justification = 1.0
    (all x)(P e x x)    justification = 1.0
    (all x)(all y)(all z)(all u)(all v1)(all w)[((P x y u) & ((P y z v1) & (P u z w))) -> (P x v1 w)]    justification = 1.0
    (all x)(all y)(all z)(all u)(all v1)(all w)[((P x y u) & ((P y z v1) & (P x v1 w))) -> (P u z w)]    justification = 1.0
    (all x)(P x x e)    justification = 1.0
    (P a b c)    justification = 1.0

Ultimate epistemic interests:
    (P b a c)    interest = 1.0
"
	  ))

#| This is similar to def-forwards-reason except that it does not put the reason into
*forwards-substantive-reasons*. |#
(defmacro define-forwards-reason
  (name &key reason-forwards-premises reason-backwards-premises conclusion
        (strength 1.0) variables defeasible? description)
  ; (setf n name fp reason-forwards-premises bp reason-backwards-premises c conclusion v variables d defeasible?)
  ; (break)
  #| (step (define-forwards-reason n :reason-forwards-premises (eval fp) :reason-backwards-premises (eval bp)
                                   :conclusion (eval c) :variables (eval v) :defeasible? (eval d)))  |#
  (when (stringp name) (setf name (read-from-string name)))

  `(progn
     (proclaim (list 'special ',name))

     (setf ,name
           (make-forwards-reason
             :reason-name ',name
             :reason-forwards-premises (rectify-forwards-premises* ,reason-forwards-premises ,variables)
             :reason-backwards-premises (rectify-backwards-premises* ,reason-backwards-premises ,variables)
             :reason-conclusions ,conclusion
             :reason-conclusions-function (conclusion-instantiator ,conclusion ,variables ,defeasible?)
             :reason-variables ,variables
             :reason-strength ,strength
             :reason-defeasible-rule ,defeasible?
             :reason-description ,description))
     ,name))

(defun rectify-forwards-premises* (premise-list variables)
  (if premise-list
    (let ((premises nil)
          (used-premise-variables nil))
      (loop
        (let* ((premise (car premise-list))
               (formula (car premise))
               (premise-variables (subset #'(lambda (v) (occur* v formula)) variables))
               (premise-variables* (intersection premise-variables used-premise-variables))
               (binding-function (binding-function formula premise-variables)))
          (setf premise-list (cdr premise-list))
          (push
            (make-forwards-premise
              :formula formula
              :condition (mem2 premise)
              :binding-function (eval binding-function)
              :variables premise-variables
              :instantiator (reason-instantiator formula premise-variables*))
            premises)
          (setf used-premise-variables
                (union used-premise-variables premise-variables)))
        (when (null premise-list) (return (reverse premises)))))))

#| This is similar to def-backwards-reason except that it does not put the reason into
*backwards-substantive-reasons*. |#

(defmacro define-backwards-reason
  (name &key reason-forwards-premises reason-backwards-premises conclusion (strength 1.0)
        condition variables defeasible? description)
  (when (stringp name) (setf name (read-from-string name)))

  `(progn
     (proclaim (list 'special ',name))

     (let* ((c-vars (remove-if-not #'(lambda (v) (occur* v ,conclusion)) ,variables))
            (c-binding-function (eval (binding-function ,conclusion c-vars))))
       (setf ,name
             (make-backwards-reason
               :reason-name ',name
               :reason-forwards-premises (rectify-forwards-premises* ,reason-forwards-premises ,variables)
               :reason-backwards-premises (rectify-backwards-premises* ,reason-backwards-premises ,variables)
               :reason-conclusions (list ,conclusion)
               :reason-conclusions-function (conclusion-instantiator ,conclusion ,variables ,defeasible?)
               :reason-variables ,variables
               :reason-strength ,strength
               :reason-defeasible-rule ,defeasible?
               :b-reason-conclusion-variables c-vars
               :b-reason-conclusions-binding-function c-binding-function
               :b-reason-condition ,condition
               :reason-description ,description)))
     ,name))

(defun rectify-backwards-premises* (premise-list variables)
  (if premise-list
    (let ((premises nil))
      (loop
        (let* ((premise* (car premise-list))
               (premise (car premise*))
               (premise-variables (subset #'(lambda (v) (occur* v premise)) variables))
               (condition1 (mem1 (mem2 premise*)))
               (condition2 (mem2 (mem2 premise*))))
          (setf premise-list (cdr premise-list))
          (push
            (make-backwards-premise
              :formula premise
              :condition1 condition1
              :condition2 condition2
              :instantiator (reason-instantiator premise premise-variables))
            premises))
        (when (null premise-list) (return (reverse premises)))))))

#| This displays the problems in *problems* in readable form.  If n is non-nill,
it displays just problem n. |#
(defun display-problems (&optional n)
  (cond ((null n)
         (dolist (P *problems*) (display-problem P)))
        (t (display-problem (assoc n *problems*)))))

#| This finds the first occurrence (if any) of string1 in string2, and returns the next position
after the end of string1.  If string1 does not occur in string2, this returns nil.  The comparison
is not case-sensitive unless case-sensitive is set to t. |#
(defun find-string (string1 string2 &optional case-sensitive)
  (let ((length (length string1))
        (position (search string1 string2 :test (if case-sensitive 'string= 'string-equal))))
    (when position (+ length position))))
;                      INFERENCE-RULES FOR THE PROPOSITIONAL
;                                                 AND PREDICATE CALCULI

(proclaim '(special simp neg-elim neg-disj neg-condit  neg-bicondit-simp
                    DM bicondit-simp modus-ponens1 modus-ponens2 modus-tollens1
                    modus-tollens2 disj-syl11 disj-syl12 disj-syl21 disj-syl22
                    exportation E-removal A-removal E2-removal A2-removal
                    adjunction neg-intro i-neg-disj i-neg-condit i-neg-bicondit
                    bicondit-intro disj-cond  i-DM conditionalization reductio
                    neg-ug neg-eg i-neg-ug i-neg-eg ui ei ug eg
                    disj-cond-2 disj-antecedent-simp negation-in
                    disj-simp contraposition i-contraposition conditional-modus-tollens
                    undercutter-permutation cond-antecedent-simp
                    cond-simp1 cond-simp2
                    ))

; Forwards inference rules:

(setf simp
      (make-forwards-reason
        :reason-name "simp"
        :reason-forwards-premises (list (cfp '(& P Q) '(P Q)))
        :reason-variables '(P Q)))

(defun simp (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let ((p (hypernode-formula c)))
      (draw-conclusion (conjunct1 p) (list c) simp (list t) 1.0 depth nil nil)
      (draw-conclusion (conjunct2 p) (list c) simp (list t) 1.0 depth nil nil))))

(setf (reason-function simp) #'simp)

(setf neg-elim
      (make-forwards-reason
        :reason-name "neg-elim"
        :reason-forwards-premises (list (cfp '(~ (~ P)) '(P)))
        :reason-variables '(P)))

(defun neg-elim (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion (negand (negand p)) (list c) neg-elim (list t) 1.0 depth nil nil))))

(setf (reason-function neg-elim) #'neg-elim)

(setf neg-disj
      (make-forwards-reason
        :reason-name "neg-disj"
        :reason-forwards-premises (list (cfp '(~ (v P Q)) '(P Q)))
        :reason-variables '(P Q)))

(defun neg-disj (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion (neg (disjunct1 (negand p))) (list c) neg-disj (list t) 1.0 depth nil nil)
      (draw-conclusion (neg (disjunct2 (negand p))) (list c) neg-disj (list t) 1.0 depth nil nil))))

(setf (reason-function neg-disj) #'neg-disj)

(setf neg-condit
      (make-forwards-reason
        :reason-name "neg-condit"
        :reason-forwards-premises (list (cfp '(~ (-> P Q)) '(P Q)))
        :reason-variables '(P Q)))

(defun neg-condit (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion (antecedent (negand p)) (list c) neg-condit (list t) 1.0 depth nil nil)
      (draw-conclusion (neg (consequent (negand p))) (list c) neg-condit (list t) 1.0 depth nil nil))))

(setf (reason-function neg-condit) #'neg-condit)

#| This form must be used to make invert-contradictors work properly by only computing
contradictors in cases syntactically appropriate for adopting reductio-interests. |#

(setf neg-bicondit-simp
      (make-forwards-reason
        :reason-name "neg-bicondit-simp"
        :reason-forwards-premises (list (cfp '(~ (<-> P Q)) '(P Q)))
        :reason-variables '(P Q)))

(defun neg-bicondit-simp (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    "~(P <-> Q) implies (~P <-> Q)"
    (let* ((p (hypernode-formula c)))
      (draw-conclusion
        (bicondit (neg (bicond1 (negand p))) (bicond2 (negand p)))
        (list c) neg-bicondit-simp (list t) 1.0 depth nil nil))))

(setf (reason-function neg-bicondit-simp) #'neg-bicondit-simp)

(setf DM
      (make-forwards-reason
        :reason-name "DM"
        :reason-forwards-premises (list (cfp '(~ (& P Q)) '(P Q)))
        :reason-variables '(P Q)))

(defun DM (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion
        (disj (neg (conjunct1 (negand p))) (neg (conjunct2 (negand p))))
        (list c) DM (list t) 1.0 depth nil nil))))

(setf (reason-function DM) #'DM)

(setf bicondit-simp
      (make-forwards-reason
        :reason-name "bicondit-simp"
        :reason-forwards-premises (list (cfp '(<-> P Q) '(P Q)))
        :reason-variables '(P Q)))

(defun bicondit-simp (c depth ip)
  (declare (ignore ip))
  ; (when (eq c (node 252)) (setf n c d depth i ip) (break))
  ;; (step (bicondit-simp n d i))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion (condit (bicond1 p) (bicond2 p)) (list c) bicondit-simp (list t) 1.0 depth nil nil)
      (draw-conclusion (condit (bicond2 p) (bicond1 p)) (list c) bicondit-simp (list t) 1.0 depth nil nil))))

(setf (reason-function bicondit-simp) #'bicondit-simp)

(setf exportation
      (make-forwards-reason
        :reason-name "exportation"
        :reason-forwards-premises (list (cfp '(-> (& P Q) R) '(P Q R)))
        :reason-variables '(P Q R)))

(defun exportation (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion
        (condit (conjunct1 (antecedent p))
                (condit (conjunct2 (antecedent p)) (consequent p)))
        (list c) exportation (list t) 1.0 depth nil nil))))

(setf (reason-function exportation) #'exportation)

(setf disj-antecedent-simp
      (make-forwards-reason
        :reason-name "disj-antecedent-simp"
        :reason-forwards-premises (list (cfp '(-> (v P Q) R) '(P Q R)))
        :reason-variables '(P Q R)))

(defun disj-antecedent-simp (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (when (and (conditionalp p)
                 (disjunctionp (antecedent p)))
        (draw-conclusion (condit (disjunct1 (antecedent p)) (consequent p))
                         (list c) disj-antecedent-simp (list t) 1.0 depth nil nil)
        (draw-conclusion (condit (disjunct2 (antecedent p)) (consequent p))
                         (list c) disj-antecedent-simp (list t) 1.0 depth nil nil)))))

(setf (reason-function disj-antecedent-simp) #'disj-antecedent-simp)

(setf cond-antecedent-simp
      (make-forwards-reason
        :reason-name "cond-antecedent-simp"
        :reason-forwards-premises (list (cfp '(-> (-> P Q) R) '(P Q R)))
        :reason-variables '(P Q R)))

(defun cond-antecedent-simp (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (when (and (conditionalp p)
                 (conditionalp (antecedent p)))
        (draw-conclusion (condit (neg (antecedent (antecedent p))) (consequent p))
                         (list c) cond-antecedent-simp (list t) 1.0 depth nil nil)
        (draw-conclusion (condit (consequent (antecedent p)) (consequent p))
                         (list c) cond-antecedent-simp (list t) 1.0 depth nil nil)))))

(setf (reason-function cond-antecedent-simp) #'cond-antecedent-simp)

(defun neg-in (P)
  (cond ((u-genp P)
         (list 'some (mem2 P) (neg-in (mem3 P))))
        ((e-genp P)
         (list 'all (mem2 P) (neg-in (mem3 P))))
        ((negationp P) (negand P))
        ((conjunctionp P) (disj (neg-in (conjunct1 P)) (neg-in (conjunct2 P))))
        ((disjunctionp P) (conj (neg-in (disjunct1 P)) (neg-in (disjunct2 P))))
        ((conditionalp P) (conj (antecedent P) (neg-in (consequent P))))
        ((biconditionalp P)
         (disj (conj (bicond1 P) (bicond2 P))
               (conj (neg-in (bicond1 P)) (neg-in (bicond2 P)))))
        (t (neg P))))

(setf disj-simp
      (make-forwards-reason
        :reason-name "disj-simp"
        :reason-forwards-premises (list (cfp '(v P Q) '(P Q)))
        :reason-variables '(P Q)))

(defun disj-simp (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (draw-conclusion (condit (neg-in (disjunct1 p)) (disjunct2 p))
                       (list c) disj-simp (list t) 1.0 depth nil nil))))

(setf (reason-function disj-simp) #'disj-simp)

(setf cond-simp1
      (make-forwards-reason
        :reason-name "cond-simp1"
        :reason-forwards-premises (list (cfp '(-> P (~ P)) '(P)))
        :reason-variables '(P)))

(defun cond-simp1 (c depth ip)
  (declare (ignore ip))
  ; (when (eq c (node 248)) (setf n c d depth i ip) (break))
  ;; (step (cond-simp1 n d i))
  (when (is-inference c)
    (let* ((p (hypernode-formula c))
           (q (consequent p)))
      (when (negationp q)
        (let ((match
                (catch 'unifier
                       (parallelize-match
                         (mgu (antecedent p) (negand q) (hypernode-variables c)) (hypernode-variables c)))))
          (when match
            (draw-conclusion
              (match-sublis match q) (list c) cond-simp1
              (list match) 1.0 depth nil nil)
            ))))))

(setf (reason-function cond-simp1) #'cond-simp1)

(setf cond-simp2
      (make-forwards-reason
        :reason-name "cond-simp2"
        :reason-forwards-premises (list (cfp '(-> (~ P) P) '(P)))
        :reason-variables '(P)))

(defun cond-simp2 (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c))
           (q (antecedent p)))
      (let ((match
              (catch 'unifier
                     (parallelize-match
                       (mgu (negand q) (consequent p) (hypernode-variables c)) (hypernode-variables c)))))
        (when match
          (draw-conclusion
            (match-sublis match (consequent p)) (list c) cond-simp2
            (list match) 1.0 depth nil nil)
          )))))

(setf (reason-function cond-simp2) #'cond-simp2)

(setf E-removal
      (make-forwards-reason
        :reason-name "E-removal"
        :reason-forwards-premises (list (cfp '(-> (some x P) Q) '(P Q)))
        :reason-variables '(P Q)))

(defun E-removal (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (let* ((new-var (gensym "z")))
        (draw-conclusion
          (u-gen new-var
                 (condit (subst new-var
                                (q-variable (antecedent p))
                                (q-matrix (antecedent p)))
                         (consequent p)))
          (list c) E-removal (list t) 1.0 depth nil nil)))))

(setf (reason-function E-removal) #'E-removal)

(setf A-removal
      (make-forwards-reason
        :reason-name "A-removal"
        :reason-forwards-premises (list (cfp '(-> (all x P) Q) '(P Q)))
        :reason-variables '(P Q)))

(defun A-removal (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (let* ((new-var (gensym "z")))
        (draw-conclusion
          (e-gen new-var
                 (condit (subst new-var
                                (q-variable (antecedent p))
                                (q-matrix (antecedent p)))
                         (consequent p)))
          (list c) A-removal (list t) 1.0 depth nil nil)))))

(setf (reason-function A-removal) #'A-removal)

(setf modus-ponens1
      (make-forwards-reason
        :reason-name "modus-ponens1"
        :reason-forwards-premises
        (list (cfp '(-> %P %Q) '(%P %Q))
              (cfp '%P '(%P)))
        :reason-conclusions '%Q
        :reason-variables '(%P %Q)))

(defun modus-ponens1 (c depth ip)
  ; (when (eq c (node 4)) (setf n c d depth i ip) (break))
  ;; (step (modus-ponens1 n d i))
  (when (is-inference c)
    (let* ((p (hypernode-formula c))
           (p-vars (hypernode-variables c)))
      (multiple-value-bind (profile term-list) (formula-code (antecedent p))
        (let* ((binding (list (cons '%p (antecedent p)) (cons '%q (consequent p))))
               (dn
                 (ip-d-node
                   (store-instantiated-premise
                     modus-ponens2 c nil binding (list t) ip (cdr (reason-forwards-premises modus-ponens1)) profile))))
          (dolist (c-list (d-node-c-lists dn))
            (when (c-list-processed-nodes c-list)
              (let ((unifier
                      (unifier (c-list-term-list c-list) term-list (c-list-variables c-list) p-vars)))
                (when unifier
                  (let ((formula (match-sublis (mem2 unifier) (consequent p))))
                    (dolist (c* (c-list-processed-nodes c-list))
                      (when (is-inference c*)
                        (draw-conclusion
                          formula (list c* c) modus-ponens1 unifier 1.0 depth nil nil)))))))))))))

(setf (reason-function modus-ponens1) #'modus-ponens1)

(setf modus-ponens2
      (make-forwards-reason
        :reason-name "modus-ponens2"
        :reason-forwards-premises
        (list (cfp '%P '(%P)))
        :reason-variables '(%P)))

(defun modus-ponens2 (c depth ip)
  ; (when (eq c (node 3)) (setf n c d depth i ip) (break))
  ;; (step (modus-ponens2 n d i))
  (when (is-inference c)
    (when (eq (ip-reason ip) modus-ponens2)
      (let* ((p (hypernode-formula c))
             (p-vars (hypernode-variables c))
             (node (mem1 (ip-basis ip)))
             (unifier
               (unifier p (cdr (mem1 (ip-binding ip))) p-vars (hypernode-variables node))))
        (when unifier
          (let ((formula (match-sublis (mem2 unifier) (cdr (mem2 (ip-binding ip))))))
            (draw-conclusion
              formula (list c node) modus-ponens2 unifier 1.0 depth nil nil)))))))

(setf (reason-function modus-ponens2) #'modus-ponens2)

(setf modus-tollens1
      (make-forwards-reason
        :reason-name "modus-tollens1"
        :reason-forwards-premises
        (list (cfp '(-> %P %Q) '(%P %Q))
              (cfp '(~ %Q) '(%Q)))
        :reason-conclusions '(~ %P)
        :reason-variables '(%P %Q)))

(defun modus-tollens1 (c depth ip)
  (when (is-inference c)
    (let* ((p (hypernode-formula c))
           (p-vars (hypernode-variables c)))
      (multiple-value-bind (profile term-list) (formula-code (neg (consequent p)))
        (let* ((binding (list (cons '%p (antecedent p)) (cons '%q (consequent p))))
               (dn
                 (ip-d-node
                   (store-instantiated-premise
                     modus-tollens2 c nil binding (list t) ip (cdr (reason-forwards-premises modus-tollens1)) profile))))
          (dolist (c-list (d-node-c-lists dn))
            (when (c-list-processed-nodes c-list)
              (let ((unifier
                      (unifier (c-list-term-list c-list) term-list (c-list-variables c-list) p-vars)))
                (when unifier
                  (let ((formula (match-sublis (mem2 unifier) (neg (antecedent p)))))
                    (dolist (c* (c-list-processed-nodes c-list))
                      (when (is-inference c*)
                        (draw-conclusion
                          formula (list c* c) modus-tollens1 unifier 1.0 depth nil nil)))))))))))))

(setf (reason-function modus-tollens1) #'modus-tollens1)

(setf modus-tollens2
      (make-forwards-reason
        :reason-name "modus-tollens2"
        :reason-forwards-premises
        (list (cfp '(~ %Q) '(%Q)))
        :reason-variables '(%Q)))

(defun modus-tollens2 (c depth ip)
  ; (when (eq c (node 136)) (setf n c d depth i ip) (break))
  ;; (step (modus-tollens2 n d i))
  (when (is-inference c)
    (when (eq (ip-reason ip) modus-tollens2)
      (let* ((p- (neg (hypernode-formula c)))
             (p-vars (hypernode-variables c))
             (node (mem1 (ip-basis ip)))
             (unifier
               (unifier p- (cdr (mem2 (ip-binding ip))) p-vars (hypernode-variables node))))
        (when unifier
          (let ((formula (match-sublis (mem2 unifier) (neg (cdr (mem1 (ip-binding ip)))))))
            (draw-conclusion
              formula (list c node) modus-tollens2 unifier 1.0 depth nil nil)))))))

(setf (reason-function modus-tollens2) #'modus-tollens2)

#| From (P -> Q) and (P -> ~Q), infer ~P. |#
(setf conditional-modus-tollens
      (make-forwards-reason
        :reason-name "conditional-modus-tollens"
        :reason-forwards-premises (list (cfp '(-> P Q) '(P Q)))
        :reason-variables '(P Q)))

(defun conditional-modus-tollens (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c))
           (p-vars (hypernode-variables c)))
      (let ((p- (condit (antecedent p) (neg (consequent p)))))
        (multiple-value-bind (profile term-list) (formula-code p-)
          (let ((dn (pursue-d-node-for profile *top-d-node*)))
            (when dn
              (dolist (c-list (d-node-c-lists dn))
                (when (c-list-processed-nodes c-list)
                  (let ((unifier
                          (unifier term-list (c-list-term-list c-list) p-vars (c-list-variables c-list))))
                    (when unifier
                      (let ((formula (match-sublis (mem1 unifier) (neg (antecedent p)))))
                        (dolist (c* (c-list-processed-nodes c-list))
                          (when (is-inference c*)
                            (draw-conclusion
                              formula (list c c*) conditional-modus-tollens
                              unifier 1.0 depth nil nil)))))))))))))))

(setf (reason-function conditional-modus-tollens) #'conditional-modus-tollens)

(setf neg-UG
      (make-forwards-reason
        :reason-name "neg-ug"
        :reason-forwards-premises (list (cfp '(~ (all x P)) '(P)))
        :reason-variables '(P)))

(defun neg-UG (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (let* ((p- (negand p)))
        (draw-conclusion
          (e-gen (q-variable p-) (neg (q-matrix p-)))
          (list c) neg-ug (list t) 1.0 depth nil nil)))))

(setf (reason-function neg-ug) #'neg-ug)

(setf neg-EG
      (make-forwards-reason
        :reason-name "neg-eg"
        :reason-forwards-premises (list (cfp '(~ (some x P)) '(P)))
        :reason-variables '(P)))

(defun neg-EG (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c)))
      (let* ((p- (negand p)))
        (draw-conclusion
          (u-gen (q-variable p-) (neg (q-matrix p-)))
          (list c) neg-eg (list t) 1.0 depth nil nil)))))

(setf (reason-function neg-eg) #'neg-eg)

(setf UI
      (make-forwards-reason
        :reason-name "UI"
        :reason-forwards-premises (list (cfp '(all x P) '(P)))
        :reason-variables '(P)))

(defun UI (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let ((p (hypernode-formula c)))
      (when (not (eq (mem3 p) :type))
        (let* ((p* (q-matrix p))
               (var (make-conclusion-variable)))
          (draw-conclusion
            (subst var (q-variable p) p*)
            (list c) UI (list t) 1.0 depth nil nil))))))

(setf (reason-function UI) #'UI)

(setf EI
      (make-forwards-reason
        :reason-name "EI"
        :reason-forwards-premises (list (cfp '(some x P) '(P)))
        :reason-variables '(x P)))

(defun ei-level (var) (get var 'ei-level))

(labels ()

  (defun occurs-disjunctively-with (x y P)
    (cond
     ((conditionalp P)
      (or (occurs-conjunctively-with x y (antecedent P)) (occurs-disjunctively-with x y (consequent P))))
     ((disjunctionp P)
      (or (occurs-disjunctively-with x y (disjunct1 P)) (occurs-disjunctively-with x y (disjunct2 P))))
     ((negationp P) (occurs-conjunctively-with x y (negand P)))
     ((e-genp P) (occurs-disjunctively-with x y (e-matrix P)))
     (t (and (occur x P) (occur y P)))))

  (defun occurs-conjunctively-with (x y P)
    (cond
     ((conjunctionp P)
      (or (occurs-conjunctively-with x y (conjunct1 P)) (occurs-conjunctively-with x y (conjunct2 P))))
     ((negationp P) (occurs-disjunctively-with x y (negand P)))
     ((u-genp P) (occurs-conjunctively-with x y (u-matrix P)))
     (t (and (occur x P) (occur y P)))))

  )

(defun EI (c depth ip)
  (declare (ignore ip))
  (when (is-inference c)
    (let* ((p (hypernode-formula c))
           (q-var (q-variable p))
           (u-vars (hypernode-variables c))
           (u=vars (subset #'(lambda (v) (occurs-disjunctively-with v q-var (q-matrix p))) u-vars))
           (s-funs (skolem-functions (hypernode-formula c)))
           (fun (if u=vars (make-skolem-e-function) (make-skolem-e-constant)))
           (substitution (if u=vars (cons fun u=vars) fun))
           (level (1+ (maximum0 (mapcar #'ei-level s-funs))))
           (discount (expt .4 (- level 1)))
           (p* (subst substitution q-var (q-matrix p)))
           (conjuncts (conjuncts p*))
           (dn (d-node-for p*)))
      (when
        (and
          (not (some #'(lambda (L) (eq (hyperlink-rule L) EG))
                     (hypernode-hyperlinks c)))
          (or (null dn)
              (not
                (some
                  #'(lambda (q)
                      (some
                        #'(lambda (cl)
                            (let ((m (match q (c-list-formula cl) (list fun))))
                              (when m
                                (let ((sup (match-sublis m (hypernode-supposition c))))
                                  (and
                                    (some #'(lambda (c*) (subsetp= (hypernode-supposition c*) sup))
                                          (c-list-nodes cl))
                                    (every
                                      #'(lambda (r)
                                          (let ((clr (c-list-for (match-sublis m r))))
                                            (and clr
                                                 (some
                                                   #'(lambda (c*)
                                                       (subsetp= (hypernode-supposition c*) sup))
                                                   (c-list-nodes clr)))))
                                      (remove-if-equal q conjuncts)))))))
                        (d-node-c-lists dn)))
                  conjuncts))))
        (setf (get fun 'ei-level) level)
        (draw-conclusion p* (list c) EI (list t) discount depth nil nil)))))

(setf (reason-function EI) #'EI)


(setf *forwards-logical-reasons*
      (reverse
        (list
          neg-ug neg-eg EI UI
          E-removal A-removal
          simp neg-elim neg-disj neg-condit neg-bicondit-simp
          DM bicondit-simp modus-ponens1 ;modus-ponens2
          modus-tollens1 ;modus-tollens2
          conditional-modus-tollens
          exportation
          disj-antecedent-simp
          cond-antecedent-simp
          disj-simp
          cond-simp1 cond-simp2
          )))

(defun set-conclusions-function (reason)
  (setf (reason-conclusions-function reason)
        (conclusion-instantiator
          (mem1 (reason-conclusions reason)) (reason-variables reason) (reason-defeasible-rule reason))))

; Flat backwards inference rules:

(setf adjunction
      (make-backwards-reason
        :reason-name "adjunction"
        :reason-conclusions '((& p q))
        :reason-backwards-premises
        (list (cbp 'p nil nil '(p)) (cbp 'q nil nil '(q)))
        :reason-variables '(p q)
        :b-reason-length 2))

(defun adjunction (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil adjunction interest depth priority
      (list (cons 'p (element 1 p)) (cons 'q (element 2 p))) (interest-supposition interest))))

(set-conclusions-function adjunction)
(setf (reason-function adjunction) #'adjunction)

(setf neg-intro
      (make-backwards-reason
        :reason-name "neg-intro"
        :reason-conclusions '((~ (~ p)))
        :reason-backwards-premises
        (list (cbp 'p nil nil '(p)))
        :reason-variables '(p)))

(defun neg-intro (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil neg-intro interest depth priority
      (list (cons 'p (element 1 (element 1 p)))) (interest-supposition interest))))

(set-conclusions-function neg-intro)
(setf (reason-function neg-intro) #'neg-intro)

(setf i-neg-disj
      (make-backwards-reason
        :reason-name "i-neg-disj"
        :reason-conclusions '((~ (v p q)))
        :reason-backwards-premises
        (list (cbp '(~ p) nil nil '(p)) (cbp '(~ q) nil nil '(q)))
        :reason-variables '(p q)
        :b-reason-length 2))

(defun i-neg-disj (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil i-neg-disj interest depth priority
      (list (cons 'p (element 1 (element 1 p))) (cons 'q (element 2 (element 1 p))))
      (interest-supposition interest))))

(set-conclusions-function i-neg-disj)
(setf (reason-function i-neg-disj) #'i-neg-disj)

(setf i-neg-condit
      (make-backwards-reason
        :reason-name "i-neg-condit"
        :reason-conclusions '((~ (-> p q)))
        :reason-backwards-premises
        (list (cbp '(~ q) nil nil '(q)) (cbp 'p nil nil '(p)))
        :reason-variables '(p q)
        :b-reason-length 2))

(defun i-neg-condit (interest depth priority)
  ; (when (eq interest (interest 4)) (break))
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil i-neg-condit interest depth priority
      (list (cons 'p (element 1 (element 1 p))) (cons 'q (element 2 (element 1 p))))
      (interest-supposition interest))))

(set-conclusions-function i-neg-condit)
(setf (reason-function i-neg-condit) #'i-neg-condit)

(setf bicondit-intro
      (make-backwards-reason
        :reason-name "bicondit-intro"
        :reason-conclusions '((<-> p q))
        :reason-backwards-premises
        (list (cbp '(-> q p) nil nil '(p q)) (cbp '(-> p q) nil nil '(p q)))
        :reason-variables '(p q)
        :b-reason-length 2))

(defun bicondit-intro (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil bicondit-intro interest depth priority
      (list (cons 'p (element 1 p)) (cons 'q (element 2 p)))
      (interest-supposition interest))))

(set-conclusions-function bicondit-intro)
(setf (reason-function bicondit-intro) #'bicondit-intro)

(setf i-neg-bicondit
      (make-backwards-reason
        :reason-name "i-neg-bicondit"
        :reason-conclusions '((~ (<-> p q)))
        :reason-backwards-premises
        (list (cbp '(<-> p (~ q)) nil nil '(p q)))
        :reason-variables '(p q)))

(defun i-neg-bicondit (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil i-neg-bicondit interest depth priority
      (list (cons 'p (element 1 (element 1 p))) (cons 'q (element 2 (element 1 p))))
      (interest-supposition interest))))

(set-conclusions-function i-neg-bicondit)
(setf (reason-function i-neg-bicondit) #'i-neg-bicondit)

(setf disj-cond
      (make-backwards-reason
        :reason-name "disj-cond"
        :reason-conclusions '((v p q))
        :reason-backwards-premises
        (list (cbp '(-> (~ p) q) nil nil '(p q)))
        :reason-variables '(p q)))

(defun disj-cond (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil disj-cond interest depth priority
      (list (cons 'p (element 1 p)) (cons 'q (element 2 p)))
      (interest-supposition interest))))

(set-conclusions-function disj-cond)
(setf (reason-function disj-cond) #'disj-cond)

(setf disj-cond-2
      (make-backwards-reason
        :reason-name "disj-cond-2"
        :reason-conclusions '((v p q))
        :reason-backwards-premises
        (list (cbp '(-> (~ q) p) nil nil '(p q)))
        :reason-variables '(p q)))

(defun disj-cond-2 (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil disj-cond-2 interest depth priority
      (list (cons 'p (element 1 p)) (cons 'q (element 2 p)))
      (interest-supposition interest))))

(set-conclusions-function disj-cond-2)
(setf (reason-function disj-cond-2) #'disj-cond-2)

(setf i-DM
      (make-backwards-reason
        :reason-name "i-DM"
        :reason-conclusions '((~ (& p q)))
        :reason-backwards-premises
        (list (cbp '(v (~ p) (~ q)) nil nil '(p q)))
        :reason-variables '(p q)))

(defun i-DM (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil i-DM interest depth priority
      (list (cons 'p (element 1 (element 1 p))) (cons 'q (element 2 (element 1 p))))
      (interest-supposition interest))))

(set-conclusions-function i-DM)
(setf (reason-function i-DM) #'i-DM)

(setf i-neg-eg
      (make-backwards-reason
        :reason-name "i-neg-eg"
        :reason-conclusions '((~ (some x q)))
        :reason-conclusions-function
        #'(lambda (binding) (let ((x (cdr (assoc 'x binding))) (q (cdr (assoc 'q binding)))) (list '~ (list 'all x q))))
        :reason-backwards-premises
        (list (cbp '(all x (~ q)) nil nil '(x q)))
        :reason-variables '(x q)
        :b-reason-length 1))

(defun i-neg-eg (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil i-neg-eg interest depth priority
      (list (cons 'x (element 1 (element 1 p))) (cons 'q (element 2 (element 1 p))))
      (interest-supposition interest))))

(set-conclusions-function i-neg-eg)
(setf (reason-function i-neg-eg) #'i-neg-eg)

(setf i-neg-ug
      (make-backwards-reason
        :reason-name "i-neg-ug"
        :reason-conclusions '((~ (all x q)))
        :reason-backwards-premises
        (list (cbp '(some x (~ q)) nil nil '(x q)))
        :reason-variables '(x q)
        :b-reason-length 1))

(defun i-neg-ug (interest depth priority)
  (let ((p (interest-formula interest)))
    (construct-initial-interest-link
      nil nil i-neg-ug interest depth priority
      (list (cons 'x (element 1 (element 1 p))) (cons 'q (element 2 (element 1 p))))
      (interest-supposition interest))))

(set-conclusions-function i-neg-ug)
(setf (reason-function i-neg-ug) #'i-neg-ug)

(setf UG
      (make-backwards-reason
        :reason-name "UG"
        :reason-conclusions '((all x q))
        :reason-backwards-premises 'q
        :reason-variables '(x q)
        :b-reason-length 1))

(defun UG (interest depth priority)
  (let* ((p (interest-formula interest))
         (q-var (q-variable p))
         (e-vars (interest-variables interest))
         (e=vars (subset #'(lambda (v) (occurs-conjunctively-with v q-var (q-matrix p))) e-vars))
         (fun (if e=vars (make-skolem-i-function) (make-skolem-i-constant)))
         (substitution (if e=vars (cons fun e=vars) fun))
         (ug-condition
           #'(lambda (c unifier binding)
               (declare (ignore binding))
               (and
                 (or (not (listp (mem2 unifier)))
                     (not (some #'(lambda (x) (occur* fun (cdr x))) (mem2 unifier))))
                 (not (occur fun (match-sublis (mem1 unifier) (hypernode-supposition c)))))))
         (link
           (make-interest-link
             :link-number (incf *interest-link-number*)
             :link-resultant-interest interest
             :link-interest-formula (subst substitution q-var (q-matrix p))
             :link-interest-condition ug-condition
             :link-rule ug
             :link-supposition (interest-supposition interest)
             :link-strength (interest-maximum-degree-of-interest interest)
             :link-binding (list (cons 'x (element 1 p)) (cons 'q (element 2 p)))
             )))
    (push link *interest-links*)
    (push link (interest-left-links interest))
    (setf (get fun 'ei-level) 0)
    (compute-link-interest
      link #'(lambda (i) (eq (interest-discharge-condition i) ug-condition))
      #'(lambda (i) (setf (interest-discharge-condition i) ug-condition))
      (interest-degree-of-interest interest) (interest-maximum-degree-of-interest interest) depth priority)
    (discharge-link link (1+ depth) (interest-degree-of-interest interest) priority nil)
    ))

(set-conclusions-function UG)
(setf (reason-function UG) #'UG)

(setf EG
      (make-backwards-reason
        :reason-name "EG"
        :reason-conclusions '((some x q))
        :reason-backwards-premises 'q
        :reason-variables '(x q)
        :b-reason-length 1))

(defun EG (interest depth priority)
  (let* ((p (interest-formula interest))
         (var (make-interest-variable))
         (link
           (make-interest-link
             :link-number (incf *interest-link-number*)
             :link-resultant-interest interest
             :link-interest-formula (subst var (q-variable p) (q-matrix p))
             :link-rule eg
             :link-supposition (interest-supposition interest)
             :link-strength (interest-maximum-degree-of-interest interest)
             :link-binding (list (cons 'x (element 1 p)) (cons 'q (element 2 p)))
             )))
    (push link *interest-links*)
    (push link (interest-left-links interest))
    (compute-link-interest
      link nil nil (interest-degree-of-interest interest) (interest-maximum-degree-of-interest interest) depth priority (list var))
    (discharge-link link (1+ depth) (interest-degree-of-interest interest) priority nil)
    ))

(set-conclusions-function EG)
(setf (reason-function EG) #'EG)

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

(defun rerun (&rest args)
  (progn
    (terpri) (princ "(") (princ "                                 ") (princ *version*) (princ "          ")
    (let ((time (multiple-value-list (get-decoded-time))))
      (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
      (princ (mem6 time)) (princ "          ") (princ (mem3 time))
      (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
      (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
      (terpri) (terpri))
    (princ "*reductio-discount* = ") (princ *reductio-discount*) (terpri)
    (princ "*reductio-interest* = ") (princ *reductio-interest*) (terpri)
    (princ "*skolem-multiplier* = ") (princ *skolem-multiplier*) (terpri)
    (princ "*quantifier-discount* = ") (princ *quantifier-discount*) (terpri))
  (if (stringp (mem1 *test-log*)) (setf *test-log* (cdr (mem6 *test-log*))))
  (let ((rest (cons *problem-number* args)))
    (cond ((equal (mem1 rest) :skip)
           ;; (test :skip i j k)
           (dolist (P *problems*)
             (when (not (mem (car P) (cdr rest)))
               (run-reasoning-problem P)
               (when *pause*
                 (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                 (read-char)))))
          (t (let ((start (mem1 rest)))
               (cond
                 ((null (cdr rest))
                  ;; (test n)
                  (run-reasoning-problem (assoc start *problems*)))
                 ((eq (mem2 rest) t)
                  ;; (test n t)
                  (dolist (P (mem (assoc start *problems*) *problems*))
                    (run-reasoning-problem P)
                    (when *pause*
                      (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                      (read-char))))
                 ((equal (mem2 rest) :skip)
                  ;; (test n :skip i j k)
                  (dolist (P (mem (assoc start *problems*) *problems*))
                    (when (not (mem (car P) (cdr rest)))
                      (run-reasoning-problem P)
                      (when *pause*
                        (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                        (read-char)))))
                 ((numberp (mem2 rest))
                  ;; (test n m) and (test n m :skip i j k)
                  (dolist (P (mem (assoc start *problems*) *problems*))
                    (when (and (not (mem (car P) (cdddr rest))) (not (> (car P) (mem2 rest))))
                      (run-reasoning-problem P)
                      (when (and *pause* (not (= (car P) (mem2 rest))))
                        (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                        (read-char))))))))))
  (setf *test-log*
        (list *version* *reductio-discount* *reductio-interest* *skolem-multiplier*
              *quantifier-discount* *test-log*))
  (when (not *display?*) (display-test-log))
  (terpri)
  (princ *test-log*)
  (terpri) (princ ")") (terpri))

(defun run (&rest args)
  (progn
    (terpri) (princ "(") (princ "                                 ") (princ *version*) (princ "          ")
    (let ((time (multiple-value-list (get-decoded-time))))
      (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
      (princ (mem6 time)) (princ "          ") (princ (mem3 time))
      (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
      (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
      (terpri) (terpri))
    (princ "*reductio-discount* = ") (princ *reductio-discount*) (terpri)
    (princ "*reductio-interest* = ") (princ *reductio-interest*) (terpri)
    (princ "*skolem-multiplier* = ") (princ *skolem-multiplier*) (terpri)
    (princ "*quantifier-discount* = ") (princ *quantifier-discount*) (terpri))
  (when (stringp (mem1 *test-log*)) (setf *test-log* (mem6 *test-log*)))
  (let ((rest (cons (1+ *problem-number*) args)))
    (cond ((equal (mem1 rest) :skip)
           ;; (test :skip i j k)
           (dolist (P *problems*)
             (when (not (mem (car P) (cdr rest)))
               (run-reasoning-problem P)
               (when *pause*
                 (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                 (read-char)))))
          (t (let ((start (mem1 rest)))
               (cond
                 ((null (cdr rest))
                  ;; (test n)
                  (run-reasoning-problem (assoc start *problems*)))
                 ((eq (mem2 rest) t)
                  ;; (test n t)
                  (dolist (P (mem (assoc start *problems*) *problems*))
                    (run-reasoning-problem P)
                    (when *pause*
                      (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                      (read-char))))
                 ((equal (mem2 rest) :skip)
                  ;; (test n :skip i j k)
                  (dolist (P (mem (assoc start *problems*) *problems*))
                    (when (not (mem (car P) (cdr rest)))
                      (run-reasoning-problem P)
                      (when *pause*
                        (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                        (read-char)))))
                 ((numberp (mem2 rest))
                  ;; (test n m) and (test n m :skip i j k)
                  (dolist (P (mem (assoc start *problems*) *problems*))
                    (when (and (not (mem (car P) (cdddr rest))) (not (> (car P) (mem2 rest))))
                      (run-reasoning-problem P)
                      (when (and *pause* (not (= (car P) (mem2 rest))))
                        (terpri) (princ "Type any key to continue.") (terpri) (terpri)
                        (read-char))))))))))
  (setf *test-log*
        (list *version* *reductio-discount* *reductio-interest* *skolem-multiplier*
              *quantifier-discount* *test-log*))
  (when (not *display?*) (display-test-log))
  (terpri)
  (princ *test-log*)
  (terpri) (princ ")") (terpri))

(proclaim '(special *comparison-graphs*))

(defun COGITATE0 ()
  (initialize-reasoner)
  (dolist (query *ultimate-epistemic-interests*)
    (reason-backwards-from-query query (query-strength query) 0))
  (catch 'die
         (loop
           (incf *cycle*)
           (dolist (premise *premises*)
             (when (eql (mem3 premise) *cycle*)
               (pull premise *premises*)
               (queue-premise (list (mem1 premise) nil (mem2 premise)))))
           (think-or-die))
         ))

(defun run-reasoning-problem* (P)
  (setf *problem-number* (car P))
  (setf *pretty-list* nil *string-symbols* nil)
  (setf *premises* (mem2 P))
  (setf *fixed-ultimate-epistemic-interests* nil)
  (setf *ultimate-epistemic-interests* nil)
  (setf *query-number* 0)
  (dolist (interest (mem3 P))
    (let ((query
            (make-query
              :query-number (incf *query-number*)
              :query-formula (reform-if-string (mem1 interest))
              :query-strength (mem2 interest))))
      (push query *fixed-ultimate-epistemic-interests*)))
  (setf *forwards-substantive-reasons* (append (mem4 P) (mem5 P)))
  (setf *backwards-substantive-reasons* (append (mem6 P) (mem7 P)))
  (cogitate0))

(defun test* (&optional n)
  (cond ((null n)
         (dolist (P *problems*)
           (run-reasoning-problem* P)))
        (t (run-reasoning-problem* (assoc n *problems*)))))

(defun test&load ()
  (setf *comparison-graphs* nil)
  (dolist (P *problems*)
    (run-reasoning-problem* P)
    (push *hypergraph* *comparison-graphs*))
  (setf *comparison-graphs* (reverse *comparison-graphs*)))

(defun test&compare ()
  (let ((comparison-graphs *comparison-graphs*))
    (dolist (P *problems*)
      (run-reasoning-problem* P)
      (let ((graph (car comparison-graphs)))
        (setf comparison-graphs (cdr comparison-graphs))
        (dolist (node *hypergraph*)
          (when (not (= (hypernode-degree-of-justification node)
                        (hypernode-degree-of-justification (mem1 graph))))
            (PRINC "problem #") (princ *problem-number*) (princ ": ")
            (princ "Hypernode ") (princ (hypernode-number node)) (princ " differs") (terpri))
          (setf graph (cdr graph)))))))

#| This restarts the reasoning, beginning with the inference-queue item x.  x can be the
number of a queue-node, or an interest or a conclusion.  If x is empty, reasoning restarts
without altering the inference-queue. |#
(defun try (&optional x)
  (when x
    (let ((Q
            (cond ((numberp x)
                   (find-if #'(lambda (item) (eql (queue-number item) x)) *inference-queue*))
                  ((interest-p x) (interest-queue-node x))
                  ((hypernode-p x) (hypernode-queue-node x)))))
      (setf *inference-queue* (cons Q (remove Q *inference-queue*)))))
  (catch 'die
         (loop (incf *cycle*) (think-or-die)))
  (terpri)
  (display-queries) (terpri)
  (let ((nodes nil))
    (dolist (query *ultimate-epistemic-interests*)
      (dolist (N (query-answers query))
        (pushnew N nodes)))
    (compute-relevant-nodes nodes)
    (let ((argument-length (length *relevant-nodes*)))
      (cond (*proofs?* (terpri) (show-arguments))
            (t
              (princ "Cumulative size of arguments = ") (princ argument-length) (terpri))))))

#| When the following is run before a problem is run, when an interest of number n is
queued, it goes on the front of the inference-queue. |#
(defun try-interest (&optional n)
  (cond ((null n) (setf *priority-interests* nil))
        (t (push n *priority-interests*))))

(defun display-reasoning-for (node)
  (progn
    (princ "(") (terpri)
    (princ "===========================================================================")
    (terpri) (princ "THE FOLLOWING IS THE REASONING RELATED TO NODE ") (princ (hypernode-number node))
    (terpri)
    (princ "Hypernodes marked DEFEATED have that status at the end of the reasoning.")
    (terpri)(terpri))
  (let ((nodes (list node)))
    (compute-relevant-nodes nodes)
    (let* (
           (enabling-interests
             (union (unionmapcar+ #'hypernode-enabling-interests *relevant-nodes*)
                    (unionmapcar+ #'hypernode-generating-defeat-interests *relevant-nodes*)))
           (closure (generated-nodes-and-interests *relevant-nodes* enabling-interests nil))
           (nodes-used (remove-duplicates (mem1 closure)))
           (interests-used (remove-duplicates (mem2 closure)))
           (interests-used-in-proof (remove-duplicates (mem3 closure)))
           (log (reverse *reasoning-log*))
           (boundary nil)
           (nodes-displayed nil))
      (when *graph-log* (make-oscar-window))
      (dolist (x log)
        (cond ((hypernode-p x)
               (when (member x nodes-used)
                 (display-node
                   x *relevant-nodes* nodes-used interests-used enabling-interests nodes-displayed)
                 (push x nodes-displayed)))
              ((interest-p x)
               (when (member x interests-used)
                 (display-used-interest
                   x *relevant-nodes* nodes-used interests-used
                   enabling-interests interests-used-in-proof)))
              (t (setf boundary (display-peripherals x boundary nodes-used)))))
      (when (and *graph-log* (boundp '*speak*) *speak*)
        (setf nodes
              (subset
                #'(lambda (n)
                    (some #'(lambda (q) (>= (current-degree-of-justification n) (query-strength q)))
                          (hypernode-answered-queries n)))
                nodes))
        (when nodes
          (speak-text
            (cond
              ((cdr nodes)
               (cat-list
                 (list "In conclusion, " (pranc-to-string (pretty (hypernode-formula (car nodes))))
                       (mapcar #'(lambda (n) (cat ", " (pranc-to-string (pretty (hypernode-formula n)))))
                               (cdr nodes)))))
              (t (cat "In conclusion, " (pranc-to-string (pretty (hypernode-formula (car nodes))))))))))
      (when *graph-log* (invalidate-view *og*))
      (princ "============================================================")
      (terpri)
      (princ ")") (terpri))))

(defun store-interest-record (in record)
  (let ((in-record (assoc in *interest-record*)))
    (cond (in-record (push record (cdr in-record)))
          (t (push (list in record) *interest-record*)))))

;(defun generating-right-link (in used-interests used-nodes)
;   ; (when (eq in (interest 19)) (setf i in u used-interests un used-nodes) (break))
;   ;; (step (generating-right-link i u un))
;    (let ((L (find-if
;                  #'(lambda (L)
;                        (and
;                          (member (link-resultant-interest L) used-interests)
;                          (some #'(lambda (n) (member n used-nodes)) (interest-discharging-nodes (link-interest L)))))
;                  (interest-right-links in))))
;       (when (null L)
;            (setf L
;                     (find-if
;                       #'(lambda (L)
;                             (some #'(lambda (n) (member n used-nodes)) (interest-discharging-nodes (link-interest L))))
;                       (interest-right-links in))))
;       (when (null L)
;            (setf L (mem1
;                          (last (subset
;                                    #'(lambda (L) (member (link-resultant-interest L) used-interests))
;                                                (interest-right-links in))))))
;       (when (null L)
;            (setf L (mem1 (last (interest-right-links in)))))
;       L))

(defun relevant-nodes (node &optional nodes-used)
  (when (not (member node nodes-used))
    (setf nodes-used (cons node nodes-used))
    (dolist (m (hypernode-motivating-nodes node))
      (setf nodes-used (union (relevant-nodes m nodes-used) nodes-used)))
    (dolist (L (hypernode-hyperlinks node))
      (dolist (b (hyperlink-basis L))
        (setf nodes-used (union (relevant-nodes b nodes-used) nodes-used)))
      (dolist (d (hyperlink-defeaters L))
        (setf nodes-used (union (relevant-nodes (hyper-defeat-link-root d) nodes-used) nodes-used))))
    nodes-used))

(defun is (n)
  (find-if #'(lambda (x) (equal (ip-number x) n)) (list-interest-schemes)))

(defun list-instantiated-premises (&optional d-node)
  (when (null d-node) (setf d-node (d-node 1)))
  (append (d-node-forwards-reasons d-node)
          (unionmapcar #'(lambda (d) (list-instantiated-premises (cdr d)))
                       (d-node-discrimination-tests d-node))))

(defun ip (n)
  (find-if #'(lambda (x) (equal (ip-number x) n)) (list-instantiated-premises)))

(defun analyze-interest-schemes ()
  (let ((schemes (list-interest-schemes))
        (reasons nil))
    (dolist (s schemes)
      (when (not (member (ip-reason s) *backwards-logical-reasons*))
        (pushnew (ip-reason s) reasons)))
    (dolist (R reasons)
      (princ "There are ")
      (princ (number-of schemes #'(lambda (x) (eq (ip-reason x) R))))
      (princ " interest-schemes employing the reason ")
      (princ R) (terpri))))

(defun analyze-instantiated-premises ()
  (let ((schemes (list-instantiated-premises))
        (reasons nil))
    (dolist (s schemes)
      (when (not (member (ip-reason s) *forwards-logical-reasons*))
        (pushnew (ip-reason s) reasons)))
    (dolist (R reasons)
      (princ "There are ")
      (princ (number-of schemes #'(lambda (x) (eq (ip-reason x) R))))
      (princ " instantiated-premises employing the reason ")
      (princ R) (terpri))))

(defun analyze-schemes ()
  (analyze-instantiated-premises)
  (analyze-interest-schemes))

#| X and Y are sets of sequents, and every member of X subsumes some member of Y. |#
(defun subsumes-basis (X Y)
  (every
    #'(lambda (a)
        (some
          #'(lambda (b) (subsumes a b))
          Y))
    X))

;#|  This returns the list of two c-lists, one supporting the rebutting defeater and the
;other supporting the undercutting defeater.  It creates them if necessary.  |#
;(defun defeaters-for (sequent basis)
;    (let* ((formula (sequent-formula sequent))
;              (base (mapcar #'sequent-formula basis))
;              (rebut (neg formula))
;              (undercut (make-@ (gen-conjunction base) formula))
;              (rebutting-c-list (c-list-for rebut))
;              (undercutting-c-list (c-list-for undercut)))
;       (when (null rebutting-c-list)
;            (setf rebutting-c-list
;                     (make-c-list
;                       :c-list-formula rebut
;                       :c-list-corresponding-i-lists (matching-i-lists-for rebut nil)))
;            (push (cons rebut rebutting-c-list) *conclusions*))
;       (when (null undercutting-c-list)
;            (setf undercutting-c-list
;                     (make-c-list
;                       :c-list-formula undercut
;                       :c-list-corresponding-i-lists (matching-i-lists-for undercut nil)))
;            (push (cons undercut undercutting-c-list) *conclusions*))
;       (list rebutting-c-list undercutting-c-list)))

(defun condition-satisfying-interest (S condition link vars)
  (multiple-value-bind
    (interests match)
    (interests-for (sequent-formula S) vars)
    (when interests
      (let ((sup (match-sublis match (sequent-supposition S))))
        (find-if #'(lambda (i)
                     (and (eq (interest-deductive i)
                              (interest-deductive (link-resultant-interest link)))
                          (funcall* (mem1 condition) i)
                          (== (interest-supposition i) sup)))
                 interests)))))

(defun validating-node (interest degree binding)
  (let ((node nil))
    (some
      #'(lambda (cl)
          (let ((unifiers nil)
                (unifier (mem2 cl)))
            (setf node
                  (find-if
                    #'(lambda (c)
                        (and (>= (current-maximal-degree-of-justification c) degree)
                             (funcall+ (interest-discharge-condition interest) c unifier binding)
                             (setf unifiers
                                   (appropriately-related-suppositions c interest unifier))))
                    (c-list-nodes (mem1 cl))))
            (when node
              (push (list interest unifier unifiers) (hypernode-discharged-interests node)))))
      (i-list-corresponding-c-lists (interest-i-list interest)))
    node))

(defun construct-new-interest-for-sequent (S degree maximum-degree)
  ; (when (equal link (link 2))
  ;      (setf b* b l link d degree m* maximum-degree d* depth) (break))
  (let ((interest
          (make-interest
            :interest-number (incf *interest-number*)
            :interest-sequent S
            :interest-formula (sequent-formula S)
            :interest-supposition (sequent-supposition S)
            :interest-supposition-variables
            (unionmapcar= #'formula-hypernode-variables (sequent-supposition S))
            :interest-degree-of-interest degree
            :interest-maximum-degree-of-interest maximum-degree)))
    (compute-interest-supposition-nodes interest)
    (store-interest interest)
    (when *display?* (display-interest interest))
    (if *log-on* (push interest *reasoning-log*))
    interest))

#| This code is modified from DISCHARGE-LINK. |#
(defun adopt-interest (S degree defeasible? binding)
  ; (setf ss s d degree df defeasible?)
  ;; the following assumes there are no i-variables in formula
  (let ((deductive-node (validating-deductive-node S (not defeasible?))))
    (or
      deductive-node
      ;; code from condition-satisfying-interest
      (let ((interest
              (multiple-value-bind
                (interests match)
                (interests-for (sequent-formula S) nil)
                (when interests
                  (let ((sup (match-sublis match (sequent-supposition S))))
                    (find-if #'(lambda (i) (== (interest-supposition i) sup)) interests))))))
        (cond (interest
                (setf (interest-degree-of-interest interest) (min (interest-degree-of-interest interest) degree))
                (setf (interest-maximum-degree-of-interest interest)
                      (max (interest-maximum-degree-of-interest interest) degree))
                (setf (interest-priority interest) (max (interest-priority interest) degree)))
              (t
                (setf interest (construct-new-interest-for-sequent S degree degree))
                (setf (interest-priority interest) degree)
                (let ((conclusion (validating-node interest degree binding)))
                  (when conclusion
                    (when *display?*
                      (princ "                                        ")
                      (princ "Hypernode #")
                      (princ (hypernode-number conclusion))
                      (princ " discharges interest #")
                      (princ (interest-number interest))
                      (terpri) (terpri))
                    (pushnew conclusion (interest-discharging-nodes interest))
                    (when (and (not (interest-cancelled interest))
                               (equal (hypernode-formula conclusion) (interest-formula interest))
                               (subsetp= (hypernode-supposition conclusion) (interest-supposition interest))
                               (dolist (sup-node (interest-generated-suppositions interest))
                                 (when (and
                                         (equal (hypernode-generating-interests sup-node) (list interest))
                                         (deductive-in conclusion sup-node))
                                   (cancel-node sup-node 0)))))))))
        interest))))

(defun subsetp* (X Y)
  (subsetp X Y :test #'(lambda (z w)
                         (and (equal (car z) (car w))
                              (or (reductio-supposition (cdr z))
                                  (not (reductio-supposition (cdr w))))))))

;(defun inference-descendants (N)
;    (let ((consequences (hypernode-consequences N)))
;       (union consequences (unionmapcar+ #'inference-descendants consequences))))

(defun rewrite-u-vars (formula vars)
  (if vars
    (let ((a-list (mapcar #'(lambda (v) (cons v (make-interest-variable))) vars)))
      (list (sublis a-list formula) a-list))
    (list formula t)))

#| This assumes that N is a reductio-supposition-node.  The second conjunct could be
made more efficient by storing the appropriate information in a slot
non-reductio-generating-interests. |#
(defun strictly-base-reductio-supposition (N)
  (and
    (not (some #'interest-reductio (hypernode-generating-interests N)))
    (every #'(lambda (in) (equal (hypernode-formula N) (neg (interest-formula in))))
           (hypernode-generating-interests N))))

(defun make-backwards-inference
  (reason binding interest depth priority supporting-nodes clues instantiations supposition
          &optional generating-node)
  ; (when (eq *cycle* 518) (setf r reason b binding i interest d depth p priority s supporting-nodes in instantiations u supposition) (break))
  ;; (step (make-backwards-inference r b i d p s in u))
  (cond
    ((or (reason-backwards-premises reason) (reason-backwards-premises-function reason))
     (construct-initial-interest-link
       supporting-nodes instantiations reason interest depth priority binding supposition
       :generating-node generating-node :remaining-premises (reason-backwards-premises reason) :clues clues))
    ((or (numberp (reason-strength reason))
         (>= (funcall (reason-strength reason) binding supporting-nodes) (interest-degree-of-interest interest)))
     (cond
       ((reason-conclusions-function reason)
        (dolist (P (funcall (reason-conclusions-function reason) binding))
          (draw-conclusion
            (car P) supporting-nodes reason instantiations (reason-discount-factor reason) depth nil (cdr P)
            :binding binding :clues clues)))
       (t (draw-conclusion
            (interest-formula interest) supporting-nodes reason instantiations
            (reason-discount-factor reason) depth nil (reason-defeasible-rule reason) :binding binding :clues clues)))
     )))

(defun rebuts (sequent1 sequent2)
  (and (equal (sequent-formula sequent1) (neg (sequent-formula sequent2)))
       (subsetp= (sequent-supposition sequent1) (sequent-supposition sequent2))))

(defun undercuts (sequent1 basis sequent2)
  (and (equal (sequent-formula sequent1)
              (make-@ (gen-conjunction (mapcar #'hypernode-formula basis))
                      (sequent-formula sequent2)))
       (subsetp= (sequent-supposition sequent1) (sequent-supposition sequent2))
       (every #'(lambda (b)
                  (subsetp= (sequent-supposition sequent1) (hypernode-supposition b)))
              basis)))

#| sequent1 has the correct syntactical form to defeat an inference from basis
to sequent2. |#
(defun defeats (sequent1 basis sequent2)
  (or (rebuts sequent1 sequent2)
      (undercuts sequent1 basis sequent2)))

#| The following returns the pair (new-beliefs new-retractions)
where new-beliefs is the list of nodes whose undefeated-degrees-of-support have increased
as a result of the computation and new-retractions is the list of nodes whose
undefeated-degrees-of-support have decreased as a result of this computation.

(defun compute-undefeated-degrees-of-support () ; (break)
  ; (when (member (hyperlink 2) *new-links*) (break))
  ;; (step (compute-undefeated-degrees-of-support))
  (let* ((immediately-altered-nodes
           (remove-duplicates (mapcar #'hyperlink-target *altered-links*)))
         (altered-nodes (inference-descendants immediately-altered-nodes))
         (altered-nodes-
           (subset #'(lambda (N) (not (member nil (hypernode-nearest-defeasible-ancestors N)))) altered-nodes))
         (new-beliefs nil)
         (new-retractions nil))
    (dolist (N altered-nodes)
      (setf (hypernode-old-degree-of-justification N) (hypernode-degree-of-justification N)))
    (let ((undefeated-links
            (mapcar
              #'(lambda (N)
                  (cons N
                        (subset
                          #'(lambda (L)
                              (and (null (defeating-assignment-trees L))
                                   (not (some
                                          #'(lambda (b) (member b altered-nodes-))
                                          (hyperlink-basis L)))))
                          (hypernode-hyperlinks N))))
              (reverse altered-nodes))))
      (dolist (pair undefeated-links)
        (dolist (L (cdr pair))
          (when (every #'hypernode-degree-of-justification (hyperlink-basis L))
            (setf (hyperlink-degree-of-justification L)
                  (if (and (not (keywordp (hyperlink-rule L))) (reason-temporal? (hyperlink-rule L)))
                    (prog1
                      (* (hyperlink-reason-strength L)
                         (minimum
                           (mapcar #'current-degree-of-justification
                                   (hyperlink-basis L))))
                      (setf (hyperlink-temporal L) *cycle*))
                    (minimum
                      (cons (hyperlink-reason-strength L)
                            (mapcar #'current-degree-of-justification
                                    (hyperlink-basis L)))))))))
      (loop
        (when (null undefeated-links) (return))
        (let ((pair (find-if #'(lambda (pair) (every #'hyperlink-degree-of-justification (cdr pair))) undefeated-links)))
          (setf undefeated-links (remove pair undefeated-links))
          (let ((N (car pair))
                (support-values nil)
                (discounted-support-values nil))
            (dolist (L (cdr pair))
              (let ((val (hyperlink-degree-of-justification L)))
                (push val support-values)
                (push (* val (hyperlink-discount-factor L)) discounted-support-values)))
            (setf (hypernode-degree-of-justification N) (maximum0 support-values))
            (setf (hypernode-discounted-node-strength N) (maximum0 discounted-support-values))
            (dolist (L (hypernode-consequent-links N))
              (when (every #'hypernode-degree-of-justification (hyperlink-basis L))
                (setf (hyperlink-degree-of-justification L)
                      (if (and (not (keywordp (hyperlink-rule L))) (reason-temporal? (hyperlink-rule L)))
                        (prog1
                          (* (hyperlink-reason-strength L)
                             (minimum
                               (mapcar #'current-degree-of-justification
                                       (hyperlink-basis L))))
                          (setf (hyperlink-temporal L) *cycle*))
                        (minimum
                          (cons (hyperlink-reason-strength L)
                                (mapcar #'current-degree-of-justification
                                        (hyperlink-basis L)))))))))))
      (dolist (N altered-nodes)
        (when (not (zerop (hypernode-degree-of-justification N)))
          (recompute-descendant-udoss N)))
      (dolist (node altered-nodes)
        (let ((hypernode-old-degree-of-justification (compute-old-degree-of-justification node)))
          (cond
            ((null (hypernode-old-degree-of-justification node))
             (cond ((not (zerop (hypernode-degree-of-justification node)))
                    (push node new-beliefs))
                   ((not (member nil (hypernode-nearest-defeasible-ancestors node)))
                    (push node new-retractions))))
            ((> (hypernode-degree-of-justification node) hypernode-old-degree-of-justification)
             (push node new-beliefs))
            ((< (hypernode-degree-of-justification node) hypernode-old-degree-of-justification)
             (push node new-retractions)))))
      (list new-beliefs new-retractions)
      )))
|#

(defun inference-descendants (nodes)
  (let ((descendants nodes))
    (loop
      (when (null nodes) (return descendants))
      (let ((node (car nodes)))
        (setf nodes (cdr nodes))
        (dolist (L (hypernode-consequent-links node))
          (let ((N (hyperlink-target L)))
            (when (not (member N descendants))
              (push N descendants)
              (push N nodes))))))))

(defun interest-descendants (interests)
  (let ((descendants interests))
    (loop
      (let ((interest (car interests)))
        (setf interests (cdr interests))
        (dolist (L (interest-left-links interest))
          (let ((N (link-interest L)))
            (when (not (member N descendants))
              (push N descendants)
              (push N interests))))
        (when (null interests)
          (return (order descendants #'(lambda (x y) (< (interest-number x) (interest-number y))))))))))

; The nodes inferred by discharging the interest-descendants of interest.
(defun hypernode-descendants-of-interest (interest)
  (let ((interests (interest-descendants (list interest))))
    (order
      (inference-descendants
        (subset #'(lambda (N) (some #'(lambda (int) (member int interests)) (hypernode-enabling-interests N)))
                (unionmapcar #'interest-discharging-nodes interests)))
      #'(lambda (x y) (< (hypernode-number x) (hypernode-number y))))))

#| Nodes and interests generated by node or interest. |#
(defun descendants-of (N)
  (let ((interests (if (interest-p N) (list N)))
        (nodes (if (hypernode-p N) (list N)))
        (interest-descendants nil)
        (hypernode-descendants nil))
    (loop
      (when (and (null nodes) (null interests))
        (p-print
          (order interest-descendants #'(lambda (x y) (< (interest-number x) (interest-number y)))))
        (p-print
          (order hypernode-descendants #'(lambda (x y) (< (hypernode-number x) (hypernode-number y)))))
        (return nil))
      (cond (nodes
              (let ((node (car nodes)))
                (when node
                  (setf nodes (cdr nodes))
                  (dolist (L (hypernode-consequent-links node))
                    (let ((N (hyperlink-target L)))
                      (when (not (member N hypernode-descendants))
                        (push N hypernode-descendants)
                        (push N nodes))))
                  (dolist (N (hypernode-generated-defeat-interests node))
                    (when (not (member N interest-descendants))
                      (push N interest-descendants)
                      (push N interests)))
                  (dolist (L *interest-links*)
                    (when (member node (link-clues L))
                      (let ((N (link-interest L)))
                        (when (not (member N interest-descendants))
                          (push N interest-descendants)
                          (push N interests))))))))
            (interests
              (let ((interest (car interests)))
                (when interest
                  (setf interests (cdr interests))
                  (dolist (L (interest-left-links interest))
                    (let ((N (link-interest L)))
                      (when (not (member N interest-descendants))
                        (push N interest-descendants)
                        (push N interests))))
                  (dolist (N (interest-discharging-nodes interest))
                    (when (member interest (hypernode-enabling-interests N))
                      (when (not (member N hypernode-descendants))
                        (push N hypernode-descendants)
                        (push N nodes))))
                  )))))))

;;=============================================

(defun print-undefeated-degrees-of-support ()
  (terpri)
  (princ "========== UNDEFEATED DEGREES OF SUPPORT ==========") (terpri)
  (dolist (node *hypergraph*)
    (princ "Hypernode #") (princ (hypernode-number node)) (princ ":  ")
    (if (zerop (hypernode-degree-of-justification node)) (princ "defeated") (princ "undefeated")) (terpri))
  (princ "======================================") (terpri))

(defun display-inference-graph ()
  (terpri)
  (princ "================== INFERENCE-GRAPH ===================") (terpri)
  (dolist (node (reverse *hypergraph*))
    (display-hypernode node)
    (princ "---------------------------------------------------") (terpri)))

#| An argument is a list of hyperlinks. |#
(defun independent-of (sequent argument)
  (not (some #'(lambda (L)
                 (some #'(lambda (b) (subsumes (hypernode-sequent b) sequent))
                       (hyperlink-basis L)))
             argument)))

(defun sup-order (n m)
  (subsetp= (hypernode-supposition n) (hypernode-supposition m)))

(defun print-argument-relations (arg &optional (arguments *arguments*) (depth 0))
  (bar-indent depth) (princ arg) (terpri)
  (let ((subarguments nil))
    (dolist (a2 arguments)
      (when
        (and (not (eq a2 arg))
             (subsetp (argument-links a2) (argument-links arg))
             (not (some
                    #'(lambda (s) (subsetp (argument-links arg) (argument-links s)))
                    subarguments)))
        (dolist (s subarguments)
          (when (subsetp (argument-links s) (argument-links arg))
            (pull s subarguments)))
        (push a2 subarguments)))
    (dolist (s subarguments)
      (print-argument-relations s subarguments (+ 5 depth)))))

(defun display-arguments ()
  (dolist (n *nodes-done*)
    (princ n) (princ " for ") (print-sequent (hypernode-sequent n)) (terpri)
    (let ((arguments (subset #'(lambda (a) (eq (argument-node a) n)) *arguments*)))
      (dolist (arg arguments)
        (princ arg) (terpri)))
    ; (print-argument-relations arg)))
    (princ "-------------------------") (terpri)))

(defun display-settings ()
  (terpri)
  (princ "(") (terpri)
  (princ "======================================================================")
  (terpri) (terpri)
  (princ "                                 ") (princ *version*) (princ "          ")
  (let ((time (multiple-value-list (get-decoded-time))))
    (princ (mem5 time)) (princ "/") (princ (mem4 time)) (princ "/")
    (princ (mem6 time)) (princ "          ") (princ (mem3 time))
    (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem2 time))
    (princ ":") (if (< (mem2 time) 10) (princ "0")) (princ (mem1 time))
    (terpri) (terpri))
  (when *msg* (princ *msg*) (terpri) (terpri))
  (princ "Forwards-substantive-reasons:") (terpri)
  (dolist (R *forwards-substantive-reasons*)
    (princ "          ") (princ R) (terpri))
  (terpri)
  (princ "Backwards-substantive-reasons:") (terpri)
  (dolist (R *backwards-substantive-reasons*)
    (princ "          ") (princ R) (terpri))
  (terpri)
  (when (not (zerop *start-time*))
    (princ "Start reasoning at cycle ") (princ *start-time*) (terpri) (terpri))
  (princ "Inputs:") (terpri)
  (dolist (x *inputs*)
    (princ "          ") (prinp (mem2 x)) (princ " : at cycle ") (princ (mem1 x))
    (princ " with justification ") (princ (mem3 x)) (terpri))
  (terpri)
  (when **premises**
    (setf **premises** (mapcar #'(lambda (x) (cons (reform-if-string (car x)) (cdr x))) **premises**))
    (princ "Given:") (terpri)
    (dolist (P **premises**)
      (princ "          ") (prinp (mem1 P)) (princ "  : ")
      (when (mem3 P) (princ " at cycle ") (princ (mem3 P)))
      (princ " with justification = ") (princ (mem2 P)) (terpri))
    (terpri))
  ; (setf *permanent-ultimate-epistemic-interests* *fixed-ultimate-epistemic-interests*)
  (setf *fixed-ultimate-epistemic-interests* nil)
  (setf *query-number* 0)
  (when *substantive-interests*
    (princ "Ultimate epistemic interests:") (terpri)
    (dolist (interest *substantive-interests*)
      (let ((query
              (make-query
                :query-number (incf *query-number*)
                :query-formula (reform-if-string (mem1 interest))
                :query-strength (mem2 interest))))
        (pushnew query *fixed-ultimate-epistemic-interests*
                 :test #'(lambda (x y) (equal (query-formula x) (query-formula y))))
        (princ "     ")
        (prinp (query-formula query)) (princ "    degree of interest = ") (princ (mem2 interest))
        (terpri))))
  (princ "======================================================================")
  (terpri) (terpri))

#| This is a list of pairs (formula degree-of-interest). |#
(defvar *substantive-interests* nil)
(defun inference-number (x) (declare (ignore x)) (error "not implemented"))

#| SIMULATE-OSCAR updates *percepts* by looking at a predetermined list *inputs*. |#
(defun SIMULATE-OSCAR (n &optional (reductio? nil))
  (let ((problem (assoc n *simulation-problems*)))
    (when (null problem)
      (princ "There is no problem of this number.") (terpri) (return-from simulate-oscar))
    (setf *use-reductio* reductio?)
    (setf *problem-number* (mem1 problem))
    (setf *msg* (mem2 problem))
    (setf *start-time* (mem3 problem))
    (setf *forwards-substantive-reasons* (mem4 problem))
    (setf *backwards-substantive-reasons* (mem5 problem))
    (setf *inputs* (mem6 problem))
    (setf **premises** (mem7 problem))
    (setf *substantive-interests* (mem8 problem))
    (let ((pp *print-pretty*))
      (setf *print-pretty* nil)
      (display-settings)
      (setf *premises* **premises**)
      (initialize-reasoner)
      (dolist (query *ultimate-epistemic-interests*)
        (reason-backwards-from-query query (query-strength query) 0))
      (setf *empty-inference-queue* nil)
      (setf *cycle* *start-time*)
      (let* ((max-input-cycle (maximum0 (union= (domain *inputs*) (mapcar #'caddr *premises*))))
             (time (get-internal-run-time))
             (abort-time (if *time-limit* (+ (* *time-limit* internal-time-units-per-second 60) time))))
        ; (when (not *display?*) (gc))
        (catch 'die
               (loop
                 (cond (*inference-queue*
                         (if *empty-inference-queue* (setf *empty-inference-queue* nil)))
                       ((> *cycle* max-input-cycle)
                        (return))
                       ((not *empty-inference-queue*)
                        (setf *empty-inference-queue* t)
                        (when *display?*
                          (terpri) (terpri)
                          (princ "-------------------------------------------------") (terpri) (terpri)
                          (princ "                    Waiting for input") (terpri) (terpri)
                          (princ "-------------------------------------------------") (terpri)
                          (terpri) (terpri))))
                 (incf *cycle*)
                 (update-percepts)
                 (dolist (percept *percepts*)
                   (pull percept *percepts*)
                   (queue-percept percept))
                 (dolist (premise *premises*)
                   (when (eq (mem3 premise) *cycle*)
                     (pull premise *premises*)
                     (queue-premise premise)))
                 (think)
                 (when (and abort-time (> (get-internal-run-time) abort-time))
                   (princ "NO PROOF WAS FOUND WITHIN ") (princ *time-limit*) (princ " MINUTES.")
                   (throw 'die nil))
                 ; (initiate-actions)
                 ))
        (setf time (- (get-internal-run-time) time))
        (display-queries) (terpri)
        (when (not *display?*)
          (princ "Elapsed time = ") (display-run-time-in-seconds time) (terpri))
        (let ((nodes nil))
          (dolist (query *ultimate-epistemic-interests*)
            (dolist (N (query-answers query))
              (pushnew N nodes)))
          (compute-relevant-nodes nodes)
          (let ((argument-length (length *relevant-nodes*)))
            (cond (*proofs?* (terpri) (show-arguments))
                  (t (princ "Cumulative size of arguments = ") (princ argument-length) (terpri)
                     (princ "Size of inference-graph = TODO N/A") ; TODO N/A (princ *inference-number*)
                     (princ " of which ") (princ *unused-suppositions*)
                     (princ " were unused suppositions.") (terpri)
                     ; TODO N/A (princ (truncate (* argument-length 100) *inference-number*))
                     (princ "(TODO N/A) % of the inference-graph was used in the argument.") (terpri)))
            (princ *interest-number*) (princ " interests were adopted.") (terpri)
            (when *display?*
              (princ "The following nodes were used in the arguments:") (terpri)
              (print-list (order (mapcar #'inference-number *relevant-nodes*) #'<) 40))))
        (terpri)
        (when *log-on* (terpri) (display-reasoning) (display-queries))
        (princ ")") (terpri)
        (setf *print-pretty* pp)))))

(defun SO (n &optional r) (simulate-oscar n r))

(defun competing-percepts (P Q)
  (or (equal P (neg Q))
      (cond
        ((listp Q)
         (when (listp P)
           (cond  ;; P has the form ('color-of x y)
             ((equal (car P) 'color-of)
              (and
                (equal (car Q) 'color-of)
                (equal (mem2 Q) (mem2 P))
                (not (equal (mem3 Q) (mem3 P)))))
             ))))))

;(defun arithmetical-value (x)
;    (ignore-errors (eval x)))

(defmacro make-simulation-problem (&rest body)
  (when (not (boundp '*simulation-problems*)) (setf *simulation-problems* nil))
  (let* ((newbody (make-clauses body))
         (number (cadr (find-if #'(lambda (x) (eq (car x) :number)) newbody)))
         (start-time (cadr (find-if #'(lambda (x) (eq (car x) :start-time)) newbody)))
         (message
           (if number (cat-list
                        (list "Problem number " (write-to-string number) ":  "
                              (cadr (find-if #'(lambda (x) (eq (car x) :message)) newbody))))
             (cadr (find-if #'(lambda (x) (eq (car x) :message)) newbody))))
         (reasons
           (mapcar 'eval (cdr (find-if #'(lambda (x) (eq (car x) :reasons)) newbody))))
         (forwards-reasons (subset #'forwards-reason-p reasons))
         (backwards-reasons (subset #'backwards-reason-p reasons))
         (inputs
           (mapcar #'(lambda (x) (list (car x) (reform-if-string (mem2 x)) (mem3 x)))
                   (cdr (find-if #'(lambda (x) (eq (car x) :inputs)) newbody))))
         (premises (cdr (find-if #'(lambda (x) (eq (car x) :premises)) newbody)))
         (interests
           (mapcar #'(lambda (x) (cons (reform-if-string (car x)) (cdr x)))
                   (cdr (find-if #'(lambda (x) (eq (car x) :interests)) newbody)))))
    (when premises
      (setf premises
            (mapcar #'(lambda (p) (list (mem1 p) (mem2 p) (mem3 p))) premises)))
    `(setf *simulation-problems*
           (cons (list ,number ,message (or ,start-time 0) ',forwards-reasons
                       ',backwards-reasons ',inputs ',premises ',interests)
                 (remove-if-equal (assoc ,number *simulation-problems*)
                                  *simulation-problems*)))))

; `(pushnew (list ,number ,message (or ,start-time 0) ',forwards-reasons
;                     ',backwards-reasons ',inputs ',premises ',interests)
;                     *simulation-problems* :test 'equal)))

;; ======================================================================

(let ((P (gensym)) (Q (gensym)) (x (gensym)) (y (gensym)) (A (gensym)) (z (gensym)) (op (gensym)))
  (setf *reform-list* nil)
  (dolist
    (pair
      (list
        `((,P throughout (,op ,x ,y)) (throughout ,P (,op ,x ,y)) (,P ,op ,x ,y))
        `((,P at ,x) (throughout ,P (closed ,x ,x)) (,P ,x))
        `((,P now) (at ,P now) (,P))
        `(((it appears to me that ,Q) at ,x) (it-appears-to-me-that ,Q (closed ,x ,x)) (,Q ,x))
        `((the probability of ,P given ,Q) (the-probability-of ,P ,Q) (,P ,Q))
        `((I  have a percept with content ,Q) (I-have-a-percept-with-content ,Q) (,Q))
        `((,x < ,y) (< ,x ,y) (,x ,y))
        `((,x <= ,y) (<= ,x ,y) (,x ,y))
        `((,x = ,y) (= ,x ,y) (,x ,y))
        `((,x + ,y) (+ ,x ,y) (,x ,y))
        `((,x * ,y) (* ,x ,y) (,x ,y))
        `((,x expt ,y) (expt ,x ,y) (,x ,y))
        `((,x - ,y) (- ,x ,y) (,x ,y))
        `((,x is a reliable informant) (reliable-informant ,x) (,x))
        `((,x reports that ,P) (reports-that ,x ,P) (,x ,P))
        `((the color of ,x is ,y) (color-of ,x ,y) (,x ,y))
        `((,P when ,A is causally sufficient for ,Q after an interval ,x)
          (causally-sufficient ,P ,A ,Q ,x) (,P ,A ,Q ,x))
        `((,x and ,y collide) (collide ,x ,y) (,x ,y))
        `((the position of ,x is (,y ,z)) (position-of ,x ,y ,z) (,x ,y ,z))
        `((the velocity of ,x is (,y ,z)) (velocity-of ,x ,y ,z) (,x ,y ,z))
        `((,x is dead) (dead ,x) (,x))
        `((,x is alive) (alive ,x) (,x))
        `((,x is a dimensionless billiard ball) (dimensionless-billiard-ball ,x) (,x))
        ))
    (pushnew pair *reform-list* :test 'equal)))

(setf (get 'i 'pretty-form) "I")
;(setf *operators* '(at ))

;; ======================================================================

#| This forms conclusions of the form (P at t). |#

(def-forwards-reason *PERCEPTION*
                     :reason-forwards-premises "(p at time)" (:kind :percept)
                     :conclusions "(p at time)"
                     :variables p time
                     :defeasible? t
                     :strength .98
                     :description "When information is input, it is defeasibly reasonable to believe it.")

#| For now: |#
(defun projectible (p)
  (or (literal p)
      (and (conjunctionp p) (every #'literal (conjuncts p)))))

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

#| For now: |#
#|
(defun temporally-projectible (p)
  (or (literal p)
      (and (conjunctionp p) (every #'literal (conjuncts p)))))
|#

(proclaim '(special *binary-predicates*))

(setf *binary-predicates* '(alive))

(defun temporally-projectible (p)
  (or (atomic-formula p)
      (and (negationp p)
           (or (atomic-formula (negand p))
               (and (listp (negand p))
                    (mem (mem1 (negand p)) *binary-predicates*))))
      (and (conjunctionp p) (every #'atomic-formula (conjuncts p)))))

(def-backwards-reason *TEMPORAL-PROJECTION*
                      :conclusions  "(p throughout (op time* time))"
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
                      :conclusions  "(p throughout (op time* time))"
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
                      :conclusions  "(p throughout (op time* time))"
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
                      :conclusions  "(p throughout (op time* time))"
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
                     :description  "When information is input, it is defeasibly reasonable to believe it.")

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
                      :conclusions  "p"
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
;       (:condition (and (is-inference c) (not (equal w y))))
;    :variables x y w
;    :defeasible? nil)

#| Given an interest in (x < y) where x and y are numbers, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason strict-arithmetical-inequality
                      :conclusions  "(x < y)"
                      :condition  (x < y)
                      :variables  x y)

#| Given an interest in (x <= y) where x and y are numbers, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason arithmetical-inequality
                      :conclusions  "(x <= y)"
                      :condition  (x <= y)
                      :variables  x y)

#|
(def-backwards-reason arithmetical-equality
                      :conclusions  "(x = y)"
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
                      :conclusions  "~(x = y)"
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
                      :conclusions  "(x = y)"
                      :condition   (x = y)
                      :variables  x y)

(def-backwards-reason arithmetical-nonequality
                      :conclusions  "~(x = y)"
                      :condition   (not (x = y))
                      :variables  x y)

#| Given an interest in (x <= now) where x is a number, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason is-past-or-present
                      :conclusions  "(x <= now)"
                      :condition  (<= x *cycle*)
                      :variables  x)

#| Given an interest in (x < now) where x is a number, this checks to see whether it is true.
If it is then the conclusion is drawn, and if it is not then the interest is cancelled as long as it
is not a interest-reductio. |#
(def-backwards-reason is-past
                      :conclusions  "(x < now)"
                      :condition  (< x *cycle*)
                      :variables  x)

(def-backwards-reason *CAUSAL-IMPLICATION*
                      :conclusions  "(Q throughout (op time* time**))"
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
                      :defeasible?  T)

(def-backwards-reason *CAUSAL-IMPLICATION2*
                      :conclusions  "(Q throughout (op time* time**))"
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
                      :defeasible?  T)

(def-backwards-reason *CAUSAL-IMPLICATION+*
                      :conclusions  "(Q throughout (op time* time**))"
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
                      :defeasible?  T)

(def-backwards-reason *INDEXICAL-CAUSAL-IMPLICATION*
                      :conclusions  "Q"
                      :reason-forwards-premises
                      "(A when P is causally sufficient for Q after an interval interval)"
                      (:condition (every #'temporally-projectible (conjuncts Q)))
                      "(A at time)"
                      (:condition ((time + interval) < now))
                      :reason-backwards-premises
                      "(P at time)"
                      :variables  A P Q interval time
                      :defeasible?  T
                      :strength  (expt *temporal-reason-decay* (- now time))
                      :reason-temporal? T)

(def-backwards-undercutter *CAUSAL-UNDERCUTTER*
                           :defeatee *temporal-projection*
                           :reason-forwards-premises
                           "(define -p (neg p))"
                           "(A when Q is causally sufficient for -p after an interval interval)"
                           "(A at time1)"
                           (:condition (and (time0 <= (time1 + interval)) ((time1 + interval) < time)))
                           :reason-backwards-premises
                           "(Q at time00)"
                           (:condition (time00 <= time1))
                           :variables  A Q p -p time0 time00 time time* time1 interval op
                           :defeasible?  T)

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
                           :defeasible?  T)

(def-backwards-undercutter *INDEXICAL-CAUSAL-UNDERCUTTER*
                           :defeatee *indexical-temporal-projection*
                           :reason-forwards-premises
                           "(define -p (neg p))"
                           "(A when Q is causally sufficient for -p after an interval interval)"
                           "(A at time1)"
                           (:condition (and (time0 <= (time1 + interval)) ((time1 + interval) < time)))
                           :reason-backwards-premises
                           "(Q at time00)"
                           (:condition (time00 <= time1))
                           :variables  A Q p -p time0 time00 time time* time1 interval op
                           :defeasible?  T)

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
                           :defeasible?  T
                           :reason-temporal? T)

(def-backwards-undercutter *CAUSAL-UNDERCUTTER-FOR-CAUSAL-IMPLICATION*
                           :defeatee *causal-implication*
                           :reason-forwards-premises
                           "(define -q (neg q))"
                           "(A* when R is causally sufficient for -q after an interval interval*)"
                           "(A* at time1)"
                           (:condition (and ((time + interval) <= (time1 + interval*)) ((time1 + interval*) < time**)))
                           :reason-backwards-premises
                           "(R at time00)"
                           (:condition (time00 <= time1))
                           :variables  A P Q interval time time* time** op A* R -q interval* time1 time00
                           :defeasible?  T)

(def-backwards-undercutter *INDEXICAL-CAUSAL-UNDERCUTTER-FOR-CAUSAL-IMPLICATION*
                           :defeatee *indexical-causal-implication*
                           :reason-forwards-premises
                           "(define -q (neg q))"
                           "(A* when R is causally sufficient for -q after an interval interval*)"
                           "(A* at time1)"
                           (:condition (and ((time + interval) <= (time1 + interval*)) ((time1 + interval*) < now)))
                           :reason-backwards-premises
                           "(R at time00)"
                           (:condition (time00 <= time1))
                           :variables  A P Q interval time time* op A* R -q interval* time1 time00
                           :defeasible?  T)

(def-backwards-reason neg-at-intro
                      :conclusions  "~(P at time)"
                      :condition (not (negationp P))
                      :reason-backwards-premises   "(~P at time)"
                      :variables  P time)

(def-backwards-reason neg-at-intro
    :conclusions  "~(P at time)"
    :reason-backwards-premises   "(~P at time)"
    :variables  P time)

(def-backwards-reason neg-at-intro2
                      :conclusions  "~(~P at time)"
                      :reason-backwards-premises   "(P at time)"
                      :variables  P time)

(def-forwards-reason neg-at-elimination
                     :reason-forwards-premises   "~(P at time)"
                     (:condition (not (negationp P)))
                     :conclusions  "(~P at time)"
                     :variables  P time)

(def-backwards-reason &-at-intro
                      :conclusions  "((P & Q) at time)"
                      :reason-backwards-premises   "((P at time) & (Q at time))"
                      :variables  P Q time)

(def-forwards-reason &-at-elimination
                     :reason-forwards-premises   "((P & Q) at time)"
                     :conclusions  "((P at time) & (Q at time))"
                     :variables  P Q time)

(def-backwards-reason ETERNAL-TRUTHS
                      :conclusions  "(P at time)"
                      :reason-backwards-premises  "P"
                      :variables   P time)

(def-backwards-reason *COLLISION*
                      :conclusions  "((b1 and b2 collide) at time)"
                      :reason-backwards-premises
                      "(some x)(some y)(((the position of b1 is (x y)) at time) & ((the position of b2 is (x y)) at time))"
                      :variables   b1 b2 time)

#| Should this be a degenerate backwards-reason? |#
(def-forwards-reason COLLISION-SYMMETRY
                     :reason-forwards-premises   "((B1 and B2 collide) at time)"
                     :conclusions  "((B2 and B1 collide) at time)"
                     :variables  B1 B2 time)

(def-backwards-reason *NEW-POSITION*
                      :conclusions  "((the position of b is (x y)) at time1)"
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
                     :conclusions  "~((the position of b is (z w)) at time)"
                     :reason-forwards-premises
                     "((the position of b is (x y)) at time)"
                     "((the position of b is (z w)) at time)"
                     (:condition (or (not (x = z)) (not (y = w))))
                     (:clue? t)
                     :variables  b time x y z w)

#|
(def-backwards-reason *POSITION-INCOMPATIBILITY*
                      :conclusions  "~((the position of b is (z w)) at time)"
                      :reason-forwards-premises
                      "((the position of b is (x y)) at time)"
                      (:condition (or (not (x = z)) (not (y = w))))
                      :variables  b time x y z w)
|#

(def-backwards-reason *POSITION-INCOMPATIBILITY-1*
                      :conclusions  "~((the position of b is (z w)) at time)"
                      :reason-forwards-premises
                      "((the position of b is (x y)) at time)"
                      (:condition (not (x = z)))
                      :variables  b time x y z w)

(def-backwards-reason *POSITION-INCOMPATIBILITY-2*
                      :conclusions  "~((the position of b is (z w)) at time)"
                      :reason-forwards-premises
                      "((the position of b is (x y)) at time)"
                      (:condition  (not (y = w)))
                      :variables  b time x y z w)

(def-backwards-reason *VELOCITY-INCOMPATIBILITY-1*
                      :conclusions  "~((the velocity of b is (z w)) at time)"
                      :reason-forwards-premises   "((the velocity of b is (x y)) at time)"
                      :reason-backwards-premises  "~(x = z)"
                      :variables  b time x y z w)

(def-backwards-reason *VELOCITY-INCOMPATIBILITY-2*
                      :conclusions  "~((the velocity of b is (z w)) at time)"
                      :reason-forwards-premises   "((the velocity of b is (x y)) at time)"
                      :reason-backwards-premises  "~(y = w)"
                      :variables  b time x y z w)

(def-backwards-reason inequality-transitivity
                      :conclusions  "(x < y)"
                      :reason-forwards-premises  "(z < y)"
                      :reason-backwards-premises  "(x <= z)"
                      :variables  x y z)

(def-backwards-reason inequality-transitivity2
                      :conclusions  "(x < y)"
                      :reason-forwards-premises  "(x < z)"
                      :reason-backwards-premises  "(z <= y)"
                      :variables  x y z)

(def-backwards-reason PAIR-NONIDENTITY-AT-TIME
                      :conclusions  "(~((x y) = (z w)) at time)"
                      :reason-backwards-premises  "~((x y) = (z w))"
                      :condition  (and (numberp x) (numberp y) (numberp z) (numberp w))
                      :variables  b time x y z w )

(def-backwards-reason PAIR-NONIDENTITY
                      :conclusions  "~((x y) = (z w))"
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
                      :conclusions  "(~(x is alive) at time)"
                      :reason-backwards-premises  "((x is dead) at time)"
                      :variables   x time
                      :description "A person is dead iff he is not alive.")

(def-backwards-reason not-dead-introduction
                      :conclusions  "(~(x is dead) at time)"
                      :reason-backwards-premises  "((x is alive) at time)"
                      :variables   x time
                      :description "A person is alive iff he is not dead.")

(def-forwards-reason dead-elimination
                     :reason-forwards-premises  "((x is dead) at time)"
                     :conclusions  "(~(x is alive) at time)"
                     :variables   x time
                     :description "A person is dead iff he is not alive")

(def-backwards-reason dead-introduction
                      :conclusions  "((x is dead) at time)"
                      :reason-backwards-premises  "(~(x is alive) at time)"
                      :variables   x time
                      :description "A person is dead iff he is not alive")

;(defun readopt-interest (interest defeated-links)
;    (declare (ignore interest defeated-links)))

(def-backwards-reason *NEW-POSITION-*
                      :conclusions  "((the position of b is (x y)) at time1)"
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
                      :conclusions  "(Q throughout- (time* time**))"
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
                      :conclusions  "(p throughout- (time* time))"
                      :reason-forwards-premises
                      "(p at time0)"
                      (:condition (time0 < time*))
                      :condition  (and (temporally-projectible p) (numberp time*) (numberp time) (<= time* time))
                      :variables p time0 time* time
                      :defeasible? T
                      :strength  (- (* 2 (expt *temporal-reason-decay* (- now time0))) 1)
                      :description
                      "It is defeasibly reasonable to expect temporally projectible truths to remain unchanged.")
;; This runs on OSCAR_3.31
#| To run these problems, first load Perception-Causes_3.31a.lisp.
Then load this file. To run problem n, execute (simulate-oscar n). |#

(setf *simulation-problems* nil)

;======================================================================

(make-simulation-problem
  :number  1
  :message
  "This is the perceptual updating problem.  First, Fred looks red to me.  Later, Fred looks blue to me.
What should I conclude about the color of Fred?"
  :reasons
  *PERCEPTION*
  *TEMPORAL-PROJECTION*
  *incompatible-colors*
  :inputs
  (1   "(the color of Fred is red)" 1.0)
  (30   "(the color of Fred is blue)" 1.0)
  :interests
  ("(? x)((the color of Fred is x) at 50)" 0.2)
  )

;======================================================================

(make-simulation-problem
  :number  2
  :message
  "This is the perceptual updating problem.  First, Fred looks red to me.  Later, Fred looks blue to me.
What should I conclude about the color of Fred?"
  :reasons
  *INDEXICAL-PERCEPTION*
  *indexical-incompatible-colors*
  :inputs
  (1   "(the color of Fred is red)" 1.0)
  (30   "(the color of Fred is blue)" 1.0)
  :interests
  ("(? x)(the color of Fred is x)" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  3
  :message
  "First, Fred looks red to me.  Later, I am informed by Merrill that I am then
wearing blue-tinted glasses.  Later still, Fred looks blue to me.  All along, I know that the
probability is not high of Fred being blue given that Fred looks blue to me, but I am
wearing blue tinted glasses.  What should I conclude about the color of Fred?"
  :reasons
  *PERCEPTION*
  *RELIABLE-INFORMANT*
  *PERCEPTUAL-RELIABILITY*
  *TEMPORAL-PROJECTION*
  *INCOMPATIBLE-COLORS*
  :inputs
  (1   "(the color of Fred is red)" 0.8)
  (20   "(Merrill reports that I_am_wearing_blue_tinted_glasses)" 1.0)
  (30   "(the color of Fred is blue)" 0.8)
  :premises
  ("((the probability of (the color of Fred is blue) given
    ((I have a percept with content (the color of Fred is blue)) & I_am_wearing_blue_tinted_glasses)) <= .8)"
    1.0)
  ("(Merrill is a reliable informant)" 1.0)
  :interests
  ("(? x)((the color of Fred is x) at 50)" 0.55)
  )

;======================================================================
;; This requires the temporal-projectibility of ~my_surroundings_are_illuminated_by_red_light.

(make-simulation-problem
  :number  4
  :message
  "This illustrates the use of discounted-perception and perceptual-unreliability."
  :reasons
  *perception*
  *discounted-perception*
  *perceptual-reliability*
  *perceptual-unreliability*
  *temporal-projection*
  neg-at-intro
  :inputs
  (10 "(the color of Fred is red)" 1.0)

  :premises
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red))
       & my_surroundings_are_illuminated_by_red_light)) <= .7)"
    1.0)
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red)) & I_am_wearing_red_tinted_glasses)) <= .8)"
    1.0)
  ("(I_am_wearing_red_tinted_glasses at 1)" 1.0 15)
  ("(my_surroundings_are_illuminated_by_red_light at 1)" 1.0 30)
  ("(~my_surroundings_are_illuminated_by_red_light at 8)" 1.0 50)
  :interests
  ("((the color of Fred is red) at 10)" 0.5)
  )

;======================================================================
;; This requires the temporal-projectibility of ~my_surroundings_are_illuminated_by_red_light.

(make-simulation-problem
  :number  5
  :message
  "This illustrates the use of discounted-indexical-perception and indexical-perceptual-unreliability."
  :reasons
  *indexical-perception*
  *discounted-indexical-perception*
  *indexical-perceptual-reliability*
  *indexical-perceptual-unreliability*
  *temporal-projection*
  neg-at-intro
  :inputs
  (10 "(the color of Fred is red)" 1.0)

  :premises
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red))
       & my_surroundings_are_illuminated_by_red_light)) <= .7)"
    1.0)
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red)) & I_am_wearing_red_tinted_glasses)) <= .8)"
    1.0)
  ("(I_am_wearing_red_tinted_glasses at 1)" 1.0 15)
  ("(my_surroundings_are_illuminated_by_red_light at 1)" 1.0 30)
  ("(~my_surroundings_are_illuminated_by_red_light at 8)" 1.0 50)
  :interests
  ("(the color of Fred is red)" 0.5)
  )

;======================================================================
(make-simulation-problem
  :number  6
  :message
  "This is the Yale Shooting Problem.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired.  Should I conclude that Jones becomes dead?"
  :reasons
  neg-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER+*
  *CAUSAL-IMPLICATION*
  neg-at-intro
  :inputs
  :premises
  ("(the_gun_is_loaded at 20)" 1.0)
  ("((Jones is alive) at 20)" 1.0)
  ("(the_gun_is_fired at 30)" 1.0)
  ("(all x)(all time)(((x is dead) at time) <-> ~((x is alive) at time))" 1.0)
  ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           (Jones is dead) after an interval 10)" 1.0)
  :interests
  ("((Jones is alive) at 50)" 0.75)
  ("((Jones is dead) at 50)" 0.75)
  )

;======================================================================
(make-simulation-problem
 :number  7
 :message
  "This is the solved Yale Shooting Problem.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired.  Should I conclude that Jones becomes dead?"
  :reasons
   neg-at-elimination
   *TEMPORAL-PROJECTION*
   *CAUSAL-UNDERCUTTER*
   *CAUSAL-IMPLICATION*
   neg-at-intro
   :inputs
   :premises
   ("(the_gun_is_loaded at 20)" 1.0)
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   :interests
    ("(? ((Jones is alive) at 50))" 0.75)
   )

;======================================================================
(make-simulation-problem
 :number  13
 :message
  "This illustrates sequential causation. This requires causal undercutting for
causal implication.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired. But I also know that he will be resuscitated later, and then he will
be alive.  Should I conclude that Jones becomes dead? This version is solved incorrectly."
  :reasons
   neg-at-elimination
   *TEMPORAL-PROJECTION*
   *CAUSAL-UNDERCUTTER*
   *CAUSAL-IMPLICATION*
   neg-at-intro
   neg-at-intro2
   :inputs
   :premises
   ("(the_gun_is_loaded at 20)" 1.0)
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(Jones_is_resuscitated at 45)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   ("(Jones_is_resuscitated when ~(Jones is alive) is causally sufficient for
                           (Jones is alive) after an interval 5)" 1.0)
   :interests
    ("(? ((Jones is alive) at 60))" 0.75)
   )
;======================================================================
(make-simulation-problem
 :number  14
 :message
  "This illustrates sequential causation. This requires causal undercutting for
causal implication.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired. But I also know that he will be resuscitated later, and then he will
be alive.  Should I conclude that Jones becomes dead?"
  :reasons
   neg-at-elimination
   *TEMPORAL-PROJECTION*
   *CAUSAL-UNDERCUTTER*
   *CAUSAL-IMPLICATION*
   *CAUSAL-UNDERCUTTER-FOR-CAUSAL-IMPLICATION*
   neg-at-intro
   neg-at-intro2
   :inputs
   :premises
   ("(the_gun_is_loaded at 20)" 1.0)
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(Jones_is_resuscitated at 45)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   ("(Jones_is_resuscitated when ~(Jones is alive) is causally sufficient for
                           (Jones is alive) after an interval 5)" 1.0)
   :interests
    ("(? ((Jones is alive) at 60))" 0.75)
   )
;======================================================================
(make-simulation-problem
 :number  8
 :message
  "This is the indexical Yale Shooting Problem.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired.  Should I conclude that Jones becomes dead?"
  :reasons
   *INDEXICAL-TEMPORAL-PROJECTION*
   *TEMPORAL-PROJECTION*
   *INDEXICAL-CAUSAL-UNDERCUTTER*
   *INDEXICAL-CAUSAL-IMPLICATION*
   :start-time 50
   :inputs
   :premises
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_loaded at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   :interests
   ("(? (Jones is alive))" 0.75)
   )

;======================================================================

(make-simulation-problem
  :number  9
  :message
  "1.  An interest in whether b1 and b2 collide at 10 generates an interest in their positions at 10.
Because we know their positions at 0, we adopt interest in their velocities between 0 and 10.

2.  We know the velocities at 0, and temporal-projection leads to an inference that those velocities
remain unchanged between 0 and 10.  From that we can compute the positions at 10, and infer
that b1 and b2 collide at 10.

3.  However, temporal projection also leads to an inference that the positions at 10 are the
same as those at 0.  Because the velocities at 0 are nonzero, causal undercutting defeats this
inference, leaving us with a unique conclusion regarding the positions at 10 (they are at (5.0 3.0)).
"
  :reasons
  neg-at-elimination
  &-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER*
  *COLLISION*
  *NEW-POSITION*
  *POSITION-INCOMPATIBILITY-1*
  *POSITION-INCOMPATIBILITY-2*
  strict-arithmetical-inequality
  arithmetical-inequality
  is-past-or-present
  neg-at-intro
  arithmetical-nonequality
  inequality-transitivity
  pair-nonidentity
  pair-nonidentity-at-time
  &-at-intro
  arithmetical-equality
  :inputs
  :premises
  ("((the position of b1 is (0.0 3.0)) at 0)" 1.0)
  ("((the position of b2 is (1.0 0.0)) at 0)" 1.0)
  ("(all b)(all x)(all y)(all vx)(all vy)
  ((the velocity of b is (vx vy))
     when ((the position of b is (x y)) & ~((vx vy) = (0.0 0.0)))
  is causally sufficient for ~(the position of b is (x y)) after an interval 0)" 1.0)
  ("((the velocity of b1 is (.5 0.0)) at 0)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 0)" 1.0)
  ("(5.0 = (0.0 + (0.5 * (10 - 0))))" 1.0)
  ("(3.0 = (3.0 + (0.0 * (10 - 0))))" 1.0)
  ("(5.0 = (1.0 + (0.4 * (10 - 0))))" 1.0)
  ("(3.0 = (0.0 + (0.3 * (10 - 0))))" 1.0)

  :interests
;  ("(? ((b1 and b2 collide) at 10))" 0.75)
  ("(? x)(? y) ((the position of b1 is (x y)) at 10)" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  10
  :message
"
1.  An interest in whether b1 and b2 collide at 10 generates an interest in their positions at 10.
Because we know their positions at 0, we adopt interest in their velocities between 0 and 10.

2.  We know the velocities at 0, and temporal-projection leads to an inference that those velocities
remain unchanged between 0 and 10.  From that we can compute the positions at 10, and infer
that b1 and b2 collide at 10.

3.  However, temporal projection also leads to an inference that the positions at 10 are the
same as those at 0.  Because the velocities at 0 are nonzero, causal undercutting defeats this
inference, leaving us with a unique conclusion regarding the positions at 10 (they are at (5.0 3.0)).
"
  :reasons
  neg-at-elimination
  &-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER*
  *COLLISION*
  *NEW-POSITION*
  *POSITION-INCOMPATIBILITY-1*
  *POSITION-INCOMPATIBILITY-2*
  strict-arithmetical-inequality
  arithmetical-inequality
  is-past-or-present
  neg-at-intro
  arithmetical-nonequality
  inequality-transitivity
  pair-nonidentity
  pair-nonidentity-at-time
  &-at-intro
  arithmetical-equality
  ; *CAUSAL-IMPLICATION*
  ; COLLISION-SYMMETRY
  ; *CAUSAL-UNDERCUTTER+*
  :inputs
  :premises
  ("((the position of b1 is (0.0 3.0)) at 0)" 1.0)
  ("((the position of b2 is (1.0 0.0)) at 0)" 1.0)
  ("(all b)(all x)(all y)(all vx)(all vy)
  ((the velocity of b is (vx vy))
     when ((the position of b is (x y)) & ~((vx vy) = (0.0 0.0)))
  is causally sufficient for ~(the position of b is (x y)) after an interval 0)" 1.0)
  ("((the velocity of b1 is (.5 0.0)) at 0)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 0)" 1.0)
  ("(5.0 = (0.0 + (0.5 * (10 - 0))))" 1.0)
  ("(3.0 = (3.0 + (0.0 * (10 - 0))))" 1.0)
  ("(5.0 = (1.0 + (0.4 * (10 - 0))))" 1.0)
  ("(3.0 = (0.0 + (0.3 * (10 - 0))))" 1.0)
 ; ("((0 + 0) < 10)" 1.0)

  :interests
  ("(? ((b1 and b2 collide) at 10))" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  11
  :message
  "1.  We are given the velocities of b1 and b2 at 0, and are told they collide at (5 3) at 10.
We are interested in the velocity of b1 at 20.

2.  By causal-implication, we can infer that the velocity of b1 at 20 is (.4 .3).

3.  By temporal projection, we can also infer that the velocity of b1 at 20 is (.5 .0).  But this
is defeated by causal-undercutter+, because we also know that if the velocity is (.4 .3) then
it is not (.5 .0).
"
  :reasons
  neg-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER+*
  *CAUSAL-UNDERCUTTER*
  *CAUSAL-IMPLICATION*
  *COLLISION*
  *NEW-POSITION*
  strict-arithmetical-inequality
  arithmetical-inequality
  is-past-or-present
  neg-at-intro
  arithmetical-nonequality
  inequality-transitivity
  :inputs
  :premises
  ("((the velocity of b1 is (.5 0.0)) at 10)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 10)" 1.0)
  ("(b1 is a dimensionless billiard ball)" 1.0)
  ("(b2 is a dimensionless billiard ball)" 1.0)
  ("((b1 and b2 collide) at 10)" 1.0)
  ("(((.5 expt 2) + (0.0 expt 2)) = ((.4 expt 2) + (.3 expt 2)))" 1.0)
  ("(same-mass b1 b2)" 1.0)
  ("(all b)(all time) (((the velocity of b is (0.4 0.3)) at time)
                              -> ~((the velocity of b is (0.5 0.0)) at time))" 1.0)
  ("(all b)(all time) (((the velocity of b is (0.5 0.0)) at time)
                              -> ~((the velocity of b is (0.4 0.3)) at time))" 1.0)
  ("(all b1)(all b2)(all v1x)(all v1y)(all v2x)(all v2y)
    ((((b1 is a dimensionless billiard ball) & (b2 is a dimensionless billiard ball))
      & ((same-mass b1 b2) & (((v1x expt 2) + (v1y expt 2)) = ((v2x expt 2) + (v2y expt 2)))))
      ->
      ((b1 and b2 collide)
         when (the velocity of b2 is (v2x v2y))
        is causally sufficient for (the velocity of b1 is (v2x v2y))
        after an interval 0))" 1.0)
  ("(all b1)(all b2)(all v1x)(all v1y)(all v2x)(all v2y)
    ((((b1 is a dimensionless billiard ball) & (b2 is a dimensionless billiard ball))
      & ((same-mass b1 b2) & (((v1x expt 2) + (v1y expt 2)) = ((v2x expt 2) + (v2y expt 2)))))
      ->
      ((b1 and b2 collide)
         when (the velocity of b1 is (v2x v2y))
        is causally sufficient for (the velocity of b2 is (v2x v2y))
        after an interval 0))" 1.0)

  :interests
  ("(? x)(? y) ((the velocity of b1 is (x y)) at 20)" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  12
  :message
"  This is the Extended Prediction Problem.

1.  We are given the velocities of b1 and b2 at 0, and are told they collide at (5 3) at 10.
We are interested in the position of b1 at 20.  Given knowledge of the position of b1 at 10,
this generates an interest in the velocity of b1 between 10 and 20.

2.  By causal-implication, we can infer that the velocity of b1 between 10 and 20 is (.4 .3).
From this we can compute that the position of b1 at 20 is (9.0 6.0).

3.  By temporal projection, we can also infer that the velocity of b1 at 20 is (.5 .0).  But this
is defeated by causal-undercutter, because we also know that if the velocity is (.4 .3) then
it is not (.5 .0).

4.  By temporal projection, we can infer that the position of b1 at 20 is the same as at 0.
But this is defeated by causal-undercutter, because we know that the velocity of b1 at 0
is nonzero.

5.  By temporal projection, we can infer that the position of b1 at 20 is the same as at 10.
This is defeated in the same fashion as (4), because we know the velocity of
b1 between 0 and 10, and we are given that 10 is between 0 and 10.
"
  :reasons
  *CAUSAL-IMPLICATION*
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER*
  *COLLISION*
  *NEW-POSITION*
  *POSITION-INCOMPATIBILITY*
  pair-nonidentity
  pair-nonidentity-at-time
  &-at-intro
  :inputs
  :premises
  ("((the position of b1 is (0.0 3.0)) at 0)" 1.0)
  ("((the position of b2 is (1.0 0.0)) at 0)" 1.0)
  ("((the velocity of b1 is (.5 0.0)) at 0)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 0)" 1.0)
  ("(b1 is a dimensionless billiard ball)" 1.0)
  ("(b2 is a dimensionless billiard ball)" 1.0)
  ("(all b)(all x)(all y)(all vx)(all vy)
  ((the position of b is (x y))
     when ((the velocity of b is (vx vy)) & ~((vx vy) = (0.0 0.0)))
  is causally sufficient for ~(the position of b is (x y)) after an interval 0)" 1.0)
   ("(all b1)(all b2)(all v1x)(all v1y)(all v2x)(all v2y)
    ((((b1 is a dimensionless billiard ball) & (b2 is a dimensionless billiard ball))
      & ((same-mass b1 b2) & (((v1x expt 2) + (v1y expt 2)) = ((v2x expt 2) + (v2y expt 2)))))
      ->
      ((b1 and b2 collide)
         when (the velocity of b2 is (v2x v2y))
        is causally sufficient for (the velocity of b1 is (v2x v2y))
        after an interval 0))" 1.0)
  ("(same-mass b1 b2)" 1.0)
  ("(5.0 = (0.0 + (0.5 * (10 - 0))))" 1.0)
  ("(3.0 = (3.0 + (0.0 * (10 - 0))))" 1.0)
  ("(5.0 = (1.0 + (0.4 * (10 - 0))))" 1.0)
  ("(3.0 = (0.0 + (0.3 * (10 - 0))))" 1.0)
  ("(9.0 = (5.0 + (0.4 * (20 - 10))))" 1.0)
  ("(6.0 = (3.0 + (0.3 * (20 - 10))))" 1.0)
  ("(((.5 expt 2) + (0.0 expt 2)) = ((.4 expt 2) + (.3 expt 2)))" 1.0)

  :interests
  ("(? ((b1 and b2 collide) at 10))" 0.75)
 ; ("(? x)(? y) ((the velocity of b1 is (x y)) throughout (clopen 10 20))" 0.75)
  ("(? x)(? y) ((the position of b1 is (x y)) at 20)" 0.75)
  )

(setf *problems* (eval-when (:compile-toplevel :execute) (default-problem-list)))

(trace-on)
(display-on)
(proof-on)
(logic-on)
(reductio-on)
(log-on)
(IQ-on)
(graph-log-on)

(test)

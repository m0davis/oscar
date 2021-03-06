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

#| This is a list of pairs (formula degree-of-interest). |#
(defvar *substantive-interests* nil)

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

;;;; removed b/c redefined below
;;;;(defun update-percepts ()
;;;;    (dolist (input (e-assoc *cycle* *inputs*)) (apply #'form-percept input)))

(defun update-percepts ()
  (dolist (input *inputs*)
    (when (eq (car input) *cycle*) (apply #'form-percept (cdr input)))))

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

;(def-backwards-reason neg-at-intro
;    :conclusions  "~(P at time)"
;    :reason-backwards-premises   "(~P at time)"
;    :variables  P time)

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

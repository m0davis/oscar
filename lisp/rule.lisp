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
        :forwards-premises (list (cfp '(& P Q) '(P Q)))
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
        :forwards-premises (list (cfp '(~ (~ P)) '(P)))
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
        :forwards-premises (list (cfp '(~ (v P Q)) '(P Q)))
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
        :forwards-premises (list (cfp '(~ (-> P Q)) '(P Q)))
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
        :forwards-premises (list (cfp '(~ (<-> P Q)) '(P Q)))
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
        :forwards-premises (list (cfp '(~ (& P Q)) '(P Q)))
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
        :forwards-premises (list (cfp '(<-> P Q) '(P Q)))
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
        :forwards-premises (list (cfp '(-> (& P Q) R) '(P Q R)))
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
        :forwards-premises (list (cfp '(-> (v P Q) R) '(P Q R)))
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
        :forwards-premises (list (cfp '(-> (-> P Q) R) '(P Q R)))
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

(setf disj-simp
      (make-forwards-reason
        :reason-name "disj-simp"
        :forwards-premises (list (cfp '(v P Q) '(P Q)))
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
        :forwards-premises (list (cfp '(-> P (~ P)) '(P)))
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
        :forwards-premises (list (cfp '(-> (~ P) P) '(P)))
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
        :forwards-premises (list (cfp '(-> (some x P) Q) '(P Q)))
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
        :forwards-premises (list (cfp '(-> (all x P) Q) '(P Q)))
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
        :forwards-premises
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
                     modus-ponens2 c nil binding (list t) ip (cdr (forwards-premises modus-ponens1)) profile))))
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
        :forwards-premises
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
        :forwards-premises
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
                     modus-tollens2 c nil binding (list t) ip (cdr (forwards-premises modus-tollens1)) profile))))
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
        :forwards-premises
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
        :forwards-premises (list (cfp '(-> P Q) '(P Q)))
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
        :forwards-premises (list (cfp '(~ (all x P)) '(P)))
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
        :forwards-premises (list (cfp '(~ (some x P)) '(P)))
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
        :forwards-premises (list (cfp '(all x P) '(P)))
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
        :forwards-premises (list (cfp '(some x P) '(P)))
        :reason-variables '(x P)))

(defun ei-level (var) (get var 'ei-level))

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


(defun set-conclusions-function (reason)
  (setf (conclusions-function reason)
        (conclusion-instantiator
          (mem1 (reason-conclusions reason)) (reason-variables reason) (defeasible-rule reason))))

; Flat backwards inference rules:

(setf adjunction
      (make-backwards-reason
        :reason-name "adjunction"
        :reason-conclusions '((& p q))
        :backwards-premises
        (list (cbp 'p nil nil '(p)) (cbp 'q nil nil '(q)))
        :reason-variables '(p q)
        :reason-length 2))

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
        :backwards-premises
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
        :backwards-premises
        (list (cbp '(~ p) nil nil '(p)) (cbp '(~ q) nil nil '(q)))
        :reason-variables '(p q)
        :reason-length 2))

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
        :backwards-premises
        (list (cbp '(~ q) nil nil '(q)) (cbp 'p nil nil '(p)))
        :reason-variables '(p q)
        :reason-length 2))

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
        :backwards-premises
        (list (cbp '(-> q p) nil nil '(p q)) (cbp '(-> p q) nil nil '(p q)))
        :reason-variables '(p q)
        :reason-length 2))

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
        :backwards-premises
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
        :backwards-premises
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
        :backwards-premises
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
        :backwards-premises
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
        :conclusions-function
        #'(lambda (binding) (let ((x (cdr (assoc 'x binding))) (q (cdr (assoc 'q binding)))) (list '~ (list 'all x q))))
        :backwards-premises
        (list (cbp '(all x (~ q)) nil nil '(x q)))
        :reason-variables '(x q)
        :reason-length 1))

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
        :backwards-premises
        (list (cbp '(some x (~ q)) nil nil '(x q)))
        :reason-variables '(x q)
        :reason-length 1))

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
        :backwards-premises 'q
        :reason-variables '(x q)
        :reason-length 1))

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
             :link-strength (maximum-degree-of-interest interest)
             :link-binding (list (cons 'x (element 1 p)) (cons 'q (element 2 p)))
             )))
    (push link *interest-links*)
    (push link (interest-left-links interest))
    (setf (get fun 'ei-level) 0)
    (compute-link-interest
      link #'(lambda (i) (eq (discharge-condition i) ug-condition))
      #'(lambda (i) (setf (discharge-condition i) ug-condition))
      (interest-degree-of-interest interest) (maximum-degree-of-interest interest) depth priority)
    (discharge-link link (1+ depth) (interest-degree-of-interest interest) priority nil)
    ))

(set-conclusions-function UG)
(setf (reason-function UG) #'UG)

(setf EG
      (make-backwards-reason
        :reason-name "EG"
        :reason-conclusions '((some x q))
        :backwards-premises 'q
        :reason-variables '(x q)
        :reason-length 1))

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
             :link-strength (maximum-degree-of-interest interest)
             :link-binding (list (cons 'x (element 1 p)) (cons 'q (element 2 p)))
             )))
    (push link *interest-links*)
    (push link (interest-left-links interest))
    (compute-link-interest
      link nil nil (interest-degree-of-interest interest) (maximum-degree-of-interest interest) depth priority (list var))
    (discharge-link link (1+ depth) (interest-degree-of-interest interest) priority nil)
    ))

(set-conclusions-function EG)
(setf (reason-function EG) #'EG)

(def-backwards-reason VACUOUS-CONDITION
                      :conclusions "(p -> q)"
                      :forwards-premises
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
                      :backwards-premises "~p"
                      :discharge "~q"
                      :variables  p q)

(def-backwards-reason conditionalization
                      :conclusions "(p -> q)"
                      :condition (or (u-genp p)
                                     (and (literal p) (not (e-genp q)))
                                     (conjunctionp (quantifiers-matrix p))
                                     (not (e-genp q)))
                      :backwards-premises "q"
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

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

#|
(defstruct (hypernode (:print-function print-hypernode)
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
  (hypernode-ancestors nil)
  (hypernode-nearest-defeasible-ancestors nil)
  (hypernode-answered-queries nil)
  (hypernode-deductive-only nil)   ;; If conclusion is for deductive purposes only, this is t.
  (generated-interests nil)
  (generating-interests nil);; interest generating sup
  (cancelled-node nil)
  (discounted-node-strength nil)
  (processed? nil)  ;;  T if node has been processed.
  (hypernode-variables nil)
  (discharged-interests nil)  ;; triples (interest unifier unifiers) where unifiers is produced by
  ;; appropriately-related-suppositions.  unifier and unifiers are
  ;; left nil in cases where they will not be used.
  (hypernode-supposition-variables nil)
  (interests-discharged? nil)   ;; records whether interests have been discharged
  (reductios-discharged (not *use-reductio*))  ;; records whether reductio-interests have been discharged
  (readopted-supposition 0)  ;; number of times the node has been readopted as a supposition
  (hypernode-discount-factor 1.0)  ;; This is the discount-factor provided by the hypernode-rule.
  ;;  its only use is in ei.
  (hypernode-c-list nil)
  (hypernode-queue-node nil)
  (enabling-interests nil)  ;; if the node is obtained by discharging inference-links, this is the
  ;; list of resultant-interests of the links.
  (motivating-nodes nil)  ;; nodes motivating the inference, not included in the basis.
  (generated-direct-reductio-interests nil)
  (generated-defeat-interests nil)
  (generating-defeat-interests nil)  ;; interest in defeaters discharged by this node
  (temporal-node nil)  ;; nil or the cycle on which the node was constructed
  (background-knowledge nil)
  (non-reductio-supposition? nil)
  (anchoring-interests nil)
  (hypernode-justifications nil)  ;; list of pairs (sigma.val) used by justification
  (hypernode-in (list nil))  ;; list of  lists of links
  (hypernode-dependencies nil)   ;; list of sigmas
  )

(defstruct (hyperlink (:print-function print-hyperlink)
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

(defstruct (hyper-defeat-link (:print-function print-hyper-defeat-link)
                              (:conc-name nil))
  (hyper-defeat-link-number 0)
  (hyper-defeat-link-target nil)   ;; the hyperlink defeated by the link
  (hyper-defeat-link-root nil)   ;; an hypernode
  (hyper-defeat-link-critical? nil)  ;; list of (X.t) or (sigma.nil)
  (hyper-defeat-link-justifications nil)  ;; list of pairs (sigma.val).
  (hyper-defeat-link-in (list nil))  ;; list of  lists of links
  )
|#

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

;; d-loop is a defeat-loop
(defun sigma-defeat-loop (d-loop sigma)
  (or (null (cdr sigma)) (every #'(lambda (L) (mem (cdr sigma) (hyper-defeat-link-in L))) d-loop)))

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

(defun clear-graph-memories ()
  (dolist (node *hypergraph*) (setf (hypernode-in node) nil))
  (dolist (link *hyperlinks*) (setf (hyperlink-in link) nil))
  (dolist (DL *hyper-defeat-links*) (setf (hyper-defeat-link-in DL) nil)))

(defun compute-new-hypergraphs (link &optional sigma (indent 0))
  (clear-graph-memories)
  (split-hypergraph link sigma indent))

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
          (setf (discounted-node-strength node) (hyperlink-discount-factor link))
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

(defun compute-hypernode-degrees-of-justification ()
  ;  (when (equal *cycle* 3) (break))
  ; (step (compute-hypernode-degrees-of-justification))
  (dolist (link *new-links*) (reset-memories link))
  (dolist (link *new-links*) (compute-affected-justifications link)))

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
                     (setf (discounted-node-strength node)
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

(defun ~ (x y)
  (if (>= y x) 0.0 (- x y)))

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

(defun print-hypernode (x stream depth)
  (declare (ignore depth))
  (princ "#<" stream) (princ "Hypernode " stream)
  (princ (hypernode-number x) stream)
  (princ ": " stream)
  (if (hypernode-supposition x) (print-sequent (hypernode-sequent x) stream)
    (princ (pretty (hypernode-formula x)) stream))
  (princ ">" stream))

(defun critical-set (links paths)
  (every #'(lambda (p) (some #'(lambda (L) (member L p)) links)) paths)
  (not (some
         #'(lambda (link)
             (let ((links0 (remove link links)))
               (every #'(lambda (p) (some #'(lambda (L) (member L p)) links0)) paths)))
         links)))

; (critical-set (list (hyper-defeat-link 4)) (hyperlink-defeat-loops (hyperlink 8)))

; (critical-set (list (hyper-defeat-link 1) (hyper-defeat-link 2) (hyper-defeat-link 3)) (hyperlink-defeat-loops (hyperlink 8)))

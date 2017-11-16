(defunction DRAW-CONCLUSION
                                         (car p)
                                         (v (~ (subset #:|^x18| 
#:^@\y38)) (~ (subset #:^@\y38 #:|^x18|)))
                                         (cons node (supporting-nodes link))
                                         (#<Node 535>)
                                         (link-rule link)
                                         disj-cond
                                         instantiations = (t)   This 
is the problem. It should tell us how 535 is instantiated.
                                         (discount-factor (link-rule link))
                                         1.0
                                         depth = 4
                                         (cdr p)
                                         nil
                                         binding = ((p ~ (subset 
#:|^x18| #:^@\y38)) (q ~ (subset #:^@\y38 #:|^x18|)))
                                         (resultant-interest link)
                                         #<Interest 44>
                                         link = #<Link 19: for 
interest #44 by disj-cond>
                                         (link-clues link)
                                         nil
     (formula basis rule instantiations discount depth interests defeasible?
                    &key interest motivators binding link (supposition t) clues)
     ; (when (eql *inference-number* 10) (setf f formula b basis r 
rule i instantiations d discount d* depth in interests def 
defeasible? in* interest bi binding) (break) )
     ;;  (step (draw-conclusion f b r i d d* in def :interest in* :binding bi))
     (when (and formula (not (some #'cancelled-node basis))
                         (not (inconsistent-supposition basis)))
          (setf basis (reverse basis))
          (setf instantiations (reverse instantiations))
          (let* ((NDA (compute-nearest-defeasible-ancestors basis rule))
                    (discharge (if (backwards-reason-p rule)
                               (remove-double-negation (match-sublis 
binding (reason-discharge rule)))))
                    (CD (conclusion-data basis instantiations 
discharge supposition)))
            (when CD
                 (let* ((RA (mem1 CD))
                           (NR (mem2 CD))
                           (sup (mem3 CD))
                           (sequent (list sup formula))
                           (d-node (d-node-for formula))
                           (c-list (if d-node (fetch-c-list-for 
formula d-node)))
                           (proof-nodes (if c-list (c-list-nodes c-list)))
                           (node (find-if #'(lambda (c)
                                                       (and (eq 
(node-kind c) :inference)
                                                                (== 
(node-supposition c) sup)))
                                                 proof-nodes))
                           (new-node? (null node)))
                   (when
                        (and
                          (not (some #'(lambda (f) (mem (neg f) sup)) sup))
                          (or (null d-node)
                                (not (subsumed node basis sequent NDA 
NR rule binding d-node))))
                        (let* ((deductive-only (and (not (eq rule :reductio))
 
(some #'deductive-only basis))))
                          (when (and node (deductive-only node) (not 
deductive-only))
                               (setf (deductive-only node) nil))
                          (when (null node)
                               (setf node (make-new-conclusion sequent 
deductive-only RA NR)))
                          (let ((old-degree 
(compute-maximal-degree-of-support node))
                                  (support-link
                                    (build-support-link
                                      basis clues rule discount node 
NDA binding link instantiations depth defeasible?)))
                            (cond
                              ((null support-link)
                                (decf *support-link-number*)
                                (when new-node? (decf *inference-number*)))
                              (t
                                (setf (motivating-nodes node) (union 
clues motivators))
                                (when new-node?
                                     (push node *inference-graph*)
                                     (store-inference-node-with-c-list
                                       node (sequent-formula sequent) c-list))
                                (when interest
                                     (push interest (enabling-interests node))
                                     (push node (enabled-nodes interest)))
                                (when *trace* (indent depth) (princ 
"DRAW CONCLUSION: ")
                                            (princ node) (terpri))
                                (when (read-char-no-hang) 
(clear-input) (throw 'die nil))
                                (let* ((i-lists (corresponding-i-lists 
(node-c-list node)))
                                          (increased-justification?
                                            (or new-node? (> 
(maximal-degree-of-support node) old-degree)))
                                          (cancellations
                                            (when increased-justification?
 
(discharge-interest-in-defeaters node i-lists old-degree new-node?))))
                                (when *display?* (display-support-link 
support-link))
                                  (adopt-interest-in-defeaters-for 
support-link instantiations binding)
                                  (push support-link *new-links*)
                                  ; (update-beliefs support-link node)
                                  (dolist (node* cancellations) 
(cancel-node node* (if *trace* depth 0)))
                                  (when (not (cancelled-node node))
                                       (when increased-justification?
                                            (discharge-interest-in
                                              node i-lists old-degree 
new-node? (1+ depth) interests interest)
                                            (cond (*use-reductio*
 
(discharge-immediate-reductios
                                                          node 
old-degree new-node? (1+ depth) interests interest))))
                                       (when new-node? 
(invert-contradictions node instantiations (1+ depth)))
                                       (cancel-subsumed-links 
support-link depth)))))))
                        nil))))))
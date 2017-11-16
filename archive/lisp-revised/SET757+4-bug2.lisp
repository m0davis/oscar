(defunction discharge-appropriately-related-link (link u* degree new? 
old-degree N node depth interests)
                                         link = #<Link 19: for 
interest #44 by disj-cond>
                                         u* = (t ((#:^@\y38 . #:|^x18|)))
                                         degree = 1.0
                                         new? = t
                                         old-degree = 1.0
                                         n = #<Interest 45>
                                         node = #<Node 535>
                                         depth = 4
                                         (cons n interests)
                                         (#<Interest 45>)
     ; (when (eq link  (link 19)) (setf l link u u* d degree nw new? 
od old-degree n* n nd node dp depth in interests) (break))
     ;; (step (discharge-appropriately-related-link l u d nw od n* nd dp in))
     (when *trace* (indent depth) (princ 
"DISCHARGE-APPROPRIATELY-RELATED-LINK: ") (princ link) (terpri))
     (let* ((degree* (degree-of-interest* (resultant-interest link)))
               (spec (premise-node-specifier (link-premise link)))
               (binding (if spec (cons (cons spec node) (link-binding 
link)) (link-binding link))))
        ((p ~ (subset #:^@\y39 #:^@\y38)) (q ~ (subset #:^@\y38 #:^@\y39)))
       (when (and (<= degree* degree) (or new? (> (link-strength link) 
old-degree)))
            (setf (discharged-link link) t)
            (cond ((eq (link-rule link) :answer)
                        (when (null (node-supposition node))
                             (when (not (member node (supporting-nodes link)))
                                  (push node (supporting-nodes link))
                                  (push node (query-answers 
(resultant-interest link)))
                                  (pushnew (resultant-interest link) 
(answered-queries node))
                                  (when (deductive-node node)
                                       (when (and
                                                    (every
                                                      #'(lambda (query)
                                                            (or (eq 
query (resultant-interest link))
 
(some #'deductive-node (query-answers query))))
 
*ultimate-epistemic-interests*)
                                                    (not (some
 
#'(lambda (Q) (eq (item-kind Q) :query))
 
*inference-queue*)))
                                            (setf 
(undefeated-degree-of-support node) 1.0)
                                            (setf (answered? 
(resultant-interest link)) T)
                                            (let ((deductive-links nil)
                                                    (deductive-nodes nil))
                                              (dolist (L *new-links*)
                                                  (when 
(deductive-node (support-link-target L))
                                                       (push L deductive-links)
                                                       (push 
(support-link-target L) deductive-nodes)))
                                              (dolist (N 
deductive-nodes) (setf (undefeated-degree-of-support N) 1.0))
                                              (dolist (L 
deductive-links) (setf (support-link-strength L) 1.0))
                                              (display-belief-changes
                                                *new-links*
                                                deductive-nodes
                                                nil))
                                            (dolist (instruction 
(positive-query-instructions (resultant-interest link)))
                                                (funcall instruction node))
                                            (when *display?*
                                                 (terpri)
                                                 (princ " 
ALL QUERIES HAVE BEEN ANSWERED DEDUCTIVELY.")
                                                 (terpri))
                                            ; (cancel-interest-in 
(link-interest link) 0)
                                            (throw 'die nil)))
                                  ; (record-query-answers link)
                                  )))
                      ((and (or (non-reductio-interest 
(resultant-interest link)) (deductive-node node))
                        (funcall+ (discharge-condition N) node u*
                                               (match-sublis 
(interest-match link) binding)))
                        (let
                          (;(match (interest-match link))
                            (match* (interest-reverse-match link))) 
((#:^@\y39 . #:^@\y38) (#:^@\y38 . #:^@\y39))
                          (setf u* (match-sublis match* u*))    (t 
((#:^@\y39 . #:|^x18|)))
                          (let* ((u1 (mem1 u*))    (t)       This 
should be ((#:^@\y39 . #:^@\y38)). This is what is applied
 
		to the suppositions.
                                  (u2 (mem2 u*))    ((#:^@\y39 . #:|^x18|))
                                  (binding    ((p ~ (subset #:|^x18| 
#:^@\y38)) (q ~ (subset #:^@\y38 #:|^x18|)))
                                    (mapcar
                                      #'(lambda (assoc)
                                            (cons (car assoc) 
(match-sublis u2 (cdr assoc)))) binding))
                                  (instantiations    (t)
                                    (cons u1
                                              (mapcar
                                                #'(lambda (in)
                                                      (cond ((eq in t) u2)
                                                                  (t 
(match-sublis u2 in))))
                                                               ; (t 
(cons (car in) (match-sublis u2 (cdr in))))))
                                                (link-instantiations link))))
                                  (supposition (match-sublis u2 
(link-supposition link))))    nil
                          (cond
                            ((remaining-premises link)
                              (construct-interest-link
                                link node instantiations binding 
(remaining-premises link) supposition
                                (degree-of-interest N) 
(maximum-degree-of-interest N) (1+ depth)
                                (interest-priority (resultant-interest 
link)) interests))
                            ((or (null (right-links (resultant-interest link)))
                                   (some #'(lambda (L) (eq (link-rule L) ug))
                                         (right-links 
(resultant-interest link)))
                                   (some #'(lambda (L)
                                   (funcall+ (discharge-condition 
(resultant-interest link)) nil (list u1 u2)
 
(match-sublis (interest-match link) (link-binding L))))
                                         (right-links 
(resultant-interest link))))
                              (cond
                                ((conclusions-function (link-rule link))
                             binding = ((p ~ (subset #:|^x18| 
#:^@\y38)) (q ~ (subset #:^@\y38 #:|^x18|)))
                                  (dolist (P (funcall 
(conclusions-function (link-rule link)) binding))
                                         (((v (~ (subset #:|^x18| 
#:^@\y38)) (~ (subset #:^@\y38 #:|^x18|)))))
                                      (draw-conclusion
                                         (car p)
                                         (v (~ (subset #:|^x18| 
#:^@\y38)) (~ (subset #:^@\y38 #:|^x18|)))
                                         (cons node (supporting-nodes link))
                                         (#<Node 535>)
                                         (link-rule link)
                                         disj-cond
                                         instantiations = (t)
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
                                        (car P) (cons node 
(supporting-nodes link)) (link-rule link) instantiations
                                        (discount-factor (link-rule 
link)) depth nil (cdr P) :binding binding :interest
                                        (resultant-interest link) 
:link link :clues (link-clues link))))
                                (t
                                  (draw-conclusion
                                    (interest-formula 
(resultant-interest link)) (cons node (supporting-nodes link))
                                    (link-rule link) instantiations 
(discount-factor (link-rule link)) depth nil
                                    (defeasible-rule (link-rule link)) 
:binding binding :interest (resultant-interest link)
                                    :link link :clues (link-clues link)))
                                ))))))))))
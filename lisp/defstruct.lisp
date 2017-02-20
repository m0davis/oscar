(defstruct (argument (:print-function print-argument) (:conc-name nil))
  (argument-number 0)
  (argument-links nil)
  (argument-node nil)
  (argument-defeaters nil)
  (argument-defeatees nil)
  (argument-strength 0)
  (argument-ultimate-interest nil)
  (argument-inclusive-nodes nil)
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
(defstruct (d-node (:conc-name nil) (:print-function print-d-node))
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
(defstruct (c-list (:print-function print-c-list)
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
(defstruct (query (:print-function print-query)
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
(defstruct (instantiated-premise (:print-function print-instantiated-premise) (:conc-name ip-))
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
                            (:print-function print-interest-scheme) (:conc-name is-))
  (target-interest nil)
  (supposition nil)
  (supposition-variables nil)
  (instance-function nil)
  (generating-node nil))
(defstruct (interest-link (:print-function print-interest-link)
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
(defstruct (interest (:print-function print-interest)
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
(defstruct (i-list (:print-function print-i-list)
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
(defstruct (reason (:print-function print-reason) (:conc-name nil))
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
(defstruct (forwards-premise (:print-function print-f-premise) (:conc-name fp-))
  (formula nil)
  (kind :inference)
  (condition nil)
  (binding-function nil)
  (variables nil)
  (instantiator nil)
  (clue? nil)
  (hypernode-specifier nil)  ;; bound to the node instantiating the premise in a link
  )
(defstruct (backwards-premise (:print-function print-b-premise) (:conc-name bp-))
  (formula nil)
  (condition1 nil)
  (condition2 nil)
  (instantiator nil)
  (clue? nil)
  (text-condition nil)  ;; text specification of the discharge condition
  (hypernode-specifier nil)  ;; bound to the node instantiating the premise in a link
  )
(defstruct (forwards-reason (:include reason) (:print-function print-reason)
                            (:conc-name nil)))
(defstruct (backwards-reason (:include reason) (:print-function print-reason)
                             (:conc-name nil))
  (b-reason-condition nil)  ;; this is a predicate applied to the binding
  (b-reason-discharge nil)
  (b-reason-length 1)  ;; this is the number of backwards-premises
  (b-reason-conclusions-binding-function nil)
  (b-reason-conclusion-variables nil)
  (b-reason-immediate nil))
(defstruct (inference-queue-node (:print-function print-inference-queue-node)
                                 (:conc-name nil))
  (queue-number 0)
  (queue-item nil)  ;; either an interest or a conclusion or a query
  (queue-item-kind nil)   ;; this will be :conclusion, :interest, or :query
  (queue-item-complexity 0)
  (queue-discounted-strength 0)
  (queue-degree-of-preference 0))
(defstruct (goal (:print-function print-goal) (:conc-name nil))
  (goal-number 0)
  (goal-formula nil)
  (goal-strength 1)
  (goal-supporting-node nil)  ;; the node supporting this as a suitable goal
  (goal-generating-desire nil)  ;; the desire, if there is on, that generates the goal
  ; (plans-for nil)  ;; the list of candidate plans that aim at the satisfaction of this goal
  ; (user-question-asked? nil)
  )
(defstruct (desire (:print-function print-desire) (:conc-name nil))
  (desire-number 0)
  (desire-content nil)
  (desire-object nil)  ;; the object of a desire will be a goal
  (desire-strength 0)
  (desire-generated-plans nil)
  (desire-generating-interest nil)  ;; for epistemic-desires
  (desire-hypernode nil))  ;; the hypernode recording the desire
(defstruct (percept (:print-function print-percept) (:conc-name nil))
  (percept-number 0)
  (percept-content nil)
  (percept-clarity 0)
  (percept-date 0))

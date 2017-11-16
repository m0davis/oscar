
(setf *problems*
          (eval-when (:compile-toplevel :execute)
              (make-problem-list
                "
Problem #1
Given premises:
	(q -> r)                                    justification = 1.0
	(r -> (p & q))                              justification = 1.0
        (p -> (q v r))                              justification = 1.0

Ultimate epistemic interests:
	(p <-> q)                                   interest = 1.0
")))

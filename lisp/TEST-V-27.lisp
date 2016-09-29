
(setf *problems*
          (eval-when (:compile-toplevel :execute)
              (make-problem-list
                "
Problem #1
Given premises:
	(all x)((P x) <-> ((H x) & ~(P x)))         justification = 1.0

Ultimate epistemic interests:
	(all x)~(H x)                               interest = 1.0
")))

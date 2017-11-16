(defstruct str (slot 0))

(defun foo (str)
  (incf (str-slot str)))

(foo (make-str))


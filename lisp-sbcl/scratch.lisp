(defparameter *special* t)

(defun print-special ()
  (print *special*)
  (setf *special* 2))

(let ((*special* nil))
  (print-special)
  (print-special))
(print-special)
(print-special)


#|
(defun foo ()
  (multiple-value-bind
   (x y z)
   (f y e)
   (progn
     3)))

(proclaim '(optimize (debug 3)))

(defun has-eval (value)
  (eval
   `#'(lambda (arg)
	,value)))

(funcall (has-eval '(print arg)) 1) (terpri)

(defmacro not-has-eval (value)
  `#'(lambda (arg)
       ,value))

(funcall (not-has-eval (print arg)) 2) (terpri)
|#

#|
(print "1")

(defun formula-instantiator (P variables)
  (cond
   ((listp P)
    (if (eq (car P) :defeasible?) P
      (cons 'list (mapcar #'(lambda (x) (formula-instantiator x variables)) P))))
   ((member P variables) P)
   (t `',P)))

(defun conclusion-instantiator (formula variables default)
  (cond (variables
	 (eval
	  `#'(lambda (binding)
	       (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables))
		 (list (cons ,(formula-instantiator formula variables) ,default))))))
        (t #'(lambda (binding) (declare (ignore binding)) (list (cons formula default))))))

(print (funcall (conclusion-instantiator '(& p q) '(p q) nil) '((p . 1) (q . 2))))
(print (formula-instantiator '(& p q) '(p q)))
(terpri)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print "2")

(defun conclusion-instantiator-explicit (formula variables default)
  (cond (variables
	 #'(lambda (binding)
	     (let ((p (cdr (assoc 'p binding)))
		   (q (cdr (assoc 'q binding))))
	       (list (cons (list '& p q) nil)))))
        (t #'(lambda (binding) (declare (ignore binding)) (list (cons formula default))))))

(print (funcall (conclusion-instantiator-explicit '(& p q) '(p q) nil) '((p . 1) (q . 2))))
(terpri)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print "3")

(defmacro conclusion-instantiator-explicit2 (formula variables default)
;  (let ((fi '(list '& p q)))
  (let ((fi (list 'list ''& 'p 'q)))
    `(cond (,variables
	    #'(lambda (binding)
		(let ((p (cdr (assoc 'p binding)))
		      (q (cdr (assoc 'q binding))))
		  (list (cons ,fi nil)))))
	   (t #'(lambda (binding) (declare (ignore binding)) (list (cons ,formula ,default)))))))

(print (funcall (conclusion-instantiator-explicit2 '(& p q) '(p q) nil) '((p . 1) (q . 2))))
(terpri)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print "4")

(defmacro conclusion-instantiator-explicit3 (fi formula variables default)
  `(cond (,variables
	  #'(lambda (binding)
	      (let ((p (cdr (assoc 'p binding)))
		    (q (cdr (assoc 'q binding))))
		(list (cons ,fi nil)))))
	 (t #'(lambda (binding) (declare (ignore binding)) (list (cons ,formula ,default))))))

(print (funcall (conclusion-instantiator-explicit3 (list '& p q) '(& p q) '(p q) nil) '((p . 1) (q . 2))))
(terpri)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print "5")

(defun formula-instantiator-4 (P variables)
  (cond
   ((listp P)
    (if (eq (car P) :defeasible?) P
      (cons 'list (mapcar #'(lambda (x) (formula-instantiator x variables)) P))))
   ((member P variables) P)
   (t `',P)))

(defmacro conclusion-instantiator-4 (fi formula variables default)
  `(cond (,variables
	  #'(lambda (binding)
	      (let ((p (cdr (assoc 'p binding)))
		    (q (cdr (assoc 'q binding))))
		(list (cons ,fi nil)))))
	 (t #'(lambda (binding) (declare (ignore binding)) (list (cons ,formula ,default))))))

(print (funcall 'formula-instantiator-4 '(& p q) '(p q)))
(print (funcall (conclusion-instantiator-4 (list '& p q) '(& p q) '(p q) nil) '((p . 1) (q . 2))))
(terpri)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print "6")

(defun formula-instantiator-5 (P variables)
  (cond
   ((listp P)
    (if (eq (car P) :defeasible?) P
      (cons 'list (mapcar #'(lambda (x) (formula-instantiator x variables)) P))))
   ((member P variables) P)
   (t `',P)))

(defmacro conclusion-instantiator-5-inner (fi formula variables default)
  `(cond (,variables
	  #'(lambda (binding)
	      (let ((p (cdr (assoc 'p binding)))
		    (q (cdr (assoc 'q binding))))
		(list (cons ,fi nil)))))
	 (t #'(lambda (binding) (declare (ignore binding)) (list (cons ,formula ,default))))))

(defmacro conclusion-instantiator-5-outer (formula variables default)
  `(conclusion-instantiator-5-inner ,(formula-instantiator-5 formula variables) ',formula ',variables ',default))

(print (funcall 'formula-instantiator-5 '(& p q) '(p q)))
(print (funcall (conclusion-instantiator-5-outer (& p q) (p q) nil) '((p . 1) (q . 2))))
(terpri)
(print (macroexpand-1 '(conclusion-instantiator-5-outer (& p q) (p q) nil)))
(terpri)
(print (macroexpand '(conclusion-instantiator-5-outer (& p q) (p q) nil)))
(terpri)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print "7") (terpri)

(defun formula-instantiator-7 (P variables)
  (cond
   ((listp P)
    (if (eq (car P) :defeasible?) P
      (cons 'list (mapcar #'(lambda (x) (formula-instantiator x variables)) P))))
   ((member P variables) P)
   (t `',P)))

(defmacro conclusion-instantiator-7-inner (fi formula variables default)
  (declare (ignorable formula variables default))
  ;(let ((my-fi (symbol-value fi)))
    `(cond (,variables
	    #'(lambda (binding)
		(let ((p (cdr (assoc 'p binding)))
		      (q (cdr (assoc 'q binding))))
		  (list (cons ,fi nil)))))
	   (t (error "unimplemented"))));)

(defun my-eval (x)
  (print "my-eval")
  (print x)
  (print (eval x))
  (let ((r
  (cond ((null x) nil)
	((listp x)
	 (cond ((eq (car x) 'quote)
		(cadr x))
	       (t
		(error "unimplemented"))))
	(t (error "unimplemented"))))
	)
    (print r)
    r))

(defmacro conclusion-instantiator-7-outer (formula variables default)
  (let ((my-formula (my-eval formula))
	(my-variables (my-eval variables)))
    `(conclusion-instantiator-7-inner ,(formula-instantiator-7 my-formula my-variables) ',formula ',variables ',default)))

(print (funcall 'formula-instantiator-7 '(& p q) '(p q)))
(print (funcall (conclusion-instantiator-7-outer '(& p q) '(p q) nil) '((p . 1) (q . 2))))
(terpri)
|#


;(in-package "OSCAR")

#|
This file provides the code for the macros def-forwards-reason and
 def-backwards-reason.

Premises and conclusions can be either pretty-formulas (strings) or formulas (S-expressions).
Note that pretty-formulas are case-sensitive.  Do not capitalize expressions
in one part of a reason and fail to capitalize it elsewhere, and make sure capitalization agrees in the
premises of problems.  If pretty-formulas are used, then the variable-list should be quoted to avoid
problems with case-sensitivity.  Otherwise the variables can simply be listed.
 |#

#| =====================================================================

Forwards-reasons can be defined in either of two forms:

(def-forwards-reason symbol
    :forwards-premises list of formulas or formula-condition pairs (listed one after another)
    :backwards-premises  list of formulas or pairs (formula,(condition1,condition2)) 
    :conclusions formula
    :strength number
    :variables list of symbols
    :defeasible? T or NIL (NIL is default)
    :description an optional string (quoted) describing the reason
    )

(def-forwards-reason symbol
    :forwards-premises list of formulas or formula-condition pairs
    :backwards-premises  list of formulas or pairs (formula (condition1 condition2)) 
    :conclusions-function lambda expression or function
    :strength number
    :variables list of symbols
    :defeasible? T or NIL (NIL is default)
    :description an optional string (quoted) describing the reason
    )

If no premise-condition is supplied for a particular premise, the default condition
#'is-inference is used.
What is generated is forwards-reasons with reason-functions.  For example

(def-forwards-reason *THERMOMETER*
    :forwards-premises   (thermometer-reads x)
    :conclusions   (Patient-temperature-is x)
    :strength   .98
    :variables   x
    :defeasible? t)

produces the following code:

(progn
    (proclaim (list 'special '*thermometer*))
    (when (boundp '*thermometer*) (pull *thermometer* *forwards-substantive-reasons*))
    (setf *thermometer*
             (make-forwards-reason
               :reason-name '*thermometer*
               :forwards-premises
               (list (list '(thermometer-reads x)
                             #<Compiled-function is-inference #x17C13C6>
                             #'(lambda (%z %v)
                                   (declare (ignore %v))
                                   (when (and (listp %z) (equal (element 0 %z) 'thermometer-reads))
                                        (values (list (cons 'x (element 1 %z))) t)))
                             '(x)))
               :backwards-premises nil
               :reason-conclusions '(patient-temperature-is x)
               :conclusions-function nil
               :reason-variables '(x)
               :reason-strength 0.98
               :defeasible-rule t
               :reason-description nil))
    (push *thermometer* *forwards-substantive-reasons*))

On the other hand

(def-forwards-reason GREEN-SLYME
    :forwards-premises
    (Patient-has-had-green-slyme-running-out-of-his-nose-for  x  hours)
    (:condition (and (is-inference c) (numberp x)))
    :variables   x
    :conclusions-function
    `(The-probability-that the-patient-ingested-silly-putty is ,(* .5 (- 1 (exp (- x)))))
    :strength   .95
    :defeasible? T)

constructs a reason with the reason-function:

(progn
    (proclaim (list 'special 'green-slyme))
    (when (boundp 'green-slyme) (pull green-slyme *forwards-substantive-reasons*))
    (setf green-slyme
             (make-forwards-reason
               :reason-name 'green-slyme
               :forwards-premises
               (list
                 (list
                   '(patient-has-had-green-slyme-running-out-of-his-nose-for x hours)
                   #'(lambda (c binding) (let* ((x (cdr (assoc 'x binding)))) (and (is-inference c) (numberp x))))
                   #'(lambda (%z %v)
                         (declare (ignore %v))
                         (when (and (listp %z)
                                             (equal (element 2 %z) 'hours)
                                             (equal (element 0 %z) 'patient-has-had-green-slyme-running-out-of-his-nose-for))
                              (values (list (cons 'x (element 1 %z))) t)))
                   '(x)))
               :backwards-premises nil
               :reason-conclusions nil
               :conclusions-function
               #'(lambda (x)
                     (list* 'the-probability-that
                              (list* 'the-patient-ingested-silly-putty (list* 'is (list (* 0.5 (- 1 (exp (- x)))))))))
               :reason-variables '(x)
               :reason-strength 0.95
               :defeasible-rule t
               :reason-description nil))
    (push green-slyme *forwards-substantive-reasons*))

|#

;=========================================================================

(defmacro def-forwards-reason (name &rest body)
    (let* ((newbody (make-clauses body))
              (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
              (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
              (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
              (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
              (discount (cadr (find-if #'(lambda (x) (eq (car x) :discount-factor)) newbody)))
              (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :temporal?)) newbody)))
              (conclusion (find-if #'(lambda (x)
                                                  (or (eq (car x) :conclusions)
                                                        (eq (car x) :conclusion))) newbody))
              (conclusion-function
                (find-if #'(lambda (x) (eq (car x) :conclusions-function)) newbody))
              (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :backwards-premises)) newbody)))
              (premises (cdr (find-if #'(lambda (x) (eq (car x) :forwards-premises)) newbody))))
      (when description (setf description (mem2 description)))
      (when defeasible? (setf defeasible? (mem2 defeasible?)))
      (when variables (setf variables (list 'quote (cdr variables))))
      (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
      (when conclusion
           (setf conclusion
                    (list 'quote
                           (mapcar #'(lambda (x) (reform-if-string x (eval variables))) (cdr conclusion)))))
      (cond
        (conclusion-function
          (let ((c-vars (subset #'(lambda (v) (o-occur* v (mem2 conclusion-function)))
                                            (eval variables))))
            (setf conclusion-function
                     `#'(lambda (binding)
                            (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                              ,(mem2 conclusion-function))))))
        (t 
          (let ((c-vars (subset #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables))))
            (cond
              (c-vars
                (setf conclusion-function
                         `#'(lambda (binding)
                                (let* ((i-vars nil) ,@ (mapcar
                                               #'(lambda (v)
                                                     `(,v 
                                                        (let ((assoc (assoc ',v binding)))
                                                          (if assoc (cdr assoc)
                                                               (let ((i-var (make-interest-variable)))
                                                                 (push i-var i-vars) i-var)))))
                                               c-vars))
                                  (values
                                    ,(cons 'list 
                                               (rectify-conclusions-list
                                                 (mapcar
                                                   #'(lambda (x) (formula-instantiator x c-vars))
                                                   (eval conclusion)) defeasible?))
                                    i-vars)
                                    ))))
              (t
                (setf conclusion-function
                         `#'(lambda (binding) (declare (ignore binding))
                               (values
                                 ,(cons 'list (rectify-conclusions-list
                                                    (mapcar
                                                      #'(lambda (x) (formula-instantiator x nil))
                                                      (eval conclusion)) defeasible?) )
                               i-vars)
                               ))))
            )))
      (when backwards-premises
           (setf backwards-premises
                    (cons 'list (rectify-backwards-premises backwards-premises (eval variables)))))
      (when premises
           (setf premises (cons 'list (rectify-forwards-premises premises (eval variables)))))
      
      (when (stringp name) (setf name (read-from-string name)))
      
      `(progn
           (proclaim (list 'special ',name))
           
             (let ((defeaters nil))
             (when (and (boundp ',name) ,name)
                  (pull ,name *forwards-substantive-reasons*)
                  (dolist (R defeaters) (pull ,name (reason-defeatees R)))
                  (setf defeaters (undercutting-defeaters ,name)))
             
             (setf ,name
                      (make-forwards-reason
                        :reason-name ',name
                        :forwards-premises ,premises
                        :backwards-premises ,backwards-premises
                        :reason-conclusions ,conclusion
                        :conclusions-function ,conclusion-function
                        :reason-variables ,variables
                        :reason-strength ,strength
                        :discount-factor (or ,discount 1.0)
                        :defeasible-rule ,defeasible?
                        :temporal? ,temporal?
                        :reason-description ,description))
             
             (setf (undercutting-defeaters ,name) defeaters)
             (dolist (R defeaters) (push ,name (reason-defeatees R)))
             (push ,name *forwards-substantive-reasons*)))))

(defun rectify-conclusions-list (conclusions default)
    (let ((rectified-conclusions nil))
      (loop
        (let ((P (car conclusions)))
          (setf conclusions (cdr conclusions))
          (cond
            ((and (listp (car conclusions)) (equal (caar conclusions) :defeasible?))
              (push (list 'cons P (cadar conclusions)) rectified-conclusions)
              (setf conclusions (cdr conclusions)))
            (t (push (list 'cons P default) rectified-conclusions)))
          (when (null conclusions) (return (reverse rectified-conclusions)))))))

(defunction rectify-forwards-premises (premise-list variables &optional c-vars)
   ;  (setf p premise-list v variables c c-vars) (break)
    ;; (step (rectify-forwards-premises p v c))
    (let ((premises nil)
            (used-premise-variables c-vars))
      (loop
        (let* ((premise (reform-if-string (car premise-list) variables))
                  (premise-variables
                    (if (and (listp premise) (eq (car premise) 'define))
                      (subset #'(lambda (v) (o-occur++ v  premise)) variables)
                      (subset #'(lambda (v) (o-occur* v  premise)) variables)))
                  (premise-variables* (intersection premise-variables used-premise-variables))
                  (binding-function (binding-function premise premise-variables)))
          (setf premise-list (cdr premise-list))
          (let ((conditions nil))
            (dolist (p premise-list)
                (if (stringp p) (return))
                (push p conditions)
                (setf premise-list (cdr premise-list)))
            (let* ((kind (cadr (find-if #'(lambda (c) (eq (car c) :kind)) conditions)))
                      (clue? (cadr (find-if #'(lambda (c) (eq (car c) :clue?)) conditions)))
                      (node-specifier (cadr (find-if #'(lambda (c) (eq (car c) :node)) conditions)))
                      (condition (cadr (find-if #'(lambda (c) (eq (car c) :condition)) conditions)))
                      (new-premise
                        (make-forwards-premise
                          :formula premise
                          :kind (if kind (read-from-string (cat ":" (write-to-string kind))) :inference)
                          :condition
                          (if condition (eval `#'(lambda (c binding) ,@(formula-condition condition variables))))
                          :binding-function (eval binding-function)
                          :clue? clue?
                          :variables premise-variables
                          :node-specifier node-specifier
                          :instantiator (reason-instantiator premise premise-variables*))))
              (push new-premise premises)
              (setf used-premise-variables
                       (union used-premise-variables premise-variables))))
          (when (null premise-list) (return (reverse premises)))))))

(defun make-clauses (body)
    (let ((newbody nil))
       (loop
          (let ((clause (list (mem1 body))))
             (loop
                (setf body (cdr body))
                (when (null body) (push (reverse clause) newbody) (return))
                (when (keywordp (car body)) (push (reverse clause) newbody) (return))
                (push (car body) clause))
             (when (null body) (return))))
       newbody))

(defunction rectify-strength (formula premise-variables)
    (cond
      ((numberp formula) formula)
      (t
        (let ((formula* (rectify-formula-condition (parse-arithmetical-formula formula)))
                (variables (subset #'(lambda (v) (o-occur* v formula)) premise-variables)))
          (cond ((null premise-variables)
                      (eval `#'(lambda (binding) (declare (ignore binding)) ,formula*)))
                    (t
                     (eval
                        `#'(lambda (binding basis)
                               ,@ (cond ((not (occur 'basis formula)) `((declare (ignore basis))))
                                              ((null variables) `((declare (ignore binding)))))
                               (let*
                                 ,@
                                 (list
                                   (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables)
                                   formula*))))))))))

#| This allows us to write the conditions in forwards-reasons in the form '(x < y) or '(x <= y), or logical
combinations thereof, without incorporating a check that x and y have arithmetical values.  +, *, -, /, and
= can be used in infix notation. |#
(defunction formula-condition (formula premise-variables)
    (let ((formula* (rectify-formula-condition (parse-arithmetical-formula formula)))
            (variables (subset #'(lambda (v) (o-occur* v formula)) premise-variables)))
      (cond ((null premise-variables)
                  (list '(declare (ignore binding)) formula*))
                ((occur 'c formula)
                  `((let*
                       ,@
                       (list
                         (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables)
                         formula*))))
                (t
                  `((declare (ignore c))
                     (let*
                       ,@
                       (list
                         (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables)
                         formula*)))))))

(defunction rectify-formula-condition (formula)
    (let* ((p (subst '*cycle* 'now formula))
              (terms (arithmetical-terms p)))
      (if terms
        (progn
            (let ((terms* nil) (a-list nil))
              (dolist (v terms)
                  (cond ((and (not (eq v '*cycle*)) (not (numberp v)))
                              (let ((v* (gensym)))
                                (push v* terms*)
                                (push (cons v v*) a-list)))
                            (t (pull v terms))))
              `(let
                 ,@
                 (list (mapcar #'(lambda (v) `(,(cdr (assoc v a-list)) (ignore-errors (eval ,v)))) terms)
                        `(and ,@ terms* ,(sublis a-list p))))))
        p)))

(defunction arithmetical-terms (formula &optional terms)
    (cond ((null formula) terms)
              ((listp formula)
                (cond 
                  ((or (eq (car formula) '<) (eq (car formula) '<=) (eq (car formula) '=))
                    (union= (remove '*cycle* (cdr formula)) terms))
                  (t (arithmetical-terms (cdr formula) (arithmetical-terms (car formula) terms)))))
              (t terms)))

(defunction parse-arithmetical-formula (p)
    (cond ((null p) nil)
              ((listp p)
                (let ((p2 (cadr p)))
                  (cond ((and
                               (mem3 p)
                               (or (eq p2 '<) (eq p2 '<=) (eq p2 '+) (eq p2 '-) (eq p2 '*) (eq p2 '/) (eq p2 '=)))
                              (list p2 (parse-arithmetical-formula (car p)) (parse-arithmetical-formula (mem3 p))))
                            (t (mapcar #'parse-arithmetical-formula p)))))
              (t p)))

(defunction rectify-backwards-premises (premise-list variables &optional c-vars)
    ; (setf p premise-list v variables) (break)
    ;; (step (rectify-backwards-premises p v))
    (let ((premises nil))
      (loop
        (let* ((premise? (stringp (car premise-list)))
                  (premise (reform-if-string (car premise-list) variables))
                  (premise-variables
                    (if (and (listp premise) (eq (car premise) 'define))
                      (subset #'(lambda (v) (o-occur++ v  premise)) variables)
                      (subset #'(lambda (v) (o-occur* v  premise)) variables))))
          (setf premise-list (cdr premise-list))
          (let ((conditions nil))
            (dolist (p premise-list)
                (if (or (stringp p) (and (listp p) (not (keywordp (car p))))) (return))
                (push p conditions)
                (setf premise-list (cdr premise-list)))
            (let* ((clue? (cadr (find-if #'(lambda (c) (eq (car c) :clue?)) conditions)))
                      (node-specifier (cadr (find-if #'(lambda (c) (eq (car c) :node)) conditions)))
                      (condition (cadr (find-if #'(lambda (c) (eq (car c) :condition)) conditions)))
                      (variables* (if condition (subset #'(lambda (v) (o-occur v condition)) variables)))
                      (condition*  (if condition (eval (simple-backwards-formula-condition condition variables*))))
                      (d-condition
                  (when (and condition (listp premise) (eq (car premise) 'define))
                      (eval `#'(lambda (c binding) ,@(formula-condition condition variables*)))))
                      (condition1 (cadr (find-if #'(lambda (c) (eq (car c) :condition1)) conditions)))
                      (condition2 (cadr (find-if #'(lambda (c) (eq (car c) :condition2)) conditions)))
                      (new-premise
                        (cond
                          (premise?
                            (make-backwards-premise
                              :formula premise
                              :condition1
                              (cond 
                                ((and (listp premise) (eq (car premise) 'define)) d-condition)
                                (condition1 (backwards-formula-condition condition1))
                                (condition #'(lambda (i) (eq (discharge-condition i) condition*))))
                              :condition2
                              (cond (condition2 (backwards-formula-condition condition2))
                                        (condition #'(lambda (i) (setf (discharge-condition i) condition*))))
                              :text-condition condition
                              :clue? clue?
                              :node-specifier node-specifier
                              :instantiator (reason-instantiator premise premise-variables)))
                          (t
                            (setf c-vars (subset #'(lambda (v) (o-occur* v premise))
                                                              variables))
                            (let ((new-vars
                                      (subset #'(lambda (v) (occur-quoted v premise)) c-vars)))
                              `#'(lambda (**b** binding)
                                     (declare (ignore **b**))
                                     (let (,@ (mapcar
                                                    #'(lambda (v) `(,v (cdr (assoc ',v binding))))
                                                    (subset
                                                      #'(lambda (v) (occur-unquoted v premise))
                                                      c-vars)))
                                       (make-backwards-premise
                                          :formula ,premise
                                          :condition1
                                          ,(cond (condition1 (backwards-formula-condition condition1))
                                                    (condition #'(lambda (i) (eq (discharge-condition i) condition*))))
                                          :condition2
                                          ,(cond (condition2 (backwards-formula-condition condition2))
                                                    (condition #'(lambda (i) (setf (discharge-condition i) condition*))))
                                          :text-condition condition
                                          :clue? ,clue?
                                          :node-specifier ,node-specifier
                                          :instantiator
                                          (reason-instantiator
                                            ,premise ',(subset #'(lambda (v) (occur-quoted v premise)) new-vars))))))))))
              (push new-premise premises)))
          (when (null premise-list) (return (reverse premises)))))))

(defunction simple-backwards-formula-condition (formula premise-variables)
    (let ((formula* (rectify-formula-condition (parse-arithmetical-formula formula))))
      (cond ((null premise-variables)
                  (list '(declare (ignore binding)) formula*))
                (t
                  (if premise-variables
                    (progn
                        (let ((terms* nil) (a-list nil))
                          (dolist (v premise-variables)
                              (cond ((and (not (eq v '*cycle*)) (not (numberp v)))
                                          (let ((v* (gensym)))
                                            (push v* terms*)
                                            (push (cons v v*) a-list)))
                                        (t (pull v premise-variables))))
                          `#'(lambda (node unifier binding)
                                 (declare (ignore node))
                                 (let* (,@(mapcar
                                                 #'(lambda (v)
                                                          (let ((v* (cdr (assoc v a-list))))
                                                            `(,v (let ((,v* (cdr (assoc ',v binding))))
                                                                     (match-sublis (mem2 unifier) ,v*)))))
                                                 premise-variables))
                                   ,formula*))))
                          `#'(lambda (node unifier binding) ,formula*))))))

(defunction backwards-formula-condition (formula)
    `#'(lambda (interest) ,formula))

(defunction rectify-reason-condition (formula premise-variables)
    (let ((vars (subset #'(lambda (v) (o-occur v formula)) premise-variables)))
       (when vars
            `(let*
                ,@
                (list (mapcar #'(lambda (v) `(,v (e-assoc ',v binding))) vars)
                       (rectify-formula-condition (parse-arithmetical-formula formula)))))))

(defunction formula-instantiator (P variables)
    (cond
      ((listp P)
        (if (eq (car P) :defeasible?) P
             (cons 'list (mapcar #'(lambda (x) (formula-instantiator x variables)) P))))
      ((member P variables) P)
      (t `',P)))

#| The reason-instantiator binds unbound premise-variables in the premise to new interest-variables,
and returns three values: the instantiated premise-formula, the new interest-variables, and the
extended binding. |#
(defunction reason-instantiator (P variables)
    (cond ((and (listp P) (equal (car P) 'define))
                (def-instantiator (mem3 P) (remove-if-equal (mem2 P) variables)))
              (variables
                (eval
                  `#'(lambda (binding)
                                (let* ((new-vars nil)
                                          (new-binding binding)
                                  ,@
                                      (mapcar
                                        #'(lambda (v)
                                              `(,v
                                              (let ((v* (assoc ',v binding)))
                                                (cond
                                                  (v* (cdr v*))
                                                  (t
                                                     (setf v* (make-interest-variable))
                                                     (push v* new-vars)
                                                     (push (cons ',v v*) new-binding)
                                                     v*)))))
                                        variables))
                                  (values ,(formula-instantiator P variables) new-vars new-binding)))))
              (t #'(lambda (binding) (values P nil binding)))))

(defunction conclusion-instantiator (formula variables default)
    (cond (variables
                (eval
                  `#'(lambda (binding)
                                (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables))
                                  (list (cons ,(formula-instantiator formula variables) ,default))))))
              (t #'(lambda (binding) (declare (ignore binding)) (list (cons formula default))))))

#|
(defunction reason-instantiator- (P variables)
    (cond (variables
                `#'(lambda (binding)
                       (let* ((new-vars nil)
                                 (new-binding binding)
                                 ,@
                                 (mapcar
                                   #'(lambda (v)
                                         `(,v
                                            (let ((v* (cdr (assoc ',v binding))))
                                              (when (null v*)
                                                   (setf v* (make-interest-variable))
                                                   (push v* new-vars)
                                                   (push (cons ',v v*) new-binding))
                                              v*)))
                                   variables))
                         (values ,(formula-instantiator P variables) new-vars new-binding))))
              (t `#'(lambda (binding) (values ',P nil binding)))))

(defunction reason-instantiator- (P variables)
    `#'(lambda (binding)
           (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) variables))
             ,(formula-instantiator P variables))))
|#

;=========================================================================

#|
Backwards-reasons are defined using the following form:

(def-backwards-reason symbol
    :forwards-premises list of formulas or formula-condition pairs
    :backwards-premises  list of formulas or pairs (formula,(condition1,condition2))
    :conclusions formula
    :condition  this is a predicate applied to the binding produced by thetarget sequent
    :strength number (default is 1.0)
    :variables list of symbols
    :defeasible? T or NIL (NIL is default)
    :description  an optional string (quoted) describing the reason
    )

The conditions on forwards-premises are  predicates on c interest, and the values
of the binding.  The default is #'(lambda (c interest &rest r) (declare (ignore interest r)) (is-inference c)).

For example,

(def-backwards-reason R
    :forwards-premises   (F x y)   (G y z) (:condition (numberp z))
    :backwards-premises   (H z w)
    :conclusions   (K x w)
    :variables   x y z w
    :strength   .95
    :defeasible? T)

expands into the following code:

(progn
    (proclaim (list 'special 'r))
    (when (boundp 'r) (pull r *backwards-substantive-reasons*))
    (let* ((c-vars (remove-if-not #'(lambda (v) (o-occur* v '(k x w))) '(x y z w)))
              (c-binding-function (eval (binding-function '(k x w) c-vars))))
      (setf r
               (make-backwards-reason
                 :reason-name 'r
                 :forwards-premises
                 (list
                   (list
                     '(f x y)
                     #<Compiled-function is-inference #x17C13C6>
                     #'(lambda (%z %v)
                           (declare (ignore %v))
                           (when (and (listp %z) (equal (element 0 %z) 'f))
                                (values (list (cons 'y (element 2 %z)) (cons 'x (element 1 %z))) t)))
                     '(x y))
                   (list
                     '(g y z)
                     #'(lambda (c binding) (and (eq (node-kind c) :inference)
                                                                 (let* ((z (cdr (assoc 'z binding)))) (numberp z))))
                     #'(lambda (%z %v)
                           (declare (ignore %v))
                           (when (and (listp %z) (equal (element 0 %z) 'g))
                                (values (list (cons 'z (element 2 %z)) (cons 'y (element 1 %z))) t)))
                     '(y z)))
                 :backwards-premises (list (list '(h z w) '(nil nil)))
                 :reason-conclusions '(k x w)
                 :conclusions-function nil
                 :reason-variables '(x y z w)
                 :reason-length 1
                 :reason-strength 0.95
                 :defeasible-rule t
                 :conclusions-binding-function c-binding-function
                 :reason-condition nil
                 :reason-description nil)))
    (push r *backwards-substantive-reasons*))

|#

(defmacro def-backwards-reason (name &rest body)
    (let* ((newbody (make-clauses body))
              (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
              (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
              (condition (find-if #'(lambda (x) (eq (car x) :condition)) newbody))
              (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
              (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
              (discount (cadr (find-if #'(lambda (x) (eq (car x) :discount-factor)) newbody)))
              (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :temporal?)) newbody)))
              (immediate (cadr (find-if #'(lambda (x) (eq (car x) :immediate)) newbody)))
              (conclusion (find-if #'(lambda (x)
                                                  (or (eq (car x) :conclusions)
                                                        (eq (car x) :conclusion))) newbody))
              (conclusion-function
                (find-if #'(lambda (x) (eq (car x) :conclusions-function)) newbody))
              (c-vars nil)
              (discharge (find-if #'(lambda (x) (eq (car x) :discharge)) newbody))
              (forwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :forwards-premises)) newbody)))
              (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :backwards-premises)) newbody))))
      (when description (setf description (mem2 description)))
      (when defeasible? (setf defeasible? (mem2 defeasible?)))
      (when variables (setf variables (list 'quote (cdr variables))))
      (when condition
           (setf condition
                    `#'(lambda (binding) ,(rectify-reason-condition (mem2 condition) (eval variables)))))
      (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
      (when discharge
           (setf discharge (list 'quote (reform-if-string (mem2 discharge) (eval variables)))))
      (when conclusion
           (setf conclusion
                    (list 'quote
                           (mapcar #'(lambda (x) (reform-if-string x (eval variables))) (cdr conclusion)))))
      (cond
        (conclusion-function
          (setf c-vars (subset #'(lambda (v) (o-occur* v (mem2 conclusion-function)))
                                            (eval variables)))
          (setf conclusion-function
                   `#'(lambda (binding)
                          (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                            ,(mem2 conclusion-function)))))
        (t 
          (setf c-vars (subset #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables)))
          (cond
            (c-vars
              (setf conclusion-function
                       `#'(lambda (binding)
                              (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                                ,(cons 'list 
                                           (rectify-conclusions-list
                                             (mapcar
                                               #'(lambda (x) (formula-instantiator x c-vars))
                                               (eval conclusion)) defeasible?))))))
            (t
              (setf conclusion-function
                         `#'(lambda (binding) (declare (ignore binding))
                               ,(cons 'list (rectify-conclusions-list
                                                  (mapcar
                                                    #'(lambda (x) (formula-instantiator x nil))
                                                    (eval conclusion)) defeasible?) )))))))
      (when forwards-premises
           (setf forwards-premises
                    (cons 'list (rectify-forwards-premises forwards-premises (eval variables) c-vars))))
      (when backwards-premises
           (setf backwards-premises
                    (cons 'list (rectify-backwards-premises backwards-premises (eval variables) c-vars))))
      (when (stringp name) (setf name (read-from-string name)))
      (let* ((c-vars (remove-if-not #'(lambda (v) (o-occur* v (eval conclusion))) (eval variables)))
                (c-binding-function (binding-function (mem1 (eval conclusion)) c-vars)))
        
        `(progn
             (proclaim (list 'special ',name))
             
             (let ((defeaters nil))
               (when (and (boundp ',name) ,name)
                    (pull ,name *backwards-substantive-reasons*)
                    (dolist (R defeaters) (pull ,name (reason-defeatees R)))
                    (setf defeaters (undercutting-defeaters ,name)))
               
               (setf ,name
                        (make-backwards-reason
                          :reason-name ',name
                          :forwards-premises ,forwards-premises
                          :backwards-premises ,backwards-premises
                          :reason-conclusions ,conclusion
                          :reason-discharge ,discharge
                          :conclusions-function ,conclusion-function
                          :reason-variables ,variables
                          :reason-length ,(length (eval backwards-premises))
                          :discount-factor (or ,discount 1.0)
                          :reason-strength ,strength
                          :defeasible-rule ,defeasible?
                          :temporal? ,temporal?
                          :immediate-reason ,immediate
                          :conclusions-binding-function ,c-binding-function
                          :reason-condition ,condition
                          :reason-description ,description))
               
               (setf (undercutting-defeaters ,name) defeaters)
               (dolist (R defeaters) (push ,name (reason-defeatees R)))
               (push ,name *backwards-substantive-reasons*))))))

(defunction occur-unquoted (x s &key (test 'eq))
    (and s (listp s) (not (eq (car s) 'quote))
              (or (funcall test (car s) x)
                    (occur-unquoted x (car s) :test test)
                    (occur-unquoted x (cdr s) :test test))))

(defunction occur-quoted (x s &key (test 'eq))
    (and s (listp s)
              (or (and (eq (car s) 'quote) (occur x (cdr s) :test test))
                    (occur-quoted x (car s) :test test)
                    (occur-quoted x (cdr s) :test test))))

(defunction o-occur (x s &key (test 'eq))
    (and (listp s)
             (or (some #'(lambda (y) (funcall test y x)) s)
                   (some #'(lambda (y) (o-occur x y :test test)) s))))

(defunction o-occur+ (x s &key (test 'eq))
    (and (listp s)
             (or (some #'(lambda (y) (funcall test y x)) (cdr s))
                   (some #'(lambda (y) (o-occur+ x y :test test)) s))))

(defunction o-occur* (x s &key (test 'eq))
    (or (funcall test x s)
          (o-occur x s :test test)))

(defunction o-occur++ (x s &key (test 'eq))
    (or (funcall test x s)
          (o-occur+ x s :test test)))

;; ======================================================================

(defmacro def-forwards-undercutter (name &rest body)
       (let* ((newbody (make-clauses body))
             (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
             (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
             (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
             (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
          (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :temporal?)) newbody)))
          (discount (cadr (find-if #'(lambda (x) (eq (car x) :discount-factor)) newbody)))
          (defeatee (find-if #'(lambda (x) (eq (car x) :defeatee)) newbody))
              (c-vars (reason-variables (eval (cadr defeatee))))
              (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :backwards-premises)) newbody)))
              (premises (cdr (find-if #'(lambda (x) (eq (car x) :forwards-premises)) newbody))))
     (when description (setf description (mem2 description)))
     (when defeasible? (setf defeasible? (mem2 defeasible?)))
     (when variables (setf variables (list 'quote (cdr variables))))
     (when c-vars (setf c-vars (list 'quote c-vars)))
     (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
    (setf defeatee (mem2 defeatee))
    (let ((conclusion `',(undercutters-for (eval defeatee)))
            (conclusion-function nil))
          (cond
            (c-vars
              (setf conclusion-function
                       `#'(lambda (binding)
                              (let (,@ (mapcar #'(lambda (v) `(,v (cdr (assoc ',v binding)))) c-vars))
                                ,(cons 'list 
                                  (mapcar
                                    #'(lambda (x) (formula-instantiator x c-vars))
                                                (eval conclusion)))))))
            (t
              (setf conclusion-function
                       `#'(lambda (binding) (declare (ignore binding)) ',(eval conclusion)))))
        (when backwards-premises
             (setf backwards-premises
                      (cons 'list (rectify-backwards-premises backwards-premises (eval variables) (eval c-vars)))))
        (when premises
             (setf premises (cons 'list (rectify-forwards-premises premises (eval variables) (eval c-vars)))))
        
        (when (stringp name) (setf name (read-from-string name)))
         
         `(progn
              (proclaim (list 'special ',name))
              
             (let ((defeaters nil))
             (when (and (boundp ',name) ,name)
                  (pull ,name *backwards-substantive-reasons*)
                  (dolist (R defeaters) (pull ,name (reason-defeatees R)))
                  (setf defeaters (undercutting-defeaters ,name)))

                (setf ,name
                         (make-forwards-reason
                           :reason-name ',name
                           :forwards-premises ,premises
                           :backwards-premises ,backwards-premises
                           :reason-conclusions ,conclusion
                           :conclusions-function ,conclusion-function
                           :reason-variables (union ,variables (reason-variables ,defeatee))
                           :reason-strength ,strength
                           :discount-factor (or ,discount 1.0)
                           :defeasible-rule ,defeasible?
                           :temporal? ,temporal?
                           :reason-description ,description))
                
                (setf (undercutting-defeaters ,name) defeaters)
                (dolist (R defeaters) (push ,name (reason-defeatees R)))
                (push ,name *forwards-substantive-reasons*))))))

(defmacro def-backwards-undercutter (name &rest body)
    (let* ((newbody (make-clauses body))
              (description (find-if #'(lambda (x) (eq (car x) :description)) newbody))
              (defeasible? (find-if #'(lambda (x) (eq (car x) :defeasible?)) newbody))
              (condition (find-if #'(lambda (x) (eq (car x) :condition)) newbody))
              (variables (find-if #'(lambda (x) (eq (car x) :variables)) newbody))
              (strength (find-if #'(lambda (x) (eq (car x) :strength)) newbody))
              (temporal? (cadr (find-if #'(lambda (x) (eq (car x) :temporal?)) newbody)))
              (discount (cadr (find-if #'(lambda (x) (eq (car x) :discount-factor)) newbody)))
              (defeatee (find-if #'(lambda (x) (eq (car x) :defeatee)) newbody))
              (c-vars (reason-variables (eval (cadr defeatee))))
              (discharge (find-if #'(lambda (x) (eq (car x) :discharge)) newbody))
              (forwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :forwards-premises)) newbody)))
              (backwards-premises (cdr (find-if #'(lambda (x) (eq (car x) :backwards-premises)) newbody)))
              ; (conclusion (find-if #'(lambda (x) (eq (car x) :conclusions)) newbody))
              )
      (when description (setf description (mem2 description)))
      (when defeasible? (setf defeasible? (mem2 defeasible?)))
      (when variables (setf variables (list 'quote (cdr variables))))
     (when c-vars (setf c-vars (list 'quote c-vars)))
      (when condition
           (setf condition
                    `#'(lambda (binding) ,(rectify-reason-condition (mem2 condition) (eval variables)))))
      (if strength (setf strength (rectify-strength (mem2 strength) (eval variables))) (setf strength 1.0))
      (when discharge
           (setf discharge (list 'quote (reform-if-string (mem2 discharge) (eval variables)))))
      (setf defeatee (cons 'list (cdr defeatee)))
      (when forwards-premises
           (setf forwards-premises
                    (cons 'list (rectify-forwards-premises forwards-premises (eval variables) (eval c-vars)))))
      (when backwards-premises
           (setf backwards-premises
                    (cons 'list (rectify-backwards-premises backwards-premises (eval variables) (eval c-vars)))))
      (when (stringp name) (setf name (read-from-string name)))
      
      `(progn
           (proclaim (list 'special ',name))
           
           (let ((defeaters nil))
             (when (and (boundp ',name) ,name)
                  (pull ,name *backwards-substantive-reasons*)
                  (setf defeaters (undercutting-defeaters ,name))
                  (dolist (d ,defeatee) (pull ,name (undercutting-defeaters d))))
             
               (setf ,name
                        (make-backwards-reason
                          :reason-name ',name
                          :forwards-premises ,forwards-premises
                          :backwards-premises ,backwards-premises
                          :reason-defeatees ,defeatee
                          :reason-discharge ,discharge
                          :reason-variables ',(union (eval variables) (unionmapcar+ #'reason-variables (eval defeatee)))
                          :reason-length ,(length (eval backwards-premises))
                          :reason-strength ,strength
                          :discount-factor (or ,discount 1.0)
                          :defeasible-rule ,defeasible?
                          :temporal? ,temporal?
                          :reason-condition ,condition
                          :reason-description ,description))
               
               (setf (undercutting-defeaters ,name) defeaters)
               (push ,name *backwards-substantive-reasons*)
               (dolist (d ,defeatee) (push ,name (undercutting-defeaters d)))
               ))))

(defunction undercutters-for (reason)
    (mapcar
      #'(lambda (c)
            (make-@
              (gen-conjunction
                (append
                  (subset #'(lambda (p) (or (not (listp p)) (not (equal (car p) 'define))))
                                (mapcar #'fp-formula* (remove-if #'fp-clue? (forwards-premises reason))))
                  (subset #'(lambda (p) (or (not (listp p)) (not (equal (car p) 'define))))
                                (mapcar #'bp-formula (backwards-premises reason)))))
              c))
      (reason-conclusions reason)))

(defunction fp-formula* (premise)
    (let ((p (fp-formula premise)))
      (cond ((eq (fp-kind premise) :percept)
                  (list 'it-appears-to-me-that (mem2 p) (mem3 p)))
                (t p))))

;; ======================================================================

(defunction term-lists (P vars descriptor)
    (cond ((listp P)
                 (let ((elt-num 0) (term-lists nil))
                    (dolist (Q P)
                        (let ((Q-descriptor `(element ,elt-num ,descriptor)))
                           (cond ((mem Q vars)
                                        (let ((assoc (assoc Q term-lists :test 'equal)))
                                           (cond (assoc (push Q-descriptor (cdr assoc)))
                                                       (t (push (list Q Q-descriptor) term-lists)))))
                                       ((listp Q) 
                                         (let ((tl (term-lists Q vars Q-descriptor)))
                                            (dolist (term-list tl)
                                                (let ((assoc (assoc (car term-list) term-lists :test 'equal)))
                                                   (cond (assoc (setf (cdr assoc) (append (cdr term-list) (cdr assoc))))
                                                               (t (push term-list term-lists)))))))))
                        (incf elt-num))
                    term-lists))
                ((mem P vars) `((,P ,descriptor)))))

;(term-lists '(& (F x y) (G x y)) '(x y) 'z)
;((x (element 1 (element 2 z)) (element 1 (element 1 z)))
;  (y (element 2 (element 2 z)) (element 2 (element 1 z))))

(defunction formula-profile (P vars descriptor)
    (cond ((and P (listp P))
                 (let ((description nil) (elt-num 0) (term-lists nil))
                    (dolist (Q P)
                        (let ((Q-descriptor `(element ,elt-num ,descriptor)))
                           (cond ((mem Q vars)
                                        (let ((assoc (assoc Q term-lists :test 'equal)))
                                           (cond (assoc (push Q-descriptor (cdr assoc)))
                                                       (t (push (list Q Q-descriptor) term-lists)))))
                                       ((not (listp Q)) (push `(equal ,Q-descriptor ',Q) description))
                                       (t 
                                         (multiple-value-bind (d tl) (formula-profile Q vars Q-descriptor)
                                              (setf description (append description d))
                                              (dolist (term-list tl)
                                                  (let ((assoc (assoc (car term-list) term-lists :test 'equal)))
                                                     (cond (assoc (setf (cdr assoc) (append (cdr term-list) (cdr assoc))))
                                                                 (t (push term-list term-lists)))))))))
                        (incf elt-num))
                    (values (cons `(listp ,descriptor) description) term-lists)))
                ((mem P vars) (values nil `((,P ,descriptor))))
                                                        ; (list (list (mem1 vars) '`,(list descriptor)))))
                (t (values `((equal ,descriptor ',P)) nil))))

#|
(formula-profile '(& (F x y) (G x y)) '(x y) 'z nil)

((listp z)
 ; (equal (element 0 z) '&)
 ; (listp (element 1 z))
 ; (equal (element 0 (element 1 z)) 'f)
  (listp (element 2 z))
  (equal (element 0 (element 2 z)) 'g))

((x (element 1 (element 2 z)) (element 1 (element 1 z)))
  (y (element 2 (element 2 z)) (element 2 (element 1 z))))
|#

(defunction binding-function (P vars)
    (multiple-value-bind
         (profile term-lists)
         (formula-profile P vars '%z)
         (cond
           ((every #'(lambda (tl) (null (cddr tl))) term-lists)
             (cond
               (profile
                 (if vars
                 `#'(lambda (%z %v)
                        (declare (ignore %v))
                        (when
                             ,@ (list (if (cdr profile) (refined-profile profile) (car profile)))
                             (values
                               ,(cons 'list
                                           (mapcar 
                                             #'(lambda (x) (cons 'cons (cons (list 'quote (car x)) (cdr x))))
                                             term-lists))
                               t)))
                 `#'(lambda (%z %v)
                        (declare (ignore %v))
                        (when 
                             ,@ (list (if (cdr profile) (refined-profile profile) (car profile)))
                             (values nil t)))))
               (t 
                 `#'(lambda (%z %v)
                        (declare (ignore %v))
                        (values
                          ,(cons 'list
                                      (mapcar 
                                        #'(lambda (x) (cons 'cons (cons (list 'quote (car x)) (cdr x))))
                                        term-lists))
                          t)))))
           (profile
             `#'(lambda (%z %v)
                    (when
                    ,@ (list (if (cdr profile) (refined-profile profile) (car profile)))
                         (unify-premise-terms
                           ,(cons 'list (mapcar #'(lambda (b) (cons 'list b)) (a-range term-lists)))
                           ',(domain term-lists) %v T))))
           (t
             `#'(lambda (%z %v)
                    (unify-premise-terms
                      ,(cons 'list (mapcar #'(lambda (b) (cons 'list b)) (a-range term-lists)))
                      ',(domain term-lists) %v T))))))

#| This turns the formula-profile into a description, and replaces repetitive computations with lets. |#
(defunction refined-profile (profile)
    (cond ((equal (caar profile) 'listp) (cons 'and (cons (car profile) (refined-profile* (cdr profile) 0))))
              (t (cons 'and (refined-profile* profile 0)))))

(defunction refined-profile* (profile n)
    (when profile
         (cond ((and (listp (car profile)) (equal (caar profile) 'listp))
                     (let ((v (read-from-string (cat "%z" (write-to-string n))))
                             (term (cadar profile)))
                       `((let ((,v ,term))
                          (and
                            (listp ,v)
                            ,@(=subst v term (refined-profile* (cdr profile) (1+ n))))))))
                   (t (cons (car profile) (refined-profile* (cdr profile) n))))))

#| term-lists is the list of terms corresponding to the premise-variables.  This
returns the list of terms that instantiate the premise-variables and the match. |#
(defunction unify-premise-terms (term-lists premise-variables vars unifier0)
    (catch 'unifier
       (multiple-value-bind
            (terms unifier) (unify-premise-terms* term-lists vars unifier0)
            (values
              (mapcar #'(lambda (x y) (cons x y)) premise-variables terms)
              unifier))))

(defunction unify-premise-terms* (term-lists vars unifier0)
    (multiple-value-bind (term unifier) (unify-list (car term-lists) vars unifier0)
         (let ((m unifier))
            (when (not (eq unifier0 T))
                 (cond ((eq unifier T) (setf m unifier0))
                             (t (dolist (assoc unifier0)
                                    (setf (cdr assoc) (match-sublis unifier (cdr assoc)))
                                    (pushnew assoc m :test 'equal)))))
            (cond ((null (cdr term-lists)) (values (list term) m))
                        (t (multiple-value-bind
                                (terms unifier*) (unify-premise-terms* (cdr term-lists) vars m)
                                (values (cons (match-sublis unifier* term) terms) (merge-matches m unifier*))))))))

#| (unify-premise-terms* '(((f x y) (f a (g z))) ((k x)) ((h w (g b)) (h b y))) '(x y z w) T)
returns:
((f a (g b)) (k a) (h b (g b)))
((x . a) (y g b) (z . b) (w . b))
|#

#| This returns the multiple values result unifier |#
(defunction unify-list (term-list vars unifier)
    (labels
       ((unify-list-aux (term terms vars unifier0)
            (cond ((null terms) (values (match-sublis unifier0 term) unifier0))
                        (t
                          (let* ((m (parallelize-match 
                                           (mgu (match-sublis unifier0 term)
                                                    (match-sublis unifier0 (car terms))
                                                    vars) vars))
                                    (m* m))
                             (when (not (eq unifier0 T))
                                  (cond ((eq m T) (setf m* unifier0))
                                              (t (dolist (assoc unifier0)
                                                     (setf (cdr assoc) (match-sublis m (cdr assoc)))
                                                     (push assoc m*)))))
                             (unify-list-aux
                               (car terms) (cdr terms) vars m*))))))
       (unify-list-aux (car term-list) (cdr term-list) vars unifier)))

;(unify-list '(3) '(x) T)
;(unify-list '(x y z) '(x y z) T)

#| (unify-list '((f x y) (f a (g z)) (f w (g b))) '(x y z w) T)
produces
(f a (g b))
((x . a) (y g b) (z . b) (w . a))  |#

(defunction conditionally-write-to-string (s)
    (if (stringp s) s (write-to-string s)))

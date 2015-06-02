(defvar *display?* nil)
(defvar *proofs?* nil)

#| A problem is a list of the following:
     1.  problem-number
     2.  a list of premises, which are pairs (formula, degree-of-justification)
     3.  a list of desired conclusions, which are pairs (formula, degree-of-interest)
     4.  a list of forwards prima facie reasons, which are quintuples
           (name,premises,conclusion,variables,strength)
     5.  a list of forwards conclusive reasons, which are quadruples
           (name,premises,conclusion,variables)
     6.  a list of backwards prima facie reasons, which are sextuples
           (name,forwards-premises,backwards-premises,conclusion,variables,strength)
     7.  a list of backwards conclusive reasons, which are quintuples
           (name,forwards-premises,backwards-premises,conclusion,variables)
     8.  an optional string describing the problem.
All formulas can be entered as pretty formulas instead. 

Lines can be commented out, and comments are allowed at ends of lines,
by inserting semicolons in the standard way.

The listing of strengths in reasons is optional, the default being 1.0.
|#

;===================== DISPLAYING PROBLEMS =========================

#| This is similar to def-forwards-reason except that it does not put the reason into
*forwards-substantive-reasons*. |#
(defmacro define-forwards-reason
  (name &key forwards-premises backwards-premises conclusion
        (strength 1.0) variables defeasible? description)
  ; (setf n name fp forwards-premises bp backwards-premises c conclusion v variables d defeasible?)
  ; (break)
  #| (step (define-forwards-reason n :forwards-premises (eval fp) :backwards-premises (eval bp)
                                   :conclusion (eval c) :variables (eval v) :defeasible? (eval d)))  |#
  (when (stringp name) (setf name (read-from-string name)))

  `(progn
     (proclaim (list 'special ',name))

     (setf ,name
           (make-forwards-reason
             :reason-name ',name
             :forwards-premises (rectify-forwards-premises* ,forwards-premises ,variables)
             :backwards-premises (rectify-backwards-premises* ,backwards-premises ,variables)
             :reason-conclusions ,conclusion
             :conclusions-function (conclusion-instantiator ,conclusion ,variables ,defeasible?)
             :reason-variables ,variables
             :reason-strength ,strength
             :defeasible-rule ,defeasible?
             :reason-description ,description))
     ,name))

(defun rectify-forwards-premises* (premise-list variables)
  (if premise-list
    (let ((premises nil)
          (used-premise-variables nil))
      (loop
        (let* ((premise (car premise-list))
               (formula (car premise))
               (premise-variables (subset #'(lambda (v) (occur* v formula)) variables))
               (premise-variables* (intersection premise-variables used-premise-variables))
               (binding-function (binding-function formula premise-variables)))
          (setf premise-list (cdr premise-list))
          (push
            (make-forwards-premise
              :formula formula
              :condition (mem2 premise)
              :binding-function (eval binding-function)
              :variables premise-variables
              :instantiator (reason-instantiator formula premise-variables*))
            premises)
          (setf used-premise-variables
                (union used-premise-variables premise-variables)))
        (when (null premise-list) (return (reverse premises)))))))

#| This is similar to def-backwards-reason except that it does not put the reason into
*backwards-substantive-reasons*. |#

(defmacro define-backwards-reason
  (name &key forwards-premises backwards-premises conclusion (strength 1.0)
        condition variables defeasible? description)
  (when (stringp name) (setf name (read-from-string name)))

  `(progn
     (proclaim (list 'special ',name))

     (let* ((c-vars (remove-if-not #'(lambda (v) (occur* v ,conclusion)) ,variables))
            (c-binding-function (eval (binding-function ,conclusion c-vars))))
       (setf ,name
             (make-backwards-reason
               :reason-name ',name
               :forwards-premises (rectify-forwards-premises* ,forwards-premises ,variables)
               :backwards-premises (rectify-backwards-premises* ,backwards-premises ,variables)
               :reason-conclusions (list ,conclusion)
               :conclusions-function (conclusion-instantiator ,conclusion ,variables ,defeasible?)
               :reason-variables ,variables
               :reason-strength ,strength
               :defeasible-rule ,defeasible?
               :conclusion-variables c-vars
               :conclusions-binding-function c-binding-function
               :reason-condition ,condition
               :reason-description ,description)))
     ,name))

(defun rectify-backwards-premises* (premise-list variables)
  (if premise-list
    (let ((premises nil))
      (loop
        (let* ((premise* (car premise-list))
               (premise (car premise*))
               (premise-variables (subset #'(lambda (v) (occur* v premise)) variables))
               (condition1 (mem1 (mem2 premise*)))
               (condition2 (mem2 (mem2 premise*))))
          (setf premise-list (cdr premise-list))
          (push
            (make-backwards-premise
              :formula premise
              :condition1 condition1
              :condition2 condition2
              :instantiator (reason-instantiator premise premise-variables))
            premises))
        (when (null premise-list) (return (reverse premises)))))))

#| This displays the problems in *problems* in readable form.  If n is non-nill,
it displays just problem n. |#
(defun display-problems (&optional n)
  (cond ((null n)
         (dolist (P *problems*) (display-problem P)))
        (t (display-problem (assoc n *problems*)))))

(defun display-problem (P)
  (princ "Problem #") (princ (mem1 P)) (terpri)
  (when (mem8 P) (princ (mem8 P)) (terpri))
  (setf *premises* (mem2 P))
  (princ "Given premises:") (terpri)
  (dolist (premise *premises*)
    (princ "     ")
    (prinp (reform-if-string (mem1 premise)))
    (princ "    justification = ") (princ (mem2 premise))
    (terpri))
  (setf *fixed-ultimate-epistemic-interests* nil)
  (setf *ultimate-epistemic-interests* nil)
  (setf *query-number* 0)
  (princ "Ultimate epistemic interests:") (terpri)
  (dolist (interest (mem3 P))
    (let ((query
            (make-query
              :query-number (incf *query-number*)
              :query-formula (reform-if-string (mem1 interest))
              :query-strength (mem2 interest))))
      (push query *fixed-ultimate-epistemic-interests*)
      (princ "     ")
      (prinp (query-formula query)) (princ "    interest = ") (princ (mem2 interest))
      (terpri)))
  (setf *forwards-substantive-reasons* (append (mem4 P) (mem5 P)))
  (setf *backwards-substantive-reasons* (append (mem6 P) (mem7 P)))
  (display-reasons)
  )

(defun display-reasons ()
  (when (some #'defeasible-rule *forwards-substantive-reasons*)
    (terpri) (princ "    FORWARDS PRIMA FACIE REASONS") (terpri)
    (dolist (R *forwards-substantive-reasons*)
      (when (defeasible-rule R) (display-forwards-reason R))))
  (when (some #'(lambda (R) (not (defeasible-rule R))) *forwards-substantive-reasons*)
    (terpri) (princ "    FORWARDS CONCLUSIVE REASONS") (terpri)
    (dolist (R *forwards-substantive-reasons*)
      (when (not (defeasible-rule R)) (display-forwards-reason R))))
  (when (some #'defeasible-rule *backwards-substantive-reasons*)
    (terpri) (princ "    BACKWARDS PRIMA FACIE REASONS") (terpri)
    (dolist (R *backwards-substantive-reasons*)
      (when (defeasible-rule R) (display-backwards-reason R))))
  (when (some #'(lambda (R) (not (defeasible-rule R))) *backwards-substantive-reasons*)
    (terpri) (princ "    BACKWARDS CONCLUSIVE REASONS") (terpri)
    (dolist (R *backwards-substantive-reasons*)
      (when (not (defeasible-rule R)) (display-backwards-reason R))))
  (terpri))

(defun display-forwards-reason (R)
  (princ "      ") (princ (reason-name R))
  (princ ":   {") (print-premise (mem1 (forwards-premises R)))
  (for-all (cdr (forwards-premises R)) #'(lambda (p) (princ " , ") (print-premise p))) (princ "}")
  (princ " ||=> ") (prinp (reason-conclusions R))
  (cond ((reason-variables R)
         (princ "  variables = {") (princ (mem1 (reason-variables R)))
         (for-all (cdr (reason-variables R)) #'(lambda (x)
                                                 (princ ",") (princ x)))
         (princ "}")))
  (princ "   strength = ") (princ (reason-strength R)) (terpri))

(defun print-premise (P)
  (let ((kind (fp-kind P))
        (formula (fp-formula P)))
    (cond ((equal kind :inference) (prinp formula))
          ((equal kind :desire) (princ "< ") (prinp formula) (princ " , desire>"))
          ((equal kind :percept) (princ "< ") (prinp formula) (princ " , percept>")))))

(defun display-backwards-reason (R)
  (princ "      ") (princ (reason-name R)) (princ ":   {")
  (when (mem1 (forwards-premises R)) (prinp (fp-formula (mem1 (forwards-premises R)))))
  (for-all (cdr (forwards-premises R)) #'(lambda (p) (princ " , ") (prinp (fp-formula p)))) (princ "} ")
  (princ "{") (prinp (bp-formula (mem1 (backwards-premises R))))
  (for-all (cdr (backwards-premises R)) #'(lambda (p) (princ " , ") (prinp (bp-formula p)))) (princ "}")
  (princ " ||=> ") (prinp (reason-conclusions R))
  (cond ((reason-variables R)
         (princ "  variables = {") (princ (mem1 (reason-variables R)))
         (for-all (cdr (reason-variables R)) #'(lambda (x)
                                                 (princ ",") (princ x)))
         (princ "}")))
  (princ "   strength = ") (princ (reason-strength R)) (terpri))

;===================== MAKING PROBLEM LISTS =========================

(defvar *forwards-logical-reasons* nil)

(defvar *backwards-logical-reasons* nil)

#| Given a string describing a problem-set, this returns the list of problems. |#
(defun make-problem-list (set-string)
  (mapcar #'make-problem-from-string (problem-strings set-string)))

(defun make-problem-from-string (problem-string)
  (let* ((string (subseq problem-string 9))
         (pos1 (position #\Newline string))
         (problem-number (named-integer (string-trim '(#\Space #\Tab) (subseq string 0 pos1)))))
    (setf string (subseq string (1+ pos1)))
    (let* ((pos2 (search "Given premises:" string :test 'string-equal))
           (problem-description
             (string-trim '(#\Space #\Tab #\Newline) (subseq string 0 pos2))))
      (setf string
            (string-left-trim '(#\Space #\Tab #\Newline) 
                              (subseq string (+ 16 pos2))))
      (let ((premises (find-premises-from-string string)))
        (setf string
              (string-left-trim '(#\Space #\Tab #\Newline)
                                (subseq string
                                        (+ 29 (search "ultimate epistemic interests:" string :test 'string-equal)))))
        (let ((conclusions (find-conclusions-from-string string)))
          (let ((pos3 (search "forwards prima facie reasons" string :test 'string-equal))
                (forwards-pf-reasons nil))
            (when pos3
              (setf string
                    (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 29 pos3))))
              (setf forwards-pf-reasons (find-forwards-pf-reasons string problem-number)))
            (let ((pos4 (search "forwards conclusive reasons" string :test 'string-equal))
                  (forwards-con-reasons nil))
              (when pos4
                (setf string
                      (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 28 pos4))))
                (setf forwards-con-reasons (find-forwards-con-reasons string problem-number)))
              (let ((pos5 (search "backwards prima facie reasons" string :test 'string-equal))
                    (backwards-pf-reasons nil))
                (when pos5
                  (setf string
                        (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 30 pos5))))
                  (setf backwards-pf-reasons (find-backwards-pf-reasons string problem-number)))
                (let ((pos6 (search "backwards conclusive reasons" string :test 'string-equal))
                      (backwards-con-reasons nil))
                  (when pos6
                    (setf string
                          (string-left-trim '(#\Space #\Tab #\Newline) (subseq string (+ 29 pos6))))
                    (setf backwards-con-reasons (find-backwards-con-reasons string problem-number)))
                  (list problem-number
                        (reverse premises)
                        (reverse conclusions)
                        (reverse forwards-pf-reasons)
                        (reverse forwards-con-reasons)
                        (reverse backwards-pf-reasons)
                        (reverse backwards-con-reasons)
                        problem-description))))))))))

#| This finds the first occurrence (if any) of string1 in string2, and returns the next position
after the end of string1.  If string1 does not occur in string2, this returns nil.  The comparison
is not case-sensitive unless case-sensitive is set to t. |#
(defun find-string (string1 string2 &optional case-sensitive)
  (let ((length (length string1))
        (position (search string1 string2 :test (if case-sensitive 'string= 'string-equal))))
    (when position (+ length position))))

#| This removes comment-lines or comments from ends of lines. |#
(defun trim-comments (string)
  (let ((pos (position #\; string)))
    (if pos
      (let ((pos2 (position #\Newline string :start pos)))
        (trim-comments
          (cat (subseq string 0 pos)
               (if (char= (char string (1- pos)) #\Newline)
                 (subseq string (1+ pos2))
                 (subseq string pos2)))))
      string)))

#| Given a string set-string describing a set of problems, this returns the list of strings
describing the individual problems. |#
(defun problem-strings (set-string)
  (setf set-string (trim-comments set-string))
  (let ((start (search "Problem #" set-string :test 'string-equal))
        (strings nil))
    (loop
      (let ((end (search "Problem #" set-string :start2 (1+ start) :test 'string-equal)))
        (cond (end
                (push (subseq set-string start end) strings)
                (setf start end))
              (t
                (push (subseq set-string start) strings)
                (return (reverse strings))))))))

#| If a strength is not listed, it is taken to be 1.0. |#
(defun find-forwards-pf-reasons (string problem-number)
  (let ((reasons nil)
        (pos (search "forwards conclusive reasons" string :test 'string-equal)))
    (when (null pos)
      (setf pos (search "backwards prima facie reasons" string :test 'string-equal)))
    (when (null pos)
      (setf pos (search "backwards conclusive reasons" string :test 'string-equal)))
    (let ((reason-string (subseq string 0 pos)))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos2 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos2))))
            (setf reason-string (subseq reason-string pos2))
            (let* ((pos4 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                   (premises (reform-forwards-premise-list premise-string)))
              (setf reason-string (subseq reason-string pos4))
              (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                (setf reason-string (subseq reason-string pos5))
                (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                      (variables nil)
                      (conclusion nil))
                  (when pos6
                    (setf conclusion
                          (reform
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6))))
                    (let ((pos7 (position #\} reason-string)))
                      (setf variables
                            (string-list (subseq reason-string (+ 13 pos6) pos7)))
                      (setf reason-string (subseq reason-string pos7))))
                  (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                    (when (null pos6)
                      (setf conclusion
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8))))
                    (let* ((pos9 (position #\Newline reason-string))
                           (strength
                             (if (null pos8) 1.0
                               (named-decimal-number
                                 (string-trim
                                   '(#\Space #\Tab) (subseq reason-string (+ 10 pos8) pos9))))))
                      (setf reason-string (subseq reason-string pos9))
                      (push
                        (eval `(define-forwards-reason
                                 ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                 :forwards-premises
                                 ',(mapcar #'(lambda (premise)
                                               (if (stringp premise)
                                                 (list (reform premise) nil)
                                                 (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                           premises)
                                 :conclusion ',(reform-if-string conclusion)
                                 :variables ',variables
                                 :defeasible? t
                                 :strength ',strength))
                        reasons))))))))))))

(defun find-forwards-con-reasons (string problem-number)
  (let ((reasons nil)
        (pos (search "backwards prima facie reasons" string :test 'string-equal)))
    (when (null pos)
      (setf pos (search "backwards conclusive reasons" string :test 'string-equal)))
    (let ((reason-string (subseq string 0 pos)))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos2 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos2))))
            (setf reason-string (subseq reason-string pos2))
            (let* ((pos4 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                   (premises (reform-forwards-premise-list premise-string)))
              (setf reason-string (subseq reason-string pos4))
              (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                (setf reason-string (subseq reason-string pos5))
                (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                      (variables nil)
                      (conclusion nil))
                  (when pos6
                    (setf conclusion
                          (reform
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6))))
                    (let ((pos7 (position #\} reason-string)))
                      (setf variables
                            (string-list (subseq reason-string (+ 13 pos6) pos7)))
                      (setf reason-string (subseq reason-string pos7))))
                  (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                    (when (null pos6)
                      (setf conclusion
                            (string-trim
                              '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8))))
                    (let* ((pos9 (position #\Newline reason-string)))
                      (setf reason-string (subseq reason-string pos9))
                      (push
                        (eval `(define-forwards-reason
                                 ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                 :forwards-premises ',(mapcar #'(lambda (premise)
                                                                  (if (stringp premise)
                                                                    (list (reform premise) nil)
                                                                    (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                              premises)
                                 :conclusion ',(reform-if-string conclusion)
                                 :variables ',variables))
                        reasons))))))))))))

(defun find-backwards-pf-reasons (string problem-number)
  (let ((reasons nil)
        (pos (search "backwards conclusive reasons" string :test 'string-equal)))
    (let ((reason-string (subseq string 0 pos)))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos10 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos10))))
            (setf reason-string (subseq reason-string pos10))
            (let* ((pos11 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos11)))
                   (forwards-premises
                     (mapcar #'(lambda (p) (list p nil)) (reform-list premise-string))))
              (setf reason-string (subseq reason-string pos11))
              (let* ((pos2 (position #\{ reason-string)))
                (setf reason-string (subseq reason-string pos2))
                (let* ((pos4 (position #\} reason-string))
                       (premise-string
                         (string-trim
                           '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                       (backwards-premises
                         (mapcar #'(lambda (p) (list p nil))  (reform-list premise-string))))
                  (setf reason-string (subseq reason-string pos4))
                  (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                    (setf reason-string (subseq reason-string pos5))
                    (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                          (variables nil)
                          (conclusion nil))
                      (when pos6
                        (setf conclusion
                              (list
                                (reform
                                  (string-trim
                                    '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6)))
                                nil))
                        (let ((pos7 (position #\} reason-string)))
                          (setf variables
                                (string-list (subseq reason-string (+ 13 pos6) pos7)))
                          (setf reason-string (subseq reason-string pos7))))
                      (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                        (when (null pos6)
                          (setf conclusion
                                (list
                                  (reform
                                    (string-trim
                                      '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8)))
                                  nil)))
                        (let* ((pos9 (position #\Newline reason-string))
                               (strength
                                 (if (null pos8) 1.0
                                   (named-decimal-number
                                     (string-trim
                                       '(#\Space #\Tab) (subseq reason-string (+ 10 pos8) pos9))))))
                          (setf reason-string (subseq reason-string pos9))
                          (push
                            (eval `(define-backwards-reason
                                     ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                     :forwards-premises ',(mapcar #'(lambda (premise)
                                                                      (if (stringp premise)
                                                                        (list (reform premise) nil)
                                                                        (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                  forwards-premises)
                                     :backwards-premises ',(mapcar #'(lambda (premise)
                                                                       (if (stringp premise)
                                                                         (list (reform premise) nil)
                                                                         (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                   backwards-premises)
                                     :conclusion ',(if (stringp conclusion)
                                                     (reform conclusion)
                                                     (reform-if-string (mem1 conclusion)))
                                     :condition ',(if (stringp conclusion)
                                                    nil
                                                    (mem2 conclusion))
                                     :variables ',variables
                                     :defeasible? t
                                     :strength ',strength))
                            reasons))))))))))))))

(defun find-backwards-con-reasons (string problem-number)
  (let ((reasons nil))
    (let ((reason-string string))
      (loop
        (let ((pos1 (search "||=>" reason-string :test 'string-equal)))
          (when (null pos1) (return reasons))
          (let* ((pos10 (position #\{ reason-string))
                 (name (string-trim
                         '(#\Space #\Tab #\Newline #\:) (subseq reason-string 0 pos10))))
            (setf reason-string (subseq reason-string pos10))
            (let* ((pos11 (position #\} reason-string))
                   (premise-string
                     (string-trim
                       '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos11)))
                   (forwards-premises
                     (mapcar #'(lambda (p) (list p nil)) (reform-list premise-string))))
              (setf reason-string (subseq reason-string pos11))
              (let* ((pos2 (position #\{ reason-string)))
                (setf reason-string (subseq reason-string pos2))
                (let* ((pos4 (position #\} reason-string))
                       (premise-string
                         (string-trim
                           '(#\Space #\Tab #\Newline #\{ #\}) (subseq reason-string 0 pos4)))
                       (backwards-premises
                         (mapcar #'(lambda (p) (list p nil))  (reform-list premise-string))))
                  (setf reason-string (subseq reason-string pos4))
                  (let ((pos5 (search "||=>" reason-string :test 'string-equal)))
                    (setf reason-string (subseq reason-string pos5))
                    (let ((pos6 (search "variables = {" reason-string :test 'string-equal))
                          (variables nil)
                          (conclusion nil))
                      (when pos6
                        (setf conclusion
                              (list
                                (reform
                                  (string-trim
                                    '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos6)))
                                nil))
                        (let ((pos7 (position #\} reason-string)))
                          (setf variables
                                (string-list (subseq reason-string (+ 13 pos6) pos7)))
                          (setf reason-string (subseq reason-string pos7))))
                      (let ((pos8 (search "strength =" reason-string :test 'string-equal)))
                        (when (null pos6)
                          (setf conclusion
                                (list
                                  (reform
                                    (string-trim
                                      '(#\Space #\Tab #\Newline) (subseq reason-string 4 pos8)))
                                  nil)))
                        (let* ((pos9 (position #\Newline reason-string)))
                          (setf reason-string (subseq reason-string pos9))
                          (push
                            (eval `(define-backwards-reason
                                     ,(read-from-string (cat-list (list name "." (string-rep problem-number))))
                                     :forwards-premises ',(mapcar #'(lambda (premise)
                                                                      (if (stringp premise)
                                                                        (list (reform premise) nil)
                                                                        (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                  forwards-premises)
                                     :backwards-premises ',(mapcar #'(lambda (premise)
                                                                       (if (stringp premise)
                                                                         (list (reform premise) nil)
                                                                         (list (reform-if-string (mem1 premise)) (mem2 premise))))
                                                                   backwards-premises)
                                     :conclusion ',(if (stringp conclusion)
                                                     (reform conclusion)
                                                     (reform-if-string (mem1 conclusion)))
                                     :condition ',(if (stringp conclusion)
                                                    nil
                                                    (mem2 conclusion))
                                     :variables ',variables))
                            reasons))))))))))))))

#| Where string contains spaces, this returns the list of words separated by spaces.
Words can be separated by commas, provided there is whitespace between commas
and adjoining words.  The commas are then removed. |#
(defun string-list (string)
  (let ((string* (string-trim '(#\Space #\Tab #\Newline) string))
        (words nil))
    (when (not (eql (length string*) 0))
      (loop
        (let ((pos (search " " string*)))
          (when (null pos)
            (push string* words)
            (setf words (reverse (remove-if-equal "," words)))
            (return nil))
          (push (subseq string* 0 pos) words)
          (setf string* (string-left-trim '(#\Space) (subseq string* pos))))))
    (collapse-strings words)))

#| Where string is a string of pretty-formulas separated by commas (and whitespace on
                                                                        either side of the commas, if desired), this returns the list of formulas. |#
(defun reform-list (string)
  (let ((formulas nil)
        (string-remainder string))
    (loop
      (let ((pos (position #\, string-remainder)))
        (when (null pos)
          (let ((formula-string (string-trim '(#\Space) string-remainder)))
            (when (not (equal formula-string ""))
              (push formula-string formulas)))
          (return nil))
        (push (string-trim '(#\Space) (subseq string-remainder 0 pos)) formulas)
        (setf string-remainder (subseq string-remainder (1+ pos)))))
    (mapcar #'reform (reverse formulas))))

#| This allows the premises of a forwards-reason to be entered either as a single
formula, or as a pair <formula , condition> where condition is either "inference",
"desire", or "percept" (entered without quotes).  If a formula is entered alone,
the default condition NIL is used. |#
(defun reform-forwards-premise-list (string)
  ; (setf s string) (break)
  (let ((premises nil)
        (string-remainder (string-trim '(#\Space) string)))
    (loop
      (cond ((equal (length string-remainder) 0) (return nil))
            ((equal (subseq string-remainder 0 1) "<")
             (let* ((pos (position #\> string-remainder))
                    (premise-string (subseq string-remainder 1 pos))
                    (pos1 (position #\, premise-string))
                    (formula-string (string-trim '(#\Space) (subseq premise-string 0 pos1)))
                    (condition-string (string-trim '(#\Space) (subseq premise-string (1+ pos1))))
                    (condition
                      (cond ((equal condition-string "inference") is-inference)
                            ((equal condition-string "desire") is-desire)
                            ((equal condition-string "percept") is-percept))))
               (setf string-remainder
                     (string-trim '(#\Space #\,) (subseq string-remainder (1+ pos))))
               (push (list (reform formula-string) condition) premises)))
            (t
              (let ((pos (position #\, string-remainder)))
                (when (null pos)
                  (let ((formula-string (string-trim '(#\Space) string-remainder)))
                    (when (not (equal formula-string ""))
                      (push (list (reform formula-string) NIL) premises)))
                  (return nil))
                (push
                  (list (reform (string-trim '(#\Space) (subseq string-remainder 0 pos)))
                        is-inference)
                  premises)
                (setf string-remainder
                      (string-trim '(#\Space) (subseq string-remainder (1+ pos))))))))
    (reverse premises)))

#| This recombines logical formulas containing whitespace that were taken apart by
string-list. |#
(defun collapse-strings (strings)
  (cond ((< (length strings) 2) strings)
        ((mem (mem2 strings) '("v" "->" "<->" "&" "@"))
         (let ((cs (collapse-strings (cddr strings))))
           (cons (concatenate 'string (mem1 strings) " " (mem2 strings) " " (mem1 cs))
                 (cdr cs))))
        (t (cons (mem1 strings) (collapse-strings (cdr strings))))))

(defun find-premises-from-string (string)
  (let ((premises nil)
        (subseq string))
    (loop
      (let ((pos (search "justification =" subseq :test 'string-equal)))
        (when (null pos) (return premises))
        (let ((premise (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 0 pos))))
          (setf subseq (subseq subseq pos))
          (setf pos (position #\Newline subseq))
          (let ((degree
                  (named-decimal-number
                    (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 15 pos)))))
            (setf subseq (subseq subseq pos))
            (push (list (reform premise) degree) premises)))))))

(defun find-conclusions-from-string (string)
  (let ((conclusions nil)
        (subseq string))
    (loop
      (let ((pos (search "interest =" subseq :test 'string-equal)))
        (when (null pos) (return conclusions))
        (let ((conclusion (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 0 pos))))
          (setf subseq (subseq subseq pos))
          (setf pos (position #\Newline subseq))
          (let ((degree
                  (named-decimal-number (string-trim '(#\Space #\Tab #\Newline) (subseq subseq 10 pos)))))
            (setf subseq (subseq subseq pos))
            (push (list (reform conclusion) degree) conclusions)))))))

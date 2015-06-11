(proclaim '(special *arguments* *nodes-done* *arg-number* *nodes-used*))

(defun print-argument (x stream depth)
  (declare (ignore depth))
  (princ "#<" stream) (princ "argument " stream)
  (princ (argument-number x) stream)
  (princ " for node " stream) (princ (argument-node x) stream)
  (princ ">" stream))

(defstruct (argument (:print-function print-argument) (:conc-name nil))
  (argument-number 0)
  (argument-links nil)
  (argument-node nil)
  (argument-defeaters nil)
  (argument-defeatees nil)
  (argument-strength 0)
  (argument-ultimate-interest nil)
  (argument-inclusive-nodes nil))

(defun hypernode-arguments (node &optional used-sequents)
  (if (hypernode-hyperlinks node)
    (let ((S (hypernode-sequent node)))
      ; (union=
      (unionmapcar=
        #'(lambda (L)
            (if (hyperlink-basis L)
              (when
                (and
                  (not (some #'(lambda (b)
                                 (and (is-inference b) (subsumes (hypernode-sequent b) S)))
                             (hyperlink-basis L)))
                  (not (some #'(lambda (S)
                                 (some #'(lambda (b)
                                           (and (is-inference b) (subsumes (hypernode-sequent b) S)))
                                       (hyperlink-basis L)))
                             used-sequents)))
                (mapcar
                  #'(lambda (arg) (cons L arg))
                  (mapcar
                    #'genunion
                    (gencrossproduct
                      (append
                        (mapcar
                          #'(lambda (b) (hypernode-arguments b (cons S used-sequents)))
                          (motivating-nodes node))
                        (mapcar
                          #'(lambda (b) (hypernode-arguments b (cons S used-sequents)))
                          (hyperlink-basis L)))))))
              (list (list L))))
        (hypernode-hyperlinks node)))
    (list nil)))

#| An argument is a list of hyperlinks. |#
(defun independent-of (sequent argument)
  (not (some #'(lambda (L)
                 (some #'(lambda (b) (subsumes (hypernode-sequent b) sequent))
                       (hyperlink-basis L)))
             argument)))

#| If nodes is nonempty, this constructs all arguments relevant to nodes.  Otherwise, it
constructs all arguments relevant to ultimate-epistemic-interests. |#
(defun show-arguments (&optional nodes)
  (setf *arg-number* 0 *nodes-used* nil *arguments* nil *nodes-done* nil)
  (when (null nodes)
    (setf nodes (unionmapcar+ #'query-answers *ultimate-epistemic-interests*)))
  (dolist (n nodes)
    (push n *nodes-done*)
    (push n *nodes-used*)
    (dolist (arg (hypernode-arguments n))
      (when
        (not
          (some
            #'(lambda (a2)
                (and
                  (eq n (argument-node a2))
                  (subsetp (argument-links a2) arg)))
            *arguments*))
        (dolist (a2 *arguments*)
          (when
            (and
              (eq n (argument-node a2))
              (subsetp arg (argument-links a2)))
            (pull a2 *arguments*)))
        (let ((argument
                (make-argument
                  :argument-number (incf *arg-number*)
                  :argument-links arg
                  :argument-node n
                  :argument-strength
                  (minimum0 (mapcar #'hyperlink-strength+ arg))
                  ; (if (every #'(lambda (L) (null (defeating-assignment-trees L))) arg)
                  ;    (minimum0 (mapcar #'hyperlink-strength+ arg)) 0)
                  :argument-ultimate-interest (mem1 (hypernode-answered-queries n))
                  :argument-inclusive-nodes (list n))))
          (push argument *arguments*)
          (dolist (m (motivating-nodes n))
            (pushnew m (argument-inclusive-nodes argument))
            (pushnew m *nodes-used*))
          (dolist (L (argument-links argument))
            (dolist (b (hyperlink-basis L))
              (pushnew b (argument-inclusive-nodes argument))
              (pushnew b *nodes-used*)
              (dolist (m (motivating-nodes b))
                (pushnew m (argument-inclusive-nodes argument))
                (pushnew m *nodes-used*))))))))
  (dolist (argument *arguments*)
    (find-defeating-arguments argument))
  (dolist (argument (reverse *arguments*))
    (display-argument argument))
  (let ((argument-length (length *nodes-used*))
        (graph-size *hypernode-number*))
    (princ "===========================================================================")
    (terpri)
    (terpri) (terpri)
    (princ "Cumulative size of arguments = ") (princ argument-length) (terpri)
    (princ "Size of inference-graph = ") (princ graph-size)
    (princ " of which ") (princ *unused-suppositions*)
    (princ " were unused suppositions.") (terpri)
    (princ (truncate (* argument-length 100) graph-size))
    (princ "% of the inference-graph was used in the argument.") (terpri)))

(defun hyperlink-strength+ (L)
  (or (hyperlink-degree-of-justification L)
      (if (not (defeasible-rule (hyperlink-rule L))) 1.0 0)))

(defun find-defeating-arguments (argument)
  (dolist (L (argument-links argument))
    (when (hyperlink-defeasible? L)
      (dolist (d (hyperlink-defeaters L))
        (cond ((member d *nodes-done*)
               (dolist (arg *arguments*)
                 (when (eq (argument-node arg) d)
                   (pushnew arg (argument-defeaters argument))
                   (pushnew argument (argument-defeatees arg)))))
              (t
                (push d *nodes-done*)
                (push d *nodes-used*)
                (dolist (d-arg (hypernode-arguments d))
                  (when
                    (not
                      (some
                        #'(lambda (a2)
                            (and
                              (eq d (argument-node a2))
                              (subsetp (argument-links a2) d-arg)))
                        *arguments*))
                    (dolist (a2 *arguments*)
                      (when
                        (and
                          (eq d (argument-node a2))
                          (subsetp d-arg (argument-links a2)))
                        (pull a2 *arguments*)))
                    (let ((d-argument
                            (make-argument
                              :argument-number (incf *arg-number*)
                              :argument-links d-arg
                              :argument-node d
                              :argument-strength
                              (minimum0 (mapcar #'hyperlink-degree-of-justification d-arg))
                              :argument-inclusive-nodes (list d))))
                      (push d-argument *arguments*)
                      (dolist (m (motivating-nodes d))
                        (pushnew m (argument-inclusive-nodes d-argument))
                        (pushnew m *nodes-used*))
                      (pushnew d-argument (argument-defeaters argument))
                      (pushnew argument (argument-defeatees d-argument))
                      (dolist (L (argument-links d-argument))
                        (dolist (b (hyperlink-basis L))
                          (pushnew b (argument-inclusive-nodes d-argument))
                          (pushnew b *nodes-used*)
                          (dolist (m (motivating-nodes b))
                            (pushnew m (argument-inclusive-nodes d-argument))
                            (pushnew m *nodes-used*))))
                      (find-defeating-arguments d-argument))))))))))

(defun deductive-argument (arg)
  (every #'(lambda (L) (not (hyperlink-defeasible? L))) (argument-links arg)))

(defun display-argument (arg &optional fw)
  (let ((n (argument-node arg)))
    (princ "===========================================================================" fw)
    (terpri fw) (princ "ARGUMENT #" fw) (princ (argument-number arg) fw)
    (terpri fw) (princ "This is " fw)
    (cond ((deductive-argument arg) (princ "a deductive argument for:" fw))
          ((zerop (argument-strength arg)) (princ "a defeated argument for:" fw))
          (t (princ "an undefeated argument of strength " fw) (princ (argument-strength arg) fw)
             (princ " for:" fw)))
    (terpri fw) (princ "      " fw)
    (if (hypernode-supposition n) (prinp-sequent (hypernode-sequent n) fw) (prinp (hypernode-formula n) fw)) (terpri fw)
    (when (argument-ultimate-interest arg)
      (princ " which is of ultimate interest." fw) (terpri fw))
    (format-argument arg fw) (terpri fw)
    (let ((d-args
            (order (mapcar #'argument-number (argument-defeaters arg)) #'<)))
      (when d-args
        (cond ((> (length d-args) 1)
               (princ "Arguments " fw))
              (t (princ "Argument " fw)))
        (princ "#" fw) (princ (car d-args) fw)
        (dolist (d-arg (cdr d-args)) (princ ", #" fw) (princ d-arg fw))
        (princ " support defeaters for this argument." fw) (terpri fw)))
    (when (and (argument-defeaters arg) (argument-defeatees arg)) (terpri fw))
    (let ((d-args
            (order (mapcar #'argument-number (argument-defeatees arg)) #'<)))
      (when d-args
        (princ "This argument supports defeaters for " fw)
        (princ "{ " fw)
        (let ((L (car (hypernode-defeatees n))))
          (princ "link " fw)
          (princ (hyperlink-number L) fw) (princ " for node " fw)
          (princ (hypernode-number (hyperlink-target L)) fw))
        (dolist (L (cdr (hypernode-defeatees n)))
          (princ " , " fw)
          (princ "link " fw)
          (princ (hyperlink-number L)) (princ " for node " fw)
          (princ (hypernode-number (hyperlink-target L)) fw))
        (princ " }" fw)
        (princ " thereby providing defeaters for " fw)
        (cond ((> (length d-args) 1)
               (princ "arguments " fw))
              (t (princ "argument " fw)))
        (princ "#" fw) (princ (car d-args) fw)
        (dolist (d-arg (cdr d-args)) (princ ", #" fw) (princ d-arg fw))
        (terpri fw)))
    ))

(defun hypernode-basis-in-arg (node arg)
  (let ((link (find-if #'(lambda (L) (eq (hyperlink-target L) node)) (argument-links arg))))
    ; (union (motivating-nodes node)
    (if link (hyperlink-basis link)))) ;)

#| Choose the first node all of whose ancestors are already in lines and whose
supposition is the same as the last one, if there is one.  Otherwise, choose the
first node all of whose ancestors are already in lines and whose supposition is
such that every node having that supposition is such that all of its ancestors are
either already in a line or have that same supposition.    Otherwise, choose the
first node all of whose ancestors are already in lines and whose supposition
is already used, if there is one.  Otherwise, choose the first line all of whose
ancestors are already in lines, and put its supposition in sups-used. |#
(defun format-argument (arg  &optional fw)
  (let* ((nodes (order (argument-inclusive-nodes arg) 'sup-order))
         (sups-used (list nil))
         (sup nil)
         (nodes-done nil))
    (loop
      ; (princ nodes) (terpri)
      ; (princ nodes-done) (terpri)
      (let ((next
              (find-if
                #'(lambda (x)
                    (and
                      (equal (hypernode-supposition x) sup)
                      (subsetp (hypernode-basis-in-arg x arg) nodes-done)))
                nodes)))
        (when (null next)
          (setq next
                (find-if
                  #'(lambda (x)
                      (and (subsetp (hypernode-basis-in-arg x arg) nodes-done)
                           (let ((sup (hypernode-supposition x)))
                             (every
                               #'(lambda (n)
                                   (or (member n nodes-done)
                                       (not (subsetp= sup (hypernode-supposition n)))
                                       (every
                                         #'(lambda (anc)
                                             (or (member anc nodes-done)
                                                 (equal (hypernode-supposition anc) sup)))
                                         (hypernode-basis-in-arg x arg))))
                               nodes))))
                  nodes))
          (when (null next)
            (setq next
                  (find-if
                    #'(lambda (x)
                        (and (mem (hypernode-supposition x) sups-used)
                             (subsetp (hypernode-basis-in-arg x arg) nodes-done)))
                    nodes))
            (when (null next)
              (setq next
                    (find-if
                      #'(lambda (x)
                          (subsetp (hypernode-basis-in-arg x arg) nodes-done))
                      nodes)))))
        (pushnew (hypernode-supposition next) sups-used)
        (setq sup (hypernode-supposition next))
        (pull next nodes)
        (push next nodes-done))
      (when (null nodes) (return)))
    (print-formatted-argument (reverse nodes-done) arg fw)))

(defun print-formatted-argument (nodes arg &optional fw)
  (let ((nodes-left nodes)
        (current-sup nil)
        (depth-list (list (cons 0 nil)))
        (indent-value 0))
    (loop
      (let* ((n (mem1 nodes-left))
             (sup (hypernode-supposition n))
             (depth (length sup)))
        (cond ((not (equal sup current-sup))
               (cond ((or (<= indent-value depth)
                          (not (equal sup (e-assoc depth depth-list))))
                      (setq depth-list (cons (cons depth sup) depth-list))
                      (print-supposition sup depth fw)))
               (setq indent-value depth)
               (setq current-sup sup)))
        (terpri fw)
        (clear-indent indent-value fw) (princ " " fw) (princ (hypernode-number n) fw) (princ ".  " fw)
        (when (equal (hypernode-kind n) :percept) (princ "It appears that " fw))
        (prinp (hypernode-formula n) fw)
        (princ "     " fw)
        (let ((link (find-if #'(lambda (L) (eq (hyperlink-target L) n)) (argument-links arg))))
          (cond ((equal (hypernode-kind n) :percept) (princ "given" fw))
                ((hypernode-justification n) (princ (hypernode-justification n) fw))
                (link
                  (princ (hyperlink-rule link) fw)
                  (princ " from " fw)
                  (princ-set (mapcar #'hypernode-number (hyperlink-basis link)) fw))
                (t (let ((args (subset #'(lambda (A) (eq (argument-node A) n)) *arguments*)))
                     (cond ((eql (length args) 1)
                            (princ "by argument #" fw) (princ (argument-number (mem1 args)) fw))
                           ((> (length args) 1)
                            (princ "by arguments #" fw) (princ (argument-number (mem1 args)) fw)
                            (dolist (A (cdr args))
                              (princ ", #" fw) (princ (argument-number A) fw))))))))
        (setq nodes-left (cdr nodes-left))
        (if (null nodes-left) (return))))
    (terpri fw)))

(defun sup-order (n m)
  (subsetp= (hypernode-supposition n) (hypernode-supposition m)))

(defun print-supposition (sup indent-value &optional fw)
  (cond (sup
          (terpri fw)
          (clear-indent indent-value fw)
          (princ "----------------------------------------------------------" fw)
          (terpri fw) (clear-indent indent-value fw)
          (princ " Suppose:  " fw)
          (set-prinp sup fw)
          (terpri fw)
          (clear-indent indent-value fw)
          (princ "----------------------------------------------------------" fw)
          )))

(defun clear-indent (n &optional fw)
  (dotimes (x n) (princ "        " fw))
  (if (not (zerop n)) (princ "|" fw)))

(defun display-arguments ()
  (dolist (n *nodes-done*)
    (princ n) (princ " for ") (print-sequent (hypernode-sequent n)) (terpri)
    (let ((arguments (subset #'(lambda (a) (eq (argument-node a) n)) *arguments*)))
      (dolist (arg arguments)
        (princ arg) (terpri)))
    ; (print-argument-relations arg)))
    (princ "-------------------------") (terpri)))

(defun print-argument-relations (arg &optional (arguments *arguments*) (depth 0))
  (bar-indent depth) (princ arg) (terpri)
  (let ((subarguments nil))
    (dolist (a2 arguments)
      (when
        (and (not (eq a2 arg))
             (subsetp (argument-links a2) (argument-links arg))
             (not (some
                    #'(lambda (s) (subsetp (argument-links arg) (argument-links s)))
                    subarguments)))
        (dolist (s subarguments)
          (when (subsetp (argument-links s) (argument-links arg))
            (pull s subarguments)))
        (push a2 subarguments)))
    (dolist (s subarguments)
      (print-argument-relations s subarguments (+ 5 depth)))))

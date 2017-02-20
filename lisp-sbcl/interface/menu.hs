;; This defines display tools that only work in Macintosh Common LISP

(defunction add-OSCAR-menu ()
    (let* ((menubar (menubar))
              (OSCAR-menu (find-if #'(lambda (item) (equal (menu-title item) *version*)) menubar))
              (new-OSCAR-menu
                (make-instance 'menu
                  :menu-title *version*
                  :menu-items
                  (list
                    (make-instance 'menu-item
                         :menu-item-title "Tear off menu"
                         :menu-item-action #'(lambda nil (tear-off-oscar-menu)))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Display on"
                         :menu-item-action #'(lambda nil (m-display-on))
                         :disabled *display?*)
                    (make-instance 'menu-item
                         :menu-item-title "Display off"
                         :menu-item-action
                         #'(lambda nil (m-display-off))
                         :disabled (not *display?*))
                    (make-instance 'menu-item
                         :menu-item-title "Display from"
                         :menu-item-action
                         #'(lambda nil
                               (setf *menu-dialog*
                                        (make-instance 'dialog
                                             :window-type :double-edge-box
                                             :view-position #@(60 51)
                                             :view-size #@(222 98)
                                             :close-box-p nil
                                             :view-font '("Chicago" 12 :srcor :plain)
                                             :view-subviews
                                             (list 
                                               (make-dialog-item
                                                 'static-text-dialog-item #@(8 12) #@(208 50)
                                                 "Enter the cycle at which display is to begin and type a carriage-return."
                                                 'nil
                                                 :text-justification :center)
                                               (make-dialog-item
                                                 'editable-text-dialog-item #@(85 75) #@(48 16)
                                                 (write-to-string *start-display*)
                                                 #'(lambda (item)
                                                       (let ((text (dialog-item-text item)))
                                                          (when (and (> (length text) 0)
                                                                                (equal (substring text (1- (length text))) "
"))
                                                               (display-from (read-from-string text))
                                                               (window-close *menu-dialog*))))
                                                 :allow-returns t))))))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Trace on"
                         :menu-item-action #'(lambda nil (m-Trace-on))
                         :disabled *trace*)
                    (make-instance 'menu-item
                         :menu-item-title "Trace off"
                         :menu-item-action #'(lambda nil (m-Trace-off))
                         :disabled (not *trace*))
                    (make-instance 'menu-item
                         :menu-item-title "Trace from"
                         :menu-item-action
                         #'(lambda nil
                               (setf *menu-dialog*
                                        (make-instance 'dialog
                                             :window-type :double-edge-box
                                             :view-position #@(60 51)
                                             :view-size #@(222 98)
                                             :close-box-p nil
                                             :view-font '("Chicago" 12 :srcor :plain)
                                             :view-subviews
                                             (list 
                                               (make-dialog-item
                                                 'static-text-dialog-item #@(8 12) #@(208 50)
                                                 "Enter the cycle at which trace is to begin and type a carriage-return."
                                                 'nil
                                                 :text-justification :center)
                                               (make-dialog-item
                                                 'editable-text-dialog-item #@(85 75) #@(48 16)
                                                 (write-to-string *start-trace*)
                                                 #'(lambda (item)
                                                       (let ((text (dialog-item-text item)))
                                                          (when (and (> (length text) 0)
                                                                                (equal (substring text (1- (length text))) "
"))
                                                               (trace-from (read-from-string text))
                                                               (window-close *menu-dialog*))))
                                                 :allow-returns t))))))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Log on"
                         :menu-item-action #'(lambda nil (m-Log-on))
                         :disabled *log-on*)
                    (make-instance 'menu-item
                         :menu-item-title "Log off"
                         :menu-item-action #'(lambda nil (m-Log-off))
                         :disabled (not *log-on*))
                    (make-instance 'menu-item
                         :menu-item-title "Display Log Now"
                         :menu-item-action #'(lambda nil (display-reasoning)))
                    ; (make-instance 'menu-item
                    ;      :menu-item-title "Display Log Now, completely"
                    ;      :menu-item-action #'(lambda nil (display-reasoning t)))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Proof on"
                         :menu-item-action #'(lambda nil (m-Proof-on))
                         :disabled *proofs?*)
                    (make-instance 'menu-item
                         :menu-item-title "Proof off"
                         :menu-item-action #'(lambda nil (m-Proof-off))
                         :disabled (not *proofs?*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Logic on"
                         :menu-item-action #'(lambda nil (m-Logic-on))
                         :disabled *use-logic*)
                    (make-instance 'menu-item
                         :menu-item-title "Logic off"
                         :menu-item-action #'(lambda nil (m-Logic-off))
                         :disabled (not *use-logic*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Reductio on"
                         :menu-item-action #'(lambda nil (m-Reductio-on))
                         :disabled *use-reductio*)
                    (make-instance 'menu-item
                         :menu-item-title "Reductio off"
                         :menu-item-action #'(lambda nil (m-Reductio-off))
                         :disabled (not *use-reductio*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Deductive only"
                         :menu-item-action #'(lambda nil (do-deductive-only))
                         :disabled *deductive-only*)
                    (make-instance 'menu-item
                         :menu-item-title "All Reasoning"
                         :menu-item-action #'(lambda nil (do-all-reasoning))
                         :disabled (not *deductive-only*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Show inference-queue"
                         :menu-item-action #'(lambda nil (m-IQ-on))
                         :disabled *display-inference-queue*)
                    (make-instance 'menu-item
                         :menu-item-title "Do not show inference-queue"
                         :menu-item-action #'(lambda nil (m-IQ-off))
                         :disabled (not *display-inference-queue*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Initialize OSCAR Graphics"
                         :menu-item-action
                         #'(lambda nil
                               (princ "Loading oscar-graphics") (terpri)
                               (load (merge-pathnames oscar-pathname "oscar-graphics_4-02"))
                               (eval '(initialize-graphics))))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title (cat "Enter package " *package-name*)
                         :menu-item-action
                         (eval `#'(lambda nil (in-package ,*package-name*))))
                    ))))
       (if OSCAR-menu
          (set-menubar (replace-item-in-list OSCAR-menu new-OSCAR-menu menubar))
          (set-menubar (append menubar (list new-OSCAR-menu))))))

(proclaim '(special *display-box*))

(defunction tear-off-OSCAR-menu ()
    (make-instance 'windoid
         :window-type :tool
         :view-position #@(242 40)
         :view-size #@(217 351)
         :view-font '("Helvetica" 9 :srcor :plain)
         :window-title *version*
         :close-box-p t
         :view-subviews
         (list
           (setf *display-button*
                    (make-dialog-item
                      'check-box-dialog-item #@(6 3) #@(188 22)
                      "Display on" 'b-display-on 
                      :check-box-checked-p *display?*))
           (make-dialog-item
             'check-box-dialog-item #@(6 21) #@(188 22)
             "Display from"
             #'(lambda (item)
                   (check-box-uncheck item)
                   (setf *menu-dialog*
                            (make-instance 'dialog
                                 :window-type :double-edge-box
                                 :view-position #@(60 51)
                                 :view-size #@(222 98)
                                 :close-box-p nil
                                 :view-font '("Chicago" 12 :srcor :plain)
                                 :view-subviews
                                 (list 
                                   (make-dialog-item
                                     'static-text-dialog-item #@(8 12) #@(208 50)
                                     "Enter the cycle at which display is to begin and type a carriage-return."
                                     'nil
                                     :text-justification :center)
                                   (make-dialog-item
                                     'editable-text-dialog-item #@(85 75) #@(48 16)
                                     (write-to-string *start-display*)
                                     #'(lambda (item)
                                           (let ((text (dialog-item-text item)))
                                             (when (and (> (length text) 0)
                                                                 (equal (substring text (1- (length text))) "
"))
                                                  (display-from (read-from-string text))
                                                  (window-close *menu-dialog*))))
                                     :allow-returns t))))))
           (make-dialog-item
             'static-text-dialog-item  #@(6 39) #@(188 22)
             "---------------------------------------------")
           (setf *trace-button*
                    (make-dialog-item
                      'check-box-dialog-item #@(6 50) #@(188 22)
                      "Trace on" 'b-trace-on 
                      :check-box-checked-p *trace*))
           (make-dialog-item
             'check-box-dialog-item #@(6 68) #@(188 22)
             "Trace from"
             #'(lambda (item)
                   (check-box-uncheck item)
                   (setf *menu-dialog*
                            (setf *menu-dialog*
                                     (make-instance 'dialog
                                          :window-type :double-edge-box
                                          :view-position #@(60 51)
                                          :view-size #@(222 98)
                                          :close-box-p nil
                                          :view-font '("Chicago" 12 :srcor :plain)
                                          :view-subviews
                                          (list 
                                            (make-dialog-item
                                              'static-text-dialog-item #@(8 12) #@(208 50)
                                              "Enter the cycle at which trace is to begin and type a carriage-return."
                                              'nil
                                              :text-justification :center)
                                            (make-dialog-item
                                              'editable-text-dialog-item #@(85 75) #@(48 16)
                                              (write-to-string *start-trace*)
                                              #'(lambda (item)
                                                    (let ((text (dialog-item-text item)))
                                                      (when (and (> (length text) 0)
                                                                          (equal (substring text (1- (length text))) "
"))
                                                           (trace-from (read-from-string text))
                                                           (window-close *menu-dialog*))))
                                              :allow-returns t)))))))
           (make-dialog-item
             'static-text-dialog-item  #@(6 86) #@(188 22)
             "---------------------------------------------")
           (make-dialog-item
             'check-box-dialog-item #@(6 97) #@(188 22)
             "Log on" 'b-log-on 
             :check-box-checked-p *log-on*)
           (make-dialog-item
             'check-box-dialog-item #@(6 115) #@(188 22)
             "Display log now" #'(lambda (item) (check-box-uncheck item) (display-reasoning)))
           (make-dialog-item
             'check-box-dialog-item #@(6 133) #@(188 22)
             "Proof on" 'b-proof-on 
             :check-box-checked-p *proofs?*)
           (make-dialog-item
             'static-text-dialog-item  #@(6 151) #@(188 22)
             "---------------------------------------------")
           (make-dialog-item
             'check-box-dialog-item #@(6 166) #@(188 22)
             "Logic on" 'b-logic-on 
             :check-box-checked-p *use-logic*)
           (make-dialog-item
             'check-box-dialog-item #@(6 184) #@(188 22)
             "Reductio on" 'b-reductio-on 
             :check-box-checked-p *use-reductio*)
           (make-dialog-item
             'check-box-dialog-item #@(6 202) #@(188 22)
             "Deductive only" 'b-deductive-only 
             :check-box-checked-p *deductive-only*)
           (make-dialog-item
             'static-text-dialog-item  #@(6 220) #@(188 22)
             "---------------------------------------------")
           (make-dialog-item
             'check-box-dialog-item #@(6 231) #@(188 22)
             "Show inference queue" 'b-IQ-on 
             :check-box-checked-p *display-inference-queue*)
           (make-dialog-item
             'static-text-dialog-item  #@(6 285) #@(188 22)
             "---------------------------------------------")
           (make-dialog-item
             'check-box-dialog-item #@(6 296) #@(188 22)
             "Initialize OSCAR Graphics"
             #'(lambda (item)
                   (check-box-check item)
                   (princ "Loading oscar-graphics") (terpri)
                   (load (merge-pathnames oscar-pathname "oscar-graphics_4-02"))
                   (eval '(initialize-graphics))))
           (make-dialog-item
             'static-text-dialog-item  #@(6 314) #@(188 22)
             "---------------------------------------------")
           (make-dialog-item
             'check-box-dialog-item #@(6 325) #@(200 22)
             (cat "Enter package " *package-name*)
             (eval `#'(lambda (item) (declare (ignore item)) (in-package ,*package-name*)))
             :check-box-checked-p *trace*)
           )))

(defun b-display-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Display on"))
                (menu-item-enable (oscar-menu-item "Display off"))
                (setf *display?* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Display off"))
                (menu-item-enable (oscar-menu-item "Display on"))
                (check-box-uncheck *trace-button*)
                (trace-off)
                (setf *display?* nil *start-trace* nil *start-display* nil))))

(defun b-trace-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Trace on"))
                (menu-item-enable (oscar-menu-item "Trace off"))
                (check-box-check *display-button*)
                (display-on)
                (setf *trace* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Trace off"))
                (menu-item-enable (oscar-menu-item "Trace on"))
                (trace-off)
                (setf *trace* nil *start-trace* nil))))

(defun b-log-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Log on"))
                (menu-item-enable (oscar-menu-item "Log off"))
                (setf *log-on* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Log off"))
                (menu-item-enable (oscar-menu-item "Log on"))
                (trace-off)
                (setf *log-on* nil))))

(defun b-proof-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Proof on"))
                (menu-item-enable (oscar-menu-item "Proof off"))
                (setf *proofs?* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Proof off"))
                (menu-item-enable (oscar-menu-item "Proof on"))
                (trace-off)
                (setf *proofs?* nil))))

(defun b-logic-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Logic on"))
                (menu-item-enable (oscar-menu-item "Logic off"))
                (setf *use-logic* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Logic off"))
                (menu-item-enable (oscar-menu-item "Logic on"))
                (trace-off)
                (setf *use-logic* nil))))

(defun b-reductio-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Reductio on"))
                (menu-item-enable (oscar-menu-item "Reductio off"))
                (reductio-on))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Reductio off"))
                (menu-item-enable (oscar-menu-item "Reductio on"))
                (trace-off)
                (reductio-off))))

(defun b-deductive-only (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "All Reasoning"))
                (menu-item-enable (oscar-menu-item "Deductive only"))
                (setf *deductive-only* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Deductive only"))
                (menu-item-enable (oscar-menu-item "All Reasoning"))
                (trace-off)
                (setf *deductive-only* nil))))

(defun b-IQ-on (item)
    (cond ((check-box-checked-p item)
                (check-box-check item)
                (menu-item-disable (oscar-menu-item "Show inference-queue"))
                (menu-item-enable (oscar-menu-item "Do not show inference-queue"))
                (setf *display-inference-queue* t))
              (t
                (check-box-uncheck item)
                (menu-item-disable (oscar-menu-item "Do not show inference-queue"))
                (menu-item-enable (oscar-menu-item "Show inference-queue"))
                (trace-off)
                (setf *display-inference-queue* nil))))

(defunction oscar-menu-item (string)
    (let ((oscar-menu
              (find-if #'(lambda (item) (equal (menu-title item) *version*)) (menubar))))
       (find-if #'(lambda (item) (equal (menu-title item) string)) (menu-items oscar-menu))))

(defun m-display-on ()
    (menu-item-disable (oscar-menu-item "Display on"))
    (menu-item-enable (oscar-menu-item "Display off"))
    (setf *display?* t))

(defun m-display-off ()
    (menu-item-disable (oscar-menu-item "Display off"))
    (menu-item-enable (oscar-menu-item "Display on"))
    (menu-item-enable (oscar-menu-item "Display from"))
    (trace-off)
    (setf *display?* nil *start-trace* nil *start-display* nil))

(defun m-display-from (n)
    (display-off)
    (trace-off)
    (setf *start-trace* nil *start-display* n))

(defunction m-trace-on ()
    (menu-item-disable (oscar-menu-item "Trace on"))
    (menu-item-enable (oscar-menu-item "Trace off"))
    (display-on)
    (setf *trace* t))

(defunction m-trace-off ()
    (menu-item-enable (oscar-menu-item "Trace on"))
    (menu-item-disable (oscar-menu-item "Trace off"))
    (setf *trace* nil *start-trace* nil))

(defunction m-trace-from (n)
    (display-off)
    (trace-off)
    (setf *start-trace* n))

(defun m-log-on ()
    (menu-item-disable (oscar-menu-item "Log on"))
    (menu-item-enable (oscar-menu-item "Log off"))
    (setf *log-on* t))

(defun m-log-off ()
    (menu-item-disable (oscar-menu-item "Log off"))
    (menu-item-enable (oscar-menu-item "Log on"))
    (setf *log-on* nil))

(defun m-proof-on ()
    (menu-item-disable (oscar-menu-item "Proof on"))
    (menu-item-enable (oscar-menu-item "Proof off"))
    (setf *proofs?* t))

(defun m-proof-off ()
    (menu-item-disable (oscar-menu-item "Proof off"))
    (menu-item-enable (oscar-menu-item "Proof on"))
    (setf *proofs?* nil))

(defun m-logic-on ()
    (menu-item-disable (oscar-menu-item "Logic on"))
    (menu-item-enable (oscar-menu-item "Logic off"))
    (setf *use-logic* t)
    (reductio-on))

(defun m-logic-off ()
    (menu-item-disable (oscar-menu-item "Logic off"))
    (menu-item-enable (oscar-menu-item "Logic on"))
    (setf *use-logic* nil)
    (reductio-off))

(defun m-reductio-on ()
    (menu-item-disable (oscar-menu-item "Reductio on"))
    (menu-item-enable (oscar-menu-item "Reductio off"))
    (reductio-on))

(defun m-reductio-off ()
    (menu-item-disable (oscar-menu-item "Reductio off"))
    (menu-item-enable (oscar-menu-item "Reductio on"))
    (reductio-off))

(defun do-deductive-only ()
    (menu-item-disable (oscar-menu-item "Deductive only"))
    (menu-item-enable (oscar-menu-item "All Reasoning"))
    (setf *deductive-only* t)
    (logic-on))

(defun do-all-reasoning ()
    (menu-item-disable (oscar-menu-item "All Reasoning"))
    (menu-item-enable (oscar-menu-item "Deductive only"))
    (setf *deductive-only* nil))

(defun m-IQ-on ()
    (menu-item-disable (oscar-menu-item "Show inference-queue"))
    (menu-item-enable (oscar-menu-item "Do not show inference-queue"))
    (setf *display-inference-queue* t))

(defun m-IQ-off ()
    (menu-item-disable (oscar-menu-item "Do not show inference-queue"))
    (menu-item-enable (oscar-menu-item "Show inference-queue"))
    (setf *display-inference-queue* nil))

(defun display-package-options ()
    (let ((names
              (sort
                (set-difference
                  (mapcar #'package-name (list-all-packages))
                  (list "ansi-loop" "ccl" "common-lisp" "completion" "inspector" "keyword" "setf" "traps")
                  :test #'string-equal)
                #'string<))
            (items nil)
            (height 21))
       (dolist (name names)
           (push
             (list name height
                     `#'(lambda (item)
                            (declare (ignore item))
                            (in-package ,name)
                            (window-close (find-window "Choose package"))))
             items)
           (incf height 22))
       (make-instance 'dialog
            :window-type :tool
            :view-position #@(242 40)
            :view-size #@(217 416)
            :view-font '("Chicago" 12 :srcor :plain)
            :window-title "Choose package"
            :view-subviews
            (cons
              (make-dialog-item
                'static-text-dialog-item #@(5 3) #@(185 18) "Click on desired package:" 'nil)
              (mapcar
                #'(lambda (item)
                      (make-dialog-item
                        'check-box-dialog-item (make-point 6 (mem2 item)) #@(188 22)
                        (mem1 item) (eval (mem3 item))))
                items)))))

(progn
    (let* ((menubar (menubar))
              (tools-menu 
                (find-if #'(lambda (item) (equal (menu-title item) "Tools")) menubar)))
       (when
            (null (find-if #'(lambda (item) (equal (menu-title item) "Packages..."))
                                  (menu-items tools-menu)))
            (add-menu-items
              tools-menu
              (make-instance 'menu-item :menu-item-title "-" :disabled t)
              (make-instance 'menu-item
                   :menu-item-title "Packages..." :menu-item-action 'display-package-options)))
       (add-OSCAR-menu)
       ))

;;;; Macintosh Graphical User Interface for OSCAR
;;;; Real time display version .1
;;;; Artilects, LLC       DFH
;;; 
;;;; first need to set up window

;(when (null (find-package "OSCAR_3.5"))
;     (make-package "OSCAR_3.5"
;                                   :use '("COMMON-LISP-USER" "CCL" "COMMON-LISP")))
;(in-package "OSCAR_3.5")

(load "G4 HOME:APPLICATIONS (MAC OS 9):Programming:MCL 4.2:library:quickdraw.lisp")
(require :quickdraw)

(proclaim '(special  *move-to-be-made* *hypernode-to-be-moved* *hypernode-radius* *screen-height*
                     *screen-width* *start-sweep* *end-sweep* *start-i-sweep* *end-i-sweep*
                     *incf-sweep* *minimum-distance-between-nodes* *maximum-distance-between-nodes*
                     *last-hypernode-terminal* *last-interest-terminal* *open-position* *og*
                      *interest-graph* *mes* *speak* *top-line* *show-formulas* *msg*
                      *supposition-color* *undefeated-node-color* *interest-to-be-moved*
                      *defeated-node-color* *delay* *inspect-hypernode-dialog* *menu-dialog*
                      *graphics-initialized* *graphics-on* *graph-log* *nodes-to-be-moved*
                    *graphics-pause* *nodes-displayed* *nodes-to-graph* *graph-interests*
                    *interests-to-be-moved* *graph-arguments* *graph-hypernode-arguments*
                    *move-all-nodes* *move-all-interests* *guide-interest* *monochrome*
                    *flash-terminal-deductive-ancestors* *strongly-relevant-nodes* *nodes-done*
                    *terminal-deductive-ancestors* *region-start-position* *selection-region*
                    *line-color* *back-color* *show-motivators*))

; (use-package "SPEECH")
;(load (merge-pathnames oscar-pathname "SPEECH.LIS"))          
;(load (merge-pathnames oscar-pathname "SPEECH-M.LIS"))   

(defvar *show-formulas* t)
(defvar *show-motivators* nil)
(defvar *msg* nil)
(defvar *delay* 0)
(defvar *flash-affected-nodes* nil)
(defvar *flash-defeatees* nil)
(defvar *flash-defeaters* nil)
(defvar *flash-ancestors* nil)
(defvar *flash-consequences* nil)
(defvar *flash-hyperlink-bases* nil)
(defvar *flash-hyperlinks* nil)
(defvar *flash-relevant-nodes* nil)
(defvar *flash-terminal-deductive-ancestors* nil)
(defvar *graph-ancestors* nil)
(defvar *graph-relevant-nodes* nil)
(defvar *menu-dialog* nil)
(defvar *message* nil)
(defvar *nodes-to-graph* nil)
(defvar *graph-interests* nil)
(defvar *nodes-to-be-moved* nil)
(defvar *interests-to-be-moved* nil)
(defvar *graph-arguments* nil)
(defvar *graph-hypernode-arguments* nil)
(defvar *move-all-nodes* nil)
(defvar *move-all-interests* nil)
(defvar *guide-node* nil)
(defvar *guide-interest* nil)
(defvar *monochrome* nil)
(defvar *region-start-position* nil)
(defvar *selection-region* nil)
(defvar *line-color* *white-color*)
(defvar *back-color* *black-color*)


(defun speech-on () (setf *speak* t))
(defun speech-off () (setf *speak* nil))

(defun show-formulas () (setf *show-formulas* t))
(defun do-not-show-formulas () (setf *show-formulas* nil))

(defclass og-window (window)
  ((hypernode-list :initarg :hypernode-list :initform nil :accessor hypernode-list)
   (interest-list :initarg :interest-list :initform nil :accessor interest-list)
   (show-formulas-in :initarg :show-formulas-in :initform *show-formulas* :accessor show-formulas-in)
   (inf-graph :initform nil :accessor inf-graph)
   (int-graph :initform nil :accessor int-graph))
    (:default-initargs 
      :window-type :document-with-grow
      :window-title "OSCAR_3.0"
      :color-p t
      :window-do-first-click t))

(defun make-oscar-window ()
    (setf *nodes-displayed* nil)
    (when *og* (window-close *og*))
    (setf *og* (make-instance 'og-window 
                           :window-title "OSCAR -- Graph of Problem"
                           :view-position *open-position*
                           :view-size (make-point *screen-width* *screen-height*)))
    (set-part-color *og* :content *back-color*))

(defun flash-nodes (nodes view color times &optional message)
    (cond
      (nodes
        (dotimes (n times)
            (let ((colors (mapcar #'(lambda (node) (hypernode-color node view)) nodes)))
               (dolist (node nodes)
                   (draw-just-node (hypernode-position node view) view node color))
               (sleep .1)
               (mapc #'(lambda (node color)
                                 (draw-just-node (hypernode-position node view) view node color))
                            nodes colors)
               (sleep .1)))
       ; (invalidate-view view)
        )
      (message
        (let ((mes (make-top-message message)))
           (sleep 1)
           (window-close mes)))))

(defunction flash-node (number)
    (let ((node (node number)))
       (dotimes (n 5)
           (let ((color (hypernode-color node *og*)))
              (draw-just-node (hypernode-position node *og*) *og* node *yellow-color*)
              (sleep .1)
              (draw-just-node (hypernode-position node *og*) *og* node color)
              (sleep .1)))))

(defunction temporarily-color-nodes (nodes)
    (setf nodes (remove-if-not #'(lambda (x) (assoc x (hypernode-list *og*))) nodes))
    (dolist (node nodes)
        (draw-just-node (hypernode-position node *og*) *og* node *yellow-color*))
    (pause-graphics)
    (invalidate-view *og* t))

;(defmethod view-draw-contents ((wind og-window))
;    (dolist (pos (hypernode-list wind))
;        (when (not (hypernode-cancelled-node (car pos)))
;             (draw-node (cadr pos) wind (car pos))))
;    (dolist (i (interest-list wind))
;        (when (not (cancelled-interest (car i)))
;             (draw-interest (cdr i) wind (car i)))))

(defmethod view-draw-contents ((wind og-window))
    (dolist (pos (hypernode-list wind))
        (draw-node (cadr pos) wind (car pos)))
    (dolist (i (interest-list wind))
        (draw-interest (cdr i) wind (car i))))

(defun ontop (position1 position2)
    (< (length-line position1 position2) *hypernode-radius*))

;;;;;  Main problem with this port is that we must now keep track of everything drawn
;;;;; to window so that we can redraw using view-draw-contents.  Only things to be
;;;;; drawn to window are NODES and hyperlinkS.  The display of a node will
;;;;; automatically draw in support links, e.g. when a node is drawn, so is its support
;;;;; links, so for the present, only NODE positions will be kept track of.  Only nodes
;;;;; will be clickable for now, just as in the old version.  

;;;;; hypernode positions will be stored in list of dotted pairs, (node number . position),
;;;;; which is the hypernode-list of *og*, the window in which the problem is being graphed

;;;; DRAW-NODE == takes position, view, text and number as arguments

(defun draw-node (position view node)
    (draw-just-node position view node (hypernode-color node view))
    (draw-hyperlinks position view node)
    (attach-discharged-interests position view node)
    (draw-arrows-to-generated-direct-reductio-interests position view node)
    (attach-arrows-to-defeated-nodes position view node)
    (if *show-motivators* (draw-arrows-from-motivating-nodes position view node))
    )

(defunction hypernode-color (node view)
    (mem2 (e-assoc node (hypernode-list view))))

(defunction hypernode-position (node view)
    (mem1 (e-assoc node (hypernode-list view))))

(defunction attach-discharged-interests (position view node)
    (when (hypernode-discharged-interests node)
         (dolist (int (mapcar #'car (hypernode-discharged-interests node)))
             (when (interest-p int)
                  (let ((posi (interest-position int view)))
                     (when posi 
                          (when (not *monochrome*) (set-fore-color view *purple-color*))
                          (draw-arrow position posi view)
                          (when (not *monochrome*) (set-fore-color view *black-color*))))))))

(defunction draw-arrows-to-generated-direct-reductio-interests (position view node)
    (when (generated-direct-reductio-interests node)
         (dolist (int (generated-direct-reductio-interests node))
             (let ((posi (interest-position int view)))
                (when posi 
                     (set-fore-color view *orange-color*)
                     (draw-arrow position posi view)
                     (set-fore-color view *black-color*))))))

(defunction attach-arrows-to-defeated-nodes (position view node)
    (let ((targets nil))
       (dolist (slink (hypernode-defeatees node))
           (push (hyperlink-target slink) targets))
       (setf targets (remove-duplicates targets))
       (dolist (target targets)
           (let ((pos-target (hypernode-position target view)))
              (when pos-target
                   (draw-defeat-arrow position pos-target view))))))

(defunction draw-arrows-from-motivating-nodes (position view node)
    (dolist (target (hypernode-motivating-nodes node))
        (let ((pos-target (hypernode-position target view)))
           (when pos-target
                (cond (*monochrome* (set-fore-color view *light-gray-color*))
                            (t (set-fore-color view *yellow-color*)))
                (set-pen-size view #@(4 4))
                (draw-arrow pos-target position view)
                (set-fore-color view *black-color*)
                (set-pen-size view #@(1 1))))))

(defunction draw-hyperlinks (position view node)
   ; (when (eq node (node 146)) (setf p position v view n node) (break))
    ;; (step (draw-hyperlinks p v n))
    (dolist (sl (hypernode-hyperlinks node))
        (when (hyperlink-defeasible? sl) (set-fore-color view *gray-color*))
        (dolist (nb (hyperlink-basis sl))
            (let ((pos-nb (hypernode-position nb view)))
               (when pos-nb 
                    (draw-arrow pos-nb position view))))))

(defun draw-undefeated-node (position view node)
    (draw-just-undefeated-node position view node)
    (draw-hyperlinks position view node)
    (attach-discharged-interests position view node)
   ; (draw-arrows-to-generated-direct-reductio-interests position view node)
    (attach-arrows-to-defeated-nodes position view node))

#| The hypernode-list is a list of triples (list node position color). |#
(defun draw-just-node (position view node color)
    ; (setf p position v view n node c color)
    (pull (assoc node (hypernode-list view)) (hypernode-list view))
    (push (list node position color) (hypernode-list view))
    ;;; draw the node itself
    (let* ((x (point-h position))
              (y (point-v position))
              (left (- x *hypernode-radius*))
              (top (- y *hypernode-radius*))
              (right (+ x *hypernode-radius*))
              (bottom (+ y *hypernode-radius*)))
       ;; clear the space
       (erase-oval view left top right bottom)
       ;;  fill it with appropriate color
       (cond (*monochrome*
                    (if (eql (undefeated-degree-of-support node) 0.0)
                       (set-fore-color view *light-gray-color*)))
                   (t (set-fore-color view color)))
       (when (or (not *monochrome*) (eql (undefeated-degree-of-support node) 0.0))
            (paint-oval view left top right bottom))
       (set-fore-color view *black-color*)
       ;; frame it
       (cond
         ((equal view (find-window "Affected-nodes"))
           (cond ((not (member node *affected-nodes*))
                        (set-pen-size view #@(3 3)) (set-fore-color view *brown-color*)
                        (frame-oval view left top right bottom)
                        (set-pen-size view #@(1 1)) (set-fore-color view *line-color*))
                       ((hypernode-answered-queries node)
                         (set-pen-size view #@(3 3)) (set-fore-color view *red-color*)
                         (frame-oval view left top right bottom)
                         (set-pen-size view #@(1 1)) (set-fore-color view *line-color*))
                       (t (frame-oval view left top right bottom))))
         ((hypernode-answered-queries node)
           (set-pen-size view #@(3 3))
           (when (not *monochrome*) (set-fore-color view *red-color*))
           (frame-oval view left top right bottom)
           (set-pen-size view #@(1 1)) (set-fore-color view *line-color*))
         (t (frame-oval view left top right bottom)))
       ;;write text
       (cond
         ((< (hypernode-number node) 10)
           (move-to view (- x 2) (+ y 3)))
         ((< (hypernode-number node) 100)
           (move-to view (- x 5) (+ y 3)))
         (t (move-to view (- x 8) (+ y 3))))
       (set-fore-color view *black-color*)
       (princ (hypernode-number node) view)
       (set-fore-color view *line-color*)
       (when (or *show-formulas* (show-formulas-in view))
            (move-to view (+ x *hypernode-radius* 3) (+ y 3))
            (show-formula node x y view))))

(defunction show-formula (node x y view)
    (let* ((formula
               (cond
                 ((equal (hypernode-kind node) "percept")
                   (cat "It appears to me that " (pretty (hypernode-formula node))))
                 (t (pretty (hypernode-formula node))))))
       (princ formula view))
    (when (hypernode-supposition node)
       (move-to view (+ x *hypernode-radius* 3) (+ y 13))
       (princ
         (cat-list
           (cons " given " (commatize (mapcar #'pretty (hypernode-supposition node))))) view)))

(defunction draw-just-undefeated-node  (position view node)
    (draw-just-node
      position view node
      (cond ((hypernode-supposition node) *supposition-color*)
                  ((is-percept node) *yellow-color*)
                  (t *undefeated-node-color*)))
    (draw-hyperlinks position view node)
    (attach-discharged-interests position view node)
    (draw-arrows-to-generated-direct-reductio-interests position view node)
    (attach-arrows-to-defeated-nodes position view node)
    (if *show-motivators* (draw-arrows-from-motivating-nodes position view node)))

(defunction draw-just-defeated-node  (position view node)
    (draw-just-node
      position view node
      (if (hypernode-supposition node) *light-blue-color* *defeated-node-color*))
    (draw-hyperlinks position view node)
    (attach-discharged-interests position view node)
    (draw-arrows-to-generated-direct-reductio-interests position view node)
    (attach-arrows-to-defeated-nodes position view node)
    (if *show-motivators* (draw-arrows-from-motivating-nodes position view node)))

(defunction draw-n (node view &optional nodes-displayed)
    (cond
      ((member node nodes-displayed)
        (let ((pos (hypernode-position node view)))
           (draw-hyperlinks pos view node)
           (attach-discharged-interests pos view node)
           (draw-arrows-to-generated-direct-reductio-interests pos view node)
           (attach-arrows-to-defeated-nodes pos view node)
           (if *show-motivators* (draw-arrows-from-motivating-nodes pos view node))))
      (t
        (let* ((pos (find-position-for-node node view nodes-displayed)))
           ; (pos 
           ;   (if pos1 
           ;      (if (or *show-formulas* (show-formulas-in view))
           ;         (adjust-again (adjust-for-text pos1)) pos1) nil)))
           (when pos
                (draw-undefeated-node pos view node)))))
    (announce-node node))

(defunction announce-node (node)
    (when (and (boundp '*speak*) *speak*)
         (sleep .5)
         (cond
           ((equal (hypernode-justification node) :given)
             (speak-text
               (cat "I am given that "
                       (pranc-to-string (pretty (hypernode-formula node))))))
           ((equal (hypernode-kind node) :percept)
             (speak-text
               (cat-list (list "It appears to me that "
                                     (pranc-to-string (pretty (hypernode-formula node)))
                                     " by perceptual input"))))
           ((equal (hypernode-justification node) :supposition)
             (speak-text
               (cat "Let us suppose that "
                       (pranc-to-string (pretty (hypernode-formula node))))))
           ((equal (hypernode-justification node) :reductio-supposition)
             (speak-text
               (cat "Let us suppose that "
                       (pranc-to-string (pretty (hypernode-formula node))))))
           ((some #'(lambda (L) (null (hyperlink-basis L))) (hypernode-hyperlinks node))
             (speak-text
               (cat "It is true a priori that "
                       (pranc-to-string (pretty (hypernode-formula node))))))
           (t (let
                 ((msg
                    (list 
                      (if (some #'hyperlink-defeasible? (hypernode-hyperlinks node))
                         "It follows defeasibly that "
                         "It follows that ")
                      (pranc-to-string (pretty (hypernode-formula node))))))
                 (when (hypernode-supposition node)
                      (setf msg
                               (append
                                 msg
                                 (list
                                   "given the supposition that"
                                   (pranc-to-string (pretty (gen-conjunction (hypernode-supposition node))))))))
                 (speak-text (cat-list msg)))
               ; (dolist (x (hypernode-hyperlinks node))
               ;     (when (or (null *nodes-displayed*) (subsetp (hyperlink-basis x) *nodes-displayed*))
               ;          (speak-text (cat "by " (pranc-to-string (princ-to-string (hyperlink-rule x)))))))
               ))))

;;;;  DRAWING ROUTINES FOR INTERESTS


(defun draw-i (interest view)
    (let ((pos (find-position-for-interest interest view)))
       (cond
         (pos
           (draw-interest pos view interest)
           (push (cons interest pos) (interest-list view)))
         (t nil)))
    (announce-interest interest))

(defunction announce-interest (interest)
    (when (and (boundp '*speak*) *speak*)
         (sleep .5)
         (speak-text (cat "I adopt interest "  (princ-to-string (interest-number interest))))
         (speak-text (pranc-to-string (pretty (interest-formula interest))))
         (cond
           ((interest-defeatees interest)
             (speak-text (cat "because it is a potential defeater for support links of node " 
                                          (princ-to-string
                                            (mapcar #'hypernode-number
                                                           (mapcar #'hyperlink-target (interest-defeatees interest)))))))
           (t nil))))

(defunction interest-position (interest view)
    (e-assoc interest (interest-list view)))

(defun draw-interest (position view node)
   ; (setf p position v view n node)
    ;; (step (draw-interest p v n))
    (draw-just-interest position view node)
    ;; draw arrows
    (dolist (drl (right-links node))
        (let* ((int (resultant-interest drl))
                  (pos (if (interest-p int) (interest-position int  view))))
           (if pos (draw-arrow  pos position view))))
    ;;;  draw arrows to generated suppositions
    (dolist (nod (generated-suppositions node))
        (let ((posi (hypernode-position nod view)))
           (when posi 
                (when (not *monochrome*) (set-fore-color view *blue-color*))
                (draw-arrow position posi view)
                (set-fore-color view *line-color*))))
    ;;; draw arrows to generating nodes ;; orange if reductio interest
   ; (dolist (nod (mapcar #'hyperlink-target (interest-defeatees node)))
   ;     (let ((posi (hypernode-position nod view)))
   ;        (when posi
   ;             (set-fore-color view (if (reductio-interest node) *orange-color* *yellow-color*))
   ;             (draw-arrow posi position view)
   ;             (set-fore-color view *line-color*))))
    )

(defun draw-just-interest (position view node)
    ;;; draw the node itself
    (let* ((x (point-h position))
              (y (point-v position))
              (left (- x *hypernode-radius*))
              (top (- y *hypernode-radius*))
              (right (+ x *hypernode-radius*))
              (bottom (+ y *hypernode-radius*))
              (wincolor
                (if (some #'(lambda (L) (equal (link-rule L) "answer")) (right-links node))
                   3538753 9405695)))
       ;; clear the space
       (erase-oval view left top right bottom)
       (when (not *monochrome*)
            ;;  fill it with appropriate color
            (set-fore-color view wincolor)
            (paint-oval view left top right bottom)
            (set-fore-color view *line-color*))
       ;; frame it and write text
       (frame-oval view left top right bottom)
       (cond
         ((< (interest-number node) 10)
           (move-to view (- x 2) (+ y 3)))
         ((< (interest-number node) 100)
           (move-to view (- x 5) (+ y 3)))
         (t (move-to view (- x 8) (+ y 3))))
       (set-fore-color view *black-color*)
       (princ (interest-number node) view)
       (set-fore-color view *line-color*)
       (when (or *show-formulas* (show-formulas-in view))
            (move-to view (+ x *hypernode-radius* 3) (+ y 3))
            (show-i-formula node x y view))))

(defunction show-i-formula (interest x y view)
    (princ (pretty (interest-formula interest)) view)
    (when (interest-supposition interest)
       (move-to view (+ x *hypernode-radius* 3) (+ y 13))
       (princ
         (cat-list
           (cons " given " (commatize (mapcar #'pretty (interest-supposition interest))))) view)))

(defunction find-position-for-interest (int view)
  ;  (setf i int v view) (break)
    ;; (step (find-position-for-interest i v))
    ;;; if it has been drawn already, return nil (for now)
    (cond
      ((assoc int (interest-list view)) nil)
      ;;;; if it has no support links, or it is a query interest, figure out where to put it
      ;;;; using a slide along the bottom algorithm
      ((or (null (right-links int))
              (some #'(lambda (L) (equal (link-rule L) "answer")) (right-links int)))
        (let* ((condition
                   (< (point-h *last-interest-terminal*)
                        (- *screen-width*  *minimum-distance-between-nodes*)))
                  (h-pos (if condition
                                 (+ (point-h *last-interest-terminal*) *minimum-distance-between-nodes*)
                                 (round (/ *screen-width* 2))))
                  (v-pos (if condition
                                 (point-v *last-interest-terminal*)
                                 (- (point-v *last-interest-terminal*) *minimum-distance-between-nodes*))))
           (loop 
              (if (good-position h-pos v-pos view) (return (make-point h-pos v-pos)))
              (cond ((< h-pos (- *screen-width*  *minimum-distance-between-nodes*))
                           (setf h-pos (+ h-pos *minimum-distance-between-nodes*)))
                          (t
                            (setf h-pos (round (/ *screen-width* 100)))
                            (setf v-pos (- v-pos *minimum-distance-between-nodes*)))))))
      ;;;; if it has hyperlinks, then figure it out by the position of its support links
      (t  
        (let* ((sweep *start-i-sweep*)
                  (longth *minimum-distance-between-nodes*)
                  (suppos
                    (if (right-links int)
                       (interest-position (resultant-interest (first (last (right-links int)))) view)))
                  (h (if suppos (adjusted-h-position (point-h suppos) int) 50))
                  (v (if suppos (i-adjusted-v-position (point-v suppos) int) 450))
                  (h-pos (+ h (round (* longth  (cosd sweep)))))
                  (v-pos (- v (round (* longth  (sind sweep))))))
           (loop           
              (if (good-position h-pos v-pos view) (return (make-point h-pos v-pos)))
              (cond ((<= sweep *end-i-sweep*) 
                           (setf sweep *start-i-sweep*) 
                           (setf longth (+ longth 10))
                           (setf h-pos (+ h (round (* longth  (cosd sweep)))))
                           (setf v-pos (- v (round (* longth  (sind sweep))))))
                          (t (setf sweep (- sweep 30))
                              (setf h-pos (+ h (round (* longth  (cosd sweep)))))
                              (setf v-pos (- v (round (* longth  (sind sweep))))))))))))

(defunction i-adjusted-v-position (x int)
    (- x (expt (rem (+ 2 (interest-number int)) 5) 2)))

;;;;  ;; FIND-POSITION-FOR-NODE  This function finds a place for the new node, inserts it into
;;;; ;  the list of positions, and calls view-draw-contents to make sure that the entire
;;;;;   window is updated.

;;;; first some basic geometry  --  degrees to radians

(defun dtr (degrees)
    (/ degrees 57.2))

(defun sind (degrees)
    (sin (dtr degrees)))

(defun cosd (degrees)
    (cos (dtr degrees)))
    
(defunction find-position-for-node (node view &optional nodes-displayed)
   ; (setf n node v view nd nodes-displayed)
    ;; (step (find-position-for-node n v nd))
    ;;; if it has been drawn already, return nil (for now)
    (cond
      ((assoc node (hypernode-list view)) nil)
      ;;;; if it has no support links, figure out where to put it using a slide along the top algorithm
      ((or (null (hypernode-hyperlinks node)) (null nodes-displayed)
              (every
                #'(lambda (L)
                      (or (null (hyperlink-basis L))
                            (not (subsetp (hyperlink-basis L) nodes-displayed))))
                (hypernode-hyperlinks node)))
        (let* ((condition
                   (< (point-h *last-hypernode-terminal*) 
                        (- *screen-width*  *minimum-distance-between-nodes*)))
                  (h-pos (if condition
                                 (+ (point-h *last-hypernode-terminal*) *minimum-distance-between-nodes*)
                                 (round (/ *screen-width* 100))))
                  (v-pos (if condition
                                 (point-v *last-hypernode-terminal*)
                                 (+ (point-v *last-hypernode-terminal*) *minimum-distance-between-nodes*))))
           (loop 
              (if (good-position h-pos v-pos view) (return (make-point h-pos v-pos)))
              (cond ((< h-pos (- *screen-width*  *minimum-distance-between-nodes*))
                           (setf h-pos (+ h-pos *minimum-distance-between-nodes*)))
                          (t
                            (setf h-pos (round (/ *screen-width* 100)))
                            (setf v-pos (+ v-pos *minimum-distance-between-nodes*)))))))
      ;;;; if it has hyperlinks, then figure it out by the position of its support links
      (t  
        (let* ((sweep *start-sweep*)
                  (longth *minimum-distance-between-nodes*)
                  (suppos (hypernode-position (first (hyperlink-basis (first (last (hypernode-hyperlinks node))))) view))
                  (h (adjusted-h-position (point-h suppos) node))
                  (v (adjusted-v-position (point-v suppos) node))
                  (h-pos (+ h (round (* longth  (cosd sweep)))))
                  (v-pos (- v (round (* longth  (sind sweep))))))
           (loop           
              (if (good-position h-pos v-pos view) (return (make-point h-pos v-pos)))
              (cond ((>= sweep *end-sweep*) 
                           (setf sweep *start-sweep*) 
                           (setf longth (+ longth 10))
                           (setf h-pos (+ h (round (* longth  (cosd sweep)))))
                           (setf v-pos (- v (round (* longth  (sind sweep))))))
                          (t (setf sweep (+ sweep 30))
                              (setf h-pos (+ h (round (* longth  (cosd sweep)))))
                              (setf v-pos (- v (round (* longth  (sind sweep))))))))))))

(defunction adjusted-h-position (x node)
    (+ x (expt (rem (hypernode-number node) 5) 2)))

(defunction adjusted-v-position (x node)
    (+ x (expt (rem (+ 2 (hypernode-number node)) 5) 2)))

;;;  GOODPOSITION -- This function simply checks to make sure that the position
;;; isn't on top of anything in the hypernode-list and that it is within the bounds of the screen

(defunction good-position (h-pos v-pos view)
    (and (>= h-pos *hypernode-radius*) (> v-pos 15)
               (<= v-pos (- *screen-height* *hypernode-radius*))
                (<= h-pos (- *screen-width* *hypernode-radius*))
               (every #'(lambda (item) (away-from h-pos v-pos (cadr item))) (hypernode-list view))
               (every #'(lambda (item) (away-from h-pos v-pos (cdr item))) (interest-list view))))

(defunction away-from (h-pos v-pos place)
    (let* ((h-diff (- h-pos (point-h place)))
              (v-diff (- v-pos (point-v place)))
              (distance (sqrt (+ (expt h-diff 2) (expt v-diff 2)))))
       (< (- *minimum-distance-between-nodes* 5) distance)))

(defun length-line (position1 position2)
    (let ((diffvector (subtract-points position1 position2)))
       (sqrt (+ (expt (point-h diffvector) 2) (expt (point-v diffvector) 2)))))

;;; a little trigonometry

(defun point-to-line (end1 end2 point1)   
    (let* ((a (length-line point1 end1))
              (b (length-line point1 end2))
              (c (length-line end1 end2))
              (s (/ (+ a b c) 2))
              (sina (/ (* 2 (sqrt (* s (- s a) (- s b) (- s c)))) (* b c))))
       (* sina b)))


;;;  this takes a position, scans to see if any nodes are to the left of it, and
;;;  moves it up or down appropriately

(defun adjust-for-text (pos)
    (let ((left-side (- (point-h pos) (* 1 *minimum-distance-between-nodes*)))
            (top-side (- (point-v pos) (round (* .5 *hypernode-radius*))))
            (right-side (point-h pos))
            (bottom-side (+ (point-v pos) (round (* .5 *hypernode-radius*))))
            (violator nil))
       (if (some #'(lambda (p)
                              (setf violator (cadr p))
                              (point-in-box left-side top-side right-side bottom-side (cadr p)))
                        (hypernode-list *og*))
          (cond ((< (point-v pos) 20) (make-point (point-h pos) (+ (point-v pos) (* 2 *hypernode-radius*))))
                      (t (make-point (point-h pos) (+ (point-v pos) (round (* 1.2 *hypernode-radius*))))))
          pos)))

(defun adjust-for-text-i (pos)
    (let ((left-side (- (point-h pos) (* 1 *minimum-distance-between-nodes*)))
            (top-side (- (point-v pos) (round (* .5 *hypernode-radius*))))
            (right-side (point-h pos))
            (bottom-side (+ (point-v pos) (round (* .5 *hypernode-radius*))))
            (violator nil))
       (if (some #'(lambda (p) (setf violator (cdr p))
                             (point-in-box left-side top-side right-side bottom-side (cdr p))) 
                        (interest-list *og*))
          (cond ((< (point-v pos) 20) (make-point (point-h pos) (- (point-v pos) (* 2 *hypernode-radius*))))
                      ((< (point-v pos) (point-v violator)) (make-point (point-h pos) (+ (point-v pos) (* 1 *hypernode-radius*))))
                      (t (make-point (point-h pos) (- (point-v pos) (round (* 1.5 *hypernode-radius*))))))
          pos)))


(defun point-in-box (left top right bottom point)
    (let ((h (point-h point))
            (v (point-v point)))
       (and 
         (<= h right) (>= h left) (>= v top) (<= v bottom))))

;;;; now a function that returns t if the hypothetical position for a node will not result in drawing
;;;; lines through any other nodes

(defun draw-arrow (position1 position2 view)
    (let* ((lbn (length-line position1 position2))
              (xpos (round (/ (* *hypernode-radius* (- (point-h position2) (point-h position1))) lbn)))
              (ypos (round (/ (* *hypernode-radius* (- (point-v position2) (point-v position1))) lbn)))
              (l (sqrt (+ (expt xpos 2) (expt ypos 2))))
              (destpos (make-point (- (point-h position2) xpos) (- (point-v position2) ypos)))
              (angle-off (+ (acos (/ (* (if (< (point-v position2) (point-v position1)) 1 -1) xpos) l))
                                     (if (< (point-v position2) (point-v position1)) (dtr 180) 0)))
              (point-low (make-point (+ (point-h destpos) (round (* l .5 (cos (- angle-off (dtr 30))))))
                                                        (- (point-v destpos) (round (* l  .5 (sin (- angle-off (dtr 30))))))))
              (point-high (make-point (+ (point-h destpos) (round (* l  .5 (cos (+ angle-off (dtr 30))))))
                                                        (- (point-v destpos) (round (* l  .5 (sin (+ angle-off (dtr 30)))))))))
       (move-to view position1)
       (move view xpos ypos)
       (line-to view destpos)
       (line-to view point-low)
       (move-to view destpos)
       (line-to view point-high)))   

(defun draw-defeat-arrow (position1 position2 view)
     (let ((pp (pen-size view)))
        (cond (*monochrome*
                     (set-fore-color view *light-gray-color*)
                     (set-pen-size view #@(3 3)))
                    (t (set-fore-color view *red-color*)))
       (draw-arrow position1 position2 view)
       (set-fore-color view *line-color*)
       (set-pen-size view pp)))

(defun pranc-to-string (astring)
     (let* ((lstr (read-from-string (concatenate 'string "("  astring ")")))
                 (nstr
                   (sublis
                     '((~ . not) (v . or) (-> . implies) (<-> . "if and only if")
                        (@ "does not guarantee that ")
                        (x0 "a person")  ;; temporary
                        (disj-simp "disjunctive simplification") (modus-ponens1 "modus ponens")
                        (modus-tollens1 "modus tollens") (modus-tollens2 "modus tollens")
                        (i-neg-condit "introduction of negated conditional")
                        (neg-condit "conditional negation")
                        (i-neg-disj "introduction of negated disjunction")
                        (neg-disj "disjunction negation")
                        (disj-cond-2 "transformation of conditionals to disjunctions")
                        (UI "universal instantiation")
                        (EI "existential instantiation")
                        (UG "universal generalization")
                        (EG "existential generalization")
                        (i-DM "DeMorgan's laws")
                        (DM "DeMorgan's laws")
                        (modus-ponens1 "modus ponens")
                        (modus-ponens2 "modus ponens")
                        (*perception* "perception")
                        (*indexical-perception* "indexical-perception")
                        (*indexical-perceptual-reliability* "indexical-perceptual-reliability")
                        (*perceptual-reliability* "perceptual-reliability")
                        (*perception-update-from-competing-percept* "perception-update-from-competing-percept")
                        (*defeat-for-perception-update-from-competing-percept*
                          "defeat-for-perception-update-from-competing-percept")
                        (*temporal-projection* "temporal-projection")
                        (*causal-undercutter+* "causal-undercutter")
                        (*causal-undercutter* "causal-undercutter")
                        (*causal-implication* "causal-implication")
                        (strict-arithmetical-inequality "arithmetic")
                        (arithmetical-inequality "arithmetic")
                        (Tucson "Two son")
                        (Maria "Ma riia")
                        ) lstr)))
        (princ-to-string nstr)))

(defun graph-problem (&key full)
    (if *og* (window-close *og*))
    (setf *og* (make-instance 'og-window 
                           :window-title "OSCAR -- Graph of Problem"
                           :view-position *open-position*
                           :view-size (make-point *screen-width* *screen-height* )))
    (set-part-color *og* :content *back-color*)
  ;  (set-back-color *og* *back-color*)
    ;;;; set up somewhat simplified version of interest graph, for display purposes will skip display
    ;;;; of interests with different suppositions but same formulas
    ;;;; announce problem
    (when (and (boundp '*speak*) *speak*)
         (speak-text "I am Oscar.")
         (cond
           (*msg* (speak-text *msg*))
           ((boundp '*problem-number*)
             (speak-text (cat "I will now solve problem number " (princ-to-string *problem-number*)))
             (if (or *forwards-substantive-reasons* *backwards-substantive-reasons*)
                (speak-text " using both logic and the substantive reasons provided to me...")
                (speak-text " using logic..."))))
         (sleep 1))
    ;;;;;  draw stuff
    (let ((nodes nil))
       (dolist (query *ultimate-epistemic-interests*)
           (dolist (N (query-answers query)) (pushnew N nodes)))
       (let* ((proof-nodes (if full nil *relevant-nodes*))
                 (ultimate-interests (mapcar #'query-interest *ultimate-epistemic-interests*))
                 (enabling-interests
                   (unionmapcar+ #'hypernode-enabling-interests proof-nodes))
                 (closure (generated-nodes-and-interests
                                  proof-nodes (union ultimate-interests enabling-interests) ultimate-interests))
                 (nodes-used (mem1 closure))
                 (interests-used (mem2 closure))
                 (reasoning-log nil)
                 (nodes-displayed nil))
          (if full
             (setf reasoning-log (reverse *reasoning-log*))
             (dolist (x *reasoning-log*)
                 (cond
                   ((hypernode-p x) (if (member x nodes-used) (push x reasoning-log)))
                   ((interest-p x) (if (member x interests-used) (push x reasoning-log)))
                   (t (push x reasoning-log)))))
          (let ((last-entry nil))
             (dolist (x reasoning-log)
                 (if (and (boundp '*speak*) *speak*) (sleep 1) (sleep *delay*))
                 (cond
                   ((hypernode-p x) (draw-n x *og* nodes-displayed)
                     (push x nodes-displayed) (setf last-entry x))
                   ((interest-p x) (if *graph-interests* (draw-i x *og*)) (setf last-entry x))
                   ((listp x)
                     ;;; recolor node / will blink in event that stays same color               
                     (cond ((and (equal (mem1 x) :increased-support)
                                           (or full (member (mem2 x) nodes-used)))
                                  (let* ((nod (mem2 x))
                                            (posi (hypernode-position nod *og*)))
                                     (when posi
                                          (draw-just-undefeated-node posi *og* nod)))
                                  (when (and (boundp '*speak*) *speak*)
                                       (speak-text "The undefeeted-degree-of-support of node ")
                                       (speak-text (write-to-string (hypernode-number (mem2 x))))
                                       (speak-text "has increased to")
                                       (speak-text (write-to-string (undefeated-degree-of-support (mem2 x))))))
                                 ((and (equal (mem1 x) :defeated) (or full (member (mem2 x) nodes-used)))
                                   ;; recolor node
                                   (let* ((nod (mem2 x))
                                             (posi (hypernode-position nod *og*)))
                                      (when posi
                                           (draw-just-defeated-node posi *og* nod)))
                                   (when (and (boundp '*speak*) *speak*)
                                        (speak-text "Node ")
                                        (speak-text (write-to-string (hypernode-number (mem2 x))))
                                        (if (equal (mem2 x) last-entry)
                                           (speak-text "is defeated.")
                                           (speak-text "has become defeated."))))
                                 ((and (equal (mem1 x) :decreased-support) (or full (member (mem2 x) nodes-used)))
                                   (when (and (boundp '*speak*) *speak*)
                                        (speak-text "The undefeeted-degree-of-support of node ")
                                        (speak-text (write-to-string (hypernode-number (mem2 x))))
                                        (speak-text "has decreased to")
                                        (speak-text (write-to-string (undefeated-degree-of-support (mem2 x))))))
                                 ((and (equal (mem1 x) :answer-query) (or full (member (mem2 x) nodes-used)))
                                   (when (and (boundp '*speak*) *speak*)
                                        (speak-text "Node ")
                                        (speak-text (write-to-string (hypernode-number (mem2 x))))
                                        (speak-text "answers query ")
                                        (speak-text (write-to-string (query-number (mem3 x))))))
                                 )))))
          (when (and (boundp '*speak*) *speak*)
               (setf nodes
                        (subset
                          #'(lambda (n) 
                                (some #'(lambda (q) (>= (undefeated-degree-of-support n) (query-strength q)))
                                             (hypernode-answered-queries n)))
                          nodes))
               (when nodes
                    (speak-text
                      (cond
                        ((cdr nodes)
                          (cat-list
                            (list "In conclusion, " (pranc-to-string (princ-to-string (hypernode-formula (car nodes))))
                                    (mapcar #'(lambda (n) (cat ", " (pranc-to-string (princ-to-string (hypernode-formula n)))))
                                                    (cdr nodes)))))
                        (t (cat "In conclusion, " (pranc-to-string (princ-to-string (hypernode-formula (car nodes))))))))))
          (invalidate-view *og*))))

(defunction adjust-again (pos)
    (make-point (point-h pos)
                           (+ (point-v pos) (round (/ (* (point-h pos) .3 *hypernode-radius*)
                                                                        *minimum-distance-between-nodes*)))))

(defunction adjust-again-i (pos)
    (make-point (point-h pos)
                           (- (point-v pos) (round (/ (* (point-h pos) .3 *hypernode-radius*)
                                                                       *minimum-distance-between-nodes*)))))

(defunction graph-nodes (nodes window &optional (title"OSCAR -- Graph of Nodes" ) show-formulas)
    (let ((wind (find-window title)))
       (when wind (window-close wind)))
    (let ((view (make-instance 'og-window 
                            :window-title title
                            :view-position *open-position*
                            :view-size (make-point *screen-width* *screen-height*)
                            :show-formulas-in show-formulas)))
       (set-part-color view :content *back-color*)
       (setf (hypernode-list view) (subset #'(lambda (x) (member (car x) nodes)) (hypernode-list window)))
       (invalidate-view view)))

(defunction graph-affected-nodes (view)
    (graph-nodes
      (union *affected-nodes*
                           (unionmapcar+
                             #'(lambda (N) (unionmapcar+ #'hyperlink-basis (hypernode-hyperlinks N)))
                             *affected-nodes*))
      view)
    "Affected-nodes")

 #| Nodes can be a single node or a list of nodes. |#
(defunction graph-ancestors (nodes view)
    (when (not (listp nodes)) (setf nodes (list nodes)))
    (graph-nodes
      (union nodes (unionmapcar+ #'hypernode-ancestors nodes))
      view
      (cat-list 
        (append (list "hypernode-ancestors for node" (if (cdr nodes) "s " " "))
                         (commatize
                           (mapcar #'(lambda (n) (write-to-string (hypernode-number n))) nodes))))))

 #| Nodes can be a single node or a list of nodes.  If nodes is empty, nodes relevant
to all query-answers are graphed. |#
(defunction graph-relevant-nodes (view &optional nodes)
    (when (null nodes)
         (dolist (query *ultimate-epistemic-interests*)
             (dolist (N (query-answers query))
                 (pushnew N nodes))))
    (when (not (listp nodes)) (setf nodes (list nodes)))
    (let ((rn *relevant-nodes*))
       (compute-relevant-nodes nodes)
       (graph-nodes
         *relevant-nodes* view
         (cat-list 
           (append (list "Nodes relevant to node" (if (cdr nodes) "s " " "))
                            (commatize
                              (mapcar #'(lambda (n) (write-to-string (hypernode-number n))) nodes)))))
       (setf *relevant-nodes* rn))
    nil)

#| Insert commas between the members of the list strings |#
(defunction commatize (strings)
    (let ((new-strings (list (car strings))))
       (loop
          (setf strings (cdr strings))
          (when (null strings) (return (reverse new-strings)))
          (push " , " new-strings)
          (push (car strings) new-strings))))

(defun initialize-graphics ()
    (setf *move-to-be-made* nil)
    (setf *msg* nil)
    (setf *inspect-hypernode-dialog* nil)
    (setf *hypernode-to-be-moved* nil)
    (setf *hypernode-radius* 10)
    (setf *start-sweep* 210)
    (setf *end-sweep* 330)
    (setf *show-formulas* nil)
    (setf *start-i-sweep* 120)
    (setf *end-i-sweep* 30)
    (setf *incf-sweep* 10)
    (setf *minimum-distance-between-nodes* 40)
    (setf *maximum-distance-between-nodes* 600)
    (setf *last-hypernode-terminal* (make-point -20 20))
    (setf *top-line* 20)
    (setf *last-interest-terminal* (make-point -20 (- *screen-height* 15)))
    (setf *open-position* #@(100 100))
    (setf *supposition-color* 16716008)
    (setf *undefeated-node-color* 16732939)
    (setf *defeated-node-color* 16750228)
    (size-OSCAR-graphics-window)
    (setf *graphics-initialized* t)
    (setf *graphics-on* nil)
    (add-graphics-menu-items)
    (add-nodes-menu)
    )

(defunction size-OSCAR-graphics-window ()
    (setf *og*
             (make-instance 'dialog
                  :window-type
                  :document-with-zoom
                  :window-title
                  "Position OSCAR Graphics Window"
                  :view-position
                  2686978
                  :view-size
                  #@(632 459)
                  :view-font
                  '("Chicago" 12 :srcor :plain)
                  :view-subviews
                  (list (make-dialog-item
                           'static-text-dialog-item
                           #@(32 16)
                           #@(235 49)
                           "Position and size this window to
adjust the position and size of the
OSCAR graphics window."
                           'nil)
                          (make-dialog-item
                            'button-dialog-item
                            #@(128 77)
                            #@(39 22)
                            "OK"
                            #'(lambda (item)
                                  (declare (ignore item))
                                  (setf *open-position* (view-position *og*))
                                  (setf *screen-height* (point-v (view-size *og*)))
                                  (setf *screen-width* (point-h (view-size *og*)))
                                  (window-close *og*))
                            :default-button t)))))

(defunction add-graphics-menu-items ()
    (let* ((menubar (menubar))
              (oscar-item 
                (find-if #'(lambda (item) (equal (menu-title item) "GRAPHICS")) menubar)))
       (set-menubar
         (append
           (remove oscar-item menubar)
           (list
             (make-instance 'menu
                  :menu-title
                  "GRAPHICS"
                  :menu-items
                  (list
                    (make-instance 'menu-item
                         :menu-item-title "Graph reasoning"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Graph reasoning"))
                               (menu-item-enable (oscar-graphics-menu-item "Do not graph reasoning"))
                               (setf *graphics-on* t))
                         :disabled *graphics-on*)
                    (make-instance 'menu-item
                         :menu-item-title "Do not graph reasoning"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Do not graph reasoning"))
                               (menu-item-enable (oscar-graphics-menu-item "Graph reasoning"))
                               (setf *graphics-on* nil))
                         :disabled (not *graphics-on*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Graph reasoning-log"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Graph reasoning-log"))
                               (menu-item-enable (oscar-graphics-menu-item "Do not graph reasoning-log"))
                               (setf *graph-log* t))
                         :disabled *graph-log*)
                    (make-instance 'menu-item
                         :menu-item-title "Do not graph reasoning-log"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Do not graph reasoning-log"))
                               (menu-item-enable (oscar-graphics-menu-item "Graph reasoning-log"))
                               (setf *graph-log* nil))
                         :disabled (not *graph-log*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Graph problem"
                         :menu-item-action #'(lambda nil (eval-enqueue '(graph-problem))))
                    (make-instance 'menu-item
                         :menu-item-title "Graph problem completely"
                         :menu-item-action #'(lambda nil (eval-enqueue '(graph-problem :full t))))
                    (make-instance 'menu-item
                         :menu-item-title "Abbreviated graph"
                         :menu-item-action
                         #'(lambda nil (eval-enqueue '(draw-abbreviated-display (front-window :class 'og-window)))))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Pause on"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Pause on"))
                               (menu-item-enable (oscar-graphics-menu-item "Pause off"))
                               (setf *graphics-pause* t))
                         :disabled *graphics-pause*)
                    (make-instance 'menu-item
                         :menu-item-title "Pause off"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Pause off"))
                               (menu-item-enable (oscar-graphics-menu-item "Pause on"))
                               (setf *graphics-pause* nil))
                         :disabled (not *graphics-pause*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Speech on"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Speech on"))
                               (menu-item-enable (oscar-graphics-menu-item "Speech off"))
                               (get-default-speech-channel-from-user) (setf *speak* t))
                         :disabled (and (boundp '*speak*) *speak*))
                    (make-instance 'menu-item
                         :menu-item-title "Speech off"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Speech off"))
                               (menu-item-enable (oscar-graphics-menu-item "Speech on"))
                               (setf *speak* nil))
                         :disabled (not (and (boundp '*speak*) *speak*)))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Graph interests"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Graph interests"))
                               (menu-item-enable (oscar-graphics-menu-item "Do not graph interests"))
                               (setf *graph-interests* t))
                         :disabled *graph-interests*)
                    (make-instance 'menu-item
                         :menu-item-title "Do not graph interests"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-disable (oscar-graphics-menu-item "Do not graph interests"))
                               (menu-item-enable (oscar-graphics-menu-item "Graph interests"))
                               (setf *graph-interests* nil))
                         :disabled (not *graph-interests*))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Show formulas"
                         :menu-item-action
                         #'(lambda nil
                               (menu-item-enable (oscar-graphics-menu-item "Do not show formulas"))
                               (let ((window (front-window)))
                                  (cond ((typep window 'og-window)
                                               (setf (show-formulas-in window) t)
                                               (invalidate-view window t))
                                              (t 
                                                (setf *show-formulas* t)
                                               ; (menu-item-disable (oscar-graphics-menu-item "Show formulas"))
                                               ; (menu-item-enable (oscar-graphics-menu-item "Do not show formulas"))
                                                ))))
                        ; :disabled *show-formulas*
                         )
                    (make-instance 'menu-item
                         :menu-item-title "Do not show formulas"
                         :menu-item-action
                         #'(lambda nil
                               (let ((window (front-window)))
                                  (cond ((typep window 'og-window)
                                               (setf (show-formulas-in window) nil)
                                               (invalidate-view window t))
                                              (t (setf *show-formulas* nil)
                                                 ; (menu-item-disable (oscar-graphics-menu-item "Do not show formulas"))
                                                 ; (menu-item-enable (oscar-graphics-menu-item "Show formulas"))
                                                  ))))
                         ;:disabled (not *show-formulas*)
                         )
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "hypernode-radius"
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
                                                 'static-text-dialog-item #@(22 15) #@(177 34)
                                                 "Enter the hypernode-radius and type a carriage-return."
                                                 'nil
                                                 :text-justification :center)
                                               (make-dialog-item
                                                 'editable-text-dialog-item #@(86 64) #@(48 16) 
                                                 (write-to-string *hypernode-radius*)
                                                 #'(lambda (item)
                                                       (let ((text (dialog-item-text item)))
                                                          (when (and (> (length text) 0)
                                                                                (equal (substring text (1- (length text))) "
"))
                                                               (setf *hypernode-radius* (read-from-string text))
                                                               (window-close *menu-dialog*))))
                                                 :allow-returns t))))))
                    (make-instance 'menu-item
                         :menu-item-title "Minimum-distance-between-nodes"
                         :menu-item-action
                         #'(lambda nil
                               (setf *menu-dialog*
                                        (make-instance 'dialog
                                             :window-type :double-edge-box
                                             :view-position #@(60 51)
                                             :view-size #@(251 116)
                                             :close-box-p nil
                                             :view-font '("Chicago" 12 :srcor :plain)
                                             :view-subviews
                                             (list
                                               (make-dialog-item
                                                 'static-text-dialog-item #@(9 12) #@(240 54)
                                                 "Enter the minimum-distance-between-nodes and type a carriage-return."
                                                 'nil)
                                               (make-dialog-item
                                                 'editable-text-dialog-item #@(99 74) #@(48 16)
                                                 (write-to-string *minimum-distance-between-nodes*)
                                                 #'(lambda (item)
                                                       (let ((text (dialog-item-text item)))
                                                          (when (and (> (length text) 0)
                                                                                (equal (substring text (1- (length text))) "
"))
                                                               (setf *minimum-distance-between-nodes*
                                                                        (read-from-string text))
                                                               (window-close *menu-dialog*))))
                                                 :allow-returns t))))))
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Color with black background"
                         :menu-item-action
                         #'(lambda nil
                               (let ((view (front-window :class 'og-window)))
                                  (menu-item-disable (oscar-graphics-menu-item "Color with black background"))
                                  (menu-item-enable (oscar-graphics-menu-item "Color with white background"))
                                  (menu-item-enable (oscar-graphics-menu-item "Monochrome"))
                                  (setf *monochrome* nil)
                                  (setf *back-color* *black-color*)
                                  (set-back-color view *back-color*)
                                  (setf *line-color* *white-color*)
                                  (invalidate-view view t)))
                         :disabled (and (not *monochrome*) (equal *back-color* *black-color*)))
                    (make-instance 'menu-item
                         :menu-item-title "Color with white background"
                         :menu-item-action
                         #'(lambda nil
                               (let ((view (front-window :class 'og-window)))
                                  (menu-item-disable (oscar-graphics-menu-item "Color with white background"))
                                  (menu-item-enable (oscar-graphics-menu-item "Color with black background"))
                                  (menu-item-enable (oscar-graphics-menu-item "Monochrome"))
                                  (setf *monochrome* nil)
                                  (setf *back-color* *white-color*)
                                  (set-back-color view *back-color*)
                                  (setf *line-color* *black-color*)
                                  (invalidate-view view t)))
                         :disabled (and (not *monochrome*) (equal *back-color* *white-color*)))
                    (make-instance 'menu-item
                         :menu-item-title "Monochrome"
                         :menu-item-action
                         #'(lambda nil
                               (let ((view (front-window :class 'og-window)))
                                  (menu-item-disable (oscar-graphics-menu-item "Monochrome"))
                                  (menu-item-enable (oscar-graphics-menu-item "Color with black background"))
                                  (menu-item-enable (oscar-graphics-menu-item "Color with white background"))
                                  (setf *monochrome* t)
                                  (setf *back-color* *white-color*)
                                  (set-back-color view *white-color*)
                                  (setf *line-color* *black-color*)
                                  (invalidate-view view t)))
                         :disabled *monochrome*)
                    (make-instance 'menu-item :menu-item-title "-" :disabled t)
                    (make-instance 'menu-item
                         :menu-item-title "Refresh Window"
                         :menu-item-action
                         #'(lambda nil (invalidate-view (front-window :class 'og-window) t)))
                    (make-instance 'menu-item
                         :menu-item-title "Resize Window"
                         :menu-item-action
                         #'(lambda nil (size-OSCAR-graphics-window))))))))))

(defunction oscar-graphics-menu-item (string)
    (let ((oscar-menu
              (find-if #'(lambda (item) (equal (menu-title item) "GRAPHICS")) (menubar))))
       (find-if #'(lambda (item) (equal (menu-title item) string)) (menu-items oscar-menu))))

(defunction add-nodes-menu ()
    (let ((menubar (menubar)))
       (set-menubar
         (append
           (remove
             (find-if #'(lambda (item) (equal (menu-title item) "NODES")) menubar)
             menubar)
           (list
             (make-instance 'menu
                  :menu-title "NODES"
                  :menu-items
                  (list
                    (make-instance 'menu-item
                         :menu-item-title "Flash Nodes:"
                         :style :underline
                         :menu-item-action #'(lambda nil))
                    (make-instance 'menu-item
                         :menu-item-title "     Node"
                         :menu-item-action #'(lambda nil (flash-queried-node)))
                    (make-instance 'menu-item
                         :menu-item-title "     hyperlink"
                         :menu-item-action #'(lambda nil (flash-queried-hyperlink)))
                    (make-instance 'menu-item
                         :menu-item-title "     ......"
                         :menu-item-action #'(lambda nil))
                    (make-instance 'menu-item
                         :menu-item-title "     Affected-nodes"
                         :menu-item-action #'(lambda nil (setf *flash-affected-nodes* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Ancestors"
                         :menu-item-action #'(lambda nil (setf *flash-ancestors* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Consequences"
                         :menu-item-action #'(lambda nil (setf *flash-consequences* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Defeatees"
                         :menu-item-action #'(lambda nil (setf *flash-defeatees* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Defeaters"
                         :menu-item-action #'(lambda nil (setf *flash-defeaters* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Relevant nodes"
                         :menu-item-action #'(lambda nil (setf *flash-relevant-nodes* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     hyperlink-bases"
                         :menu-item-action #'(lambda nil (setf *flash-hyperlink-bases* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     hyperlinks"
                         :menu-item-action #'(lambda nil (setf *flash-hyperlinks* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Terminal-deductive-ancestors"
                         :menu-item-action #'(lambda nil (setf *flash-terminal-deductive-ancestors* t)))
                    (make-instance 'menu-item
                         :menu-item-title "Graph Nodes:"
                         :style :underline
                         :menu-item-action #'(lambda nil))
                    (make-instance 'menu-item
                         :menu-item-title "     Ancestors"
                         :menu-item-action
                         #'(lambda nil
                               (setf *message*
                                        (make-top-message
                                             "Click on nodes whose ancestors are to be graphed, then click elsewhere"))
                               (setf *graph-ancestors* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Arguments for"
                         :menu-item-action
                         #'(lambda nil
                               (setf *message*
                                        (make-top-message
                                             "Click on node whose arguments are to be graphed"))
                               (setf *graph-hypernode-arguments* t)))
                    (make-instance 'menu-item
                         :menu-item-title "     Current-affected-nodes"
                         :menu-item-action
                         #'(lambda nil
                               (window-select (front-window :class 'og-window))
                               (graph-affected-nodes (front-window))))
                    (make-instance 'menu-item
                         :menu-item-title "     Nodes relevant to ultimate-interests"
                         :menu-item-action
                         #'(lambda nil
                               (window-select (front-window :class 'og-window))
                               (graph-relevant-nodes (front-window))))
                    (make-instance 'menu-item
                         :menu-item-title "     Relevant nodes"
                         :menu-item-action
                         #'(lambda nil 
                               (setf
                                 *message*
                                 (make-top-message
                                   "Click on nodes whose relevant-nodes are to be graphed, then click elsewhere"))
                               (setf *graph-relevant-nodes* t)))
                    (make-instance 'menu-item
                         :menu-item-title "Move All:"
                         :style :underline
                         :menu-item-action #'(lambda nil))
                    (make-instance 'menu-item
                         :menu-item-title "     Nodes"
                         :menu-item-action #'move-all-nodes)
                    (make-instance 'menu-item
                         :menu-item-title "     Interests"
                         :menu-item-action #'move-all-interests)
                    )))))))

(defmethod view-click-event-handler ((wind og-window) position)
    (let ((selected-node (car (find-if #'(lambda (x) (ontop position (mem2 x))) (hypernode-list wind)))))
       (cond
         (selected-node
           (cond
             (*flash-affected-nodes* (flash-affected-nodes selected-node wind))
             (*flash-ancestors* (flash-ancestors selected-node wind))
             (*flash-consequences* (flash-consequences selected-node wind))
             (*flash-defeatees* (flash-defeaters selected-node wind))
             (*flash-defeaters*  (flash-defeatees selected-node wind))
             (*flash-relevant-nodes* (flash-relevant-nodes selected-node wind))
             (*flash-hyperlink-bases* (flash-hyperlink-bases selected-node wind))
             (*flash-hyperlinks* (flash-hyperlinks selected-node wind))
             (*flash-terminal-deductive-ancestors*
               (flash-terminal-deductive-ancestors selected-node wind))
             (*graph-ancestors* (select-nodes-to-graph-ancestors selected-node wind))
             (*graph-hypernode-arguments* (graph-hypernode-arguments selected-node wind))
             (*graph-relevant-nodes* (select-nodes-to-graph-relevant-nodes selected-node wind))
             (*move-all-nodes* (set-guide-node selected-node))
             ((shift-key-p) (select-nodes-to-move selected-node wind))
             ((command-key-p) (inspect selected-node))
             (t (display-hypernode-sequent selected-node wind))))
         (t
           (cond
             (*graph-relevant-nodes*
               (graph-relevant-nodes wind *nodes-to-graph*) (setf *graph-relevant-nodes* nil)
               (setf *nodes-to-graph* nil) (window-close *message*))
             (*graph-ancestors*
               (graph-ancestors *nodes-to-graph* wind) (setf *graph-ancestors* nil)
               (setf *nodes-to-graph* nil) (window-close *message*))
             (*nodes-to-be-moved* (move-nodes-in-window wind position))
             (*move-all-nodes* (move-all-nodes-to position wind))
             (t (let ((interest (car (rassoc position (interest-list wind) :test #'ontop))))
                   (cond
                     (interest
                       (cond
                         (*move-all-interests* (set-guide-interest interest))
                         ((shift-key-p) (select-interests-to-move interest wind))
                         ((command-key-p) (inspect interest))
                         (t (display-interest-sequent interest wind))))
                     (*move-all-interests* (move-all-interests-to position wind))
                     (*interests-to-be-moved* (move-interests-in-window wind position))
                     ((shift-key-p) (select-nodes-in-region wind position))
                     (t 
                       (setf *nodes-to-graph* nil) (when *message* (window-close *message*)))
                     ))))))))

(defunction select-nodes-to-move (selected-node wind)
    (if *message* (window-close *message*))
    (cond
      ((member selected-node *nodes-to-be-moved*)
        (redraw-node selected-node wind)
        (pull selected-node *nodes-to-be-moved*)
        (cond (*nodes-to-be-moved*
                     (setf *hypernode-to-be-moved* (mem1 *nodes-to-be-moved*))
                     (setf *message*
                              (make-top-message
                                (cat-list
                                  (list "Click on New Location for Node "
                                          (princ-to-string (hypernode-number *hypernode-to-be-moved*))
                                          " or select more nodes to be moved"))))
                     (window-select wind))
                    (t (setf *hypernode-to-be-moved* nil))))
      (t
        (frame-node selected-node *light-gray-color* wind)
        (setf *message*
                 (make-top-message
                   (cat-list
                     (list "Click on New Location for Node "
                             (princ-to-string (hypernode-number selected-node))
                             " or select more nodes to be moved"))))
        (setf *hypernode-to-be-moved* selected-node)
        (push selected-node *nodes-to-be-moved*)
        (window-select wind))))

(defunction select-interests-to-move (interest wind)
    (if *message* (window-close *message*))
    (cond
      ((member interest *interests-to-be-moved*)
        (redraw-interest interest wind)
        (pull interest *interests-to-be-moved*)
        (cond (*interests-to-be-moved*
                     (setf *interest-to-be-moved* (mem1 *interests-to-be-moved*))
                     (setf *message*
                              (make-top-message
                                (cat-list
                                  (list "Click on New Location for Interest "
                                          (princ-to-string (interest-number *interest-to-be-moved*))
                                          " or select more interests to be moved"))))
                     (window-select wind))
                    (t (setf *interest-to-be-moved* nil))))
      (t
        (frame-interest interest *light-gray-color* wind)
        (setf *message*
                 (make-top-message
                   (cat-list
                     (list "Click on New Location for Interest "
                             (princ-to-string (Interest-number interest))
                             " or select more interests to be moved"))))
        (setf *interest-to-be-moved* interest)
        (push interest *interests-to-be-moved*)
        (window-select wind))))

(defunction make-top-message (string)
    (let ((width (* 8 (length string))))
       (make-instance 'windoid
            :window-type :tool
            :window-title string
            :view-position
            (make-point (+ (point-h *open-position*) (round (/ (- *screen-width* width) 2)))
                                   (point-v *open-position*))
            :view-size width
            :close-box-p nil
            :view-font '("Helvetica" 12 :srcor :plain))))

(defunction redraw-node (node view)
    (draw-just-node (hypernode-position node view) view node (hypernode-color node view)))

(defunction redraw-interest (interest view)
    (draw-just-interest (interest-position interest view) view interest))

(defunction select-nodes-to-graph-relevant-nodes (selected-node wind)
    (cond
      ((member selected-node *nodes-to-graph*)
        (redraw-node selected-node wind)
        (pull selected-node *nodes-to-graph*)
        (when (null *nodes-to-graph*)
             (setf *graph-relevant-nodes* nil) (window-close *message*)))
      (t
        (push selected-node *nodes-to-graph*)
        (frame-node selected-node *light-gray-color* wind)
        (window-select wind))))

(defunction select-nodes-to-graph-ancestors (selected-node wind)
    (cond
      ((member selected-node *nodes-to-graph*)
        (redraw-node selected-node wind)
        (pull selected-node *nodes-to-graph*)
        (when (null *nodes-to-graph*)
             (setf *graph-ancestors* nil) (window-close *message*)))
      (t
        (push selected-node *nodes-to-graph*)
        (frame-node selected-node *light-gray-color* wind)
        (window-select wind))))

(defunction flash-affected-nodes (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (mem2 (compute-effects (car (hypernode-hyperlinks selected-node)))))
      wind *yellow-color* 5
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node)) " has no affected-nodes")))
    (setf *flash-affected-nodes* nil))

(defunction flash-ancestors (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind))) (hypernode-ancestors selected-node))
      wind *blue-color* 5
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node)) " has no ancestors")))
    (setf *flash-ancestors* nil))

(defunction flash-consequences (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (mapcar #'hyperlink-target (hypernode-consequent-links selected-node)))
      wind *blue-color* 10
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node)) " has no consequences")))
    (setf *flash-consequences* nil))

(defunction flash-defeaters (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (mapcar #'hyperlink-target (hypernode-defeatees selected-node)))
      wind *red-color* 10
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node)) " has no defeatees")))
    (setf *flash-defeatees* nil))

(defunction flash-defeatees (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (flash-nodes (unionmapcar+ #'hyperlink-hypernode-defeaters (hypernode-hyperlinks selected-node))
                                             wind *red-color* 10
                                             (cat-list
                                               (list "Node " (write-to-string (hypernode-number selected-node)) " has no defeaters"))))
      wind *red-color* 10)
    (setf *flash-defeaters* nil))

(defunction flash-relevant-nodes (selected-node wind)
    (let ((rn *relevant-nodes*))
       (compute-relevant-nodes (list selected-node))
       (flash-nodes
         (subset #'(lambda (n) (assoc n (hypernode-list wind))) *relevant-nodes*)
         wind *red-color* 10
         (cat-list
           (list "Node " (write-to-string (hypernode-number selected-node)) " has no relevant-nodes")))
       (setf *relevant-nodes* rn))
    (setf *flash-relevant-nodes* nil))

(defunction flash-hyperlink-bases (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (unionmapcar+ #'hyperlink-basis (hypernode-hyperlinks selected-node)))
      wind *blue-color* 10
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node)) " has no hyperlink-bases")))
    (setf *flash-hyperlink-bases* nil))

(defunction flash-hyperlinks (selected-node wind)
    (let ((links (hypernode-hyperlinks selected-node)))
       (cond
         (links
           (dolist (l links)
               (let ((mes
                         (make-top-message
                           (cat "hyperlink  " (princ-to-string (hyperlink-number L))))))
                  (flash-nodes (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                                                        (hyperlink-basis l))
                                          wind *blue-color* 5)
                  (window-close mes))))
         (t
           (let ((mes
                     (make-top-message
                       (cat-list
                         (list "Node " (write-to-string (hypernode-number selected-node)) " has no hyperlinks")))))
              (sleep 1)
              (window-close mes)))))
    (setf *flash-hyperlinks* nil))

(defunction flash-terminal-deductive-ancestors (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (compute-terminal-deductive-ancestors selected-node))
      wind *blue-color* 5
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node))
                " has no terminal-deductive-ancestors")))
    (when (not (shift-key-p))
         (setf *flash-terminal-deductive-ancestors* nil)))

(defunction graph-hypernode-arguments (selected-node wind)
    (setf *graph-arguments* t)
    (setf *graph-hypernode-arguments* nil)
    (window-close *message*)
    (with-cursor *watch-cursor*
         (show-arguments-for selected-node wind)))

(defunction move-nodes-in-window (wind new-position)
    (let* ((assoc (assoc *hypernode-to-be-moved* (hypernode-list wind)))
              (move-h (- (point-h new-position) (point-h (mem2 assoc))))
              (move-v (- (point-v new-position) (point-v (mem2 assoc)))))
       (dolist (n *nodes-to-be-moved*)
           (let ((assoc (assoc n (hypernode-list wind))))
              (pull assoc (hypernode-list wind))
              (push (list n
                                 (make-point
                                   (+ (point-h (mem2 assoc)) move-h)
                                   (+ (point-v (mem2 assoc)) move-v))
                                 (mem3 assoc)) (hypernode-list wind))))
       (setf *hypernode-to-be-moved* nil)
       (setf *nodes-to-be-moved* nil)
       (window-close *message*)
       (invalidate-view wind t)))

(defunction move-interests-in-window (wind position)
    (let* ((assoc (assoc *interest-to-be-moved* (interest-list wind)))
              (move-h (- (point-h position) (point-h (cdr assoc))))
              (move-v (- (point-v position) (point-v (cdr assoc)))))
       (dolist (n *interests-to-be-moved*)
           (let ((assoc (assoc n (interest-list wind))))
              (pull assoc (interest-list wind))
              (push (cons n
                                     (make-point
                                       (+ (point-h (cdr assoc)) move-h)
                                       (+ (point-v (cdr assoc)) move-v)))
                          (interest-list wind))))
       (setf *interest-to-be-moved* nil)
       (setf *interests-to-be-moved* nil)
       (window-close *message*)
       (invalidate-view wind t)))

(defunction flash-queried-node ()
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
                      'static-text-dialog-item #@(22 15) #@(177 34)
                      "Enter hypernode-number and type a carriage-return."
                      'nil
                      :text-justification :center)
                    (make-dialog-item
                      'editable-text-dialog-item #@(86 64) #@(48 16) 
                      "   ?"
                      #'(lambda (item)
                            (let ((text (dialog-item-text item)))
                               (when (and (> (length text) 0)
                                                     (equal (substring text (1- (length text))) "
"))
                                    (let ((node (node (read-from-string text)))
                                            (window (front-window :class 'og-window)))
                                       (window-close *menu-dialog*)
                                       (invalidate-view window t)
                                       (when node
                                            (window-select window)
                                            (flash-nodes
                                              (list node) window *yellow-color* 5))))))
                      :allow-returns t)))))

(defunction flash-queried-hyperlink ()
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
                      'static-text-dialog-item #@(9 12) #@(240 54)
                      "Enter hyperlink-number and type a carriage-return."
                      'nil
                      :text-justification :center)
                    (make-dialog-item
                      'editable-text-dialog-item #@(86 64) #@(48 16) 
                      "   ?"
                      #'(lambda (item)
                            (let ((text (dialog-item-text item)))
                               (when (and (> (length text) 0)
                                                     (equal (substring text (1- (length text))) "
"))
                                    (let ((link (hyperlink (read-from-string text))))
                                       (window-close *menu-dialog*)
                                       (when link
                                            (window-select (front-window :class 'og-window))
                                            (flash-nodes
                                              (cons (hyperlink-target link) (hyperlink-basis link))
                                              (front-window) *yellow-color* 5))))))
                      :allow-returns t)))))

(defunction frame-node (node color view)
   (let* ((position (hypernode-position node view))
             (x (point-h position))
             (y (point-v position))
             (left (- x *hypernode-radius*))
             (top (- y *hypernode-radius*))
              (right (+ x *hypernode-radius*))
              (bottom (+ y *hypernode-radius*)))
       (set-pen-size view #@(3 3)) (set-fore-color view color)
       (frame-oval view left top right bottom)
       (set-pen-size view #@(1 1)) (set-fore-color view *line-color*)))

(defunction temporarily-frame-node (node color view)
    (let* ((position (hypernode-position node view))
              (x (point-h position))
              (y (point-v position))
              (left (- x *hypernode-radius*))
              (top (- y *hypernode-radius*))
              (right (+ x *hypernode-radius*))
              (bottom (+ y *hypernode-radius*)))
       (set-pen-size view #@(3 3)) (set-fore-color view color)
       (frame-oval view left top right bottom)
       (sleep 1)
       (erase-oval view left top right bottom)
       (set-fore-color view (hypernode-color node view))
       (paint-oval view left top right bottom)
       (set-fore-color view *black-color*)
       (cond
         ((hypernode-answered-queries node)
           (set-pen-size view #@(3 3)) (set-fore-color view *red-color*)
           (frame-oval view left top right bottom)
           (set-pen-size view #@(1 1)) (set-fore-color view *black-color*))
         (t 
           (set-pen-size view #@(1 1)) (set-fore-color view *black-color*)
           (frame-oval view left top right bottom)))
       (move-to view (- x 6) (+ y 1))
       (princ (hypernode-number node) *og*)
       (move-to view (- x (- *hypernode-radius* 3)) (+ y 3))
       ))

(defunction frame-interest (interest color view)
   (let* ((position (interest-position interest view))
             (x (point-h position))
             (y (point-v position))
             (left (- x *hypernode-radius*))
             (top (- y *hypernode-radius*))
              (right (+ x *hypernode-radius*))
              (bottom (+ y *hypernode-radius*)))
       (set-pen-size view #@(3 3)) (set-fore-color view color)
       (frame-oval view left top right bottom)
       (set-pen-size view #@(1 1)) (set-fore-color view *line-color*)))

(defunction pause-graphics ()
    (let ((win (front-window)))
       (window-select (find-window "Listener"))
       (read-char)
       (window-select win)))

(defunction show-arguments-for (n window)
    (setf *arg-number* 0 *nodes-used* nil *arguments* nil *nodes-done* nil)
    (when (null window) (setf window (front-window)))
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
                         (if (every #'(lambda (L) (null (defeating-assignment-trees L))) arg)
                            (minimum0 (mapcar #'hyperlink-strength arg)) 0)
                         :argument-ultimate-interest (mem1 (hypernode-answered-queries n))
                         :argument-inclusive-nodes (list n))))
                (push argument *arguments*)
                (dolist (m (hypernode-motivating-nodes n))
                    (pushnew m (argument-inclusive-nodes argument))
                    (pushnew m *nodes-used*))
                (dolist (L (argument-links argument))
                    (dolist (b (hyperlink-basis L))
                        (pushnew b (argument-inclusive-nodes argument))
                        (pushnew b *nodes-used*)
                        (dolist (m (hypernode-motivating-nodes b))
                            (pushnew m (argument-inclusive-nodes argument))
                            (pushnew m *nodes-used*)))))))
    (dolist (argument (reverse *arguments*))
        (display-argument argument)
        (when *graph-arguments*
             (graph-nodes (argument-inclusive-nodes argument)
               window
               (cat-list
                 (list "Graph of Argument " (write-to-string (argument-number argument))
                         " for node " (write-to-string (hypernode-number n))))
               t))))

(defunction move-all-nodes ()
    (setf *message* (make-top-message "Select guide-node"))
    (setf *move-all-nodes* t))

(defunction move-all-interests ()
    (setf *message* (make-top-message "Select guide-interest"))
    (setf *move-all-interests* t))

(defunction set-guide-node (node)
    (setf *guide-node* node)
    (window-close *message*)
    (setf *message* (make-top-message "Click on new position for guide node")))

(defunction set-guide-interest (interest)
    (setf *guide-interest* interest)
    (window-close *message*)
    (setf *message* (make-top-message "Click on new position for guide interest")))

(defunction move-all-nodes-to (new-position wind)
    (when *guide-node*
         (let* ((assoc (assoc *guide-node* (hypernode-list wind)))
                   (move-h (- (point-h new-position) (point-h (mem2 assoc))))
                   (move-v (- (point-v new-position) (point-v (mem2 assoc)))))
            (dolist (x (hypernode-list wind))
                (pull x (hypernode-list wind))
                (push (list (mem1 x)
                                   (make-point
                                     (+ (point-h (mem2 x)) move-h)
                                     (+ (point-v (mem2 x)) move-v))
                                   (mem3 x)) (hypernode-list wind))))
         (setf *guide-node* nil)
         (setf *move-all-nodes* nil)
         (window-close *message*)
         (invalidate-view wind t)))

(defunction move-all-interests-to (new-position wind)
    (when *guide-interest*
         (let* ((assoc (assoc *guide-interest* (interest-list wind)))
                   (move-h (- (point-h new-position) (point-h (cdr assoc))))
                   (move-v (- (point-v new-position) (point-v (cdr assoc)))))
            (dolist (x (interest-list wind))
                (pull x (interest-list wind))
                (push (cons (mem1 x)
                                   (make-point
                                     (+ (point-h (cdr x)) move-h)
                                     (+ (point-v (cdr x)) move-v)))
                            (interest-list wind))))
         (setf *guide-interest* nil)
         (setf *move-all-interests* nil)
         (window-close *message*)
         (invalidate-view wind t)))

(defunction display-hypernode-sequent (node wind)
    (let* ((sequent (hypernode-sequent node))
              (identifier (cat "Node " (write-to-string (hypernode-number node))))
              (formula (pretty (sequent-formula sequent)))
              (sup (mapcar #'pretty (sequent-supposition sequent)))
              (width (* 5 (maximum
                                   (append (list (+ 10 (length identifier)) (length formula)) (mapcar #'length sup)))))
              (height (if sup (* 12 (+ 2 (length sup))) 12))
              (position (hypernode-position node wind))
              (hypernode-h (point-h position))
              (hypernode-v (point-v position)))
       (make-instance 'windoid
            :window-type :tool
            :view-position
            (let ((h (+ (* 2 *hypernode-radius*) hypernode-h))
                    (hw (point-h (view-size wind)))
                    (v (+ 48 (* 2 *hypernode-radius*) hypernode-v))
                    (vw (point-v (view-size wind))))
               (make-point (if (>= h hw) (- hw 120) h) (if (>= v vw) vw v)))
            :view-size (make-point (+ 2 width) (+ 4 height))
            :window-title identifier
            :view-font '("Helvetica" 10 :srcor :plain)
            :view-subviews
            (list (make-dialog-item
                      'static-text-dialog-item
                      #@(1 2)
                      (make-point width height)
                      (vertical-string (cons formula (if sup (cons "given" sup))))
                      'nil
                      :view-font '("Helvetica" 10 :srcor :plain))))))

(defunction display-interest-sequent (interest wind)
    (let* ((sequent (interest-sequent interest))
              (identifier (cat "Interest " (write-to-string (interest-number interest))))
              (formula (pretty (sequent-formula sequent)))
              (sup (mapcar #'pretty (sequent-supposition sequent)))
              (width (* 5 (maximum
                                   (append (list (+ 10 (length identifier)) (length formula)) (mapcar #'length sup)))))
              (height (if sup (* 12 (+ 2 (length sup))) 12))
              (position (interest-position interest wind))
              (interest-h (point-h position))
              (interest-v (point-v position)))
       (make-instance 'windoid
            :window-type :tool
            :view-position 
            (let ((h (+ (* 2 *hypernode-radius*) interest-h))
                    (hw (point-h (view-size wind)))
                    (v (+ 48 (* 2 *hypernode-radius*) interest-v))
                    (vw (point-v (view-size wind))))
               (make-point (if (>= h hw) (- hw 120) h) (if (>= v vw) vw v)))
            :view-size (make-point (+ 2 width) (+ 4 height))
            :window-title identifier
            :view-font '("Helvetica" 10 :srcor :plain)
            :view-subviews
            (list (make-dialog-item
                      'static-text-dialog-item
                      #@(1 2)
                      (make-point width height)
                      (vertical-string (cons formula (if sup (cons "given" sup))))
                      'nil
                      :view-font '("Helvetica" 10 :srcor :plain))))))

(defunction vertical-string (strings)
    (let ((new-strings (list (car strings))))
       (loop
          (setf strings (cdr strings))
          (when (null strings) (return (cat-list (reverse new-strings))))
          (push "
" new-strings)
          (push (car strings) new-strings))))

(defclass abbreviated-og-window (og-window) (window))

(defmethod view-draw-contents ((wind abbreviated-og-window))
    (dolist (pos (hypernode-list wind))
        (when (not (hypernode-cancelled-node (car pos)))
             (draw-abbreviated-node (cadr pos) wind (car pos))))
    (dolist (i (interest-list wind))
        (when (not (cancelled-interest (car i)))
             (draw-interest (cdr i) wind (car i)))))

(defunction draw-abbreviated-node (position view node)
    (draw-just-node position view node (hypernode-color node view))
    (draw-abbreviated-hyperlinks position view node)
    (attach-arrows-to-defeated-nodes position view node))

(defunction draw-abbreviated-hyperlinks (position view node)
    (dolist (L (hypernode-hyperlinks node))
        (when (hyperlink-defeasible? L)
             (set-fore-color view *gray-color*)
             (dolist (b (hyperlink-basis L))
                 (let ((pos-b (hypernode-position b view)))
                    (when pos-b 
                         (draw-arrow pos-b position view))))
             (set-fore-color view *line-color*))
        (dolist (b (compute-terminal-deductive-ancestors node))
            (let ((pos-b (hypernode-position b view)))
               (when pos-b 
                    (draw-arrow pos-b position view))))))

(defunction compute-strongly-relevant-nodes (nodes)
    (setf *strongly-relevant-nodes* nil)
    (dolist (node nodes) (add-strongly-relevant-nodes node))
    *strongly-relevant-nodes*)

(defunction add-strongly-relevant-nodes (node)
    (when (not (member node *strongly-relevant-nodes*))
         (push node *strongly-relevant-nodes*)
         (dolist (m (hypernode-motivating-nodes node))
             (add-strongly-relevant-nodes m))
         (dolist (L (hypernode-hyperlinks node))
             (when (hyperlink-defeasible? L)
                  (dolist (b (hyperlink-basis L)) (add-strongly-relevant-nodes b))
                  (dolist (d (hyperlink-hypernode-defeaters L)) (add-strongly-relevant-nodes d))))
         (dolist (b (compute-terminal-deductive-ancestors node))
             (add-strongly-relevant-nodes b))))

(defunction compute-terminal-deductive-ancestors (node)
    (setf *terminal-deductive-ancestors* nil *nodes-done* nil)
    (add-terminal-deductive-ancestors node)
    *terminal-deductive-ancestors*)

(defunction add-terminal-deductive-ancestors (node)
    (when (not (member node *nodes-done*))
         (push node *nodes-done*)
         (dolist (L (hypernode-hyperlinks node))
             (when
               (not (hyperlink-defeasible? L))
                 (dolist (b (hyperlink-basis L))
                     (when
                          (or (initial-node b) (some #'hyperlink-defeasible? (hypernode-hyperlinks b)))
                          (pushnew b  *terminal-deductive-ancestors*))
                     (add-terminal-deductive-ancestors b))))))

(defunction initial-node (node)
    (or (null (hypernode-hyperlinks node))
          (some #'(lambda (L) (null (hyperlink-basis L))) (hypernode-hyperlinks node))))

(defunction draw-abbreviated-display (window &optional (title "Abbreviated Node Display"))
    (let ((wind (find-window title)))
       (when wind (window-close wind)))
    (let ((view (make-instance 'abbreviated-og-window 
                            :view-position *open-position*
                            :window-title title
                            :view-size (make-point *screen-width* *screen-height*)))
            (nodes (compute-strongly-relevant-nodes
                           (unionmapcar+ #'query-answers *ultimate-epistemic-interests*))))
       (setf (hypernode-list view) (subset #'(lambda (x) (member (car x) nodes)) (hypernode-list window)))
       (invalidate-view view)))

(defunction flash-terminal-deductive-ancestors (selected-node wind)
    (flash-nodes
      (subset #'(lambda (n) (assoc n (hypernode-list wind)))
                     (compute-terminal-deductive-ancestors selected-node))
      wind *blue-color* 5
      (cat-list
        (list "Node " (write-to-string (hypernode-number selected-node))
                " has no terminal-deductive-ancestors")))
    (setf *flash-ancestors* nil))

(defunction select-nodes-in-region (wind position)
    (cond
      ((double-click-p)
        (line-to wind position)
        (move-to wind position)
        (line-to wind *region-start-position*)
        (setf *selection-region* (close-region wind))
        (dolist (x (hypernode-list wind))
            (when (point-in-region-p *selection-region* (mem2 x))
                 (frame-node (mem1 x) *light-gray-color* wind)
                 (setf *hypernode-to-be-moved* (mem1 x))
                 (push (mem1 x) *nodes-to-be-moved*)))
       ; (paint-region wind *selection-region*)
        (when *nodes-to-be-moved*
             (when *message* (window-close *message*))
             (setf *message*
                      (make-top-message
                        (cat-list
                          (list "Click on New Location for Node "
                                  (princ-to-string (hypernode-number (mem1 *nodes-to-be-moved*)))
                                  " or select more nodes to be moved")))))
        (setf *selection-region* nil)
        (setf *region-start-position* nil)
        (set-pen-size wind #@ (1 1))
        (set-fore-color wind *line-color*))
      ((null *region-start-position*)
        (setf *region-start-position* position)
        (move-to wind position)
        (open-region wind)
        (pen-show wind)
        (set-pen-size wind #@ (4 4))
        (set-fore-color wind *gray-color*)
      ;  (when *message* (window-close *message*))
      ;  (setf *message* (make-top-message "Enclose nodes to be moved"))
        )
      (t
        (line-to wind position)
        (move-to wind position)
        )))



;(load (merge-pathnames oscar-pathname "Graph-nodes.lsp"))

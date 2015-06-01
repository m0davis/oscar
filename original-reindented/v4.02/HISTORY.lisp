
==============================================
Definition overwritten 5/31/2015     17:23:59
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:24:0
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     17:35:14
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:35:14
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     17:37:53
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:37:54
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     17:39:24
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:39:24
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     17:49:53
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:49:54
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     17:56:36
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:56:37
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     17:58:4
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     17:58:4
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     18:3:32
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     18:3:33
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     18:28:18
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     18:28:18
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     18:35:41
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     18:35:41
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     18:36:50
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     18:36:50
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

==============================================
Definition overwritten 5/31/2015     18:38:15
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION
        &OPTIONAL GENERATING-NODE)
  (COND
   ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
    (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON
                                     INTEREST DEPTH PRIORITY BINDING
                                     SUPPOSITION :GENERATING-NODE
                                     GENERATING-NODE :REMAINING-PREMISES
                                     (BACKWARDS-PREMISES REASON) :CLUES CLUES))
   ((OR (NUMBERP (REASON-STRENGTH REASON))
        (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
            (DEGREE-OF-INTEREST INTEREST)))
    (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
      (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
                       (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING
                       BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 5/31/2015     18:38:16
--------------------------------------------------------------------------------
(DEFUN RUN-REASONING-PROBLEM (P)
  (SETF *PROBLEM-NUMBER* (CAR P))
  (SETF *PRETTY-LIST* NIL
        *STRING-SYMBOLS* NIL)
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (PRINC
   "******************************************************************************************")
  (TERPRI)
  (DISPLAY-PROBLEM P)
  (COGITATE)
  (TERPRI))

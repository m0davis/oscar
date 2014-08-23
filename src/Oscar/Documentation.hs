{-# LANGUAGE NoImplicitPrelude #-}

{- | __So, you want to write an OSCAR problem__

Here is an example of a valid Problem, represented as a Text ⁞ ƮProblemsWithLineComments.

@
; This is a line comment, starting with a semicolon. All such comments are
; ignored when parsing an Oscar 'Problem'.
Problem #42 ; The 'ProblemNumber' must be given as an integer.

Here is a 'ProblemDescription', which may be given starting on a line
following the 'ProblemNumber'.

The description ends at the first 'Section' identifier.

A (case-sensitive) section identifier is a line containing __exactly one__
(sans whitespace, which is ignored) of the following bulleted items:
    * Ultimate epistemic interests:      ; (__required__)
    * Given premises:                    ; (optional)
    * FORWARDS PRIMA FACIE REASONS       ; (optional)
    * FORWARDS CONCLUSIVE REASONS        ; (optional)
    * BACKWARDS PRIMA FACIE REASONS      ; (optional)
    * BACKWARDS CONCLUSIVE REASONS       ; (optional)

No repeats of sections are allowed.

Given premises: ; Here's a section identifier.
                ; Note that the "Given premises:" above in the description is
                ; __not__ a Section identifier since it does not occur by
                ; itself (it's preceded by a "*").

    ; A 'ProblemPremise' is a 'Formula' and a 'ProblemJustificationDegree'.

    TheMatIsOnTheFloor     justification = 0.8

    ~TheMatIsOnTheFloor -> ~TheCatIsOnTheMat
        ; Newlines are ignored when reading formulas, so long formulas may be
        ; split across lines, ending with its justification.
                           justification = 1.0

    ; Formulas may be quantified.
    (all x)((Cat x) -> (LikesLasagna x))
                           justification = 1.0

    ~(LikesLasagna fido)   justification = 1.0

    A                      justification = 0.1
    B                      justification = 0.2
    C                      justification = 0.3
    D                      justification = 0.4
    E                      justification = 0.5
    F                      justification = 0.6
    G                      justification = 0.7

Ultimate epistemic interests:
    ; An 'ProblemInterest' is a 'Formula' and a 'ProblemInterestDegree'
    TheCatIsOnTheMat                      interest = 0.7
    ~(Cat fido)                           interest = 1.0
    P v ~P                                interest = 1.0

FORWARDS PRIMA FACIE REASONS
    ; A 'ProblemForwardsPrimaFacieReason' is a 'ProblemReasonName',
    ; a 'ForwardsReason', and a 'ProblemStrengthDegree'.
    ;
    ; Prima facie reasons differ from conclusive ones in that they may be
    ; undercut or defeated. TODO Provide more details on the semantics
    ; of reasons.
    ;
    ; A 'ForwardsReason' is
    ; * a set of ({curly-braced}, comma-delimited) 'Formula's, representing
    ;   the forwards premises.
    ; * a conclusion.

    fpf-reason_1:       ; the 'ProblemReasonName', which may be any sequence
                        ; of characters up to a colon.
        {A,B}           ; 'Formula's of the '_frForwardsPremises'
        ||=>            ; an arrow separating the premises from the conclusion
        Z               ; '_frConclusion'
        strength = 1.0

    fpf-reason_2:   {TheCatIsOnTheMat} ||=> TheCatIsHungry  strength = 1.0

FORWARDS CONCLUSIVE REASONS
    ; A 'ProblemForwardsConclusiveReason' is similar to a prima facie one,
    ; except that its strength must be 1.0.
    fcon-reason_1:   {TheCatWasJustFed} ||=> ~TheCatIsHungry   strength = 1.0

    ; TODO Specification of the strength of conclusive reasons should be
    ; optional, since all such reasons have a strength of unity.

BACKWARDS PRIMA FACIE REASONS
    ; A 'ProblemBackwardsPrimaFacieReason' is similar to a forwards one,
    ; except that it contains a 'BackwardsReason' instead of a
    ; 'ForwardsReason'.
    bpf-reason_1:       ; 'ProblemReasonName'
        {A}             ; '_brForwardsPremises'
        {B,C}           ; '_brBackwardsPremises'
        ||=>            ; an arrow separating the premises from the conclusion
        Z               ; '_brConclusion'
        strength = 1.0
    bpf-reason_2:   {} {C} ||=> ~R   strength = 1.0
    bpf-reason_3:   {B} {D} ||=> C    strength = 1.0

BACKWARDS CONCLUSIVE REASONS
    ; Each of these represents a 'ProblemBackwardsConclusiveReason'.
    bcon-reason_1:   {} {Q1 , Q2 , Q3} ||=> (Q1 & (Q2 & Q3))   strength = 1.0
@
-}

module Oscar.Documentation where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem
import Oscar.Formula
import Oscar.ProblemParser.Internal.Section
import Oscar.ProblemParser.Internal.Tags

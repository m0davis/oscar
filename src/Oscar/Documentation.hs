{-# LANGUAGE NoImplicitPrelude #-}

module Oscar.Documentation (
    -- * Who is Oscar?
    -- $WhoIsOscar

    -- * What is defeasible reasoning?
    -- $WhatIsDefeasibleReasoning

    -- * So, you want to write an OSCAR @Problem@
    -- $ExampleOfProblem

    -- * So, you want to write an OSCAR @Formula@
    -- $ExampleOfFormula
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem
import Oscar.Formula
import Oscar.ProblemParser.Internal.Section
import Oscar.ProblemParser.Internal.Tags

{- $WhoIsOscar

Oscar is the agent implemented as part of the
<http://johnpollock.us/ftp/OSCAR-web-page/oscar.html OSCAR Project>.

Oscar is (potentially) capable of

    * first-order theorem proving
    * defeasible reasoning
    * probabilistic reasoning
    * planning

Originally written in LISP, there are known bugs in Oscar's theorem-proving
engine as well as in its code for probabilistic reasoning. After John L.
Pollock's untimely death, one of his students, Martin Stone Davis (me), took
up the challenge to fix Oscar. I have elected to rewrite Oscar in Haskell, in
the hopes that Haskell's strong typing will facilitate writing a more robust
codebase.

-}

{- $WhatIsDefeasibleReasoning

Defeasible reasoning was pioneered by the original author, progenitor, and
brother of Oscar, John L. Pollock. I will illustrate it with an example.

__Seeing is believing?__

You see before you what appears to be a reddish-colored ball. Is it reasonable
for you to infer that there actually __is__ a red ball before you? Under what
circumstances is it not?

Perhaps you have rose-colored glasses on! If that were the case, you would
see a red ball even if the ball were white. Perhaps you recall that you
recently injested a strong hallucinogen. In that case, you would be
well-advised to mistrust almost all of your perceptions.

Reasoning defeasibly, you may make a __prima facie__ inference to the
conclusion that there is a red ball before you, allowing for the possibility
that that inference may later be undercut or rebutted.

Knowing that you are wearing rose-colored glasses gives you an
__undercutting defeater__ to link between the premise that the ball appears
to be red and the conclusion that the ball actually is red. Importantly, you
do not conclude that there is no ball or that the ball isn't red. You simply
withhold belief in the proposition that it is red.

There are also __rebutting defeaters__. Suppose Alice tells you that it's
raining. You consider Alice to be trustworthy and so infer that it's raining.
But then Bob tells you that it isn't. If you consider Bob to be equally as
trustworthy as Alice, your inference that it is raining is rebutted by another
inference that it is not raining.

-}

{- $ExampleOfProblem

Here is an example of a valid 'Problem', represented as a Text ⁞ ƮWithLineComments.

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
    bpf-reason_2:   {}  {C} ||=> ~R   strength = 1.0
    bpf-reason_3:   {B} {D} ||=> C    strength = 1.0

BACKWARDS CONCLUSIVE REASONS
    ; Each of these represents a 'ProblemBackwardsConclusiveReason'.
    bcon-reason_1:   {} {Q1 , Q2 , Q3} ||=> (Q1 & (Q2 & Q3))   strength = 1.0
@
-}

{- $ExampleOfFormula

An 'Formula' represents a superset of standard first-order logic.
In addition to quantification, conjunction, negation, etc., there are also
defeat relations between formulas and a unary "whether-or-not" operator.

Here are some examples:

@
    P                 ; a simple 'Predication'
    P a               ; predication of a constant
    P (g a) b         ; predication of a 'DomainFunction' of a constant
                      ; and another constant
    ~P                ; 'Negation'
    P v Q             ; 'Disjunction'
    P & Q             ; 'Conjunction'
    P -> Q            ; 'Conditional' (material implication)
    P \<-> Q           ; 'Biconditional'
    (all x)(P x)      ; a 'Universal' 'Quantifier'
    (some x)(P x)     ; an 'Existential' 'Quantifier'
    P @ Q             ; a 'Defeater', read as "P defeats Q"
    ?P                ; a 'Whether' operator
                      ; TODO Explain the semantics of this operator.
@

Since "v" is used as a symbol for disjunction, it may not be used as a
constant or quantification variable.
-}

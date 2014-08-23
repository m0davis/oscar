{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
-- {-# LANGUAGE DataKinds #-}

module Oscar.Main where

import Oscar.Main.Prelude

import Oscar.ProblemParser.Internal.Tags    (ƮProblemsWithLineComments)
import Oscar.Main.ProblemBase

import Oscar.Problem

combinedProblems ∷ FilePath ⁞ ƮProblemsWithLineComments
combinedProblems = ƭ $ fpFromString "combined-problems"

getBaseProblem ∷ Problem → Problem
getBaseProblem bp'@(BaseProblem _ _ _ _ _ _) = bp'
getBaseProblem _ = error "impossible? Problem does not match BaseProblem"

testProblemFromProblemParser ∷ Text ⁞ ƮProblemsWithLineComments
testProblemFromProblemParser = ƭ . pack $ "Problem #42 \n\
\Some description of this problem. \n\
\The description ends at the first section identifier. \n\
\A section identifier is a line containing one of the following bulleted items: \n\
\    * Given premises: \n\
\    * Ultimate epistemic interests: \n\
\    * FORWARDS PRIMA FACIE REASONS \n\
\    * FORWARDS CONCLUSIVE REASONS \n\
\    * BACKWARDS PRIMA FACIE REASONS \n\
\    * BACKWARDS CONCLUSIVE REASONS \n\
\ \n\
\Note that the section identifier is case sensitive.  \n\
\ \n\
\The premise and interest sections __must__ be present. No repeats of sections is allowed. \n\
\ \n\
\Given premises: \n\
\     ; This is a line comment. \n\
\     APremiseFormula       justification = 0.9 ; Note that justifications take on valid values between 0 (exclusive) and 1 (inclusive). \n\
\     AnotherPremiseFormula justification = 0.5 ; The names of premises are usually given by a single letter, but may be any sequence of alpha-numeric characters. \n\
\     BnotherPremiseFormula  \n\
\                     ; Newlines are ignored when reading formulas, so long formulas may be split \n\
\                     ; across lines, ending with its justification. \n\
\                     justification = 1.0 \n\
\Ultimate epistemic interests: \n\
\     J    interest = 1.0 ;  \n\
\     K    interest = 1.0 \n\
\     L    interest = 1.0 \n\
\ \n\
\    FORWARDS PRIMA FACIE REASONS \n\
\      pf-reason_1:   {A} ||=> D   strength = 1.0 \n\
\      pf-reason_2:   {D} ||=> G   strength = 1.0 \n\
\      pf-reason_3:   {B} ||=> ~D   strength = 1.0 \n\
\      pf-reason_4:   {C} ||=> F   strength = 1.0 \n\
\      pf-reason_5:   {I} ||=> L   strength = 1.0 \n\
\ \n\
\    FORWARDS CONCLUSIVE REASONS \n\
\      con-reason_1:   {G} ||=> J   strength = 1.0 \n\
\      con-reason_2:   {~D} ||=> H   strength = 1.0 \n\
\      con-reason_3:   {H} ||=> K   strength = 1.0 \n\
\      con-reason_4:   {F} ||=> I   strength = 1.0 \n\
\      con-reason_5:   {~D} ||=> M   strength = 1.0 \n\
\      con-reason_6:   {M} ||=> N   strength = 1.0 \n\
\      con-reason_7:   {N} ||=> (C @ F)   strength = 1.0 \n\
\      con-reason_8:   {F} ||=> (B @ ~D)   strength = 1.0 \n\
\ \n\
\    BACKWARDS PRIMA FACIE REASONS \n\
\      pf-reason_4:   {} {C} ||=> ~R   strength = 1.0 \n\
\      pf-reason_5:   {} {B} ||=> C   strength = 1.0 \n\
\ \n\
\    BACKWARDS CONCLUSIVE REASONS \n\
\      con-reason_11:   {} {Q1 , Q2 , Q3} ||=> (Q1 & (Q2 & Q3))   strength = 1.0 \n\
\"

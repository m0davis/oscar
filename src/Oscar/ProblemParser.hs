{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}

{- | __So, you want to write an OSCAR problem__

Documentation for ProblemParser



Here is an example of a valid Problem (i.e. @Text \⁞ [Problem]@)

@
Problem #42
Some description of this problem.
The description ends at the first section identifier.
A section identifier is a line containing one of the following bulleted items:
    * Given premises:
    * Ultimate epistemic interests:
    * FORWARDS PRIMA FACIE REASONS
    * FORWARDS CONCLUSIVE REASONS
    * BACKWARDS PRIMA FACIE REASONS
    * BACKWARDS CONCLUSIVE REASONS

Note that the section identifier is case sensitive. 

The premise and interest sections __must__ be present. No repeats of sections is allowed.

Given premises:
     ; This is a line comment.
     APremiseFormula       justification = 0.9 ; Note that justifications take on valid values between 0 (exclusive) and 1 (inclusive).
     AnotherPremiseFormula justification = 0.5 ; The names of premises are usually given by a single letter, but may be any sequence of alpha-numeric characters.
     AnotherPremiseFormula -> APremiseFormula 
                     ; Newlines are ignored when reading formulas, so long formulas may be split
                     ; across lines, ending with its justification.
                     justification = 1.0
Ultimate epistemic interests:
     J    interest = 1.0 ; 
     K    interest = 1.0
     L    interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      pf-reason_1:   {A} ||=> D   strength = 1.0
      pf-reason_2:   {D} ||=> G   strength = 1.0
      pf-reason_3:   {B} ||=> ~D   strength = 1.0
      pf-reason_4:   {C} ||=> F   strength = 1.0
      pf-reason_5:   {I} ||=> L   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      con-reason_1:   {G} ||=> J   strength = 1.0
      con-reason_2:   {~D} ||=> H   strength = 1.0
      con-reason_3:   {H} ||=> K   strength = 1.0
      con-reason_4:   {F} ||=> I   strength = 1.0
      con-reason_5:   {~D} ||=> M   strength = 1.0
      con-reason_6:   {M} ||=> N   strength = 1.0
      con-reason_7:   {N} ||=> (C @ F)   strength = 1.0
      con-reason_8:   {F} ||=> (B @ ~D)   strength = 1.0

    BACKWARDS PRIMA FACIE REASONS
      pf-reason_4:   {} {C} ||=> ~R   strength = 1.0
      pf-reason_5:   {} {B} ||=> C   strength = 1.0

    BACKWARDS CONCLUSIVE REASONS
      con-reason_11:   {} {Q1 , Q2 , Q3} ||=> (Q1 & (Q2 & Q3))   strength = 1.0
@


-}

module Oscar.ProblemParser (
    readFileProblems,
    readProblemsTextFile,
    ) where

import Oscar.Main.Prelude

import Oscar.ProblemParser.Internal     (partitionProblemsText)
import Oscar.ProblemParser.Internal     (problemFromText)
import Oscar.Problem                    (Problem)

-- | This is the highest-level problem decoder available in this module. Uses "readProblemsTextFile".
readFileProblems ∷ FilePath ⁞ [Problem] → IO [Problem]
readFileProblems = return . map problemFromText . partitionProblemsText <=< readProblemsTextFile

-- | Wrapper around "readFile".
readProblemsTextFile ∷ (FilePath ⁞ [Problem])  -- ^ The input file is presumed to represent one or more problems...
                     → IO (Text ⁞ [Problem])   -- ^ as 'Text'. 'IO' obtained via 'readFile'.
readProblemsTextFile = map ƭ . readFile . unƭ

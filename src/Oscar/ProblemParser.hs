{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}

{- | __So, you want to write an OSCAR problem__

Documentation for ProblemParser

Here is an example of a valid Problem (i.e. @'Text' '\(⁞)' 'ƮProblemsWithLineComments'@)

@
; This is a line comment, starting with a semicolon. All such comments are 
; ignored when parsing an Oscar 'Problem'.
Problem #42 ; The 'ProblemNumber' must be given as an integer.

Here is a 'ProblemDescription', which may be given starting on a line 
following the 'ProblemNumber'.

The description ends at the first 'Section' identifier (c.f. 'sectionParser').

A (case-sensitive) section identifier is a line containing __exactly one__ 
(sans whitespace) of the following bulleted items:
    * Ultimate epistemic interests:      ; (required)
    * Given premises:                    ; (optional)
    * FORWARDS PRIMA FACIE REASONS       ; (optional)
    * FORWARDS CONCLUSIVE REASONS        ; (optional)
    * BACKWARDS PRIMA FACIE REASONS      ; (optional)
    * BACKWARDS CONCLUSIVE REASONS       ; (optional)

No repeats of sections are allowed.

Given premises: ; Here's a section identifier. 
                ; Note that the "Given premises:" above in the description is 
                ; __not__ a Section identifier since it does not occur by 
                ; itself (it is preceded by a "*").
     ; A 'Premise' is a 'Formula' and a 'ProblemJustificationDegree'.
     TheCatIsOnTheMat       justification = 0.9
     TheMatIsOnTheFloor     justification = 0.5
     ~TheCatIsOnTheMat -> TheCatIsHungry
                     ; Newlines are ignored when reading formulas, so long formulas may be split
                     ; across lines, ending with its justification.
                     justification = 1.0

Ultimate epistemic interests:
     ; An 'Interest' is a 'Formula' and a 'ProblemInterestDegree'
     ~TheCatIsHungry v TheCatIsOnTheMat    interest = 1.0
     K v ~K                                interest = 1.0

    FORWARDS PRIMA FACIE REASONS
      ; A 'ProblemForwardsPrimaFacieReason' is a 'ProblemReasonName', a 'ForwardsReason', and a 'ProblemStrengthDegree'.
      pf-reason_1:   {A} ||=> D   strength = 1.0
      pf-reason_2:   {D} ||=> G   strength = 1.0
      pf-reason_3:   {B} ||=> ~D   strength = 1.0
      pf-reason_4:   {C} ||=> F   strength = 1.0
      pf-reason_5:   {I} ||=> L   strength = 1.0

    FORWARDS CONCLUSIVE REASONS
      ; A 'ProblemForwardsConclusiveReason' is similar to a prima facie one, except that 
      ; * its strength must be 1.0
      ; * it is treated differently from the perspective of defeasible reasoning.
      con-reason_1:   {G} ||=> J   strength = 1.0
      con-reason_2:   {~D} ||=> H   strength = 1.0
      con-reason_3:   {H} ||=> K   strength = 1.0
      con-reason_4:   {F} ||=> I   strength = 1.0
      con-reason_5:   {~D} ||=> M   strength = 1.0
      con-reason_6:   {M} ||=> N   strength = 1.0
      con-reason_7:   {N} ||=> (C \@ F)   strength = 1.0
      con-reason_8:   {F} ||=> (B \@ ~D)   strength = 1.0

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
    stripLineComments,
    ) where

import Oscar.Main.Prelude

import Data.List.Split                      (splitOn)

import Oscar.ProblemParser.Internal         (partitionProblemsText)
import Oscar.ProblemParser.Internal         (problemFromText)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemsWithLineComments)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemsWithoutLineComments)
import Oscar.Problem                        (Problem)

-- | This is the highest-level problem decoder available in this module. Uses "readProblemsTextFile".
readFileProblems ∷ FilePath ⁞ ƮProblemsWithLineComments → IO [Problem]
readFileProblems = return . map problemFromText . partitionProblemsText <=< readProblemsTextFile

-- | Wrapper around "readFile". Strips line comments.
readProblemsTextFile ∷ (FilePath ⁞ ƮProblemsWithLineComments)  -- ^ The input file is presumed to represent one or more problems...
                     → IO (Text ⁞ ƮProblemsWithoutLineComments)   -- ^ as 'Text'. 'IO' obtained via 'readFile'.
readProblemsTextFile = (map $ reƭ . stripLineComments . ƭ) . readFile . unƭ

stripLineComments ∷ Text ⁞ ƮProblemsWithLineComments → Text ⁞ ƮProblemsWithoutLineComments
stripLineComments = reƭ . map (unlines . map stripLineComment . lines)
  where
    stripLineComment ∷ Text → Text
    stripLineComment = pack . headEx . splitOn ";" . unpack

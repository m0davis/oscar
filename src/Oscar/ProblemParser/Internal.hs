{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal (
    -- * text of problems
    partitionProblemsText,
    -- * parsing problem parts
    statefulParseProblemNumber,
    statefulParseProblemDescription,
    problemSectionText,
    decodeGivenPremisesSection,
    decodeUltimateEpistemicInterestsSection,
    decodeForwardsPrimaFacieReasonSection,
    decodeForwardsConclusiveReasonSection,
    decodeBackwardsPrimaFacieReasonSection,
    decodeBackwardsConclusiveReasonSection,
    -- * Problem construction
    problemFromText,    
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Formula                                    (Formula)
import Oscar.FormulaParser                              (formulaFromText)
import Oscar.Problem                                    (LispPositiveDouble(LispPositiveDouble))
import Oscar.Problem                                    (Problem(Problem))
import Oscar.Problem                                    (ProblemBackwardsConclusiveReason)
import Oscar.Problem                                    (ProblemBackwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemDescription)
import Oscar.Problem                                    (ProblemForwardsConclusiveReason)
import Oscar.Problem                                    (ProblemForwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemInterest)
import Oscar.Problem                                    (ProblemJustificationDegree)
import Oscar.Problem                                    (ProblemNumber)
import Oscar.Problem                                    (ProblemPremise)
import Oscar.Problem                                    (ProblemStrengthDegree(ProblemStrengthDegree))
import Oscar.ProblemParser.Internal.ReasonSection       (ReasonSection)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemReasonName)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemReasonText)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemStrengthDegree)
import Oscar.ProblemParser.Internal.ReasonSection       (decodeReasonSection)
import Oscar.ProblemParser.Internal.ReasonSection       (getBackwardsReason)
import Oscar.ProblemParser.Internal.ReasonSection       (getForwardsReason)
import Oscar.ProblemParser.Internal.Section             (HasSection)
import Oscar.ProblemParser.Internal.Section             (Section)
import Oscar.ProblemParser.Internal.Section             (runSectionParser)
import Oscar.ProblemParser.Internal.Section             (section)
import Oscar.ProblemParser.Internal.Section             (sectionParser)
import Oscar.ProblemParser.Internal.StatefulParse       (parseProblemDescription)
import Oscar.ProblemParser.Internal.StatefulParse       (parseProblemNumber)
import Oscar.ProblemParser.Internal.StatefulParse       (runStatefulParse')
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(Conclusive))
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(PrimaFacie))
import Oscar.ProblemParser.Internal.Tags                (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags                (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags                (ƮGivenPremise)
import Oscar.ProblemParser.Internal.Tags                (ƮProblemAfterDescription)
import Oscar.ProblemParser.Internal.Tags                (ƮProblemAfterNumber)
import Oscar.ProblemParser.Internal.Tags                (ƮProblemAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags                (ƮReason)
import Oscar.ProblemParser.Internal.Tags                (ƮSection)
import Oscar.ProblemParser.Internal.Tags                (ƮUltimateEpistemicInterest)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemInterestDegree)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemJustificationDegree)

{- | Separate the text of concatenated problems. Each resulant problem starts after the number label, "Problem #". "ƮProblemAfterNumberLabel"

E.g., given this input

@
Problem #1
This is a case of collective rebutting defeat
Given premises:
     P    justification = 1.0
...etc...

Problem #2
Description of the second problem
...etc...
@

we get these outputs

@
1
This is a case of collective rebutting defeat
Given premises:
     P    justification = 1.0
...etc...
@
 
@
2
Description of the second problem
...etc...
@
-}
partitionProblemsText ∷ (Text ⁞ [Problem])                 -- ^ 'Text'ual 'Problem's, possibly obtained from 'readProblemsTextFile'
                      → [Text ⁞ ƮProblemAfterNumberLabel]  -- ^ Results in one 'Text' block for each 'Problem'.
partitionProblemsText = simpleParse (many p) . unƭ
  where
    p ∷ Parser (Text ⁞ ƮProblemAfterNumberLabel)
    p = do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP

    endP ∷ Parser ()
    endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

{- | E.g., given this input

@
1
This is a case of collective rebutting defeat
...etc...
@

we get this output:
@ 
 (1, \\nThis is a case of collective rebutting defeat\\n...etc...\\n) 
@
-}
statefulParseProblemNumber ∷ Text ⁞ ƮProblemAfterNumberLabel → (ProblemNumber, Text ⁞ ƮProblemAfterNumber)
statefulParseProblemNumber = runStatefulParse' parseProblemNumber

{- | E.g., given this input

@
This is a case of collective rebutting defeat
Given premises:
...etc...
@

we get this output:
@ 
 (This is a case of collective rebutting defeat, Given premises:\\n...etc...\\n) 
@
-}
statefulParseProblemDescription ∷ Text ⁞ ƮProblemAfterNumber → (ProblemDescription, Text ⁞ ƮProblemAfterDescription)
statefulParseProblemDescription = runStatefulParse' parseProblemDescription

{-
 | Gets the text of a particular section from all of the text following the description
 e.g. given the input @ Text ⁞ ƮProblemAfterDescription @:

@
Given premises:
     P    justification = 1.0
     A    justification = 1.0
Ultimate epistemic interests:
     R    interest = 1.0

   FORWARDS PRIMA FACIE REASONS
     pf-reason_1:   {P} ||=> Q   strength = 1.0
     pf-reason_2:   {Q} ||=> R   strength = 1.0
     pf-reason_3:   {C} ||=> ~R   strength = 1.0
     pf-reason_4:   {B} ||=> C   strength = 1.0
     pf-reason_5:   {A} ||=> B   strength = 1.0
@

we get the @ Text ⁞ ƮSection ƮGivenPremise @:

@
     P    justification = 1.0
     A    justification = 1.0
@

That's only if the returned kind is Text ⁞ ƮSection (ƮReason Forwards PrimaFacie), then the returned value is

@
     pf-reason_1:   {P} ||=> Q   strength = 1.0
     pf-reason_2:   {Q} ||=> R   strength = 1.0
     pf-reason_3:   {C} ||=> ~R   strength = 1.0
     pf-reason_4:   {B} ||=> C   strength = 1.0
     pf-reason_5:   {A} ||=> B   strength = 1.0
@
 
-}
problemSectionText ∷
    ∀ kind. (HasSection kind) ⇒
    Text ⁞ ƮProblemAfterDescription →
    Text ⁞ ƮSection kind
problemSectionText = ƭ . simpleParse p . unƭ
  where
    theSection ∷ Section
    theSection = section ((⊥) ∷ kind)

    p ∷ Parser Text 
    p = do
        _ ← manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== theSection) sectionParser)
        p' <|> pure (pack "")
      where
        p' ∷ Parser Text
        p' = do
            guardM (map (== theSection) sectionParser)
            pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))

{- | Examples

@
     P    justification = 1.0
     A    justification = 1.0
@

@
    [(\<formula for P>, \<justification 1.0>)
    ,(\<formula for A\>, \<justification 1.0>)
    ]
@
-}
decodeGivenPremisesSection ∷ Text ⁞ ƮSection ƮGivenPremise
                           → [ProblemPremise]
decodeGivenPremisesSection = runSectionParser p
  where
    p ∷ Parser (Formula, ProblemJustificationDegree)
    p = do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
        return (formulaFromText . pack $ t, d)

-- | similar to 'decodeGivenPremisesSection'
decodeUltimateEpistemicInterestsSection ∷ Text ⁞ ƮSection ƮUltimateEpistemicInterest
                                        → [ProblemInterest]
decodeUltimateEpistemicInterestsSection = runSectionParser $ do
    spaces
    (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
    return (formulaFromText . pack $ t, d)



-- | similar to 'decodeGivenPremisesSection'
decodeForwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards PrimaFacie) → [ProblemForwardsPrimaFacieReason]
decodeForwardsPrimaFacieReasonSection = map fpfrts . decodeReasonSection
  where
    fpfrts ∷ ReasonSection Forwards PrimaFacie → ProblemForwardsPrimaFacieReason
    fpfrts rb = (,,)
        (_rsProblemReasonName rb)
        (getForwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

-- | similar to "decodeGivenPremisesSection"
decodeForwardsConclusiveReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards Conclusive) → [ProblemForwardsConclusiveReason]
decodeForwardsConclusiveReasonSection = map fpfrts' . decodeReasonSection
  where
    fpfrts' ∷ ReasonSection Forwards Conclusive → ProblemForwardsConclusiveReason
    fpfrts' rb = case _rsProblemStrengthDegree rb of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getForwardsReason $ _rsProblemReasonText rb)

-- | similar to "decodeGivenPremisesSection"
decodeBackwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards PrimaFacie) → [ProblemBackwardsPrimaFacieReason]
decodeBackwardsPrimaFacieReasonSection = map bpfrts . decodeReasonSection
  where
    bpfrts ∷ ReasonSection Backwards PrimaFacie → ProblemBackwardsPrimaFacieReason
    bpfrts rb = (,,)
        (_rsProblemReasonName rb)
        (getBackwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

-- | similar to "decodeGivenPremisesSection"
decodeBackwardsConclusiveReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards Conclusive) → [ProblemBackwardsConclusiveReason]
decodeBackwardsConclusiveReasonSection = map bpfrts' . decodeReasonSection
  where
    bpfrts' ∷ ReasonSection Backwards Conclusive → ProblemBackwardsConclusiveReason
    bpfrts' rb = case (_rsProblemStrengthDegree rb) of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"

      where
        result = (,)
            (_rsProblemReasonName rb)
            (getBackwardsReason $ _rsProblemReasonText rb)


-- | The formatting of the input is documented here (TODO).
problemFromText ∷ (Text ⁞ ƮProblemAfterNumberLabel)  -- ^ possibly as obtained from 'partitionProblemsText'
                → Problem
problemFromText t = Problem
    number
    description
    (decodeGivenPremisesSection pSTaD)
    (decodeUltimateEpistemicInterestsSection pSTaD)
    (decodeForwardsPrimaFacieReasonSection pSTaD)
    (decodeForwardsConclusiveReasonSection pSTaD)
    (decodeBackwardsPrimaFacieReasonSection pSTaD)
    (decodeBackwardsConclusiveReasonSection pSTaD)
  where
    (number, afterNumber) = statefulParseProblemNumber t
    (description, afterDescription) = statefulParseProblemDescription afterNumber

    pSTaD ∷ (HasSection kind) ⇒ Text ⁞ ƮSection kind
    pSTaD = problemSectionText afterDescription

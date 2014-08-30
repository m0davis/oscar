{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal (
    -- * text of problems
    -- TODO partitionProblemsText,
    -- * parsing problem parts
    -- $StatefulParse
    -- problemSectionText,
    -- decodeGivenPremisesSection,
    -- decodeUltimateEpistemicInterestsSection,
    decodeForwardsPrimaFacieReasonSection,
    decodeForwardsConclusiveReasonSection,
    decodeBackwardsPrimaFacieReasonSection,
    decodeBackwardsConclusiveReasonSection,
    -- * Problem construction
    problemFromText,
    ) where

import Oscar.Main.Prelude

import Oscar.Problem                                    (LispPositiveDouble(LispPositiveDouble))
import Oscar.Problem                                    (Problem(Problem))
import Oscar.Problem                                    (ProblemBackwardsConclusiveReason)
import Oscar.Problem                                    (ProblemBackwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemForwardsConclusiveReason)
import Oscar.Problem                                    (ProblemForwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemStrengthDegree(ProblemStrengthDegree))
import Oscar.ProblemParser.Internal.ReasonSection       (ReasonSection)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemReasonName)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemReasonText)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemStrengthDegree)
import Oscar.ProblemParser.Internal.ReasonSection       (decodeReasonSection)
import Oscar.ProblemParser.Internal.ReasonSection       (getBackwardsReason)
import Oscar.ProblemParser.Internal.ReasonSection       (getForwardsReason)
import Oscar.ProblemParser.Internal.Section             (HasSection)
import Oscar.ProblemParser.Internal.StatefulParse       (runStatefulParser)
import Oscar.ProblemParser.Internal.StatefulParse       (evalStatefulParser)
import Oscar.ProblemParser.Internal.StatefulParse       (evalSectionWithStatefulParser)
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(Conclusive))
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(PrimaFacie))
import Oscar.ProblemParser.Internal.Tags                (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags                (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags                (ƮGivenPremise)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterDescription)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumber)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags                (ƮReason)
import Oscar.ProblemParser.Internal.Tags                (ƮSection)
import Oscar.ProblemParser.Internal.Tags                (ƮUltimateEpistemicInterest)

{- $StatefulParse

See "Oscar.ProblemParser.Internal.StatefulParse" for the polymorphic 
runStatefulParser, which can be used to obtain [Text ⁞ ƮAfterNumberLabel], 
'ProblemNumber', 'ProblemDescription', Text ⁞ ƮAfterDescription, and Text ⁞ 
ƮAfterNumber.
-}

-- | similar to 'TODO decodeGivenPremisesSection'
decodeForwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards PrimaFacie) → [ProblemForwardsPrimaFacieReason]
decodeForwardsPrimaFacieReasonSection = map fpfrts . decodeReasonSection
  where
    fpfrts ∷ ReasonSection Forwards PrimaFacie → ProblemForwardsPrimaFacieReason
    fpfrts rb = (,,)
        (_rsProblemReasonName rb)
        (getForwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

-- | similar to "TODO decodeGivenPremisesSection"
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

-- | similar to "TODO decodeGivenPremisesSection"
decodeBackwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards PrimaFacie) → [ProblemBackwardsPrimaFacieReason]
decodeBackwardsPrimaFacieReasonSection = map bpfrts . decodeReasonSection
  where
    bpfrts ∷ ReasonSection Backwards PrimaFacie → ProblemBackwardsPrimaFacieReason
    bpfrts rb = (,,)
        (_rsProblemReasonName rb)
        (getBackwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

-- | similar to "TODO decodeGivenPremisesSection"
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


{- | The formatting of the input is documented at "Oscar.Documentation".

The input must begin with the problem number (after the label, "Problem #")
-}
problemFromText ∷ (Text ⁞ ƮAfterNumberLabel)  -- ^ possibly as obtained from 'TODO partitionProblemsText'
                → Problem
problemFromText t = Problem
    number
    description
    (evalSectionWithStatefulParser (pSTaD :: Text ⁞ ƮSection ƮGivenPremise))
    (evalSectionWithStatefulParser (pSTaD :: Text ⁞ ƮSection ƮUltimateEpistemicInterest))
    (decodeForwardsPrimaFacieReasonSection pSTaD)
    (decodeForwardsConclusiveReasonSection pSTaD)
    (decodeBackwardsPrimaFacieReasonSection pSTaD)
    (decodeBackwardsConclusiveReasonSection pSTaD)
  where
    (number, (afterNumber ∷ Text ⁞ ƮAfterNumber)) = 
        runStatefulParser t
    (description, (afterDescription ∷ Text ⁞ ƮAfterDescription)) = 
        runStatefulParser afterNumber

    pSTaD ∷ (HasSection kind) ⇒ Text ⁞ ƮSection kind
    pSTaD = evalStatefulParser afterDescription

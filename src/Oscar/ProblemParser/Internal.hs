{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Oscar.ProblemParser.Internal (
    -- * text of problems
    -- TODO partitionProblemsText,
    -- * parsing problem parts
    -- $StatefulParse
    -- problemSectionText,
    -- decodeGivenPremisesSection,
    -- decodeUltimateEpistemicInterestsSection,
    -- decodeForwardsPrimaFacieReasonSection,
    -- decodeForwardsConclusiveReasonSection,
    -- decodeBackwardsPrimaFacieReasonSection,
    -- decodeBackwardsConclusiveReasonSection,
    -- * Problem construction
    problemFromText,
    -- * Helpers
    ReasonSectionDecoder(..),
    DecodeableSectionResult(..),
    evalReasonSectionWithStatefulParser,    
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
import Oscar.ProblemParser.Internal.ReasonSection       (getBackwardsReason)
import Oscar.ProblemParser.Internal.ReasonSection       (getForwardsReason)
--import Oscar.ProblemParser.Internal.Section             (HasSection)
import Oscar.ProblemParser.Internal.StatefulParse       (StatefulParser)
import Oscar.ProblemParser.Internal.StatefulParse       (runStatefulParser)
import Oscar.ProblemParser.Internal.StatefulParse       (evalStatefulParser)
import Oscar.ProblemParser.Internal.StatefulParse       (evalSectionWithStatefulParser)
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(Conclusive))
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(PrimaFacie))
import Oscar.ProblemParser.Internal.Tags                (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags                (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags                (ƮGivenPremise)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterDescription)
--import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumber)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags                (ƮReason)
import Oscar.ProblemParser.Internal.Tags                (ƮSection)
import Oscar.ProblemParser.Internal.Tags                (ƮUltimateEpistemicInterest)

import Oscar.Problem                                    (ProblemPremise)
import Oscar.Problem                                    (ProblemInterest)

{- $StatefulParse

See "Oscar.ProblemParser.Internal.StatefulParse" for the polymorphic 
runStatefulParser, which can be used to obtain [Text ⁞ ƮAfterNumberLabel], 
'ProblemNumber', 'ProblemDescription', Text ⁞ ƮAfterDescription, and Text ⁞ 
ƮAfterNumber.
-}

class ReasonSectionDecoder direction defeasibility decode | decode -> direction defeasibility where
    decodeReasonSection :: ReasonSection direction defeasibility -> decode

instance ReasonSectionDecoder Forwards PrimaFacie ProblemForwardsPrimaFacieReason where
    decodeReasonSection rb = (,,)
        (_rsProblemReasonName rb)
        (getForwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

instance ReasonSectionDecoder Forwards Conclusive ProblemForwardsConclusiveReason where
    decodeReasonSection rb = case _rsProblemStrengthDegree rb of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getForwardsReason $ _rsProblemReasonText rb)

instance ReasonSectionDecoder Backwards PrimaFacie ProblemBackwardsPrimaFacieReason where
    decodeReasonSection rb = (,,)
        (_rsProblemReasonName rb)
        (getBackwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

instance ReasonSectionDecoder Backwards Conclusive ProblemBackwardsConclusiveReason where
    decodeReasonSection rb = case (_rsProblemStrengthDegree rb) of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getBackwardsReason $ _rsProblemReasonText rb)

class DecodeableSectionResult decode where
    realSectionDecoder :: Text ⁞ ƮAfterDescription -> [decode]

instance DecodeableSectionResult ProblemPremise where
    realSectionDecoder t = evalSectionWithStatefulParser s
      where
        s :: Text ⁞ ƮSection ƮGivenPremise
        s = evalStatefulParser t

instance DecodeableSectionResult ProblemInterest where
    realSectionDecoder t = evalSectionWithStatefulParser st
      where
        st :: Text ⁞ ƮSection ƮUltimateEpistemicInterest
        st = evalStatefulParser t

instance DecodeableSectionResult ProblemForwardsPrimaFacieReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser st
      where
        st :: Text ⁞ ƮSection (ƮReason Forwards PrimaFacie)
        st = evalStatefulParser t

instance DecodeableSectionResult ProblemForwardsConclusiveReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser st
      where
        st :: Text ⁞ ƮSection (ƮReason Forwards Conclusive)
        st = evalStatefulParser t

instance DecodeableSectionResult ProblemBackwardsPrimaFacieReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser st
      where
        st :: Text ⁞ ƮSection (ƮReason Backwards PrimaFacie)
        st = evalStatefulParser t

instance DecodeableSectionResult ProblemBackwardsConclusiveReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser st
      where
        st :: Text ⁞ ƮSection (ƮReason Backwards Conclusive)
        st = evalStatefulParser t

-- | Uses 'simpleParse'.
evalReasonSectionWithStatefulParser ∷ ∀ direction defeasibility decode inSection.
    (StatefulParser (ReasonSection direction defeasibility) (ƮSection inSection) (), ReasonSectionDecoder direction defeasibility decode) ⇒ 
    Text ⁞ ƮSection inSection → [decode]
evalReasonSectionWithStatefulParser = map decodeReasonSection . evalSectionWithStatefulParser

{- | The formatting of the input is documented at "Oscar.Documentation".

The input must begin with the problem number (after the label, "Problem #")
-}
problemFromText ∷ (Text ⁞ ƮAfterNumberLabel)  -- ^ possibly as obtained from 'TODO partitionProblemsText'
                → Problem
problemFromText t = Problem
    number
    description
    (realSectionDecoder afterDescription)
    (realSectionDecoder afterDescription)
    (realSectionDecoder afterDescription)
    (realSectionDecoder afterDescription)
    (realSectionDecoder afterDescription)
    (realSectionDecoder afterDescription)
  where
    --(number, (afterNumber ∷ Text ⁞ ƮAfterNumber)) = 
    --    runStatefulParser t
    (number, afterNumber) = 
        runStatefulParser t
    --(description, (afterDescription ∷ Text ⁞ ƮAfterDescription)) = 
    --    runStatefulParser afterNumber
    (description, afterDescription) = 
        runStatefulParser afterNumber

    --pSTaD ∷ (HasSection kind) ⇒ Text ⁞ ƮSection kind
    --pSTaD = evalStatefulParser afterDescription

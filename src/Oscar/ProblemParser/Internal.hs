{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal (
    -- * Problem construction
    problemFromText,
    -- * Helpers
    -- $StatefulParse
    StatefulParser(..),
    ReasonSectionDecoder(..),
    DecodeableSectionResult(..),
    runStatefulParser,
    evalStatefulParser,
    evalSectionWithStatefulParser,
    evalReasonSectionWithStatefulParser,    
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.FormulaParser                              (formulaFromText)
import Oscar.Problem                                    (LispPositiveDouble(LispPositiveDouble))
import Oscar.Problem                                    (Problem(Problem))
import Oscar.Problem                                    (ProblemBackwardsConclusiveReason)
import Oscar.Problem                                    (ProblemBackwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemDescription(ProblemDescription))
import Oscar.Problem                                    (ProblemForwardsConclusiveReason)
import Oscar.Problem                                    (ProblemForwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemInterest)
import Oscar.Problem                                    (ProblemNumber(ProblemNumber))
import Oscar.Problem                                    (ProblemPremise)
import Oscar.Problem                                    (ProblemStrengthDegree(ProblemStrengthDegree))
import Oscar.ProblemParser.Internal.ReasonSection       (ReasonSection)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemReasonName)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemReasonText)
import Oscar.ProblemParser.Internal.ReasonSection       (_rsProblemStrengthDegree)
import Oscar.ProblemParser.Internal.ReasonSection       (getBackwardsReason)
import Oscar.ProblemParser.Internal.ReasonSection       (getForwardsReason)
import Oscar.ProblemParser.Internal.ReasonSection       (parserProblemReasonName)
import Oscar.ProblemParser.Internal.ReasonSection       (parserProblemVariablesText)
import Oscar.ProblemParser.Internal.Section             (HasSection)
import Oscar.ProblemParser.Internal.Section             (Section)
import Oscar.ProblemParser.Internal.Section             (section)
import Oscar.ProblemParser.Internal.Section             (sectionParser)
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(Conclusive))
import Oscar.ProblemParser.Internal.Tags                (Defeasibility(PrimaFacie))
import Oscar.ProblemParser.Internal.Tags                (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags                (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags                (ƮAfterDescription)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumber)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags                (ƮGivenPremise)
import Oscar.ProblemParser.Internal.Tags                (ƮReason)
import Oscar.ProblemParser.Internal.Tags                (ƮSection)
import Oscar.ProblemParser.Internal.Tags                (ƮUltimateEpistemicInterest)
import Oscar.ProblemParser.Internal.Tags                (ƮVariables)
import Oscar.ProblemParser.Internal.Tags                (ƮWithoutLineComments)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemInterestDegree)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemJustificationDegree)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemStrengthDegree)

{- $StatefulParse

See 'runStatefulParser', which can be used to obtain 
[Text ⁞ ƮAfterNumberLabel], 'ProblemNumber', 'ProblemDescription', 
Text ⁞ ƮAfterDescription, and Text ⁞ ƮAfterNumber.
-}

class StatefulParser a inState outState | a inState -> outState where
    statefulParser ∷ Parser a ⁞ (inState, outState)

{- | ƮAfterNumberLabel = after the "Problem #"

Sample Input

@
\"1 \\n Description\\n...etc...\\n"
@

Sample Output

@
(1, \" \\n Description\\n...etc...\\n")
@
-}
instance StatefulParser ProblemNumber ƮAfterNumberLabel ƮAfterNumber where
    statefulParser = ƭ $ ProblemNumber . read <$>
        manyTill anyChar (lookAhead . try $ space)

{- | ƮAfterNumber = immediately after the integer after "Problem #".

Sample Input

@

Description

Given premises:
...etc...
@

Sample Output

@
("Description", "Given premises:\\n...etc...\\n")
@
-}
instance StatefulParser ProblemDescription ƮAfterNumber ƮAfterDescription where
    statefulParser = ƭ $ spaces >> ProblemDescription . pack <$>
        (try emptyDescription <|> filledDescription)
      where
        emptyDescription = do
            manyTill space (lookAhead . try $ sectionParser >> manyTill space newline)
        filledDescription = do
            manyTill anyChar $ lookAhead . try $ manyTill space newline >> spaces >> sectionParser  >> manyTill space newline

{- | Separate the text of concatenated problems. Each resulant problem starts
     after the number label, \"Problem #". 'ƮAfterNumberLabel'

Sample input

@
Problem #1
Description of the first problem
Given premises:
     P    justification = 1.0
...etc...

Problem #2
Description of the second problem
...etc...
@

Sample outputs

@
1
Description of the first problem
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
instance StatefulParser [Text ⁞ ƮAfterNumberLabel] ƮWithoutLineComments () where
    statefulParser = ƭ . many $ do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP
      where
        endP ∷ Parser ()
        endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

{- | Gets the text of a particular section from all of the text following the
     description.

Sample Input

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

Sample Output (with kind = ƮGivenPremise):

@
     P    justification = 1.0
     A    justification = 1.0
@

Sample Output (with kind = ƮReason Forwards PrimaFacie):

@
     pf-reason_1:   {P} ||=> Q   strength = 1.0
     pf-reason_2:   {Q} ||=> R   strength = 1.0
     pf-reason_3:   {C} ||=> ~R   strength = 1.0
     pf-reason_4:   {B} ||=> C   strength = 1.0
     pf-reason_5:   {A} ||=> B   strength = 1.0
@
-}
instance ∀ kind. (HasSection kind) ⇒ StatefulParser (Text ⁞ ƮSection kind) ƮAfterDescription () where
    statefulParser = ƭ $ do
        _ ← manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== theSection) sectionParser)
        p' <|> pure (ƭ $ pack "")
      where
        p' ∷ Parser (Text ⁞ ƮSection kind)
        p' = do
            guardM (map (== theSection) sectionParser)
            ƭ . pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))

        theSection ∷ Section
        theSection = section ((⊥) ∷ kind)

{- |

Sample Input (possibly obtained from 'TODO problemSectionText')

@
     P    justification = 1.0
     A    justification = 1.0
@

Sample Output

@
    [(\<formula for P>, \<justification 1.0>)
    ,(\<formula for A\>, \<justification 1.0>)
    ]
@
-}
instance StatefulParser ProblemPremise (ƮSection ƮGivenPremise) () where
    statefulParser = ƭ $ do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
        return (formulaFromText . pack $ t, d)

-- | similar to 'TODO decodeGivenPremisesSection'
instance StatefulParser ProblemInterest (ƮSection ƮUltimateEpistemicInterest) () where
    statefulParser = ƭ $ do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
        return (formulaFromText . pack $ t, d)

instance StatefulParser (ReasonSection direction defeasibility) (ƮSection (ƮReason direction defeasibility)) () where
    statefulParser = ƭ $ do
        n ← parserProblemReasonName
        spaces
        (t, (v, d)) ← many anyChar `precededBy` p'
        return $ (,,,) n (ƭ . (pack ∷ String → Text) $ t) v d
      where
        p' ∷ Parser (Text ⁞ ƮVariables, ProblemStrengthDegree)
        p' = do
            t ← parserProblemVariablesText
            d ← parserProblemStrengthDegree
            return (t, d)

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
    realSectionDecoder t = evalSectionWithStatefulParser s
      where
        s :: Text ⁞ ƮSection ƮUltimateEpistemicInterest
        s = evalStatefulParser t

instance DecodeableSectionResult ProblemForwardsPrimaFacieReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser s
      where
        s :: Text ⁞ ƮSection (ƮReason Forwards PrimaFacie)
        s = evalStatefulParser t

instance DecodeableSectionResult ProblemForwardsConclusiveReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser s
      where
        s :: Text ⁞ ƮSection (ƮReason Forwards Conclusive)
        s = evalStatefulParser t

instance DecodeableSectionResult ProblemBackwardsPrimaFacieReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser s
      where
        s :: Text ⁞ ƮSection (ƮReason Backwards PrimaFacie)
        s = evalStatefulParser t

instance DecodeableSectionResult ProblemBackwardsConclusiveReason where
    realSectionDecoder t = evalReasonSectionWithStatefulParser s
      where
        s :: Text ⁞ ƮSection (ƮReason Backwards Conclusive)
        s = evalStatefulParser t

-- | Uses 'simpleParse'.
runStatefulParser ∷ ∀ a inState outState.
    (StatefulParser a inState outState) ⇒ Text ⁞ inState → (a, Text ⁞ outState)
runStatefulParser = simpleParse p' . unƭ
  where
    p' ∷ Parser (a, Text ⁞ outState)
    p' = do
        v ← unƭ (statefulParser ∷ Parser a ⁞ (inState, outState))
        r ← pack <$> many anyChar
        return (v, ƭ r)

-- | Uses 'simpleParse'.
evalStatefulParser ∷ ∀ a inState.
    (StatefulParser a inState ()) ⇒ Text ⁞ inState → a
evalStatefulParser = simpleParse p' . unƭ
  where
    p' ∷ Parser a
    p' = unƭ (statefulParser ∷ Parser a ⁞ (inState, ()))

-- | Uses 'simpleParse'.
evalSectionWithStatefulParser ∷ ∀ a inSection.
    (StatefulParser a (ƮSection inSection) ()) ⇒ Text ⁞ ƮSection inSection → [a]
evalSectionWithStatefulParser = simpleParse (many (try p') <* many space <* eof) . unƭ
  where
    p' ∷ Parser a
    p' = unƭ (statefulParser ∷ Parser a ⁞ (ƮSection inSection, ()))

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
    (number     , afterNumber     ) = runStatefulParser t
    (description, afterDescription) = runStatefulParser afterNumber

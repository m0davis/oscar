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
    -- * Parsing with type-level safety
    -- $StatefulParse
    StatefullyParsed(..),
    FromReasonSection(..),
    SectionElement(..),
    runStatefulParser,
    evalStatefulParser,
    evalStatefulParserOnSection,
    evalReasonSection,    
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

{- | The formatting of the input is documented at "Oscar.Documentation".

The input must begin at the problem number (after the label, \"Problem #\").
-}
problemFromText ∷ (Text ⁞ ƮAfterNumberLabel)  -- ^ possibly as obtained from 'evalStatefulParser'
                → Problem
problemFromText t = Problem
    number
    description
    (sectionElements afterDescription)
    (sectionElements afterDescription)
    (sectionElements afterDescription)
    (sectionElements afterDescription)
    (sectionElements afterDescription)
    (sectionElements afterDescription)
  where
    (number     , afterNumber     ) = runStatefulParser t
    (description, afterDescription) = runStatefulParser afterNumber

{- | Using a 'Parser' can be tricky because nothing in the type signature
     tells what sort of input it is meant to be applied to (excepting that it
     is 'Text'), nor does it tell us what sort of state the input is in
     after applying the parser. 'StatefullyParsed' allows us to define a
     parsed type with respect to these states, giving us a measure of safety
     at the type level.

     By convention, () is used as the outState when .
-}
class StatefullyParsed a inState outState | a → inState outState where
    statefulParser ∷ Parser a ⁞ (inState, outState)

{- | Separate the text of concatenated problems. Each resulant problem starts
     after the number label, \"Problem #\".
-}
instance StatefullyParsed [Text ⁞ ƮAfterNumberLabel]
                          ƮWithoutLineComments
                          ()
  where
    statefulParser = ƭ . many $ do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP
      where
        endP ∷ Parser ()
        endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

{- | Given text starting immediately after the number label, parse a 
     'ProblemNumber'. The parser\'s input then starts immediately after the 
     number.
-}
instance StatefullyParsed ProblemNumber 
                          ƮAfterNumberLabel 
                          ƮAfterNumber 
  where
    statefulParser = ƭ $ ProblemNumber . read <$>
        manyTill anyChar (lookAhead . try $ space)

{- | Given text starting immediately after the problem number, parse a
     'ProblemDescription'. The parser\'s input then starts immediately after
     the description.
-}
instance StatefullyParsed ProblemDescription 
                          ƮAfterNumber 
                          ƮAfterDescription 
  where                        
    statefulParser = ƭ $ spaces >> ProblemDescription . pack <$>
        (try emptyDescription <|> filledDescription)
      where
        emptyDescription = do
            manyTill space (lookAhead . try $ sectionParser >> manyTill space newline)
        filledDescription = do
            manyTill anyChar $ lookAhead . try $ manyTill space newline >> spaces >> sectionParser  >> manyTill space newline

{- | Given text starting immediately after the problem description, parse
     a text block consisting of a particular section, not including the
     section label.

Sample parser input Text ⁞ ƮAfterDescription:

@
Given premises:
     A    justification = 1.0
     B    justification = 1.0
Ultimate epistemic interests:
     C    interest = 1.0

   FORWARDS PRIMA FACIE REASONS
     fpf-reason_1:   {A, B} ||=> C   strength = 1.0
@

Sample Output (with kind = ƮGivenPremise):

@
     A    justification = 1.0
     B    justification = 1.0
@

Sample Output (with kind = ƮUltimateEpistemicInterest):

@
     C    interest = 1.0
@

Sample Output (with kind = ƮReason Forwards PrimaFacie):

@
     fpf-reason_1:   {A, B} ||=> C   strength = 1.0
@
-}
instance ∀ kind. (HasSection kind) ⇒ StatefullyParsed (Text ⁞ ƮSection kind) 
                                                      ƮAfterDescription
                                                      ()
  where
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

{- | Given the text of the section containing the \"Given Premises:\",
     parse 

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
instance StatefullyParsed ProblemPremise 
                          (ƮSection ƮGivenPremise)
                          ()
  where
    statefulParser = ƭ $ do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
        return (formulaFromText . pack $ t, d)

-- | similar to 'TODO decodeGivenPremisesSection'
instance StatefullyParsed ProblemInterest
                          (ƮSection ƮUltimateEpistemicInterest)
                          ()
  where
    statefulParser = ƭ $ do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
        return (formulaFromText . pack $ t, d)

instance StatefullyParsed (ReasonSection direction defeasibility)
                          (ƮSection (ƮReason direction defeasibility))
                          ()
  where
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

class FromReasonSection to fromDirection fromDefeasibility | to → fromDirection fromDefeasibility where
    fromReasonSection ∷ ReasonSection fromDirection fromDefeasibility → to

instance FromReasonSection ProblemForwardsPrimaFacieReason Forwards PrimaFacie where
    fromReasonSection rb = (,,)
        (_rsProblemReasonName rb)
        (getForwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

instance FromReasonSection ProblemForwardsConclusiveReason Forwards Conclusive where
    fromReasonSection rb = case _rsProblemStrengthDegree rb of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getForwardsReason $ _rsProblemReasonText rb)

instance FromReasonSection ProblemBackwardsPrimaFacieReason Backwards PrimaFacie where
    fromReasonSection rb = (,,)
        (_rsProblemReasonName rb)
        (getBackwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

instance FromReasonSection ProblemBackwardsConclusiveReason Backwards Conclusive where
    fromReasonSection rb = case (_rsProblemStrengthDegree rb) of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getBackwardsReason $ _rsProblemReasonText rb)

class SectionElement element where
    sectionElements ∷ Text ⁞ ƮAfterDescription → [element]

instance SectionElement ProblemPremise where
    sectionElements t = evalStatefulParserOnSection s
      where
        s ∷ Text ⁞ ƮSection ƮGivenPremise
        s = evalStatefulParser t

instance SectionElement ProblemInterest where
    sectionElements t = evalStatefulParserOnSection s
      where
        s ∷ Text ⁞ ƮSection ƮUltimateEpistemicInterest
        s = evalStatefulParser t

instance SectionElement ProblemForwardsPrimaFacieReason where
    sectionElements t = evalReasonSection s
      where
        s ∷ Text ⁞ ƮSection (ƮReason Forwards PrimaFacie)
        s = evalStatefulParser t

instance SectionElement ProblemForwardsConclusiveReason where
    sectionElements t = evalReasonSection s
      where
        s ∷ Text ⁞ ƮSection (ƮReason Forwards Conclusive)
        s = evalStatefulParser t

instance SectionElement ProblemBackwardsPrimaFacieReason where
    sectionElements t = evalReasonSection s
      where
        s ∷ Text ⁞ ƮSection (ƮReason Backwards PrimaFacie)
        s = evalStatefulParser t

instance SectionElement ProblemBackwardsConclusiveReason where
    sectionElements t = evalReasonSection s
      where
        s ∷ Text ⁞ ƮSection (ƮReason Backwards Conclusive)
        s = evalStatefulParser t

{- | Runs an appropriate 'statefulParser' on the given input, returning the
     successfully parsed value and the remainder of the input after the parse.

Pseudocode Example

@
runStatefulParser (\"1 \\n Description\\n...etc...\\n" :: Text ⁞ ƮAfterNumberLabel)

==

(1                                   :: ProblemNumber
,\" \\n Description\\n...etc...\\n"  :: Text ⁞ ƮAfterNumber
)
@
-}
runStatefulParser ∷ ∀ a inState outState.
    (StatefullyParsed a inState outState) ⇒ 
    Text ⁞ inState → (a, Text ⁞ outState)
runStatefulParser = simpleParse p' . unƭ
  where
    p' ∷ Parser (a, Text ⁞ outState)
    p' = do
        v ← unƭ (statefulParser ∷ Parser a ⁞ (inState, outState))
        r ← pack <$> many anyChar
        return (v, ƭ r)

evalStatefulParser ∷ ∀ a inState.
    (StatefullyParsed a inState ()) ⇒ 
    Text ⁞ inState → a
evalStatefulParser = fst . runStatefulParser

-- | Uses 'simpleParse'.
evalSqqtatefulParserOnSection ∷ 
    ∀ a inSection. (StatefullyParsed a (ƮSection inSection) ()) 
    ⇒ Text ⁞ ƮSection inSection 
    → [a]
evalStatefulParserOnSection = simpleParse (many (try p') <* many space <* eof) . unƭ
  where
    p' ∷ Parser a
    p' = unƭ (statefulParser ∷ Parser a ⁞ (ƮSection inSection, ()))

-- | Uses 'simpleParse'.
evalReasonSection ∷ 
    (StatefullyParsed (ReasonSection direction defeasibility) (ƮSection inSection) ()
    ,FromReasonSection decode direction defeasibility
    ) ⇒ 
    Text ⁞ ƮSection inSection → [decode]
evalReasonSection = map fromReasonSection . evalStatefulParserOnSection

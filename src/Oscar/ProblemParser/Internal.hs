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
    SectionElement(..),
    runStatefulParser,
    evalStatefulParser,
    evalStatefulParserOnSection,
    evalReasonSection,    
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.FormulaParser                              (formulaFromText)
import Oscar.Problem                                    (Problem(Problem))
import Oscar.Problem                                    (ProblemBackwardsConclusiveReason)
import Oscar.Problem                                    (ProblemBackwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemDescription(ProblemDescription))
import Oscar.Problem                                    (ProblemForwardsConclusiveReason)
import Oscar.Problem                                    (ProblemForwardsPrimaFacieReason)
import Oscar.Problem                                    (ProblemInterest)
import Oscar.Problem                                    (ProblemNumber(ProblemNumber))
import Oscar.Problem                                    (ProblemPremise)
import Oscar.Problem                                    (ProblemStrengthDegree)
import Oscar.ProblemParser.Internal.ReasonSection       (FromReasonSection(fromReasonSection))
import Oscar.ProblemParser.Internal.ReasonSection       (ReasonSection)
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
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumber)
import Oscar.ProblemParser.Internal.Tags                (ƮAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags                (ƮBeginningOfSections)
import Oscar.ProblemParser.Internal.Tags                (ƮGivenPremise)
import Oscar.ProblemParser.Internal.Tags                (ƮReason)
import Oscar.ProblemParser.Internal.Tags                (ƮSection)
import Oscar.ProblemParser.Internal.Tags                (ƮUltimateEpistemicInterest)
import Oscar.ProblemParser.Internal.Tags                (ƮVariables)
import Oscar.ProblemParser.Internal.Tags                (ƮWithoutLineComments)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemInterestDegree)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemJustificationDegree)
import Oscar.ProblemParser.Internal.UnitIntervalParsers (parserProblemStrengthDegree)

{- | The formatting of the input is documented at "Oscar.Documentation". -}
problemFromText ∷ (Text ⁞ ƮAfterNumberLabel)  -- ^ The input must begin at the problem number (after the label, \"Problem #\"). Possibly as obtained from 'evalStatefulParser'.
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

     An instance may be invoked with 'runStatefulParser'.

     Sometimes we care only about the state prior to parsing, and don\'t need 
     type-level safety on the state afterwards. By convention, in those cases, 
     () is used as the outState.
-}
class StatefullyParsed a inState outState | a → inState outState where
    statefulParser ∷ Parser a ⁞ (inState, outState)

{- | Separate the text of concatenated problems. Each resulant problem starts
     after the number label, \"Problem #\".

Sample input (a Text ⁞ ƮWithoutLineComments, possibly obtained from 
'Oscar.ProblemParser.stripLineComments'):

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

Sample outputs (obtained from 'evalStatefulParser'):

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
     'ProblemDescription'. The parser\'s input then starts at the beginning
     of the first 'Section' identifier (or at 'eof' if there are no such 
     identifiers).

     The resultant description is trimmed of whitespace.

__Example__

Input text (ƮAfterNumber)

@
    some description

Given premises:
...etc...
@

Parsed output (ProblemDescription)

@
some description
@

Input state after parsing (ƮBeginningOfSections)

@
Given premises:
...etc...
@
-}
instance StatefullyParsed ProblemDescription 
                          ƮAfterNumber 
                          ƮBeginningOfSections 
  where                        
    statefulParser = ƭ $ do 
        -- Collect any remaining whitespace up to a newline
        _ <- manyTill (notFollowedBy newline *> space) newline
        
        -- left-trim whitespace in the description
        spaces -- (*) see below

        {- parse the description, skipping any following whitespace, so that
           we end up at the beginning of the first section
        -}
        (ProblemDescription . pack <$> description) <* spaces
      where
        description = emptyDescription <|> otherDescription
          where
            {- We've already skipped spaces in (*) above, so if we immediately
               find ourselves at an apparent 'Section' identifier, the
               the description must be empty.
            -}
            emptyDescription = atSectionFollowedByNewline *> pure ""

            {- The description might yet still be empty and not parsed by
               'emptyDescription' if there is an additional newline after the
               problem number. E.g.

               @
               Problem #42

               Given premises:
               ...etc...
               @

               The above description would be successfully parsed as "" by 
               'otherDescription'.
            -}
            otherDescription = manyTill anyChar atSectionAloneOnItsOwnLine

            atSectionFollowedByNewline = lookAhead . try $ do
                _ <- sectionParser 
                _ <- manyTill space newline
                return ()

            atSectionAloneOnItsOwnLine = lookAhead . try $ do
                _ <- manyTill space newline
                spaces 
                atSectionFollowedByNewline
                return ()

{- | Given text starting immediately at the beginning of the first 'Section'
     identifier, parse a text block consisting of a particular section, not 
     including the section identifier.

Sample parser input, Text ⁞ ƮBeginningOfSections:

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
                                                      ƮBeginningOfSections
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
     parse a 'ProblemPremise'. Invoke this instance with 
     'evalStatefulParserOnSection' to obtain all of the premises.

Sample Input (a Text ƮSection ⁞ ƮGivenPremise resulting from another 
'StatefullyParsed' instance):

@
     P    justification = 1.0
     A    justification = 1.0
@

Sample Output (obtained from 'evalStatefulParserOnSection'):

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

-- | similar to the 'ProblemPremise' instance
instance StatefullyParsed ProblemInterest
                          (ƮSection ƮUltimateEpistemicInterest)
                          ()
  where
    statefulParser = ƭ $ do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
        return (formulaFromText . pack $ t, d)

-- | similar to the 'ProblemPremise' instance
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

{- | Defines a set of elements found at the ƮBeginningOfSections. -}
class SectionElement element where
    sectionElements ∷ Text ⁞ ƮBeginningOfSections → [element]

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

(1                                   :: ProblemNumber
,\" \\n Description\\n...etc...\\n"  :: Text ⁞ ƮAfterNumber
)
@
-}
runStatefulParser ∷ ∀ a inState outState.
    (StatefullyParsed a inState outState) ⇒ 
    Text ⁞ inState → (a, Text ⁞ outState)
runStatefulParser = simpleParse p . unƭ
  where
    p ∷ Parser (a, Text ⁞ outState)
    p = do
        v ← unƭ (statefulParser ∷ Parser a ⁞ (inState, outState))        
        r ← getInput
        return (v, ƭ r)

{- | Returns only the first component of 'runStatefulParser'. The 
     'StatefullyParsed' outState is restricted to () to avoid mistakenly
     ignoring relevant text following the parsed value.
-}
evalStatefulParser ∷ ∀ a inState.
    (StatefullyParsed a inState ()) ⇒ 
    Text ⁞ inState → a
evalStatefulParser = fst . runStatefulParser

{- | Special handling for 'ƮSection's. -}
evalStatefulParserOnSection ∷ 
    ∀ a inSection. (StatefullyParsed a (ƮSection inSection) ()) 
    ⇒ Text ⁞ ƮSection inSection 
    → [a]
evalStatefulParserOnSection = simpleParse (many (try p) <* many space <* eof) . unƭ
  where
    p ∷ Parser a
    p = unƭ (statefulParser ∷ Parser a ⁞ (ƮSection inSection, ()))

{- | Special handling for 'ƮSection's associated with reasons. -}
evalReasonSection ∷ 
    (StatefullyParsed (ReasonSection direction defeasibility) (ƮSection inSection) ()
    ,FromReasonSection decode direction defeasibility
    ) ⇒ 
    Text ⁞ ƮSection inSection → [decode]
evalReasonSection = map fromReasonSection . evalStatefulParserOnSection

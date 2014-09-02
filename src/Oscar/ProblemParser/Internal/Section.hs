{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | Relating to any of the six possible sections of a 'Problem'. See
     "Oscar.Documentation".
-}

module Oscar.ProblemParser.Internal.Section (
    Section(..),
    HasSection(..),
    sectionParser,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.ProblemParser.Internal.Tags    (ƮGivenPremise)
import Oscar.ProblemParser.Internal.Tags    (ƮUltimateEpistemicInterest)
import Oscar.ProblemParser.Internal.Tags    (ƮReason)
import Oscar.ProblemParser.Internal.Tags    (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags    (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags    (Defeasibility(PrimaFacie))
import Oscar.ProblemParser.Internal.Tags    (Defeasibility(Conclusive))

data Section
    = Section'GivenPremises               -- ^ "Given premises:"               
    | Section'UltimateEpistemicInterests  -- ^ "Ultimate epistemic interests:" 
    | Section'ForwardsPrimaFacieReasons   -- ^ "FORWARDS PRIMA FACIE REASONS"  
    | Section'ForwardsConclusiveReasons   -- ^ "FORWARDS CONCLUSIVE REASONS"   
    | Section'BackwardsPrimaFacieReasons  -- ^ "BACKWARDS PRIMA FACIE REASONS" 
    | Section'BackwardsConclusiveReasons  -- ^ "BACKWARDS CONCLUSIVE REASONS"  
  deriving (Eq, Show)

class HasSection s where
    -- |
    section ∷ s → Section

instance HasSection ƮGivenPremise                  where section _ = Section'GivenPremises
instance HasSection ƮUltimateEpistemicInterest     where section _ = Section'UltimateEpistemicInterests
instance HasSection (ƮReason Forwards  PrimaFacie) where section _ = Section'ForwardsPrimaFacieReasons
instance HasSection (ƮReason Forwards  Conclusive) where section _ = Section'ForwardsConclusiveReasons
instance HasSection (ƮReason Backwards PrimaFacie) where section _ = Section'BackwardsPrimaFacieReasons
instance HasSection (ƮReason Backwards Conclusive) where section _ = Section'BackwardsConclusiveReasons

sectionParser ∷ Parser Section
sectionParser =
    empty
    <|> "Given premises:"               ↦ Section'GivenPremises
    <|> "Ultimate epistemic interests:" ↦ Section'UltimateEpistemicInterests
    <|> "FORWARDS PRIMA FACIE REASONS"  ↦ Section'ForwardsPrimaFacieReasons
    <|> "FORWARDS CONCLUSIVE REASONS"   ↦ Section'ForwardsConclusiveReasons
    <|> "BACKWARDS PRIMA FACIE REASONS" ↦ Section'BackwardsPrimaFacieReasons
    <|> "BACKWARDS CONCLUSIVE REASONS"  ↦ Section'BackwardsConclusiveReasons
  where
    (↦) ∷ String → a → Parser a
    s ↦ t = try (string s) *> pure t

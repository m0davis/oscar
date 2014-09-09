{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | Relating to any of the six possible sections of a 'Problem'. See
     "Oscar.Documentation".
-}

module Oscar.ProblemParser.Internal.SectionName (
    SectionName(..),
    HasSectionName(..),
    parserSectionName,
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


data SectionName
    -- TODO is there any better way? I want to avoid this apostrophe ugliness.
    = SectionName'GivenPremises               -- ^ "Given premises:"
    | SectionName'UltimateEpistemicInterests  -- ^ "Ultimate epistemic interests:"
    | SectionName'ForwardsPrimaFacieReasons   -- ^ "FORWARDS PRIMA FACIE REASONS"
    | SectionName'ForwardsConclusiveReasons   -- ^ "FORWARDS CONCLUSIVE REASONS"
    | SectionName'BackwardsPrimaFacieReasons  -- ^ "BACKWARDS PRIMA FACIE REASONS"
    | SectionName'BackwardsConclusiveReasons  -- ^ "BACKWARDS CONCLUSIVE REASONS"
  deriving (Eq, Show)

class HasSectionName s where
    section ∷ s → SectionName

instance HasSectionName ƮGivenPremise                  where section _ = SectionName'GivenPremises
instance HasSectionName ƮUltimateEpistemicInterest     where section _ = SectionName'UltimateEpistemicInterests
instance HasSectionName (ƮReason Forwards  PrimaFacie) where section _ = SectionName'ForwardsPrimaFacieReasons
instance HasSectionName (ƮReason Forwards  Conclusive) where section _ = SectionName'ForwardsConclusiveReasons
instance HasSectionName (ƮReason Backwards PrimaFacie) where section _ = SectionName'BackwardsPrimaFacieReasons
instance HasSectionName (ƮReason Backwards Conclusive) where section _ = SectionName'BackwardsConclusiveReasons

{- | Consumes the 'SectionName', or nothing if the parse fails. -}
parserSectionName ∷ Parser SectionName
parserSectionName = try $
    empty
    <|> "Given premises:"               ↦ SectionName'GivenPremises
    <|> "Ultimate epistemic interests:" ↦ SectionName'UltimateEpistemicInterests
    <|> "FORWARDS PRIMA FACIE REASONS"  ↦ SectionName'ForwardsPrimaFacieReasons
    <|> "FORWARDS CONCLUSIVE REASONS"   ↦ SectionName'ForwardsConclusiveReasons
    <|> "BACKWARDS PRIMA FACIE REASONS" ↦ SectionName'BackwardsPrimaFacieReasons
    <|> "BACKWARDS CONCLUSIVE REASONS"  ↦ SectionName'BackwardsConclusiveReasons
  where
    (↦) ∷ String → a → Parser a
    s ↦ t = try (string s) *> pure t

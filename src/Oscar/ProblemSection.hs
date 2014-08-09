{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemSection where

import ClassyPrelude hiding (
    try,
    )

import Control.Applicative              (empty)
import Text.Parsec                      (string)
import Text.Parsec                      (try)
import Text.Parsec.Text                 (Parser)

data Section
    = Section'GivenPremises
    | Section'UltimateEpistemicInterests
    | Section'ForwardsPrimaFacieReasons
    | Section'ForwardsConclusiveReasons
    | Section'BackwardsPrimaFacieReasons
    | Section'BackwardsConclusiveReasons
  deriving (Eq, Show)

sectionParser ∷ Parser Section
sectionParser =
    empty
    <|> "Given premises:"               **> Section'GivenPremises
    <|> "Ultimate epistemic interests:" **> Section'UltimateEpistemicInterests
    <|> "FORWARDS PRIMA FACIE REASONS"  **> Section'ForwardsPrimaFacieReasons
    <|> "FORWARDS CONCLUSIVE REASONS"   **> Section'ForwardsConclusiveReasons
    <|> "BACKWARDS PRIMA FACIE REASONS" **> Section'BackwardsPrimaFacieReasons
    <|> "BACKWARDS CONCLUSIVE REASONS"  **> Section'BackwardsConclusiveReasons
  where
    (**>) ∷ String → a → Parser a
    s **> t = try (string s) *> pure t

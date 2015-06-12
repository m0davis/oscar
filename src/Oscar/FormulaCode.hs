{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.FormulaCode where

import Oscar.Main.Prelude

import Oscar.Formula hiding (Formula)
import qualified Oscar.Formula as F

type Formula = F.Formula

type UFormula = FormulaY UQuantifier UPredicate UDomainFunction UDomainVariable

{- TODO This is ugly-looking. The U prefix is meant to signify the Uniqueness of quantifier variables a la uFormula. Rename? Separate layers of abstraction? -}
type U = Int
type UQuantifier = U
type UPredicate = Symbol
type UDomainFunction = Symbol
data UDomainVariable
    = UQuantified U
    | UFree Symbol
  deriving (Eq, Read, Show)

{- TODO reformat, rename; provide some examples -}
uFormula ∷ Formula → UFormula
uFormula = snd . uFormula' 0 []
  where
    uFormula' ∷ Int                 -- ^ number of quantifiers found so far
              → [(Symbol, Int)]     -- ^ mappings of in-scope quantifiers
              → Formula             -- ^
              → (Int, UFormula)     -- ^ Int = cumulative # of quantifiers
    uFormula' n qs = uFormula''
      where
        uFormula'' ∷ Formula → (Int, UFormula)
        uFormula'' FormulaBinary {..} =
          let (n', ufl) = uFormula' n qs _formulaBinaryLeftFormula in
          let (n'', ufr) = uFormula' n' qs _formulaBinaryRightFormula in
              (n'', FormulaBinary _formulaBinaryOp ufl ufr)
        uFormula'' FormulaUnary {..} =
          let (n', uf) = uFormula' n qs _formulaUnaryFormula in
              (n', FormulaUnary _formulaUnaryOp uf)
        uFormula'' FormulaQuantification {..} =
          let (n', uf) = uFormula' (n + 1) ((_formulaQuantifierSymbol, n + 1) : qs) _formulaQuantifierFormula in
              (n', FormulaQuantification _formulaQuantifier (n + 1) uf)
        uFormula'' (FormulaPredication (Predication p dfs)) =
          (n,) $ FormulaPredication $ Predication p $ map s2i dfs
            where
              s2i ∷ DomainFunction → DomainFunctionY Symbol UDomainVariable
              s2i (DomainFunction df dfs) = DomainFunction df $ map s2i dfs
              s2i (DomainVariable dv) = DomainVariable $
                case lookup dv qs of
                  Just i → UQuantified i
                  Nothing → UFree dv

-- TODO rename
data Discriminator = Discriminator
    { _discriminationTestIndex ∷ [Int]
    , _discriminationTestPart ∷ FormulaParticle
    }
  deriving (Eq, Read, Show)

-- TODO rename
data FormulaParticle
    = FormulaParticleQuantified Quantifier
    | FormulaParticleUnary UnaryOp
    | FormulaParticleBinary BinaryOp
    | FormulaParticlePredicated Symbol
  deriving (Eq, Read, Show)

-- TODO rename
data FormulaTerm
    = FormulaTermDomainFunction Symbol [FormulaTerm]
    | FormulaTermFreeVariable Symbol
    | FormulaTermBoundVariable U
  deriving (Eq, Read, Show)

formulaCode ∷ UFormula → ([Discriminator], [FormulaTerm])
formulaCode formula = formulaCode' formula []

{- TODO this matches John's formula-code* but probably is overly-complicated. Consider using a single Int for depth instead of an array representing the _discriminatorTestIndex -}
formulaCode' ∷ UFormula
             → [Int]
             → ([Discriminator], [FormulaTerm])
formulaCode' (FormulaBinary {..}) is =
  let (l, lt) = formulaCode' _formulaBinaryLeftFormula (2 : is) in
  let (r, rt) = formulaCode' _formulaBinaryRightFormula (3 : is) in
      (Discriminator (reverse (1 : is)) (FormulaParticleBinary _formulaBinaryOp) : l ++ r, rt ++ lt)
formulaCode' (FormulaUnary {..}) is =
  let (u, ut) = formulaCode' _formulaUnaryFormula (2 : is) in
      (Discriminator (reverse (1 : is)) (FormulaParticleUnary _formulaUnaryOp) : u, ut)
formulaCode' (FormulaQuantification {..}) is =
  let (q, qt) = formulaCode' _formulaQuantifierFormula (2 : is) in
      (Discriminator (reverse (1 : is)) (FormulaParticleQuantified _formulaQuantifier) : q, qt)
formulaCode' (FormulaPredication (Predication p dfs)) is =
  ([Discriminator (reverse (1 : is)) (FormulaParticlePredicated p)], map df2ft dfs)
    where
      df2ft ∷ DomainFunctionY Symbol UDomainVariable → FormulaTerm
      df2ft (DomainFunction s dfs) = FormulaTermDomainFunction s $ map df2ft dfs
      df2ft (DomainVariable (UQuantified u)) = FormulaTermBoundVariable u
      df2ft (DomainVariable (UFree s)) = FormulaTermFreeVariable s

{- TODO it seems arbitrary that the reasonCode ignores the right-hand of a FormulaBinary when the left-hand contains a variable Predication. E.g.
    let formula = uFormula . formulaFromText $ pack "(F a & G b)"
    let f = Symbol $ pack "F"
    let g = Symbol $ pack "G"
    reasonCode formula f --> results in --> [], whereas
    reasonCode formula g --> results in --> a single element
-}
reasonCode ∷ UFormula → [Symbol] → [Discriminator]
reasonCode formula variables = fst $ break match $ fst $ formulaCode formula
  where
    match ∷ Discriminator -> Bool
    match (Discriminator _ (FormulaParticlePredicated s)) = s `elem` variables
    match _ = False

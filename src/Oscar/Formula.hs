{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Formula (
    Formula,
    FormulaY(..),
    Quantifier(..),
    UnaryOp(..),
    BinaryOp(..),
    Symbol(..),
    Predication,
    PredicationY(..),
    DomainFunction,
    DomainFunctionY(..),
    -- * "Control.Lens"
    formulaBinaryOp,
    formulaBinaryLeftFormula,
    formulaBinaryRightFormula,
    formulaUnaryOp,
    formulaUnaryFormula,
    formulaQuantifier,
    formulaQuantifierSymbol,
    formulaQuantifierFormula,
    formulaPredication,
    ) where

import Oscar.Main.Prelude

import Control.Lens

{- | See "Oscar.Documentation" for a guide to writing 'Formula's.
-}
-- TODO rename FormulaY (et al.) to Formula; modules that import and use Formula should create their own type, Formula (as below) or else add a layer of abstraction for such Formulas (? can we have a module that exports the current Formula type but also provides the current FormulaY constructors?)
data FormulaY q p df dv
    = FormulaBinary { _formulaBinaryOp ∷ !BinaryOp
                    , _formulaBinaryLeftFormula ∷ !(FormulaY q p df dv)
                    , _formulaBinaryRightFormula ∷ !(FormulaY q p df dv)
                    }
    | FormulaUnary { _formulaUnaryOp ∷ !UnaryOp
                   , _formulaUnaryFormula ∷ !(FormulaY q p df dv)
                   }
    | FormulaQuantification { _formulaQuantifier ∷ !Quantifier
                            , _formulaQuantifierSymbol ∷ !q
                            , _formulaQuantifierFormula ∷ !(FormulaY q p df dv)
                            }
    | FormulaPredication { _formulaPredication ∷ !(PredicationY p df dv) }
  deriving (Eq, Read, Show)

type Formula = FormulaY Symbol Symbol Symbol Symbol

{- | a la first-order logic -}
-- TODO rename this to QuantifierOp, for consistency?
data Quantifier
    = Universal    -- ^ (all ...)
    | Existential  -- ^ (some ...)
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

{- | Unary operations on predicates. -}
data UnaryOp
    = Negation  -- ^ ~
    | Whether   -- ^ ?
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

{- | Binary operations on predicates. -}
data BinaryOp
    = Conjunction   -- ^ &
    | Disjunction   -- ^ v
    | Conditional   -- ^ \->
    | Biconditional -- ^ \<->
    | Defeater      -- ^ @
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

{- | A name of a predicate or, domain function, domain variable, or constant.
-}
newtype Symbol = Symbol Text
  deriving (Eq, Read, Show)

{- | Predications, a la first-order logic, are statements that can be
     considered to have truth values. Strictly speaking, a 'Predication'
     doesn't necessarily have a truth value since not all of its variables
     may be bound.
-}
data PredicationY p df dv = Predication p [DomainFunctionY df dv]
  deriving (Eq, Read, Show)

type Predication = PredicationY Symbol Symbol Symbol

{- | Perhaps the simplest domain function is a constant. E.g. c stands for
     Garfield.

     It could also be a variable that could be bound by a quantifier. E.g. x
     is a domain variable in the formula
     @(all x)(IsLasagna x -> WantsToEat c x)@.

     It could also be a function that modifies a variable or a constant. E.g.
     the-litter-box-used-by is a domain function in the formula
     @(all x)(JimDavisDraws x -> ~JimDavisDraws (the-litter-box-used-by x)).
-}
data DomainFunctionY df dv
    = DomainFunction !df ![DomainFunctionY df dv] -- ^ `g' in P (g x)
    | DomainVariable !dv                   -- ^ `x' or `y' in P (g x) y
  deriving (Eq, Read, Show)

type DomainFunction = DomainFunctionY Symbol Symbol

makeLenses ''FormulaY

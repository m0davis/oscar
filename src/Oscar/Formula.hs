{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Formula (
    Formula(..),
    QuantifierOp(..),
    UnaryOp(..),
    BinaryOp(..),
    Symbol(..),
    Predication(..),
    DomainFunction(..),
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
data Formula q p df dv
    = FormulaBinary { _formulaBinaryOp ∷ !BinaryOp
                    , _formulaBinaryLeftFormula ∷ !(Formula q p df dv)
                    , _formulaBinaryRightFormula ∷ !(Formula q p df dv)
                    }
    | FormulaUnary { _formulaUnaryOp ∷ !UnaryOp
                   , _formulaUnaryFormula ∷ !(Formula q p df dv)
                   }
    | FormulaQuantification { _formulaQuantifier ∷ !QuantifierOp
                            , _formulaQuantifierSymbol ∷ !q
                            , _formulaQuantifierFormula ∷ !(Formula q p df dv)
                            }
    | FormulaPredication { _formulaPredication ∷ !(Predication p df dv) }
  deriving (Eq, Read, Show)

{- | a la first-order logic -}
-- TODO rename this to QuantifierOp, for consistency?
data QuantifierOp
    = Universal    -- ^ (all ...)
    | Existential  -- ^ (some ...)
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

{- | Unary operations on predicates. -}
data UnaryOp
    = Negation  -- ^ ~
    | Whether   -- ^ ? TODO add a quantifier-like `?' operator for ?-queries
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
data Predication p df dv = Predication p [DomainFunction df dv]
  deriving (Eq, Read, Show)

{- | Perhaps the simplest domain function is a constant. E.g. c stands for
     Garfield.

     It could also be a variable that could be bound by a quantifier. E.g. x
     is a domain variable in the formula
     @(all x)(IsLasagna x -> WantsToEat c x)@.

     It could also be a function that modifies a variable or a constant. E.g.
     the-litter-box-used-by is a domain function in the formula
     @(all x)(JimDavisDraws x -> ~JimDavisDraws (the-litter-box-used-by x)).
-}
data DomainFunction df dv
    = DomainFunction !df ![DomainFunction df dv] -- ^ `g' in P (g x)
    | DomainVariable !dv                         -- ^ `x' or `y' in P (g x) y
  deriving (Eq, Read, Show)

makeLenses ''Formula

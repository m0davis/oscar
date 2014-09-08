{-# LANGUAGE NoImplicitPrelude #-}

module Oscar.Formula (
    Formula(..),
    Quantifier(..),
    UnaryOp(..),
    BinaryOp(..),
    Symbol(..),
    Predication(..),
    DomainFunction(..),
    ) where

import Oscar.Main.Prelude

{- | See "Oscar.Documentation" for a guide to writing 'Formula's.
-}
data Formula
    = FormulaBinary !BinaryOp !Formula !Formula
    | FormulaUnary !UnaryOp !Formula
    | FormulaQuantification !Quantifier !Symbol !Formula
    | FormulaPredication !Predication
  deriving (Eq, Read, Show)

{- | a la first-order logic -}
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
data Predication = Predication Symbol [DomainFunction]
  deriving (Eq, Read, Show)

{- | Perhaps the simplest domain function is a constant. E.g. c stands for 
     Garfield. 

     It could also be a variable that could be bound by a quantifier. E.g. x
     is a domain variable in the formula @(all x)(IsLasagna x -> WantsToEat c x)@.
     
     It could also be a function that modifies a variable or a constant. E.g.
     the-litter-box-used-by is a domain function in the formula 
     @(all x)(JimDavisDraws x -> ~JimDavisDraws (the-litter-box-used-by x)).
-}
data DomainFunction
    = DomainFunction !Symbol ![DomainFunction] -- ^ `g' in P (g x)
    | DomainVariable !Symbol                   -- ^ `x' or `y' in P (g x) y
  deriving (Eq, Read, Show)

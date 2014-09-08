{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.FormulaParser.Internal (
    -- * Linear tokenization
    QToken(..),
    Parenthesis(..),
    makePQTokens,
    -- * Structuring according to parentheses
    freeFromParentheses,
    -- * Re-structuring according to quantifiers
    QSToken(..),
    ƮUnreformed,
    ƮReformed,
    makeQSTokenTree,
    reformQSTokenTree,
    -- * Formula construction
    -- $Patterns
    pattern BinaryOpP,
    pattern UnaryOpP,
    pattern QuantifierP,
    pattern ComplexPredicationP,
    pattern SimplePredicationP,
    pattern RedundantParenthesesP,
    makeFormula,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Formula                    (Formula(FormulaBinary))
import Oscar.Formula                    (Formula(FormulaQuantification))
import Oscar.Formula                    (Formula(FormulaUnary))
import Oscar.Formula                    (Formula(FormulaPredication))
import Oscar.Formula                    (Predication(Predication))
import Oscar.Formula                    (DomainFunction(DomainFunction))
import Oscar.Formula                    (DomainFunction(DomainVariable))
import Oscar.Formula                    (BinaryOp(Disjunction))
import Oscar.Formula                    (BinaryOp(Conjunction))
import Oscar.Formula                    (BinaryOp(Defeater))
import Oscar.Formula                    (BinaryOp(Conditional))
import Oscar.Formula                    (BinaryOp(Biconditional))
import Oscar.Formula                    (Quantifier(Universal))
import Oscar.Formula                    (Quantifier(Existential))
import Oscar.Formula                    (Symbol(Symbol))
import Oscar.Formula                    (UnaryOp(Negation))
import Oscar.Formula                    (UnaryOp(Whether))

{- | Compare to 'QSToken'. The `Q' in QToken indicates that, at this stage
     in the parsing of a 'Formula', we tokenize the 'Quantifier' separately
     from the quantification variable (a 'Symbol').
-}
data QToken
    = QTokenUnaryOp !UnaryOp
    | QTokenBinaryOp !BinaryOp
    | QTokenQuantifier !Quantifier
    | QTokenSymbol !Symbol
  deriving (Eq, Read, Show)

data Parenthesis = OpenParenthesis | CloseParenthesis
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

{- | Parses the alleged formula text into a sequence of tokens.

Sample input

@
~(all x)(P x)
@

Sample output

@
[Right (QTokenUnaryOp Negation)
,Left OpenParenthesis
,Right (QTokenQuantifier Universal)
,Right (QTokenSymbol \"x")
,Left CloseParenthesis
,Left OpenParenthesis
,Right (QTokenSymbol \"P")
,Right (QTokenSymbol \"x")
,Left CloseParenthesis
]
@
-}
makePQTokens ∷ Text → [Either Parenthesis QToken]
makePQTokens = simpleParse $ many $ many space *> parsePQToken
  where
    parsePQToken ∷ Parser (Either Parenthesis QToken)
    parsePQToken = empty
        <|> Left                     <$> parenthesis
        <|> Right . QTokenUnaryOp    <$> unaryOp
        <|> Right . QTokenBinaryOp   <$> binaryOp
        <|> Right . QTokenQuantifier <$> quantifier
        <|> Right . QTokenSymbol     <$> symbol
      where
        p ↦ v = try p *> pure v
        infixl 4 ↦

        parenthesis ∷ Parser Parenthesis
        parenthesis = empty
            <|> char '('            ↦ OpenParenthesis
            <|> char '['            ↦ OpenParenthesis
            <|> char ')'            ↦ CloseParenthesis
            <|> char ']'            ↦ CloseParenthesis

        unaryOp ∷ Parser UnaryOp
        unaryOp = empty
            <|> char '?'            ↦ Whether
            <|> char '~'            ↦ Negation

        binaryOp ∷ Parser BinaryOp
        binaryOp = empty
            <|> char 'v' *> space   ↦ Disjunction
            <|> char '&'            ↦ Conjunction
            <|> char '@'            ↦ Defeater
            <|> string "->"         ↦ Conditional
            <|> string "<->"        ↦ Biconditional

        quantifier ∷ Parser Quantifier
        quantifier = empty
            <|> string "all"        ↦ Universal
            <|> string "some"       ↦ Existential

        symbol ∷ Parser Symbol
        symbol = Symbol . pack <$> many1 alphaNum

{- | freeFromParentheses f xs applies f to each of the xs and creates a tree,
respecting the structure indicated by the parentheses.

Here's an example where f = id.

Sample input

@
[Right (QTokenUnaryOp Negation)
,Left OpenParenthesis
,Right (QTokenQuantifier Universal)
,Right (QTokenSymbol \"x")
,Left CloseParenthesis
,Left OpenParenthesis
,Right (QTokenSymbol \"P")
,Right (QTokenSymbol \"x")
,Left CloseParenthesis
]
@

Sample output

@
Free [Pure (QTokenUnaryOp Negation)
     ,Free [Pure (QTokenQuantifier Universal)
           ,Pure (QTokenSymbol \"x")
           ]
     ,Free [Pure (QTokenSymbol \"P")
           ,Pure (QTokenSymbol \"x")
           ]
     ]
@
-}
freeFromParentheses ∷
    ∀ as a b.
    (IsSequence as, Element as ~ a) ⇒
    (a → Either Parenthesis b)  {- ^ discriminate parentheses -} →
    as                          {- ^ input sequence -} →
    Free [] b                   {- ^ a tree, sans parentheses -}
freeFromParentheses f = fst . ffp 0 []
  where
    ffp ∷ Natural → [Free [] b] → as → (Free [] b, as)
    ffp d prev ass
        | onull ass =
            (Free prev, mempty)
        | Left OpenParenthesis ← f a =
            let (paren, rest) = ffp (succ d) [] as
            in  ffp d (prev ++ [paren]) rest
        | Left CloseParenthesis ← f a
        , d == 0 =
            error "unexpected CloseParenthesis at depth 0"
        | Left CloseParenthesis ← f a =
            (Free prev, as)
        | Right b ← f a =
            ffp d (prev ++ [Pure b]) as
        | otherwise = (⊥)
          -- suppresses an invalid non-exhaustive pattern match warning
          -- (ghc 7.8.2)
      where
        Just (a, as) = uncons ass

{- | Compare to 'QToken'. Here, we associate each quantifier with its
     variable.
-}
data QSToken
    = QSTokenUnaryOp !UnaryOp
    | QSTokenBinaryOp !BinaryOp
    | QSTokenQuantifier !Quantifier !Symbol
    | QSTokenSymbol !Symbol
  deriving (Eq, Read, Show)

-- | Converted to a QSToken tree (by 'makeQSTokenTree') but not yet reformed.
data ƮUnreformed

-- | Reformed by 'reformQSTokenTree'
data ƮReformed

{- | A simple transformation that associates the quantifier with its variable.

Sample input

@
Free [Pure (QTokenUnaryOp Negation)
     ,Free [Pure (QTokenQuantifier Universal)
           ,Pure (QTokenSymbol \"x")
           ]
     ,Free [Pure (QTokenSymbol \"P")
           ,Pure (QTokenSymbol \"x")
           ]
     ]
@

Sample output

@
Free [Pure (QSTokenUnaryOp Negation)
     ,Pure (QSTokenQuantifier Universal (QSTokenSymbol \"x"))
     ,Free [Pure (QSTokenSymbol \"P")
           ,Pure (QSTokenSymbol \"x")
           ]
     ]
@
-}
makeQSTokenTree ∷ Free [] QToken → Free [] QSToken ⁞ ƮUnreformed
makeQSTokenTree = ƭ . \case
    (Pure (QTokenUnaryOp  u)) → Pure $ QSTokenUnaryOp u
    (Pure (QTokenBinaryOp b)) → Pure $ QSTokenBinaryOp b
    (Pure (QTokenSymbol   s)) → Pure $ QSTokenSymbol s
    (Free [Pure (QTokenQuantifier q), Pure (QTokenSymbol s)]) →
        Pure $ QSTokenQuantifier q s
    (Free ts)                 → Free $ map (unƭ . makeQSTokenTree) ts
    _ → error "makeQSTokenTree: unexpected QTokenQuantifier"

{- | Restructure the tree, respecting quantifiers and unary operators.

Sample input

@
Free [Pure (QSTokenUnaryOp Negation)
     ,Pure (QSTokenQuantifier Universal (QSTokenSymbol \"x"))
     ,Free [Pure (QSTokenSymbol \"P")
           ,Pure (QSTokenSymbol \"x")
           ]
     ]
@

Sample output

@
Free [Free [Pure (QSTokenUnaryOp Negation)
           ,Free [Free [Pure (QSTokenQuantifier Universal \"x")
                       ,Free [Pure (QSTokenSymbol \"P")
                             ,Pure (QSTokenSymbol \"x")
                             ]
                       ]
                 ]
           ]
     ]
@

Note that the two Free's at the top of the tree are redundant. When we 
'makeFormula', they will be removed via 'RedundantParenthesesP'.
-}
reformQSTokenTree ∷ Free [] QSToken ⁞ ƮUnreformed → Free [] QSToken ⁞ ƮReformed
reformQSTokenTree = ƭ . ref . unƭ
  where
    ref ∷ Free [] QSToken → Free [] QSToken
    ref t@(Pure _) = t
    ref (Free ts) = Free $ reverse . rqstt . reverse $ ts where
        rqstt ∷ [Free [] QSToken] → [Free [] QSToken]
        rqstt [] =
            []
        rqstt [a, q@(Pure (QSTokenQuantifier _ _))] =
            [Free [q, ref a]]
        rqstt (a:u@(Pure (QSTokenUnaryOp _)):as) =
            let chunk = Free [u, ref a]
            in
                if null as then
                    [chunk]
                else
                    rqstt (chunk : as)
        rqstt (a:q@(Pure (QSTokenQuantifier _ _)):as) =
            rqstt $ Free [q, ref a] : as
        rqstt (a:as) =
            ref a : rqstt as

{- $Patterns

These patterns are for use by 'makeFormula'.
-}

pattern BinaryOpP left op right
        = Free [left,Pure (QSTokenBinaryOp op), right]

pattern UnaryOpP op right
        = Free [Pure (QSTokenUnaryOp op), right]

pattern QuantifierP quantifier variable formula
        = Free [Pure (QSTokenQuantifier quantifier variable), formula]

pattern ComplexPredicationP predication domainFunctions
        = Free (Pure (QSTokenSymbol predication):domainFunctions)

pattern SimplePredicationP predication
        = Pure (QSTokenSymbol predication)

pattern RedundantParenthesesP x
        = Free [x]

{- | Construct a Formula from the reformed tree.

Sample input

@
Free [Free [Pure (QSTokenUnaryOp Negation)
           ,Free [Free [Pure (QSTokenQuantifier Universal \"x")
                       ,Free [Pure (QSTokenSymbol \"P")
                             ,Pure (QSTokenSymbol \"x")
                             ]
                       ]
                 ]
           ]
     ]
@

Sample output

@
FormulaUnary Negation
    (FormulaQuantification Universal
        (FormulaPredication
            (Predication \"P")
            [DomainVariable \"x"]
        )
    )
@

-}
makeFormula ∷ (Free [] QSToken) ⁞ ƮReformed → Formula
makeFormula = mk . unƭ
  where
    mk = \case
        BinaryOpP l o r             → FormulaBinary
            o (mk l) (mk r)
        UnaryOpP o r                → FormulaUnary
            o (mk r)
        QuantifierP q v f           → FormulaQuantification
            q v (mk f)
        ComplexPredicationP p dfs   → FormulaPredication $
            Predication p $ makeDomainFunction <$> dfs
        SimplePredicationP p        → FormulaPredication $
            Predication p []
        RedundantParenthesesP f → mk f
        x → error $ "makeFormula: unexpected structure\n" ++ ppShow x
      where
        makeDomainFunction ∷ Free [] QSToken → DomainFunction
        makeDomainFunction (Pure (QSTokenSymbol s)) =
            DomainVariable s
        makeDomainFunction (Free (Pure (QSTokenSymbol s):ss)) =
            DomainFunction s $ map makeDomainFunction ss
        makeDomainFunction (Free [x]) =
            makeDomainFunction x
        makeDomainFunction x =
            error $ "makeDomainFunction: unexpected structure\n" ++ ppShow x

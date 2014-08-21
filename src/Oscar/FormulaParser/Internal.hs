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
    QToken(..),
    makePQTokens,
    Parenthesis(..),
    freeFromParentheses,
    QSToken,
    Reformed,
    Unreformed,
    makeQSTokenTree,
    reformQSTokenTree,
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

data QToken
    = QTokenUnaryOp !UnaryOp
    | QTokenBinaryOp !BinaryOp
    | QTokenQuantifier !Quantifier
    | QTokenSymbol !Symbol
  deriving (Show)

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
            <|> string "→"         ↦ Conditional
            <|> string "<→"        ↦ Biconditional

        quantifier ∷ Parser Quantifier
        quantifier = empty
            <|> string "all"        ↦ Universal
            <|> string "some"       ↦ Existential

        symbol ∷ Parser Symbol
        symbol = Symbol . pack <$> many1 alphaNum

-- | Parentheses are like this y(). See 'freeFromParentheses'
data Parenthesis = OpenParenthesis | CloseParenthesis
  deriving (Bounded, Eq, Read, Show)

freeFromParentheses ∷
    ∀ as a b.
    (IsSequence as, Element as ~ a) ⇒
    (a → Either Parenthesis b) →
    as →
    Free [] b
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
        | otherwise = error ""
          -- suppresses invalid ghc warning about non-exhaustive pattern match
        where
            Just (a, as) = uncons ass

data QSToken
    = QSTokenUnaryOp !UnaryOp
    | QSTokenBinaryOp !BinaryOp
    | QSTokenQuantifier !Quantifier !Symbol
    | QSTokenSymbol !Symbol
  deriving (Show)

data Reformed
data Unreformed

makeQSTokenTree ∷ Free [] QToken → Free [] QSToken ⁞ Unreformed
makeQSTokenTree = ƭ . \case
    (Pure (QTokenUnaryOp  u)) → Pure $ QSTokenUnaryOp u
    (Pure (QTokenBinaryOp b)) → Pure $ QSTokenBinaryOp b
    (Pure (QTokenSymbol   s)) → Pure $ QSTokenSymbol s
    (Free [Pure (QTokenQuantifier q), Pure (QTokenSymbol s)]) →
        Pure $ QSTokenQuantifier q s
    (Free ts)                 → Free $ map (unƭ . makeQSTokenTree) ts
    _ → error "makeQSTokenTree: unexpected QTokenQuantifier"

reformQSTokenTree ∷ (Free [] QSToken) ⁞ Unreformed → (Free [] QSToken) ⁞ Reformed
reformQSTokenTree = ƭ . ref . unƭ 
  where 
    ref ∷ Free [] QSToken → Free [] QSToken
    ref t@(Pure _) = t
    ref (Free ts) = Free $ reverse . rqstt . reverse $ ts where
        rqstt ∷ [Free [] QSToken] → [Free [] QSToken]
        rqstt [] =
            []
        rqstt [a, u@(Pure (QSTokenQuantifier _ _))] =
            [Free [u, ref a]]
        rqstt (a:u@(Pure (QSTokenUnaryOp _)):as) =
            let chunk = Free [u, ref a]
            in
                if null as then
                    [chunk]
                else
                    rqstt (chunk : as)
        rqstt (a:u@(Pure (QSTokenQuantifier _ _)):as) =
            rqstt $ Free [u, ref a] : as
        rqstt (a:as) =
            ref a : rqstt as

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

makeFormula ∷ (Free [] QSToken) ⁞ Reformed → Formula
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

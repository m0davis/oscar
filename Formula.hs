{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Formula where

import ClassyPrelude hiding (Text, try)
import Text.Show.Pretty (ppShow)

import Numeric.Natural
import Data.Pointed
import Data.List.Split
import Control.Applicative
import Control.Monad
import Control.Lens hiding (uncons)
import Control.Monad.Free
import Data.Either.Utils (maybeToEither)
import Data.Text.Internal.Lazy (Text)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Prim hiding ((<|>), many, uncons)
import Text.Parsec.String ()
import Text.Parsec.Text.Lazy

import Debug.Trace

--
data AToken
    =   ATokenParenthesis Parenthesis
    |   ATokenUnaryOperator UnaryOperator
    |   ATokenBinaryOperator BinaryOperator
    |   ATokenQuantifier Quantifier
    |   ATokenSymbol Text
    deriving (Show)

atoken :: Parser AToken
atoken = many space *> 
    (   empty
    <|> parenthesis 
    <|> unaryOperator 
    <|> binaryOperator 
    <|> quantifier 
    <|> symbol
    )
    where
    parenthesis = 
        empty
        <|> (char '(' *> pure (ATokenParenthesis OpenParenthesis))
        <|> (char '[' *> pure (ATokenParenthesis OpenParenthesis))
        <|> (char ')' *> pure (ATokenParenthesis CloseParenthesis))
        <|> (char ']' *> pure (ATokenParenthesis CloseParenthesis))
    unaryOperator =
        empty
        <|> (char '?' *> pure (ATokenUnaryOperator UnaryOperator_Whether))
        <|> (char '~' *> pure (ATokenUnaryOperator UnaryOperator_Negation))
    binaryOperator =
        empty
        <|> (char 'v' *> pure (ATokenBinaryOperator BinaryOperator_Disjunction))
        <|> (char '&' *> pure (ATokenBinaryOperator BinaryOperator_Conjunction))
        <|> (char '@' *> pure (ATokenBinaryOperator BinaryOperator_Defeater))
        <|> (try (string "->")  *> pure (ATokenBinaryOperator BinaryOperator_Conditional))
        <|> (try (string "<->") *> pure (ATokenBinaryOperator BinaryOperator_Biconditional))
    quantifier =
        empty
        <|> (try (string "all")  *> pure (ATokenQuantifier Quantifier_Universal))
        <|> (try (string "some") *> pure (ATokenQuantifier Quantifier_Existential))
    symbol = ATokenSymbol . pack <$> many1 (notFollowedBy (Text.Parsec.Char.oneOf "([])?~&@-<>" <|> space) *> anyChar)

aTokenTree :: [AToken] -> Free [] AToken
aTokenTree =
    treeFromParentheses (
        \case
            ATokenParenthesis p -> Left p
            x -> Right x
        )

data BToken
    =   BTokenUnaryOperator UnaryOperator
    |   BTokenBinaryOperator BinaryOperator
    |   BTokenQuantifier Quantifier Text
    |   BTokenSymbol Text
    deriving (Show)

bTokenTree :: Free [] AToken -> Free [] BToken
bTokenTree (Pure (ATokenUnaryOperator u)) = Pure (BTokenUnaryOperator u)
bTokenTree (Pure (ATokenBinaryOperator b)) = Pure (BTokenBinaryOperator b)
bTokenTree (Pure (ATokenSymbol s)) = Pure (BTokenSymbol s)
bTokenTree (Free [Pure (ATokenQuantifier q), Pure (ATokenSymbol s)]) = Pure (BTokenQuantifier q s)
bTokenTree (Free ts) = Free $ map bTokenTree ts


structurePrefixOperators :: Free [] BToken -> Free [] BToken
structurePrefixOperators t@(Pure _) = t
structurePrefixOperators (Free ts) = Free $ reverse . suo . reverse $ ts where
    suo :: [Free [] BToken] -> [Free [] BToken]
    suo [] = []
    --suo [a, u@(Pure (BTokenUnaryOperator _))] =
    --    [Free [u, structurePrefixOperators a]]
    suo [a, u@(Pure (BTokenQuantifier _ _))] =
        [Free [u, structurePrefixOperators a]]
    suo (a:u@(Pure (BTokenUnaryOperator _)):as) =
        let chunk = Free [u, structurePrefixOperators a] 
        in 
            if null as then
                [chunk]
            else
                suo (chunk:as)
    suo (a:u@(Pure (BTokenQuantifier _ _)):as) =
        suo $ Free [u, structurePrefixOperators a]:as
    suo (a:as) = structurePrefixOperators a:suo as

data Formula
    =   FormulaBinary BinaryOperator Formula Formula
    |   FormulaUnary UnaryOperator Formula
    |   FormulaQuantification Quantifier Text Formula
    |   FormulaPredication Text [Free [] Text]
    deriving (Show)

formula :: Free [] BToken -> Formula
formula (Free [l,Pure (BTokenBinaryOperator b), r]) = FormulaBinary b (formula l) (formula r)
formula (Free [Pure (BTokenUnaryOperator u), r]) = FormulaUnary u (formula r)
formula (Free [Pure (BTokenQuantifier q s), r]) = FormulaQuantification q s (formula r)
formula (Free (Pure (BTokenSymbol s):ss)) = FormulaPredication s (map subformula ss)
    where
    subformula :: Free [] BToken -> Free [] Text
    subformula (Pure (BTokenSymbol s)) = Pure s
    subformula (Free (Pure (BTokenSymbol s):ss)) = Free (Pure s:map subformula ss)
    subformula _ = error "subformula: unexpected structure"
formula (Pure (BTokenSymbol s)) = FormulaPredication s []
formula (Free [x]) = formula x
formula x = error ("formula: unexpected structure: \n" ++ ppShow x)

--
data Parenthesis = OpenParenthesis | CloseParenthesis
    deriving (Bounded, Eq, Read, Show)

class Tokenizer from to where
    tokenize :: from -> Maybe to

instance Tokenizer Char Parenthesis where
    tokenize '(' = Just OpenParenthesis
    tokenize '[' = Just OpenParenthesis
    tokenize ')' = Just CloseParenthesis
    tokenize ']' = Just CloseParenthesis
    tokenize _   = Nothing

mconcatRightPoints :: 
    (Pointed p, Semigroup s, p r ~ s) => 
    [Either l r] -> 
    [Either l s]
mconcatRightPoints [] = []
mconcatRightPoints (Left l : xs) = Left l : mconcatRightPoints xs
mconcatRightPoints (Right r : xs) = case mconcatRightPoints xs of
    (Right rs : ys) -> Right (point r <> rs) : ys
    ys              -> Right (point r      ) : ys

eitherOr :: 
    a -> 
    (a -> Maybe b) -> 
    Either a b
eitherOr a f = maybeToEither a (f a)

treeFromParentheses ::
    forall as a b.
    (IsSequence as, Element as ~ a) =>
    (a -> Either Parenthesis b) ->
    as ->
    Free [] b
treeFromParentheses f = fst . tfp 0 []
    where

    tfp :: Natural -> [Free [] b] -> as -> (Free [] b, as)
    tfp d prev ass
        |   onull ass =
                (Free prev, mempty)
        |   otherwise =
                case f a of
                    Left OpenParenthesis ->
                        let (paren, rest) = tfp (succ d) [] as
                        in  tfp d (prev ++ [paren]) rest
                    Left CloseParenthesis ->
                        case d of
                            0 -> error "unexpected CloseParenthesis at depth 0"
                            _ -> (Free prev, as)
                    Right b -> -- ^?! _Right
                        tfp d (prev ++ [Pure b]) as
        where
            Just (a, as) = uncons ass


--

newtype LexemeWord = LexemeWord Text
    deriving (Show)

lexemeWord :: Parser LexemeWord
lexemeWord = {-(LexemeWord . pack) <$> -}do
    many space
    (
        empty
        <|> (char '~' >>= (return . LexemeWord . pack . point))
        <|> (many1 validChar >>= (return . LexemeWord . pack))
        ) <* many space
    where
        validChar :: Parser Char
        validChar = do
            notFollowedBy eof
            notFollowedBy $ char '~'
            notFollowedBy $ space
            anyChar

--

-- | formula text (sans parentheses) -> list of symbols
data Quantifier
    =   Quantifier_Universal
    |   Quantifier_Existential
    deriving (Show, Eq)

instance Tokenizer LexemeWord Quantifier where
    tokenize (LexemeWord lw) = case lw of
        "all"  -> Just Quantifier_Universal
        "some" -> Just Quantifier_Existential
        _      -> Nothing

data UnaryOperator
    =   UnaryOperator_Negation
    |   UnaryOperator_Whether
    deriving (Show, Eq)

instance Tokenizer LexemeWord UnaryOperator where
    tokenize (LexemeWord lw) = case lw of
        "~"  -> Just UnaryOperator_Negation
        "?"  -> Just UnaryOperator_Whether
        _    -> Nothing

data BinaryOperator
    =   BinaryOperator_Conjunction
    |   BinaryOperator_Disjunction
    |   BinaryOperator_Conditional
    |   BinaryOperator_Biconditional
    |   BinaryOperator_Defeater
    deriving (Show, Eq)

instance Tokenizer LexemeWord BinaryOperator where
    tokenize (LexemeWord lw) = case lw of
        "&"   -> Just BinaryOperator_Conjunction
        "v"   -> Just BinaryOperator_Disjunction
        "->"  -> Just BinaryOperator_Conditional
        "<->" -> Just BinaryOperator_Biconditional
        "@"   -> Just BinaryOperator_Defeater
        _     -> Nothing

data LexemeQUOBOS
    =   LexemeQUOBOS_Quantifier Quantifier
    |   LexemeQUOBOS_UnaryOperator UnaryOperator
    |   LexemeQUOBOS_BinaryOperator BinaryOperator
    |   LexemeQUOBOS_Symbol Text
    deriving (Show, Eq)

instance Tokenizer LexemeWord LexemeQUOBOS where
    tokenize lw@(LexemeWord lw') = quantifier <|> unary <|> binary <|> symbol
        where
        quantifier = maybe Nothing (Just . LexemeQUOBOS_Quantifier    ) $ tokenize lw
        unary      = maybe Nothing (Just . LexemeQUOBOS_UnaryOperator ) $ tokenize lw
        binary     = maybe Nothing (Just . LexemeQUOBOS_BinaryOperator) $ tokenize lw
        symbol     = Just $ LexemeQUOBOS_Symbol lw'

--

simplify :: Free [] a -> Free [] a
simplify (Free [a]) = simplify a
simplify (Free as)  = Free $ map simplify as
simplify (Pure a)   = Pure a

data PrefixBinary
    =   PrefixBinary BinaryOperator PrefixBinary PrefixBinary
    |   PrefixBinary' (Free [] PrefixBinary)
    |   PrefixBinary'' LexemeQUOBOS
    deriving (Show)

prefix :: Free [] LexemeQUOBOS -> Free [] PrefixBinary
prefix (Free ls) = case splitBinary ls of
    [l,[Pure (LexemeQUOBOS_BinaryOperator b)],r] -> 
        Pure $ 
            PrefixBinary 
                b 
                (PrefixBinary' . prefix $ Free l) 
                (PrefixBinary' . prefix $ Free r)
    [e] -> Free $ map prefix e
    _ -> error "invalid use of binary operator"
    where
    splitBinary :: [Free [] LexemeQUOBOS] -> [[Free [] LexemeQUOBOS]]
    splitBinary = split (whenElt isBinary)

    isBinary :: Free [] LexemeQUOBOS -> Bool
    isBinary (Pure (LexemeQUOBOS_BinaryOperator _)) = True
    isBinary _ = False
prefix (Pure l) = Pure $ PrefixBinary'' l

data PrefixBinaryUnary
    =   PrefixBinaryUnary UnaryOperator PrefixBinaryUnary
    |   PrefixBinaryUnary' (Free [] PrefixBinaryUnary)
    |   PrefixBinaryUnary'' PrefixBinary
    deriving (Show)

prefix2 :: Free [] PrefixBinary -> Free [] PrefixBinaryUnary
prefix2 (Free ls) = case splitUnary ls of
    [[Pure (PrefixBinary'' (LexemeQUOBOS_UnaryOperator u))],r] -> 
        Pure $ 
            PrefixBinaryUnary 
                u 
                (PrefixBinaryUnary' . prefix2 $ Free r)
    [e] -> Free $ map prefix2 e
    _ -> error "invalid use of unary operator"
    where
    splitUnary :: [Free [] PrefixBinary] -> [[Free [] PrefixBinary]]
    splitUnary = split (whenElt isUnary)

    isUnary :: Free [] PrefixBinary -> Bool
    isUnary (Pure (PrefixBinary'' (LexemeQUOBOS_UnaryOperator _))) = True
    isUnary _ = False
prefix2 (Pure l) = Pure $ PrefixBinaryUnary'' l

data PrefixBinaryUnaryQuantifier
    =   PrefixBinaryUnaryQuantifier Quantifier Text PrefixBinaryUnaryQuantifier
    |   PrefixBinaryUnaryQuantifier' (Free [] PrefixBinaryUnaryQuantifier)
    |   PrefixBinaryUnaryQuantifier'' PrefixBinaryUnary
    deriving (Show)
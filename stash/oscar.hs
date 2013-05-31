module Main where
import System.Environment
import Data.Time.Clock
import Data.Time.LocalTime
import Data.Time
import Data.Time.Format
import System.Locale

main :: IO ()
main = 
  let (io, value) = test 1
  in do
    io
    putStrLn $ show value
    putStrLn $ show $ sublis [('*', '$'), ('-', '%')] value
    putStrLn $ show $ reform "(R v ~T)" []
  
  
  --putStrLn $ show snd x


_version_ = "OSCAR_3.31"

_reductioDiscount_ = 0.23
_reductioInterest_ = 0.23
_skolemMultiplier_ = 10
_quantifierDiscount_ = 0.95

--an automated lisp to haskell translator would still require another human translation to make it elegant to use

type LispInteger = Integer
type LispBool = Bool

data LispDecodedTime = LispDecodedTime { second :: LispInteger -- 0 to 59
                                       , minute :: LispInteger -- 0 to 59
                                       , hour :: LispInteger -- 0 to 23
                                       , date :: LispInteger -- depends
                                       , month :: LispInteger -- 1 to 12
                                       , year :: LispInteger
                                       , dayOfWeek :: LispInteger
                                       , daylightSavingTimeFlag :: LispBool
                                       , timeZone :: Integer
                                       } deriving (Eq, Show, Read)

-- original comment: The following runs individual problems or lists of problems from the list *problems*. (test) runs the entire set.  (test n) runs just problem n.  (test n t) starts with problem n and runs the rest of the set.  (test n m) runs problems n through m.  (test n :skip '(i j k)) starts with problem n and runs the rest of the set except for i, j, and k.  (test n m :skip '(i j k)) runs problems n through m, skipping i, j, and k.  (test :skip i j k) runs all the problems except i, j, k.
-- this version behaves like (test n) described in the original comment
test :: Int ->  (IO (), String)
test x = (io, testLog)
  where 
    io = do
      time <- getCurrentTime
      putStrLn $ ""
      putStrLn $ "(                                 " ++ _version_ ++ "          " ++ formatTime defaultTimeLocale "%D          %X" time
      putStrLn $ "*reductio-discount* = " ++ show _reductioDiscount_
      putStrLn $ "*reductio-interest* = " ++ show _reductioInterest_
      putStrLn $ "*skolem-multipler* = " ++ show _skolemMultiplier_
      putStrLn $ "*quantifier-discount* = " ++ show _quantifierDiscount_
      --(run-reasoning-problem (assoc start *problems*))
      --putStr title
      --where title = "\n(                                 " ++ show _version_ ++ "          " ++ formatTime defaultTimeLocale "%D          %X" getCurrentTime ++ "\n"

      --putStr "*quantifier-discount* = " ++ _quantifierDiscount_ ++ ""
      --print time
    testLog = "the *test-log*"
  
--makeProblemFromString :: String -> Problem
--makeProblemFromString s =

--data Problem = 
--  Problem 
--  { 
--    problemNumber :: LispInteger
--  , premises :: [Premise]
--  , conclusions :: [Conclusion]
--  , forwardsPrimaFacieReasons :: [ForwardsPrimaFacieReason]
--  , forwardsConclusiveReasons :: [ForwardsConclusiveReason]
--  , backwardsPrimaFacieReasons :: [BackwardsPrimaFacieReason]
--  , backwardsConclusiveReasons :: [BackwardsConclusiveReason]
--  , problemDescription :: String
--  }



--template for a problem:

--problem #(\d+)
--(.*?)
-- *given premises: *
--(^ *(.*?) *justification = (.*)$)+
-- *ultimate epistemic interests: *
--( *(.*?) *interest = (.*)$)+
-- *forwards prima facie reasons *
--(^ *(.*?:) *\{(.*?)\} *\|\|=> *(.*?) *(variables = \{(.*?)\})? *strength = (.*?) *$)+
-- *backwards prima facie reasons *
--(^ *(.*?:) *\{(.*?)\} *\{(.*?)\} *\|\|=> *(.*?) *(variables = {(.*?)})? *strength = (.*?) *$)+
-- *forwards conclusive reasons *
--(^ *(.*?:) *\{(.*?)\} *\|\|=> *(.*?) *(variables = \{(.*?)\})? *strength = (.*?) *$)+
-- *backwards conclusive reasons *
--(^ *(.*?:) *\{(.*?)\} *\{(.*?)\} *\|\|=> *(.*?) *(variables = {(.*?)})? *strength = (.*?) *$)+

iF :: Bool -> a -> a -> a
iF c t e = if c then t else e

sublis :: Eq a => [(a, a)] -> [a] -> [a]
sublis s l = [ sub s x | x <- l ]
  where 
    sub ((from,to):othersubs) x = iF (x == from) to (sub othersubs x)
    sub _ x = x

data Variable = String

reform :: String -> [Variable] -> String
reform s vs = lispValue $ readFromString s

lispValue (LispString s) = s

data Sexp = 
    LispList [Sexp]
  | LispAtom

data LispAtom =
    LispString String
  | LispKeyword String
  | LispInteger Integer
  | LispDouble = Double

readFromString :: String -> Sexp
readFromString ccs@(c:cs) = 
  if c == '(' then
                              (
                                LispString $ upToClose cs []
                              )
                          where upToClose (c:cs) r | c == ')' = r
                                                   | True = upToClose cs (r ++ [c])
  else LispString ccs


_bracketTransformation_ = [('[', '('), (']', ')')]

--reform' :: String -> [Variable] -> Reformation'
--reform' s vs = fixNest $ parse (sublis _bracketTransformation_ s) vs

--parse :: String -

data Symbol = OR | AND | NOT;

convertToSymbol = 0

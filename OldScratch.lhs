> {-# LANGUAGE BangPatterns #-}

> -- file: ch25/A.hs
> import System.Environment
> import Text.Printf
> import Data.List
> import Control.Applicative
> import Control.Parallel.Strategies
> 
> arguments = pure ["1e7"]
> -- arguments = getArgs
> main = do
>     [d] <- map read `fmap` arguments

>     printf "%f\n" (mean [1..d])

> -- file: ch25/G.hs
> data Pair a b = Pair !a !b
> 
> -- file: ch25/G.hs
> mean :: [Double] -> Double
> mean xs = s / fromIntegral n
>   where
>     Pair n s       = foldl' k (Pair 0 0) xs
>     k (Pair n s) x = Pair (n+1) (s+x)



% > foldl'rnf :: NFData a => (a -> b -> a) -> a -> [b] -> a
% > foldl'rnf f z xs = lgo z xs
% >     where
% >         lgo z []     = z
% >         lgo z (x:xs) = lgo z' xs
% >             where
% >                 z' = f z x `using` rdeepseq

% > mean :: [Double] -> Double
% > mean xs = s / fromIntegral n
% >   where
% >     (n, s)     = foldl'rnf k (0, 0) xs
% >     k (n, s) x = (n+1, s+x) :: (Int, Double)

% > -- file: ch25/D.hs
% > mean :: [Double] -> Double
% > mean xs = s / fromIntegral n
% >   where
% >     (n, s)     = foldl' k (0, 0) xs
% >     k (n, s) x = n `seq` s `seq` (n+1, s+x)



% >     printf "%f\n" (meansum d)

% >     printf "%f\n" (meansum $ sumupto d)

% >     printf "%f\n" (meansum $ d)

% > sumupto :: Double -> Double
% > sumupto d = sumupto' 0 d where
% >   sumupto' s 0 = s
% >   sumupto' !s !d = sumupto' (s+1) (d-1)

% > meansum :: Double -> Double
% > meansum s = meansum' (fromInteger 0,0) s where
% >   meansum' (s,n) 0 = s / n
% >   meansum' (s,n) d = meansum' (s+d,n+1) $ sumupto (d-1)



% > type JSONError = String
% > 
% > class JSON a where
% >     toJValue :: a -> JValue
% >     fromJValue :: JValue -> Either JSONError a
% > 
% > instance JSON JValue where
% >     toJValue = id
% >     fromJValue = Right
% > 



  join = (>>= id)
  fmap :: (a -> b) -> f a -> f b
  a2b :: (a -> b)
  fa :: f a
  fmap a2b fa :: f b

  fmap g = flip (>>=) (return . g)

    b >>= 

  fmap 

    m >>= f = \f m -> join (fmap f m)
    join mm = 

  join :: m (m a) -> m a

  >>= :: m a -> (a -> m b) -> m b
    b <- a
    a <- m a  




    m a
      (m 1) >>= (1 -> m a)
          





  class Functor f where
    fmap :: (a -> b) -> f a -> f b

  class Monad m where
    return :: a -> m a
    (>>=)  :: m a -> (a -> m b) -> m b
    (>>)   :: m a -> m b -> m b
    m >> n = m >>= \_ -> n
   
    fail   :: String -> m a

  instance Monad [] where
    return = (:[])
    [] >>= g = []
    (x:xs) >>= g = (g x) ++ (xs >>= g)
    fail _ = []

  instance Monad ((->) e) where
    return = flip ($)
    g >>= b = \x -> b (g x) x
    fail s = \x -> s

  :{
  data Free f a = Var a
                | Node (f (Free f a))

  instance Functor f => Functor (Free f) where
    fmap g (Var v) = Var $ g v
    fmap g (Node n) = Node $ (fmap . fmap) g n

  instance Functor f => Monad (Free f) where
    return = Var
    (Var v) >>= g = g v
    --(Node n) >>= g = Node $ fmap (flip (>>=) g) n
    (Node n) >>= g = Node $ fmap (>>= g) n
    fail s = error s
  :}

  Var :: a -> Free f a
  Node :: f (Free f a) -> Free f a
  fmap :: Functor f => (a -> b) -> f a -> f b
  (>>=) :: Functor f => Free f a -> (a -> Free f b) -> Free f b
  g :: a -> Free f b
  n :: f (Free f a)

  fmap . fmap :: Functor 1, 2 => (a -> b) -> 2 1 a -> 2 1 b

  Free f b
    Node $ f (Free f b)
      Node $ fmap (1 -> Free f b) (f 1)
        1 = Free f a
        f 1 = n
        flip (>>=) 2 = Free f a -> Free f b
        2 = g









        (1 -> Free f b)
          Var
          >>= (Free f 2) (2 -> Free f b) ; 1 = 2 -> Free f b
          g ; 1 = a
        (f 1)
          fmap
          n
        Node $ fmap g               (f a)
          Node $ fmap g               (fmap (2 -> a) (f 2))


    fmap (1 -> b) (Free f a)

    >>= $ (Var 1)  (1 -> Free f b)
      1 = a -> Free f b

    g a






      f (Free f b)
        fmap 
          2 -> 1 
          f 2

    fmap
      1 -> b
      Free f a
    >>=
      Free f 1
      1 -> Free f b
        fmap
          2 -> b



    f (Free f b)
      f 1
      1 -> Free f b
        try 1 = a
          then we get 1 -> Free f b from g
               but f a ? 
                  f 2
                  2 -> a
        try 1 = Free f a

        no, try 1 = Free f 2
          f Free f 2
          Free f 2 -> Free f b








      f (Free f 1)
      (Free f 1) -> b


  fmap Var :: f a -> f (Free f a)
  fmap Node :: f f (Free f a) -> f (Free f a)
  fmap . fmap :: (a -> b) -> 2 1 a -> 2 1 b






  fmap g :: 1 a -> 1 (Free f b)
  fmap . fmap $ g :: 2 1 a -> 2 1 (Free f b)




      

  ? :: Free f b
    --fmap :: Functor Free f => (a -> b) -> Free f a -> Free f b  
    Node :: f (Free f b) -> Free f b

      fmap :: Functor f => (1 -> Free f b) -> f 1 -> f (Free f b)

        g :: a -> Free f b
        fmap :: Functor f => (1 -> a) -> f 1 -> f a
          ? :: 1 -> a
          fmap :: Functor f => (2 -> 1) -> f 2 -> f 1
            ? :: 2 -> 1
            ? :: f 2


          ? :: (Free f a) -> a
          n :: f (Free f a)

      OR








  backwards from...
  Var
    b
  Node
    f (Free f b)
      fmap
        *1 -> Free f b
        f *1
          fmap
            *2 -> *1
            f *2
  fmap
    *1 -> b
    Free f *1


  forwards
  -
  n::f (Free f a)
  g::a->Free f b
  fmap g::* a -> * (Free f b)
  Var n :: Free f (f (Free f a))
  Node n :: Free f a


  fmap (fmap g) :: * (* a) -> * (* (Free f b))
  fmap (fmap g) n :: f (Free f (Free f b))
  Node $ fmap (fmap g) n :: Free f (Free f b)


  Node $ fmap (fmap g) n :: Free f (Free f b)

  (>>=) (Node n) :: (a -> f b) -> f b




  backwards
  -
  (>>=) (Node n) :: (a -> f b) -> f b
  (Node n) >>= g :: Free f b
  Var b
  f (Free f b)


    ((Var v) >>=) = g v

         g :: a -> b
         Node x :: Free f a
         x :: f (Free f a) :: f ((Free f) a)
         fmap g (Node x) :: Free f b
                                Var b
                              | Node (f (Free f b))
         fmap g :: e a -> e b
         fmap (fmap g) x :: f (Free f b)



         a->b    Free f a

  follow the types


  test :: Functor f => f a -> b
  test g = fmap h g


  instance Functor f => Monad (Free f) where
    return = Var
    (Var v) >>= b = 
    (Node x) >>= b = 
    fail _ = 

  fmap     

  class Functor f where
    fmap :: (a -> b) -> f a -> f b    

    let g `aap` b = \x -> flip b x $ g x






  instance Applicative Maybe where
    pure x = Just x
    Nothing <*> _ = Nothing
    u <*> Nothing = Nothing
    Just f <*> Just x = Just $ f x




  identity
  pure id <*> u = u

  homomorphism
  pure f <*> pure x === pure (f x)


  iI  Ii

  fmap :: (a->b) -> f a -> f b

  id :: a -> a
  id x = x

  fmap id /= id

  data Crazy e = Crazy String e deriving Show
  -XRank2Types
  instance Functor Crazy where
    fmap g c@(Crazy s h) = Crazy (s++"!") (g h)

  fmap id $ Crazy "hello world" 1234


  instance Functor (Foo a)
  instance Functor (Bar b)
  instance (Bar => b) Functor (Foo b)


  class (Functor f, Functor g) => Composition f g where

  class Composition f g where

  instance 

  Functor (Composition f) where
    fmap = (.)


  (.) :: (b->c)->(a->b)->(a->c)
      :: ((->) CXP
            ((->) b c) 
            ((->) 
              ((->) a b) 
              ((->) a c)))

  ((->) b)
    c
  ((->) ((->) a b))
    ((->) a c)




  fmap :: (a->b)->f a->f b

  Functor law:

  fmap f 





  data NoFunctor a b = NoFunctor b a

  fmap :: (a->b)->f a->f b

  instance Functor (NoFunctor ) where
    fmap f _ = NoFunctor


  data Pair a = Pair a a
  instance Functor Pair where
    fmap f (Pair x y) = Pair (f x) (f y)




  fmap :: (a -> b) -> [] a -> [] b
  fmap (+) [1,2] :: 
  ::fmap (n -> (n-> n)) -> [] n -> [] (n -> n)

  (.) f g = \x -> (f (g x))

  [1, 2] == 1 : ([] 2)

  (+) . [1,2]

  instance Functor [] where
    fmap :: (a->b)->([] a)->([] b)
    fmap f (x:xs) = f x : fmap f xs


  fmap = (.) ?
  fmap f g = \x -> (f (g x))

  (.) (+) [1,2]
  \x -> ((+) ([1,2] x))



  fmap g . pure :: (f a -> f b) . (c -> g c) :: (f a -> f b) . (a -> f a) :: a -> f b
  pure . g :: (a -> f a) . (b -> c) :: (a -> f a) . (b -> a)  :: b -> f a


  module Main where

  data Arrow a b = A a b

  data (,) a b = (a, b)

  instance Functor ((,) a) where 
    fmap f (a,b) = (a, f b)
    fmap f (((,) a) b) = ((,) a (f b))
    fmap f ((,) a) b = ((,) a (f b))

    fmap' f (((,) a) b) = ((,) a (f b))


  main = putStrLn "hello World!"

--data Arrow a b

--instance Functor (Arrow e);  fmap = (.)

--type Arrow e = ((->) e)

--instance Functor (Arrow e) where

--instance Functor ((->) e) where
--  fmap :: (a -> b) -> ((->) e) a -> ((->) e) b
--  fmap :: (a -> b) -> (e -> a) -> e -> b
--  fmap g h x = 
--  fmap g (f x) = f (g x)
--  fmap g (f x) = f . g $ x

--(.) :: (b -> c) -> (a -> b) -> a -> c
--(.) :: (b -> c) -> (a -> b) -> (a -> c)
--(.) :: (a -> b) -> (c -> a) -> (c -> b)
--(.) :: (a -> b) -> ((->) c a) -> ((->) c b)
--(.)    f           g         x = f (g x)
--(.)    f           g         = \x -> f (g x)

--fmap :: (a -> b) -> f a -> f b
--fmap = (.)
--fmap f g x   = (.) f g x
--fmap f g     = (.) f g
--fmap f g     = \x -> f (g x)


--fmap g (f y) = (.) g (f y)
--fmap g (f y) = \x -> g ((f y) x)
--fmap g (f x) = \x -> f (g x)
--fmap g (f x) = \y -> g ((f x) y)
--fmap g (f x) = 


--instance Functor (Either e) where
--  fmap :: (a -> b) -> (Either e) a -> (Either e) b
--  fmap _ (Left l) = Left l
--  fmap g (Right r) = Right (g r)

--  --[Premise]
--  --[Conclusion]
--  --[ForwardsPrimaFacieReason]
--  --[ForwardsConclusiveReason]
--  --[BackwardsPrimaFacieReason]
--  --[BackwardsConclusiveReason]
--  --Description

----parseProblem :: Stream s m Char => ParsecT s u m Problem
----parseProblem = do 
    

----parseString :: Stream s m Char => ParsecT s u m LispVal
----parseString = do char '"'
----                 x <- many $ (try (char '\\' >> char '"') <|> noneOf "\"")
----                 char '"'
----                 return $ String x



----  [(UltimateElpistemicInterestName, Interest)]


----type ProblemPremise = String


----problem #(\d+)
----(.*?)
---- *given premises: *
----(^ *(.*?) *justification = (.*)$)+
---- *ultimate epistemic interests: *
----( *(.*?) *interest = (.*)$)+
---- *forwards prima facie reasons *
----(^ *(.*?:) *\{(.*?)\} *\|\|=> *(.*?) *(variables = \{(.*?)\})? *strength = (.*?) *$)+
---- *backwards prima facie reasons *
----(^ *(.*?:) *\{(.*?)\} *\{(.*?)\} *\|\|=> *(.*?) *(variables = {(.*?)})? *strength = (.*?) *$)+
---- *forwards conclusive reasons *
----(^ *(.*?:) *\{(.*?)\} *\|\|=> *(.*?) *(variables = \{(.*?)\})? *strength = (.*?) *$)+
---- *backwards conclusive reasons *
----(^ *(.*?:) *\{(.*?)\} *\{(.*?)\} *\|\|=> *(.*?) *(variables = {(.*?)})? *strength = (.*?) *$)+

--Problem #1
--This is a case of collective rebutting defeat
--Given premises:
--     P    justification = 1.0
--     A    justification = 1.0
--Ultimate epistemic interests:
--     R    interest = 1.0

--    FORWARDS PRIMA FACIE REASONS
--      pf-reason_1:   {P} ||=> Q   strength = 1.0
--      pf-reason_2:   {Q} ||=> R   strength = 1.0
--      pf-reason_3:   {C} ||=> ~R   strength = 1.0
--      pf-reason_4:   {B} ||=> C   strength = 1.0
--      pf-reason_5:   {A} ||=> B   strength = 1.0



--Problem #8
--Reasoning with lists
--Given premises:
    
--Ultimate epistemic interests:
--       (~(some x)(member x a) -> (a = NIL))    interest = 1

--    FORWARDS CONCLUSIVE REASONS
--      cons-identity-1:   {((cons x y) = (cons z w))} ||=> (x = z)     variables = {x , y , z , w}    strength = 1
--      cons-identity-2:   {((cons x y) = (cons z w))} ||=> (y = w)     variables = {x , y , z , w}    strength = 1
--      member-1:   {(member x y)} ||=> ((x = (car y)) v (member x (cdr y)))     variables = {x , y}    strength = 1
--      unit-set:   {(member x (cons y NIL))} ||=> (x = y)     variables = {x , y}    strength = 1

--    BACKWARDS CONCLUSIVE REASONS
--      cons-identity-3:   {} {(x = z) , (y = w)}  ||=> ((cons x y) = (cons z w))     variables = {x , y , z , w}    strength = 1
--      member-2:   {} {((~(y = NIL) & (x = (car y))) v (member x (cdr y)))}  ||=> (member x y)     variables = {x , y}    strength = 1
--      member-3:   {} {(~(x = (car y)) & ~(member x (cdr y)))}  ||=> ~(member x y)     variables = {x , y}    strength = 1
--      self-identity:   {} {} ||=> (x = x)     variables = {x}    strength = 1
--      non-NIL:   {} {(some x)(some y)(z = (cons x y))} ||=> ~(z = NIL)     variables = {z}    strength = 1




--Problem #1
--None of the Avon letters is in the same place as any
--of the Bury letters.
--All of the Bury letters are in the same place as SOME
--of the Caton letters.
--Therefore, some of the Caton letters are not in the same place as 
--any of the Avon letters.
--Given premises:
--     (all x)(all y)[((A x) & (B y)) -> ~((p x) = (p y))]    justification = 1.0
--     (all x)[(B x) -> (some y)((C y) & ((p x) = (p y)))]    justification = 1.0
--     (some x)(B x)    justification = 1.0
--Ultimate epistemic interests:
--     (some x)[(C x) & (all y)((A y) -> ~((p x) = (p y)))]    interest = 1.0

--    FORWARDS CONCLUSIVE REASONS
--      con-reason_1:   {(x = y) , (y = z)} ||=> (x = z)  variables = {x , y , z}   strength = 1.0
--      con-reason_2:   {(x = y)} ||=> (y = x)  variables = {x , y}   strength = 1.0


--Problem #6
--Three children are standing in a line.  At least one of them is a girl, and at least one 
--of them is a boy.  Is a girl standing next to a boy?
--(N x y) means (x is next to y, and (G x) now means (x is a girl).)
--Given premises:
--     ((N a b) & (N b c))    justification = 1.0
--     (~(G a) v (~(G b) v ~(G c)))    justification = 1.0
--     ((G a) v ((G b) v (G c)))    justification = 1.0
--Ultimate epistemic interests:
--     (some x)(some y)((N x y) & (~(G x) & (G y)))    interest = 1.0

--    FORWARDS CONCLUSIVE REASONS
--      con-reason_1:   {(N x y)} ||=> (N y x)  variables = {x,y}   strength = 1.0


--Problem #17
--figure 18 -- the paradox of the preface, using logic.
--Given premises:
--     P1    justification = 1.0
--     P2    justification = 1.0
--     P3    justification = 1.0
--     S    justification = 1.0
--     T    justification = 1.0
--Ultimate epistemic interests:
--     (Q1 & (Q2 & Q3))    interest = 1.0

--    FORWARDS PRIMA FACIE REASONS
--      pf-reason_1:   {P1} ||=> Q1   strength = 1.0
--      pf-reason_2:   {P2} ||=> Q2   strength = 1.0
--      pf-reason_3:   {P3} ||=> Q3   strength = 1.0
--      pf-reason_4:   {S} ||=> R   strength = 1.0
--      pf-reason_5:   {T} ||=> ~(Q1 & (Q2 & Q3))   strength = 1.0
--      pf-reason_6:   {S1} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0
--      pf-reason_7:   {S2} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0
--      pf-reason_8:   {S3} ||=> (T @ ~(Q1 & (Q2 & Q3)))   strength = 1.0

--    FORWARDS CONCLUSIVE REASONS
--      con-reason_4:   {R , Q1 , Q3} ||=> S2   strength = 1.0
--      con-reason_5:   {R , Q2 , Q3} ||=> S1   strength = 1.0
--      con-reason_6:   {R , Q1 , Q2} ||=> S3   strength = 1.0



--Problem #1
--This is a case of collective rebutting defeat
--Given premises:
--     P    justification = 1.0
--     A    justification = 1.0
--Ultimate epistemic interests:
--     R    interest = 1.0

--    FORWARDS PRIMA FACIE REASONS
--      pf-reason_1:   {P} ||=> Q   strength = 1.0
--      pf-reason_2:   {Q} ||=> R   strength = 1.0
--      pf-reason_3:   {C} ||=> ~R   strength = 1.0
--      pf-reason_4:   {B} ||=> C   strength = 1.0
--      pf-reason_5:   {A} ||=> B   strength = 1.0

--Problem #2
--This is the same as #1 except that some reasons are backwards.
--Given premises:
--     P    justification = 1.0
--     A    justification = 1.0
--Ultimate epistemic interests:
--     R    interest = 1.0

--    FORWARDS PRIMA FACIE REASONS
--      pf-reason_1:   {P} ||=> Q   strength = 1.0
--      pf-reason_2:   {Q} ||=> R   strength = 1.0
--      pf-reason_3:   {A} ||=> B   strength = 1.0

--    BACKWARDS PRIMA FACIE REASONS
--      pf-reason_4:   {} {C} ||=> ~R   strength = 1.0
--      pf-reason_5:   {} {B} ||=> C   strength = 1.0


--Problem #1
--description of problem
--Given premises:
--     P    justification = 1
--     P    justification = 1
--     P    justification = 1
--     P    justification = 1
--     P    justification = 1

--Ultimate epistemic interests:
--     R    interest = 1
--     R    interest = 1
--     R    interest = 1

--    FORWARDS PRIMA FACIE REASONS
--      pf-reason 1:   {P , P , P} ||=> Q     variables = {x , y , z}    strength = 1
--      pf-reason 1:   {P , P , P} ||=> Q     variables = {x , y , z}    strength = 1
--      pf-reason 1:   {P , P , P} ||=> Q     variables = {x , y , z}    strength = 1
--      con-reason 1:   {<P , condition> , <P , condition>} ||=> Q     variables = {x , y , z}    strength = 1
--      con-reason 1:   {<P , condition> , <P , condition>} ||=> Q     variables = {x , y , z}    strength = 1

--    FORWARDS CONCLUSIVE REASONS
--      con-reason 1:   {P , P , P} ||=> Q     variables = {x , y , z}    strength = 1
--      con-reason 1:   {P , P , P} ||=> Q     variables = {x , y , z}    strength = 1
--      con-reason 1:   {P , P , P} ||=> Q     variables = {x , y , z}    strength = 1
--      con-reason 1:   {<P , condition> , <P , condition>} ||=> Q     variables = {x , y , z}    strength = 1
--      con-reason 1:   {<P , condition> , <P , condition>} ||=> Q     variables = {x , y , z}    strength = 1

--    BACKWARDS PRIMA FACIE REASONS
--      pf-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      pf-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      pf-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      pf-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      pf-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1

--    BACKWARDS CONCLUSIVE REASONS
--      con-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      con-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      con-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      con-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1
--      con-reason 2:   {P , P , P} {Q , Q , Q} ||=> R     variables = {x , y , z}    strength = 1




% Another literate Haskell post:

% I've tried a few times to read various documents on the web about
% Monad Transformers in Haskell. I think that in almost every case the
% authors are trying to show how clever they are rather than explaining
% their use. If I had just seen the simplest possible examples of Monad
% Transformers at work I would have been able to figure out what was going
% on and that would have given me enough information to bootstrap myself
% into Monad Transforming enlightenment.

% So to save other people the trouble I went through I'm providing you
% with examples of Monad Transformers at work. I'm not even going to
% explain in detail how they work, they're close to self-evident once the
% main features are pointed out.

% > import Control.Monad.State
% > import Control.Monad.Identity

% Firstly here are two examples of the use of the State Monad. This
% code isn't intended as a tutorial on the State Monad so I won't
% explain how they work.

% > test1 = do
% >             a <- get
% >             modify (+1)
% >             b <- get
% >             return (a,b)

% > test2 = do
% >             a <- get
% >             modify (++"1")
% >             b <- get
% >             return (a,b)

% > go1 = evalState test1 0
% > go2 = evalState test2 "0" 

% Note how evalState 'unwraps' the State Monad and gives you back the
% answer at the end.

% So the question is: how do I combine both of these states into one
% so that I can update or read either the integer or the string state
% at will? I could cheat and make a new state of type (Int,String)
% but that isn't a general solution.

% The idea is that you use a Monad Transformer. A Monad Transformer
% if like a layer of onion peel. You start with the Identity monad
% and then use Monad Transformers to add layers of functionality.
% So to get a two-state monad you take the Identity and add two
% layers of stateness to it. To get the answer at the end you need
% to unwrap the State layers and then unwrap the Identity layer too.

% When you're inside your 'do' expression you need a way to choose
% which Monad you're talking to. Ordinary Monad commands will
% talk to the outermost layer and you can use 'lift' to send your
% commands inwards by one layer.

% The following should now be self-evident:

% > test3 = do
% >     modify (+ 1)
% >     lift $ modify (++ "1")
% >     a <- get
% >     b <- lift get
% >     return (a,b)

% > go3 = runIdentity $ evalStateT (evalStateT test3 0) "0"

% Note that we use evalStateT to unwrap the State layer instead
% of evalState. evalStateT is what you use to unwrap one layer
% of the Monad. evalState is what you use when your entire Monad
% is just the State monad. When State is a layer, rather than
% the whole thing, it's called StateT. (Try :type go3 in ghci.)

% What if you want to combine IO and State? For various reasons
% the IO monad must form the innermost core of your onion so
% there's no need to wrap an IO layer around the Identity,
% you can just start with IO. And when you unwrap you don't
% need to unwrap the IO layer because the Haskell compiler does
% that for you. (Now you can see why you can't layer IO, you're
% not supposed to unwrap IO as it's the job of the code that
% calls main at the top level to do that.)

% So here we go:

% > test5 = do
% >     modify (+ 1)
% >     a <- get
% >     lift (print a)
% >     modify (+ 1)
% >     b <- get
% >     lift (print b)

% > go5 = evalStateT test5 0

% At this point you might be suspicious that IO is being handled
% slightly differently from State. So here's a StateT layer
% wrapped around State:

% > test7 = do
% >     modify (+ 1)
% >     lift $ modify (++ "1")
% >     a <- get
% >     b <- lift get
% >     return (a,b)

% > go7 = evalState (evalStateT test7 0) "0"

% You can probably safely ignore my comments and crib the code above
% directly for your own use.

% And credit where credit's due: I found the following link to be
% more helpful than any other in trying to figure this stuff out
% http://www.cs.nott.ac.uk/~nhn/MGS2006/LectureNotes/lecture03-9up.pdf
% (But I still felt that this link was obfuscating.)

% You may now be wondering where test4 and test6 are. So am I.

% Update: I just figured out that you don't always need to use the
% 'lift' operation. Some of the Monad Transformers have been defined
% so that the commands will automatically be passed into the inner
% Monad (and further) if needed. I think it's slightly confusing to
% write code this way, however.

% > main = do
% > print go2 
% > print go7 -- sequence $ fmap print [go2, go7]

% go2 :: ([Char], [Char])
% go7 :: (Integer, [Char])
% print :: Show a => a -> IO ()

% Show a, Show b => a -> b -> IO ()


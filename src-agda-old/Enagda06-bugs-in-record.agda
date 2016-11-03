module Enagda06-bugs-in-record where

record Bar (A B : Set) : Set where
  field
    f : A

record Baz (A B : Set) : Set where
  record Dummy : Set where
    postulate
      g : B
   
  open Bar public

I've managed to trigger an internal error when the verbosity is set to 100.
```agda
{-# OPTIONS -v 100 #-}

module AgdaErrorDisplayForm197 (A : Set) where

module M (_ : Set) where
  data D (n : Set) : Set where
    d : D n

open M A
```
The error message is

    An internal error has occurred. Please report this as a bug.
    Location of the error: src/full/Agda/TypeChecking/DisplayForm.hs:197

The last line in the debug window is

    displayForm for AgdaErrorDisplayForm197.M.D: context = [CtxId 126,CtxId 125,CtxId 26], dfs = [Local AgdaErrorDisplayForm197 (Display {dfFreeVars = 0, dfPats = [Apply ru(Var 1 []),Apply ru(Var 1 [])], dfRHS = DTerm (Def AgdaErrorDisplayForm197._.D [Apply ru(Var 0 [])])})]

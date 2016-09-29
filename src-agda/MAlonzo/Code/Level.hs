{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Level where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
name9 = "Level.Lift.lower"
d9 (C10 v0) = MAlonzo.RTE.mazCoerce v0
d9 v0 = MAlonzo.RTE.mazIncompleteMatch name9
name4 = "Level.Lift"
d4 a0 a1 a2 = ()
 
newtype T4 a0 = C10 a0
name10 = "Level.Lift.lift"
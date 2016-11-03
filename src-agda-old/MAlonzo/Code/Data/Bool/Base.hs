{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Bool.Base where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Unit.Base
name7 = "Data.Bool.Base.T"
d7 (True) = MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3
d7 v0 = MAlonzo.RTE.mazCoerce (d_1_7 (MAlonzo.RTE.mazCoerce v0))
  where d_1_7 (False)
          = MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Empty.d2
        d_1_7 v0 = MAlonzo.RTE.mazIncompleteMatch name7
name10 = "Data.Bool.Base.if_then_else_"
d10 v0 v1 (True) v2 v3 = MAlonzo.RTE.mazCoerce v2
d10 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d_1_10 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4))
  where d_1_10 v0 v1 (False) v2 v3 = MAlonzo.RTE.mazCoerce v3
        d_1_10 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name10
name15 = "Data.Bool.Base._\8743_"
d15 (True) v0 = MAlonzo.RTE.mazCoerce v0
d15 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_15 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_15 (False) v0 = MAlonzo.RTE.mazCoerce False
        d_1_15 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name15
name4 = "Data.Bool.Base.Bool.true"
 
d4 :: Bool
d4 = True
name21 = "Data.Bool.Base._xor_"
d21 (True) v0
  = MAlonzo.RTE.mazCoerce (d6 (MAlonzo.RTE.mazCoerce v0))
d21 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_21 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_21 (False) v0 = MAlonzo.RTE.mazCoerce v0
        d_1_21 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name21
name5 = "Data.Bool.Base.Bool.false"
 
d5 :: Bool
d5 = False
name18 = "Data.Bool.Base._\8744_"
d18 (True) v0 = MAlonzo.RTE.mazCoerce True
d18 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_18 (False) v0 = MAlonzo.RTE.mazCoerce v0
        d_1_18 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name18
name3 = "Data.Bool.Base.Bool"
d3 = ()
 
check4 :: Bool
check4 = True
 
check5 :: Bool
check5 = False
 
cover3 :: Bool -> ()
cover3 x
  = case x of
        True -> ()
        False -> ()
name6 = "Data.Bool.Base.not"
d6 (True) = MAlonzo.RTE.mazCoerce False
d6 v0 = MAlonzo.RTE.mazCoerce (d_1_6 (MAlonzo.RTE.mazCoerce v0))
  where d_1_6 (False) = MAlonzo.RTE.mazCoerce True
        d_1_6 v0 = MAlonzo.RTE.mazIncompleteMatch name6
mazBoolToHBool = let { f True = True; f False = False; } in f
mazHBoolToBool = let { f True = True; f False = False; } in f
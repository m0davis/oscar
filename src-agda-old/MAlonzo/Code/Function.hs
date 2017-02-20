{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Function where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Level
name55 = "Function._\738_"
d55 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (\ v8 ->
         v6 (MAlonzo.RTE.mazCoerce v8)
           (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v8))))
name29 = "Function._\8728\8242_"
d29 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (d19 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce (\ v8 -> v4))
         (MAlonzo.RTE.mazCoerce (\ v8 -> \ v9 -> v5))
         (MAlonzo.RTE.mazCoerce (\ v8 -> v6))
         (MAlonzo.RTE.mazCoerce v7))
name138 = "Function.case_of_"
d138 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d130 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce (\ v6 -> v3))
         (MAlonzo.RTE.mazCoerce v5))
name113 = "Function._-[_]-_"
d113 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = MAlonzo.RTE.mazCoerce
      (\ v13 ->
         \ v14 ->
           v11
             (MAlonzo.RTE.mazCoerce
                (v10 (MAlonzo.RTE.mazCoerce v13) (MAlonzo.RTE.mazCoerce v14)))
             (MAlonzo.RTE.mazCoerce
                (v12 (MAlonzo.RTE.mazCoerce v13) (MAlonzo.RTE.mazCoerce v14))))
name79 = "Function._$_"
d79 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v5))
name5 = "Function.Fun\8322"
d5 v0 v1 = MAlonzo.RTE.mazCoerce ()
name69 = "Function.flip"
d69 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (\ v7 ->
         \ v8 -> v6 (MAlonzo.RTE.mazCoerce v8) (MAlonzo.RTE.mazCoerce v7))
name130 = "Function.case_return_of_"
d130 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce (v5 (MAlonzo.RTE.mazCoerce v3))
name98 = "Function._on_"
d98 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (\ v8 ->
         \ v9 ->
           v6 (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v8)))
             (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v9))))
name2 = "Function.Fun\8321"
d2 v0 v1 = MAlonzo.RTE.mazCoerce ()
name34 = "Function.id"
d34 v0 v1 v2 = MAlonzo.RTE.mazCoerce v2
name19 = "Function._\8728_"
d19 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (\ v8 ->
         v6 (MAlonzo.RTE.mazCoerce v8)
           (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v8))))
name88 = "Function._\10216_\10217_"
d88 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (v7 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v8))
name40 = "Function.const"
d40 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazCoerce (\ v5 -> v4)
name121 = "Function._\8715_"
d121 v0 v1 v2 = MAlonzo.RTE.mazCoerce v2
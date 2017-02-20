{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.DifferenceList where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Function
name35 = "Data.DifferenceList.fromList"
d35 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d88 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d5 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d5 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d5 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d18 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1))))
name3 = "Data.DifferenceList.DiffList"
d3 v0 v1 = MAlonzo.RTE.mazCoerce ()
name54 = "Data.DifferenceList._.concat'"
d54 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (\ v3 ->
         \ v4 ->
           MAlonzo.Code.Data.List.Base.d81 (MAlonzo.RTE.mazCoerce v3)
             (MAlonzo.RTE.mazCoerce v3)
             (MAlonzo.RTE.mazCoerce
                (d3 (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4)))
             (MAlonzo.RTE.mazCoerce
                (d3 (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4)))
             (MAlonzo.RTE.mazCoerce
                (d25 (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4)))
             (MAlonzo.RTE.mazCoerce
                (d13 (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4))))
name57 = "Data.DifferenceList.take"
d57 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d206 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name25 = "Data.DifferenceList._++_"
d25 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (\ v4 ->
         v2 (MAlonzo.RTE.mazCoerce (v3 (MAlonzo.RTE.mazCoerce v4))))
name31 = "Data.DifferenceList.toList"
d31 v0 v1 v2
  = MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce []))
name21 = "Data.DifferenceList.[_]"
d21 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d17 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce
            (d13 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name48 = "Data.DifferenceList.concat"
d48 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d54 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (d31 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce
                  (d3 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
               (MAlonzo.RTE.mazCoerce v2))))
name17 = "Data.DifferenceList._\8759_"
d17 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce ((:) (MAlonzo.RTE.mazCoerce v2))))
name7 = "Data.DifferenceList.lift"
d7 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (\ v4 ->
         v2 (MAlonzo.RTE.mazCoerce (v3 (MAlonzo.RTE.mazCoerce v4))))
name42 = "Data.DifferenceList.map"
d42 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d88 (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d5 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d5 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d5 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d37 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce
                  (d31 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v5)))))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d18 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v3))))
name61 = "Data.DifferenceList.drop"
d61 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.List.Base.d214 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name13 = "Data.DifferenceList.[]"
d13 = MAlonzo.RTE.mazCoerce (\ v0 -> \ v1 -> \ v2 -> v2)
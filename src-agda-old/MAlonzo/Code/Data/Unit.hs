{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Unit where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Data.Unit.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
name14 = "Data.Unit.decSetoid"
d14
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d597 (MAlonzo.RTE.mazCoerce d7))
name10 = "Data.Unit._.antisym"
d10 (MAlonzo.Code.Data.Unit.Base.C4)
  (MAlonzo.Code.Data.Unit.Base.C4) v0 v1
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d10 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name10
name7 = "Data.Unit.decTotalOrder"
d7
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.C959
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3)))
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d7)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.C947
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Relation.Binary.C923
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Relation.Binary.C804
                           (MAlonzo.RTE.mazCoerce
                              (MAlonzo.Code.Relation.Binary.C704
                                 (MAlonzo.RTE.mazCoerce
                                    (MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d25
                                       (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
                                       (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3)))
                                 (MAlonzo.RTE.mazCoerce
                                    (\ v0 -> \ v1 -> \ v2 -> MAlonzo.Code.Data.Unit.Base.C12))
                                 (MAlonzo.RTE.mazCoerce
                                    (\ v0 ->
                                       \ v1 ->
                                         \ v2 -> \ v3 -> \ v4 -> MAlonzo.Code.Data.Unit.Base.C12))))
                           (MAlonzo.RTE.mazCoerce
                              (\ v0 ->
                                 \ v1 ->
                                   d10 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.C4)
                                     (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.C4)))))
                     (MAlonzo.RTE.mazCoerce d4)))
               (MAlonzo.RTE.mazCoerce d2)
               (MAlonzo.RTE.mazCoerce d3))))
name6 = "Data.Unit.setoid"
d6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.PropositionalEquality.d56
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3))
name3 = "Data.Unit._\8804?_"
d3 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.C11
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.C12))
name2 = "Data.Unit._\8799_"
d2 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.C11
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256))
name5 = "Data.Unit.preorder"
d5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.PropositionalEquality.d66
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3))
name4 = "Data.Unit.total"
d4 v0 v1
  = MAlonzo.RTE.mazCoerce
      (Left (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.C12))
name15 = "Data.Unit.poset"
d15
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d585 (MAlonzo.RTE.mazCoerce d7))
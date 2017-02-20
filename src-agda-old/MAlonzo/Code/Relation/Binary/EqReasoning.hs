{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.EqReasoning where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name11 = "Relation.Binary.EqReasoning._.isPreorder"
d11 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d73 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
name16 = "Relation.Binary.EqReasoning._.trans"
d16 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d72 (MAlonzo.RTE.mazCoerce v0))
name14 = "Relation.Binary.EqReasoning._.reflexive"
d14 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d70 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
name23 = "Relation.Binary.EqReasoning._.begin_"
d23
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 -> MAlonzo.Code.Relation.Binary.PreorderReasoning.d30)
name7 = "Relation.Binary.EqReasoning._._\8776_"
d7 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d66 (MAlonzo.RTE.mazCoerce v0))
name12 = "Relation.Binary.EqReasoning._.preorder"
d12 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d74 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
name13 = "Relation.Binary.EqReasoning._.refl"
d13 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d69 (MAlonzo.RTE.mazCoerce v0))
name10 = "Relation.Binary.EqReasoning._.isEquivalence"
d10 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d67 (MAlonzo.RTE.mazCoerce v0))
name19 = "Relation.Binary.EqReasoning._._\8718"
d19 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.PreorderReasoning.d49
         (MAlonzo.RTE.mazCoerce
            (d12 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name24 = "Relation.Binary.EqReasoning._.relTo"
name8 = "Relation.Binary.EqReasoning._.Carrier"
d8 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d65 (MAlonzo.RTE.mazCoerce v0))
name25 = "Relation.Binary.EqReasoning._._IsRelatedTo_.relTo"
name9 = "Relation.Binary.EqReasoning._.indexedSetoid"
d9 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d77 (MAlonzo.RTE.mazCoerce v0))
name22 = "Relation.Binary.EqReasoning._._\8776\10216\10217_"
d22
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 -> MAlonzo.Code.Relation.Binary.PreorderReasoning.d46)
name15 = "Relation.Binary.EqReasoning._.sym"
d15 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d71 (MAlonzo.RTE.mazCoerce v0))
name20 = "Relation.Binary.EqReasoning._._\8764\10216_\10217_"
d20 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.PreorderReasoning.d35
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (d12 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name21 = "Relation.Binary.EqReasoning._._\8776\10216_\10217_"
d21 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.PreorderReasoning.d41
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (d12 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name18 = "Relation.Binary.EqReasoning._._IsRelatedTo_"
d18 a0 a1 a2 a3 a4 = ()
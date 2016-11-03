{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.PreorderReasoning where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Relation.Binary
name13 = "Relation.Binary.PreorderReasoning._.refl"
d13 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d49 (MAlonzo.RTE.mazCoerce v0))
name10 = "Relation.Binary.PreorderReasoning._.Carrier"
d10 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d43 (MAlonzo.RTE.mazCoerce v0))
name23 = "Relation.Binary.PreorderReasoning._IsRelatedTo_"
d23 a0 a1 a2 a3 a4 a5 = ()
 
newtype T23 a0 = C27 a0
name12 = "Relation.Binary.PreorderReasoning._.isPreorder"
d12 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d46 (MAlonzo.RTE.mazCoerce v0))
name17 = "Relation.Binary.PreorderReasoning._._.Eq.refl"
d17 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d53 (MAlonzo.RTE.mazCoerce v0))
name49 = "Relation.Binary.PreorderReasoning._\8718"
d49 v0 v1
  = MAlonzo.RTE.mazCoerce
      (C27
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.d49 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1))))
name46 = "Relation.Binary.PreorderReasoning._\8776\10216\10217_"
d46 v0 = MAlonzo.RTE.mazCoerce v0
name14 = "Relation.Binary.PreorderReasoning._.reflexive"
d14 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d50 (MAlonzo.RTE.mazCoerce v0))
name30 = "Relation.Binary.PreorderReasoning.begin_"
d30 (C27 v0) = MAlonzo.RTE.mazCoerce v0
d30 v0 = MAlonzo.RTE.mazIncompleteMatch name30
name11 = "Relation.Binary.PreorderReasoning._.isEquivalence"
d11 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d48 (MAlonzo.RTE.mazCoerce v0))
name27 = "Relation.Binary.PreorderReasoning._IsRelatedTo_.relTo"
name16 = "Relation.Binary.PreorderReasoning._.\8764-resp-\8776"
d16 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d52 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
name18 = "Relation.Binary.PreorderReasoning._._.Eq.reflexive"
d18 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d54 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
name15 = "Relation.Binary.PreorderReasoning._.trans"
d15 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d51 (MAlonzo.RTE.mazCoerce v0))
name20 = "Relation.Binary.PreorderReasoning._._.Eq.trans"
d20 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d56 (MAlonzo.RTE.mazCoerce v0))
name9 = "Relation.Binary.PreorderReasoning._._\8776_"
d9 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d44 (MAlonzo.RTE.mazCoerce v0))
name41 = "Relation.Binary.PreorderReasoning._\8776\10216_\10217_"
d41 v0 v1 v2 v3 v4 v5 v6 v7 (C27 v8)
  = MAlonzo.RTE.mazCoerce
      (C27
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.d51 (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Relation.Binary.d50 (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v4)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v7)))
               (MAlonzo.RTE.mazCoerce v8))))
d41 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazIncompleteMatch name41
name19 = "Relation.Binary.PreorderReasoning._._.Eq.sym"
d19 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d55 (MAlonzo.RTE.mazCoerce v0))
name35 = "Relation.Binary.PreorderReasoning._\8764\10216_\10217_"
d35 v0 v1 v2 v3 v4 v5 v6 v7 (C27 v8)
  = MAlonzo.RTE.mazCoerce
      (C27
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.d51 (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6)
               (MAlonzo.RTE.mazCoerce v7)
               (MAlonzo.RTE.mazCoerce v8))))
d35 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazIncompleteMatch name35
name8 = "Relation.Binary.PreorderReasoning._._\8764_"
d8 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d45 (MAlonzo.RTE.mazCoerce v0))
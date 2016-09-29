{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.Core where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary
name93 = "Relation.Binary.Core.Symmetric"
d93 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d87 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v3))
name42 = "Relation.Binary.Core._Preserves_\10230_"
d42 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (d32 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v8))
name234 = "Relation.Binary.Core.NonEmpty"
d234 a0 a1 a2 a3 a4 a5 = ()
 
data T234 a0 a1 a2 = C247 a0 a1 a2
name170 = "Relation.Binary.Core.Substitutive"
d170 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazCoerce ()
name266 = "Relation.Binary.Core.IsEquivalence"
d266 a0 a1 a2 a3 = ()
 
data T266 a0 a1 a2 = C453 a0 a1 a2
name215 = "Relation.Binary.Core.Tri.tri>"
name87 = "Relation.Binary.Core.Sym"
d87 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (d21 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Function.d69 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v3)))
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce (\ v8 -> \ v9 -> ()))
               (MAlonzo.RTE.mazCoerce v7))))
name55 = "Relation.Binary.Core._Preserves\8322_\10230_\10230_"
d55 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = MAlonzo.RTE.mazCoerce ()
name247 = "Relation.Binary.Core.NonEmpty.nonEmpty"
name76 = "Relation.Binary.Core.Irreflexive"
d76 v0 v1 v2 v3 v4 v5 v6 v7 = MAlonzo.RTE.mazCoerce ()
name12 = "Relation.Binary.Core.Rel"
d12 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d6 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
name252 = "Relation.Binary.Core.Dummy._\8801_"
d252 a0 a1 a2 a3 = ()
 
data T252 = C256
name220 = "Relation.Binary.Core.Trichotomous"
d220 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
name225 = "Relation.Binary.Core._._>_"
d225 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d69 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce (\ v6 -> \ v7 -> ()))
         (MAlonzo.RTE.mazCoerce v5))
name161 = "Relation.Binary.Core._Respects\8322_"
d161 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.d44
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v0)))))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v0)))))
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce ()))
name187 = "Relation.Binary.Core.Total"
d187 v0 v1 v2 v3 = MAlonzo.RTE.mazCoerce ()
name256 = "Relation.Binary.Core.Dummy._\8801_.refl"
name32 = "Relation.Binary.Core._=[_]\8658_"
d32 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (d21 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Function.d98 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v3)))
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce ())
               (MAlonzo.RTE.mazCoerce v8)
               (MAlonzo.RTE.mazCoerce v7))))
name144 = "Relation.Binary.Core.Asymmetric"
d144 v0 v1 v2 v3 = MAlonzo.RTE.mazCoerce ()
name21 = "Relation.Binary.Core._\8658_"
d21 v0 v1 v2 v3 v4 v5 v6 v7 = MAlonzo.RTE.mazCoerce ()
name277 = "Relation.Binary.Core.IsEquivalence.reflexive"
d277 v0 v1 v2 v3 v4 v5 v6 (C256)
  = MAlonzo.RTE.mazCoerce
      (d274 (MAlonzo.RTE.mazCoerce v4) (MAlonzo.RTE.mazCoerce v5))
d277 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazIncompleteMatch name277
name245 = "Relation.Binary.Core.NonEmpty.y"
d245 (C247 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d245 v0 = MAlonzo.RTE.mazIncompleteMatch name245
name197 = "Relation.Binary.Core.Tri"
d197 a0 a1 a2 a3 a4 a5 = ()
 
data T197 a0 a1 a2 = C207 a0 a1 a2
                   | C211 a0 a1 a2
                   | C215 a0 a1 a2
name453 = "Relation.Binary.Core.recCon-NOT-PRINTED"
name274 = "Relation.Binary.Core.IsEquivalence.refl"
d274 (C453 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d274 v0 = MAlonzo.RTE.mazIncompleteMatch name274
name130 = "Relation.Binary.Core.Transitive"
d130 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d104 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v3))
name207 = "Relation.Binary.Core.Tri.tri<"
name276 = "Relation.Binary.Core.IsEquivalence.trans"
d276 (C453 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d276 v0 = MAlonzo.RTE.mazIncompleteMatch name276
name244 = "Relation.Binary.Core.NonEmpty.x"
d244 (C247 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d244 v0 = MAlonzo.RTE.mazIncompleteMatch name244
name180 = "Relation.Binary.Core.Decidable"
d180 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
name246 = "Relation.Binary.Core.NonEmpty.proof"
d246 (C247 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d246 v0 = MAlonzo.RTE.mazIncompleteMatch name246
name6 = "Relation.Binary.Core.REL"
d6 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazCoerce ()
name275 = "Relation.Binary.Core.IsEquivalence.sym"
d275 (C453 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d275 v0 = MAlonzo.RTE.mazIncompleteMatch name275
name211 = "Relation.Binary.Core.Tri.tri\8776"
name67 = "Relation.Binary.Core.Reflexive"
d67 v0 v1 v2 v3 = MAlonzo.RTE.mazCoerce ()
name259 = "Relation.Binary.Core.Dummy._\8802_"
d259 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.d3 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (d252 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name136 = "Relation.Binary.Core.Antisymmetric"
d136 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
name120 = "Relation.Binary.Core.TransFlip"
d120 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = MAlonzo.RTE.mazCoerce ()
name104 = "Relation.Binary.Core.Trans"
d104 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = MAlonzo.RTE.mazCoerce ()
name152 = "Relation.Binary.Core._Respects_"
d152 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
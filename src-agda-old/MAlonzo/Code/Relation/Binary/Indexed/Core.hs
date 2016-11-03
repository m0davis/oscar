{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.Indexed.Core where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Core
name57 = "Relation.Binary.Indexed.Core.IsEquivalence"
d57 a0 a1 a2 a3 a4 a5 = ()
 
data T57 a0 a1 a2 = C149 a0 a1 a2
name89 = "Relation.Binary.Indexed.Core.Setoid._.reflexive"
d89 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d71 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d84 (MAlonzo.RTE.mazCoerce v4)))
         (MAlonzo.RTE.mazCoerce (d85 (MAlonzo.RTE.mazCoerce v4)))
         (MAlonzo.RTE.mazCoerce (d86 (MAlonzo.RTE.mazCoerce v4))))
name182 = "Relation.Binary.Indexed.Core.recCon-NOT-PRINTED"
name86 = "Relation.Binary.Indexed.Core.Setoid.isEquivalence"
d86 (C182 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d86 v0 = MAlonzo.RTE.mazIncompleteMatch name86
name67 = "Relation.Binary.Indexed.Core.IsEquivalence.refl"
d67 (C149 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d67 v0 = MAlonzo.RTE.mazIncompleteMatch name67
name88 = "Relation.Binary.Indexed.Core.Setoid._.refl"
d88 v0
  = MAlonzo.RTE.mazCoerce
      (d67 (MAlonzo.RTE.mazCoerce (d86 (MAlonzo.RTE.mazCoerce v0))))
name21 = "Relation.Binary.Indexed.Core.Rel"
d21 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d11 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4))
name69 = "Relation.Binary.Indexed.Core.IsEquivalence.trans"
d69 (C149 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d69 v0 = MAlonzo.RTE.mazIncompleteMatch name69
name85 = "Relation.Binary.Indexed.Core.Setoid._\8776_"
d85 (C182 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d85 v0 = MAlonzo.RTE.mazIncompleteMatch name85
name37 = "Relation.Binary.Indexed.Core.Symmetric"
d37 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
name149 = "Relation.Binary.Indexed.Core.recCon-NOT-PRINTED"
name84 = "Relation.Binary.Indexed.Core.Setoid.Carrier"
d84 (C182 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d84 v0 = MAlonzo.RTE.mazIncompleteMatch name84
name68 = "Relation.Binary.Indexed.Core.IsEquivalence.sym"
d68 (C149 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d68 v0 = MAlonzo.RTE.mazIncompleteMatch name68
name46 = "Relation.Binary.Indexed.Core.Transitive"
d46 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
name91 = "Relation.Binary.Indexed.Core.Setoid._.trans"
d91 v0
  = MAlonzo.RTE.mazCoerce
      (d69 (MAlonzo.RTE.mazCoerce (d86 (MAlonzo.RTE.mazCoerce v0))))
name11 = "Relation.Binary.Indexed.Core.REL"
d11 v0 v1 v2 v3 v4 v5 v6 v7 v8 = MAlonzo.RTE.mazCoerce ()
name29 = "Relation.Binary.Indexed.Core.Reflexive"
d29 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazCoerce ()
name90 = "Relation.Binary.Indexed.Core.Setoid._.sym"
d90 v0
  = MAlonzo.RTE.mazCoerce
      (d68 (MAlonzo.RTE.mazCoerce (d86 (MAlonzo.RTE.mazCoerce v0))))
name71 = "Relation.Binary.Indexed.Core.IsEquivalence.reflexive"
d71 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce
      (d67 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce v8))
d71 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = MAlonzo.RTE.mazIncompleteMatch name71
name76 = "Relation.Binary.Indexed.Core.Setoid"
d76 a0 a1 a2 a3 = ()
 
data T76 a0 a1 a2 = C182 a0 a1 a2
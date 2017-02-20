{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
       where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Consequences.Core
import qualified MAlonzo.Code.Relation.Binary.Core
name21 = "Relation.Binary.PropositionalEquality.Core.resp\8322"
d21 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Consequences.Core.d10
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce
            (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name6 = "Relation.Binary.PropositionalEquality.Core.sym"
d6 v0 v1 v2 v3 (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d6 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name6
name9 = "Relation.Binary.PropositionalEquality.Core.trans"
d9 v0 v1 v2 v3 v4 (MAlonzo.Code.Relation.Binary.Core.C256) v5
  = MAlonzo.RTE.mazCoerce v5
d9 v0 v1 v2 v3 v4 v5 v6 = MAlonzo.RTE.mazIncompleteMatch name9
name25 = "Relation.Binary.PropositionalEquality.Core.isEquivalence"
d25
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           MAlonzo.Code.Relation.Binary.Core.C453
             (MAlonzo.RTE.mazCoerce
                (\ v2 -> MAlonzo.Code.Relation.Binary.Core.C256))
             (MAlonzo.RTE.mazCoerce
                (d6 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce
                (d9 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name14 = "Relation.Binary.PropositionalEquality.Core.subst"
d14 v0 v1 v2 v3 v4 v5 (MAlonzo.Code.Relation.Binary.Core.C256) v6
  = MAlonzo.RTE.mazCoerce v6
d14 v0 v1 v2 v3 v4 v5 v6 v7 = MAlonzo.RTE.mazIncompleteMatch name14
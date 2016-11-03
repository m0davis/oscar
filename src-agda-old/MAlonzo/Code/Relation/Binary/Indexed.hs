{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.Indexed where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed.Core
name13 = "Relation.Binary.Indexed._.S._\8776_"
d13 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d85
         (MAlonzo.RTE.mazCoerce v4))
name7 = "Relation.Binary.Indexed._at_"
d7 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.C738
         (MAlonzo.RTE.mazCoerce
            (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v5)))
         (MAlonzo.RTE.mazCoerce
            (d13 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v5)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.C453
               (MAlonzo.RTE.mazCoerce
                  (d16 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v4)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v5)))
               (MAlonzo.RTE.mazCoerce
                  (d18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v4)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v5)))
               (MAlonzo.RTE.mazCoerce
                  (d19 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v4)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v5))))))
name17 = "Relation.Binary.Indexed._.S.reflexive"
d17 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d89
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v4))
name14 = "Relation.Binary.Indexed._.S.Carrier"
d14 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d84
         (MAlonzo.RTE.mazCoerce v4))
name27 = "Relation.Binary.Indexed._=[_]\8658_"
d27 v0 v1 v2 v3 v4 v5 v6 v7 v8 = MAlonzo.RTE.mazCoerce ()
name16 = "Relation.Binary.Indexed._.S.refl"
d16 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d88
         (MAlonzo.RTE.mazCoerce v4))
name18 = "Relation.Binary.Indexed._.S.sym"
d18 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d90
         (MAlonzo.RTE.mazCoerce v4))
name15 = "Relation.Binary.Indexed._.S.isEquivalence"
d15 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d86
         (MAlonzo.RTE.mazCoerce v4))
name19 = "Relation.Binary.Indexed._.S.trans"
d19 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d91
         (MAlonzo.RTE.mazCoerce v4))
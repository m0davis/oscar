{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.Consequences.Core where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Relation.Binary.Core
name10 = "Relation.Binary.Consequences.Core.subst\10230resp\8322"
d10 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15
         (MAlonzo.RTE.mazCoerce
            (\ v7 ->
               v6 (MAlonzo.RTE.mazCoerce (v5 (MAlonzo.RTE.mazCoerce v7)))))
         (MAlonzo.RTE.mazCoerce
            (\ v7 ->
               v6
                 (MAlonzo.RTE.mazCoerce
                    (\ v8 ->
                       v5 (MAlonzo.RTE.mazCoerce v8) (MAlonzo.RTE.mazCoerce v7))))))
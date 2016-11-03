{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Unit.NonEta where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Level
name14 = "Data.Unit.NonEta.hide"
d14 v0 v1 v2 v3 v4 v5 (C4)
  = MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v5))
d14 v0 v1 v2 v3 v4 v5 v6 = MAlonzo.RTE.mazIncompleteMatch name14
name6 = "Data.Unit.NonEta.Hidden"
d6 v0 v1 = MAlonzo.RTE.mazCoerce ()
name19 = "Data.Unit.NonEta.reveal"
d19 v0 v1 v2
  = MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce C4))
name3 = "Data.Unit.NonEta.Unit"
d3 = ()
 
data T3 = C4
name4 = "Data.Unit.NonEta.Unit.unit"
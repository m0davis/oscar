{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Empty where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Level
name2 = "Data.Empty.\8869"
d2 = ()
 
cover2 :: Data.FFI.AgdaEmpty -> ()
cover2 x = ()
name5 = "Data.Empty.\8869-elim"
d5 _ _ _ = error "MAlonzo Runtime Error: Impossible Clause Body"
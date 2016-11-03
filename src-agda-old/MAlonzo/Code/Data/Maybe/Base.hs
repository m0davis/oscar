{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Maybe.Base where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Unit.Base
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary
name38 = "Data.Maybe.Base.maybe\8242"
d38
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           \ v2 ->
             \ v3 ->
               d28 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce (\ v4 -> v3)))
name86 = "Data.Maybe.Base.Is-nothing"
d86
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           d71 (MAlonzo.RTE.mazCoerce v0)
             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
             (MAlonzo.RTE.mazCoerce v1)
             (MAlonzo.RTE.mazCoerce (\ v2 -> MAlonzo.Code.Data.Empty.d2)))
name41 = "Data.Maybe.Base.From-just"
d41 v0 v1 (Just v2) = MAlonzo.RTE.mazCoerce v1
d41 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_41 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_41 v0 v1 (Nothing)
          = MAlonzo.RTE.mazCoerce
              (MAlonzo.Code.Level.d4
                 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
                 (MAlonzo.RTE.mazCoerce v0)
                 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.d3))
        d_1_41 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name41
name9 = "Data.Maybe.Base.Maybe.just"
 
d9 :: (forall xa. (forall xA. (xA -> (Data.FFI.AgdaMaybe xa xA))))
d9 = Just
name20 = "Data.Maybe.Base.decToMaybe"
d20 v0 v1 (MAlonzo.Code.Relation.Nullary.C11 v2)
  = MAlonzo.RTE.mazCoerce (Just (MAlonzo.RTE.mazCoerce v2))
d20 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_20 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_20 v0 v1 (MAlonzo.Code.Relation.Nullary.C13 v2)
          = MAlonzo.RTE.mazCoerce Nothing
        d_1_20 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name20
name79 = "Data.Maybe.Base.All.nothing"
name47 = "Data.Maybe.Base.from-just"
d47 (Just v0) = MAlonzo.RTE.mazCoerce v0
d47 v0 = MAlonzo.RTE.mazCoerce (d_1_47 (MAlonzo.RTE.mazCoerce v0))
  where d_1_47 (Nothing)
          = MAlonzo.RTE.mazCoerce
              (MAlonzo.Code.Level.C10
                 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.C4))
        d_1_47 v0 = MAlonzo.RTE.mazIncompleteMatch name47
name82 = "Data.Maybe.Base.Is-just"
d82
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           d59 (MAlonzo.RTE.mazCoerce v0)
             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
             (MAlonzo.RTE.mazCoerce v1)
             (MAlonzo.RTE.mazCoerce (\ v2 -> MAlonzo.Code.Data.Unit.Base.d3)))
name66 = "Data.Maybe.Base.Any.just"
name5 = "Data.Maybe.Base.Maybe"
d5 a0 a1 = ()
 
check9 ::
       (forall xa. (forall xA. (xA -> (Data.FFI.AgdaMaybe xa xA))))
check9 = Just
 
check10 :: (forall xa. (forall xA. (Data.FFI.AgdaMaybe xa xA)))
check10 = Nothing
 
cover5 :: Data.FFI.AgdaMaybe a1 a2 -> ()
cover5 x
  = case x of
        Just _ -> ()
        Nothing -> ()
name53 = "Data.Maybe.Base.map"
d53 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d28 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce
            (\ v5 -> d5 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce (\ v5 -> v3))
               (MAlonzo.RTE.mazCoerce
                  (\ v5 ->
                     \ v6 -> d5 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))
               (MAlonzo.RTE.mazCoerce (\ v5 -> Just))
               (MAlonzo.RTE.mazCoerce v4)))
         (MAlonzo.RTE.mazCoerce Nothing))
name96 = "Data.Maybe.Base.to-witness-T"
d96 v0 v1 (Just v2) v3 = MAlonzo.RTE.mazCoerce v2
d96 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_96 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_96 _ _ (Nothing) _
          = error "MAlonzo Runtime Error: Impossible Clause Body"
        d_1_96 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name96
name91 = "Data.Maybe.Base.to-witness"
d91 v0 v1 v2 (C66 v3 v4) = MAlonzo.RTE.mazCoerce v3
d91 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name91
name11 = "Data.Maybe.Base.boolToMaybe"
d11 (True)
  = MAlonzo.RTE.mazCoerce
      (Just (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Unit.Base.C4))
d11 v0 = MAlonzo.RTE.mazCoerce (d_1_11 (MAlonzo.RTE.mazCoerce v0))
  where d_1_11 (False) = MAlonzo.RTE.mazCoerce Nothing
        d_1_11 v0 = MAlonzo.RTE.mazIncompleteMatch name11
name59 = "Data.Maybe.Base.Any"
d59 a0 a1 a2 a3 a4 = ()
 
data T59 a0 a1 = C66 a0 a1
name14 = "Data.Maybe.Base.is-just"
d14 v0 v1 (Just v2) = MAlonzo.RTE.mazCoerce True
d14 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_14 v0 v1 (Nothing) = MAlonzo.RTE.mazCoerce False
        d_1_14 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name14
name78 = "Data.Maybe.Base.All.just"
name17 = "Data.Maybe.Base.is-nothing"
d17
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
             (MAlonzo.RTE.mazCoerce
                (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce (\ v2 -> MAlonzo.Code.Data.Bool.Base.d3))
             (MAlonzo.RTE.mazCoerce
                (\ v2 -> \ v3 -> MAlonzo.Code.Data.Bool.Base.d3))
             (MAlonzo.RTE.mazCoerce (\ v2 -> MAlonzo.Code.Data.Bool.Base.d6))
             (MAlonzo.RTE.mazCoerce
                (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name28 = "Data.Maybe.Base.maybe"
d28 v0 v1 v2 v3 v4 v5 (Just v6)
  = MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v6))
d28 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_28 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_28 v0 v1 v2 v3 v4 v5 (Nothing) = MAlonzo.RTE.mazCoerce v5
        d_1_28 v0 v1 v2 v3 v4 v5 v6 = MAlonzo.RTE.mazIncompleteMatch name28
name71 = "Data.Maybe.Base.All"
d71 a0 a1 a2 a3 a4 = ()
 
data T71 a0 a1 = C78 a0 a1
               | C79
name10 = "Data.Maybe.Base.Maybe.nothing"
 
d10 :: (forall xa. (forall xA. (Data.FFI.AgdaMaybe xa xA)))
d10 = Nothing
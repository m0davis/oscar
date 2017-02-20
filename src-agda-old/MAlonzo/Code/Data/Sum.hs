{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Sum where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
name69 = "Data.Sum.isInj\8322"
d69 v0 v1 v2 v3 (Left v4) = MAlonzo.RTE.mazCoerce Nothing
d69 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d_1_69 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4))
  where d_1_69 v0 v1 v2 v3 (Right v4)
          = MAlonzo.RTE.mazCoerce (Just (MAlonzo.RTE.mazCoerce v4))
        d_1_69 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name69
name37 = "Data.Sum.[_,_]\8242"
d37
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           \ v2 ->
             \ v3 ->
               \ v4 ->
                 \ v5 ->
                   d24 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v4)
                     (MAlonzo.RTE.mazCoerce (\ v6 -> v5)))
name6 = "Data.Sum._\8846_"
d6 a0 a1 a2 a3 = ()
 
check12 ::
        (forall xa. (forall xb. (forall xA. (forall xB. (xA -> (Data.FFI.AgdaEither xa xb xA xB))))))
check12 = Left
 
check14 ::
        (forall xa. (forall xb. (forall xA. (forall xB. (xB -> (Data.FFI.AgdaEither xa xb xA xB))))))
check14 = Right
 
cover6 :: Data.FFI.AgdaEither a1 a2 a3 a4 -> ()
cover6 x
  = case x of
        Left _ -> ()
        Right _ -> ()
name24 = "Data.Sum.[_,_]"
d24 v0 v1 v2 v3 v4 v5 v6 v7 (Left v8)
  = MAlonzo.RTE.mazCoerce (v6 (MAlonzo.RTE.mazCoerce v8))
d24 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (d_1_24 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce v8))
  where d_1_24 v0 v1 v2 v3 v4 v5 v6 v7 (Right v8)
          = MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v8))
        d_1_24 v0 v1 v2 v3 v4 v5 v6 v7 v8
          = MAlonzo.RTE.mazIncompleteMatch name24
name12 = "Data.Sum._\8846_.inj\8321"
 
d12 ::
    (forall xa. (forall xb. (forall xA. (forall xB. (xA -> (Data.FFI.AgdaEither xa xb xA xB))))))
d12 = Left
name55 = "Data.Sum._-\8846-_"
d55 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d113 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v3)))
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d5 (MAlonzo.RTE.mazCoerce v2)))))
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce
            (d6 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce v7))
name62 = "Data.Sum.isInj\8321"
d62 v0 v1 v2 v3 (Left v4)
  = MAlonzo.RTE.mazCoerce (Just (MAlonzo.RTE.mazCoerce v4))
d62 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d_1_62 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4))
  where d_1_62 v0 v1 v2 v3 (Right v4) = MAlonzo.RTE.mazCoerce Nothing
        d_1_62 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name62
name46 = "Data.Sum.map"
d46 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = MAlonzo.RTE.mazCoerce
      (d24 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce
            (\ v10 ->
               d6 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v6)
                 (MAlonzo.RTE.mazCoerce v7)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v2)))
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce (\ v10 -> v6))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     \ v11 ->
                       d6 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)
                         (MAlonzo.RTE.mazCoerce v6)
                         (MAlonzo.RTE.mazCoerce v7)))
               (MAlonzo.RTE.mazCoerce (\ v10 -> Left))
               (MAlonzo.RTE.mazCoerce v8)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v2)))
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce (\ v10 -> v7))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     \ v11 ->
                       d6 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)
                         (MAlonzo.RTE.mazCoerce v6)
                         (MAlonzo.RTE.mazCoerce v7)))
               (MAlonzo.RTE.mazCoerce (\ v10 -> Right))
               (MAlonzo.RTE.mazCoerce v9))))
name14 = "Data.Sum._\8846_.inj\8322"
 
d14 ::
    (forall xa. (forall xb. (forall xA. (forall xB. (xB -> (Data.FFI.AgdaEither xa xb xA xB))))))
d14 = Right
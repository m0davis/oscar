{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.List.Base where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
name156 = "Data.List.Base.scanl"
d156 v0 v1 v2 v3 v4 v5 ([])
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce []))
d156 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_156 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_156 v0 v1 v2 v3 v4 v5 ((:) v6 v7)
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v5)
                 (MAlonzo.RTE.mazCoerce
                    (d156 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce v4)
                       (MAlonzo.RTE.mazCoerce
                          (v4 (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce v6)))
                       (MAlonzo.RTE.mazCoerce v7))))
        d_1_156 v0 v1 v2 v3 v4 v5 v6
          = MAlonzo.RTE.mazIncompleteMatch name156
name252 = "Data.List.Base.dropWhile"
d252 v0 v1 v2 ([]) = MAlonzo.RTE.mazCoerce []
d252 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_252 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_252 v0 v1 v2 ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              (d258 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce v4))
        d_1_252 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name252
name92 = "Data.List.Base.foldl"
d92 v0 v1 v2 v3 v4 v5 ([]) = MAlonzo.RTE.mazCoerce v5
d92 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_92 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_92 v0 v1 v2 v3 v4 v5 ((:) v6 v7)
          = MAlonzo.RTE.mazCoerce
              (d92 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce
                    (v4 (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce v6)))
                 (MAlonzo.RTE.mazCoerce v7))
        d_1_92 v0 v1 v2 v3 v4 v5 v6 = MAlonzo.RTE.mazIncompleteMatch name92
name108 = "Data.List.Base.and"
d108
  = MAlonzo.RTE.mazCoerce
      (d81 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d15)
         (MAlonzo.RTE.mazCoerce True))
name119 = "Data.List.Base.product"
d119
  = MAlonzo.RTE.mazCoerce
      (d81 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d23)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.Nat.Base.mazIntegerToNat (1 :: Integer))))
name55 = "Data.List.Base.zipWith"
d55 v0 v1 v2 v3 v4 v5 v6 ((:) v7 v8) ((:) v9 v10)
  = MAlonzo.RTE.mazCoerce
      ((:)
         (MAlonzo.RTE.mazCoerce
            (v6 (MAlonzo.RTE.mazCoerce v7) (MAlonzo.RTE.mazCoerce v9)))
         (MAlonzo.RTE.mazCoerce
            (d55 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6)
               (MAlonzo.RTE.mazCoerce v8)
               (MAlonzo.RTE.mazCoerce v10))))
d55 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (d_1_55 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce v8))
  where d_1_55 v0 v1 v2 v3 v4 v5 v6 v7 v8 = MAlonzo.RTE.mazCoerce []
name106 = "Data.List.Base.concatMap"
d106 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce
            (\ v5 ->
               d5 (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce
                    (d5 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))))
         (MAlonzo.RTE.mazCoerce
            (\ v5 ->
               \ v6 -> d5 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (\ v5 ->
               d101 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (d37 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce
                  (d5 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))
               (MAlonzo.RTE.mazCoerce v4))))
name202 = "Data.List.Base.fromMaybe"
d202 v0 v1 (Just v2)
  = MAlonzo.RTE.mazCoerce
      (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
d202 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_202 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_202 v0 v1 (Nothing) = MAlonzo.RTE.mazCoerce []
        d_1_202 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name202
name282 = "Data.List.Base.break"
d282 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d267 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce (\ v3 -> MAlonzo.Code.Data.Bool.Base.d3))
               (MAlonzo.RTE.mazCoerce
                  (\ v3 -> \ v4 -> MAlonzo.Code.Data.Bool.Base.d3))
               (MAlonzo.RTE.mazCoerce (\ v3 -> MAlonzo.Code.Data.Bool.Base.d6))
               (MAlonzo.RTE.mazCoerce v2))))
name122 = "Data.List.Base.length"
d122
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           d81 (MAlonzo.RTE.mazCoerce v0)
             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
             (MAlonzo.RTE.mazCoerce v1)
             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d3)
             (MAlonzo.RTE.mazCoerce (\ v2 -> MAlonzo.Code.Data.Nat.Base.C6))
             (MAlonzo.RTE.mazCoerce
                (MAlonzo.Code.Data.Nat.Base.mazIntegerToNat (0 :: Integer))))
name170 = "Data.List.Base.unfold"
d170 v0 v1 v2 v3 v4 (MAlonzo.Code.Data.Nat.Base.C4) v5
  = MAlonzo.RTE.mazCoerce []
d170 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_170 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_170 v0 v1 v2 v3 v4 (MAlonzo.Code.Data.Nat.Base.C6 v5) v6
          = MAlonzo.RTE.mazCoerce
              (d179 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce v5)
                 (MAlonzo.RTE.mazCoerce v6)
                 (MAlonzo.RTE.mazCoerce
                    (v4 (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce v6))))
        d_1_170 v0 v1 v2 v3 v4 v5 v6
          = MAlonzo.RTE.mazIncompleteMatch name170
name346 = "Data.List.Base.with-345"
d346 v0 v1 v2 v3 v4 (True) (MAlonzo.Code.Data.Product.C15 v5 v6)
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15
         (MAlonzo.RTE.mazCoerce
            ((:) (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v5)))
         (MAlonzo.RTE.mazCoerce v6))
d346 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_346 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_346 v0 v1 v2 v3 v4 (False)
          (MAlonzo.Code.Data.Product.C15 v5 v6)
          = MAlonzo.RTE.mazCoerce
              (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce v5)
                 (MAlonzo.RTE.mazCoerce
                    ((:) (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v6))))
        d_1_346 v0 v1 v2 v3 v4 v5 v6
          = MAlonzo.RTE.mazIncompleteMatch name346
name141 = "Data.List.Base.with-140"
d141 v0 v1 v2 v3 v4 v5 v6 ([]) v7 = MAlonzo.RTE.mazCoerce []
d141 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (d_1_141 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce v8))
  where d_1_141 v0 v1 v2 v3 v4 v5 v6 ((:) v7 v8) v9
          = MAlonzo.RTE.mazCoerce
              ((:)
                 (MAlonzo.RTE.mazCoerce
                    (v4 (MAlonzo.RTE.mazCoerce v9) (MAlonzo.RTE.mazCoerce v7)))
                 (MAlonzo.RTE.mazCoerce
                    ((:) (MAlonzo.RTE.mazCoerce v7) (MAlonzo.RTE.mazCoerce v8))))
        d_1_141 v0 v1 v2 v3 v4 v5 v6 v7 v8
          = MAlonzo.RTE.mazIncompleteMatch name141
name109 = "Data.List.Base.or"
d109
  = MAlonzo.RTE.mazCoerce
      (d81 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d18)
         (MAlonzo.RTE.mazCoerce False))
name45 = "Data.List.Base.replicate"
d45 v0 v1 (MAlonzo.Code.Data.Nat.Base.C4) v2
  = MAlonzo.RTE.mazCoerce []
d45 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_45 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_45 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) v3
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce
                    (d45 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3))))
        d_1_45 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name45
name237 = "Data.List.Base.takeWhile"
d237 v0 v1 v2 ([]) = MAlonzo.RTE.mazCoerce []
d237 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_237 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_237 v0 v1 v2 ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              (d243 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce v4))
        d_1_237 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name237
name112 = "Data.List.Base.any"
d112 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce
            (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (\ v3 ->
               d5 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
                 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)))
         (MAlonzo.RTE.mazCoerce
            (\ v3 -> \ v4 -> MAlonzo.Code.Data.Bool.Base.d3))
         (MAlonzo.RTE.mazCoerce (\ v3 -> d109))
         (MAlonzo.RTE.mazCoerce
            (d37 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)
               (MAlonzo.RTE.mazCoerce v2))))
name299 = "Data.List.Base.InitLast.[]"
name267 = "Data.List.Base.span"
d267 v0 v1 v2 ([])
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce [])
         (MAlonzo.RTE.mazCoerce []))
d267 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_267 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_267 v0 v1 v2 ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              (d273 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce v4))
        d_1_267 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name267
name11 = "Data.List.Base.List._\8759_"
 
d11 ::
    (forall xa. (forall xA. (xA -> ((Data.FFI.AgdaList xa xA) -> (Data.FFI.AgdaList xa xA)))))
d11 = (:)
name302 = "Data.List.Base.InitLast._\8759\691'_"
name126 = "Data.List.Base.reverse"
d126
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           d92 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
             (MAlonzo.RTE.mazCoerce
                (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce v1)
             (MAlonzo.RTE.mazCoerce
                (\ v2 ->
                   \ v3 -> (:) (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v2)))
             (MAlonzo.RTE.mazCoerce []))
name30 = "Data.List.Base.null"
d30 v0 v1 ([]) = MAlonzo.RTE.mazCoerce True
d30 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_30 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_30 v0 v1 ((:) v2 v3) = MAlonzo.RTE.mazCoerce False
        d_1_30 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name30
name286 = "Data.List.Base.inits"
d286 v0 v1 ([])
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce []) (MAlonzo.RTE.mazCoerce []))
d286 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_286 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_286 v0 v1 ((:) v2 v3)
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce [])
                 (MAlonzo.RTE.mazCoerce
                    (d37 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce
                          (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
                       (MAlonzo.RTE.mazCoerce
                          (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
                       (MAlonzo.RTE.mazCoerce ((:) (MAlonzo.RTE.mazCoerce v2)))
                       (MAlonzo.RTE.mazCoerce
                          (d286 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce v3))))))
        d_1_286 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name286
name14 = "Data.List.Base.[_]"
d14 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce []))
name222 = "Data.List.Base.splitAt"
d222 v0 v1 (MAlonzo.Code.Data.Nat.Base.C4) v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce [])
         (MAlonzo.RTE.mazCoerce v2))
d222 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_222 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_222 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) ([])
          = MAlonzo.RTE.mazCoerce
              (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce [])
                 (MAlonzo.RTE.mazCoerce []))
        d_1_222 v0 v1 v2 v3
          = MAlonzo.RTE.mazCoerce
              (d_2_222 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3))
        d_2_222 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              (d229 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce
                    (d222 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v4)))
                 (MAlonzo.RTE.mazCoerce v3))
        d_2_222 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name222
name190 = "Data.List.Base.downFrom"
d190 v0
  = MAlonzo.RTE.mazCoerce
      (d170 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d3)
         (MAlonzo.RTE.mazCoerce (d194 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce (C196 (MAlonzo.RTE.mazCoerce v0))))
name206 = "Data.List.Base.take"
d206 v0 v1 (MAlonzo.Code.Data.Nat.Base.C4) v2
  = MAlonzo.RTE.mazCoerce []
d206 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_206 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_206 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) ([])
          = MAlonzo.RTE.mazCoerce []
        d_1_206 v0 v1 v2 v3
          = MAlonzo.RTE.mazCoerce
              (d_2_206 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3))
        d_2_206 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce
                    (d206 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v4))))
        d_2_206 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name206
name273 = "Data.List.Base.with-272"
d273 v0 v1 v2 v3 (True) v4
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.d94 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (\ v5 -> d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (\ v5 -> d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce ((:) (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (\ v5 ->
               MAlonzo.Code.Function.d34 (MAlonzo.RTE.mazCoerce v0)
                 (MAlonzo.RTE.mazCoerce
                    (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))))
         (MAlonzo.RTE.mazCoerce
            (d267 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v4))))
d273 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_273 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_273 v0 v1 v2 v3 (False) v4
          = MAlonzo.RTE.mazCoerce
              (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce [])
                 (MAlonzo.RTE.mazCoerce
                    ((:) (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4))))
        d_1_273 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name273
name81 = "Data.List.Base.foldr"
d81 v0 v1 v2 v3 v4 v5 ([]) = MAlonzo.RTE.mazCoerce v5
d81 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_81 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_81 v0 v1 v2 v3 v4 v5 ((:) v6 v7)
          = MAlonzo.RTE.mazCoerce
              (v4 (MAlonzo.RTE.mazCoerce v6)
                 (MAlonzo.RTE.mazCoerce
                    (d81 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce v4)
                       (MAlonzo.RTE.mazCoerce v5)
                       (MAlonzo.RTE.mazCoerce v7))))
        d_1_81 v0 v1 v2 v3 v4 v5 v6 = MAlonzo.RTE.mazIncompleteMatch name81
name196 = "Data.List.Base._.Singleton.wrap"
name116 = "Data.List.Base.all"
d116 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce
            (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (\ v3 ->
               d5 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
                 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)))
         (MAlonzo.RTE.mazCoerce
            (\ v3 -> \ v4 -> MAlonzo.Code.Data.Bool.Base.d3))
         (MAlonzo.RTE.mazCoerce (\ v3 -> d108))
         (MAlonzo.RTE.mazCoerce
            (d37 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Bool.Base.d3)
               (MAlonzo.RTE.mazCoerce v2))))
name340 = "Data.List.Base.partition"
d340 v0 v1 v2 ([])
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce [])
         (MAlonzo.RTE.mazCoerce []))
d340 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_340 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_340 v0 v1 v2 ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              (d346 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce
                    (d340 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v4))))
        d_1_340 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name340
name319 = "Data.List.Base.gfilter"
d319 v0 v1 v2 v3 v4 ([]) = MAlonzo.RTE.mazCoerce []
d319 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_319 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_319 v0 v1 v2 v3 v4 ((:) v5 v6)
          = MAlonzo.RTE.mazCoerce
              (d325 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v0)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce v5)
                 (MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v5)))
                 (MAlonzo.RTE.mazCoerce v6))
        d_1_319 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name319
name335 = "Data.List.Base.filter"
d335 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d319 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (\ v3 ->
               MAlonzo.Code.Data.Bool.Base.d10 (MAlonzo.RTE.mazCoerce v0)
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Data.Maybe.Base.d5 (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce v1)))
                 (MAlonzo.RTE.mazCoerce (v2 (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce (Just (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce Nothing))))
name306 = "Data.List.Base.initLast"
d306 v0 v1 ([]) = MAlonzo.RTE.mazCoerce C299
d306 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_306 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_306 v0 v1 ((:) v2 v3)
          = MAlonzo.RTE.mazCoerce
              (d310 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce
                    (d306 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce v2))
        d_1_306 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name306
name66 = "Data.List.Base.zip"
d66
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           \ v2 ->
             \ v3 ->
               d55 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v0)))
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Data.Product.d6 (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce (\ v4 -> v3))))
                 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Product.C15))
name258 = "Data.List.Base.with-257"
d258 v0 v1 v2 v3 (True) v4
  = MAlonzo.RTE.mazCoerce
      (d252 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v4))
d258 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_258 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_258 v0 v1 v2 v3 (False) v4
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4))
        d_1_258 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name258
name194 = "Data.List.Base._.Singleton"
d194 a0 a1 = ()
 
newtype T194 a0 = C196 a0
name18 = "Data.List.Base._++_"
d18 v0 v1 ([]) v2 = MAlonzo.RTE.mazCoerce v2
d18 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_18 v0 v1 ((:) v2 v3) v4
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce
                    (d18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce v4))))
        d_1_18 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name18
name37 = "Data.List.Base.map"
d37 v0 v1 v2 v3 v4 ([]) = MAlonzo.RTE.mazCoerce []
d37 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_37 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_37 v0 v1 v2 v3 v4 ((:) v5 v6)
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v5)))
                 (MAlonzo.RTE.mazCoerce
                    (d37 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce v4)
                       (MAlonzo.RTE.mazCoerce v6))))
        d_1_37 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name37
name133 = "Data.List.Base.scanr"
d133 v0 v1 v2 v3 v4 v5 ([])
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce []))
d133 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d_1_133 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6))
  where d_1_133 v0 v1 v2 v3 v4 v5 ((:) v6 v7)
          = MAlonzo.RTE.mazCoerce
              (d141 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce v5)
                 (MAlonzo.RTE.mazCoerce v7)
                 (MAlonzo.RTE.mazCoerce
                    (d133 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce v4)
                       (MAlonzo.RTE.mazCoerce v5)
                       (MAlonzo.RTE.mazCoerce v7)))
                 (MAlonzo.RTE.mazCoerce v6))
        d_1_133 v0 v1 v2 v3 v4 v5 v6
          = MAlonzo.RTE.mazIncompleteMatch name133
name229 = "Data.List.Base.with-228"
d229 v0 v1 v2 v3 (MAlonzo.Code.Data.Product.C15 v4 v5) v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15
         (MAlonzo.RTE.mazCoerce
            ((:) (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v4)))
         (MAlonzo.RTE.mazCoerce v5))
d229 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name229
name325 = "Data.List.Base.with-324"
d325 v0 v1 v2 v3 v4 v5 (Just v6) v7
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce
            (d319 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v7))))
d325 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (d_1_325 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v7))
  where d_1_325 v0 v1 v2 v3 v4 v5 (Nothing) v6
          = MAlonzo.RTE.mazCoerce
              (d319 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v0)
                 (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v4)
                 (MAlonzo.RTE.mazCoerce v6))
        d_1_325 v0 v1 v2 v3 v4 v5 v6 v7
          = MAlonzo.RTE.mazIncompleteMatch name325
name69 = "Data.List.Base.intersperse"
d69 v0 v1 v2 ([]) = MAlonzo.RTE.mazCoerce []
d69 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_69 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_69 v0 v1 v2 ((:) v3 ([]))
          = MAlonzo.RTE.mazCoerce
              (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v3))
        d_1_69 v0 v1 v2 v3
          = MAlonzo.RTE.mazCoerce
              (d_2_69 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3))
        d_2_69 v0 v1 v2 ((:) v3 ((:) v4 v5))
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v3)
                 (MAlonzo.RTE.mazCoerce
                    ((:) (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce
                          (d69 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce v2)
                             (MAlonzo.RTE.mazCoerce
                                ((:) (MAlonzo.RTE.mazCoerce v4) (MAlonzo.RTE.mazCoerce v5))))))))
        d_2_69 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name69
name5 = "Data.List.Base.List"
d5 a0 a1 = ()
 
check8 :: (forall xa. (forall xA. (Data.FFI.AgdaList xa xA)))
check8 = []
 
check11 ::
        (forall xa. (forall xA. (xA -> ((Data.FFI.AgdaList xa xA) -> (Data.FFI.AgdaList xa xA)))))
check11 = (:)
 
cover5 :: Data.FFI.AgdaList a1 a2 -> ()
cover5 x
  = case x of
        [] -> ()
        (:) _ _ -> ()
name101 = "Data.List.Base.concat"
d101
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           d81 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v0)
             (MAlonzo.RTE.mazCoerce
                (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce
                (d5 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce
                (d18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce []))
name296 = "Data.List.Base.InitLast"
d296 a0 a1 a2 = ()
 
data T296 a0 a1 = C299
                | C302 a0 a1
name8 = "Data.List.Base.List.[]"
 
d8 :: (forall xa. (forall xA. (Data.FFI.AgdaList xa xA)))
d8 = []
name243 = "Data.List.Base.with-242"
d243 v0 v1 v2 v3 (True) v4
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce
            (d237 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v4))))
d243 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_243 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_243 v0 v1 v2 v3 (False) v4 = MAlonzo.RTE.mazCoerce []
        d_1_243 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name243
name179 = "Data.List.Base.with-178"
d179 v0 v1 v2 v3 v4 v5 v6 (Nothing) = MAlonzo.RTE.mazCoerce []
d179 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (d_1_179 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v7))
  where d_1_179 v0 v1 v2 v3 v4 v5 v6
          (Just (MAlonzo.Code.Data.Product.C15 v7 v8))
          = MAlonzo.RTE.mazCoerce
              ((:) (MAlonzo.RTE.mazCoerce v7)
                 (MAlonzo.RTE.mazCoerce
                    (d170 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce v4)
                       (MAlonzo.RTE.mazCoerce v5)
                       (MAlonzo.RTE.mazCoerce v8))))
        d_1_179 v0 v1 v2 v3 v4 v5 v6 v7
          = MAlonzo.RTE.mazIncompleteMatch name179
name291 = "Data.List.Base.tails"
d291 v0 v1 ([])
  = MAlonzo.RTE.mazCoerce
      ((:) (MAlonzo.RTE.mazCoerce []) (MAlonzo.RTE.mazCoerce []))
d291 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_291 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_291 v0 v1 ((:) v2 v3)
          = MAlonzo.RTE.mazCoerce
              ((:)
                 (MAlonzo.RTE.mazCoerce
                    ((:) (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce
                    (d291 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v3))))
        d_1_291 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name291
name198 = "Data.List.Base._.f"
d198 v0 v1 (C196 v2)
  = MAlonzo.RTE.mazCoerce
      (Just
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.Product.C15 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce (C196 (MAlonzo.RTE.mazCoerce v1))))))
d198 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name198
name118 = "Data.List.Base.sum"
d118
  = MAlonzo.RTE.mazCoerce
      (d81 (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d3)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Data.Nat.Base.d14)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Data.Nat.Base.mazIntegerToNat (0 :: Integer))))
name214 = "Data.List.Base.drop"
d214 v0 v1 (MAlonzo.Code.Data.Nat.Base.C4) v2
  = MAlonzo.RTE.mazCoerce v2
d214 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_214 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_214 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) ([])
          = MAlonzo.RTE.mazCoerce []
        d_1_214 v0 v1 v2 v3
          = MAlonzo.RTE.mazCoerce
              (d_2_214 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v3))
        d_2_214 v0 v1 (MAlonzo.Code.Data.Nat.Base.C6 v2) ((:) v3 v4)
          = MAlonzo.RTE.mazCoerce
              (d214 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce v4))
        d_2_214 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name214
name310 = "Data.List.Base.with-309"
d310 v0 v1 v2 (C299) v3
  = MAlonzo.RTE.mazCoerce
      (C302 (MAlonzo.RTE.mazCoerce []) (MAlonzo.RTE.mazCoerce v3))
d310 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d_1_310 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4))
  where d_1_310 v0 v1 v2 (C302 v3 v4) v5
          = MAlonzo.RTE.mazCoerce
              (C302
                 (MAlonzo.RTE.mazCoerce
                    ((:) (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce v3)))
                 (MAlonzo.RTE.mazCoerce v4))
        d_1_310 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name310
name25 = "Data.List.Base._\8759\691_"
d25 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce
            (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v3))))
mazListToHList
  = let { f []        = [];      f ((:) x xs) = x : f (MAlonzo.RTE.mazCoerce xs)} in f
mazHListToList
  = let { f []     = [];      f (c:cs) = (:) c (MAlonzo.RTE.mazCoerce (f cs));} in f
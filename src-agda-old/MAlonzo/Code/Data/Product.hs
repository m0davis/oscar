{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Product where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary
name114 = "Data.Product.zip"
d114 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 (C15 v14 v15)
  (C15 v16 v17)
  = MAlonzo.RTE.mazCoerce
      (C15
         (MAlonzo.RTE.mazCoerce
            (v12 (MAlonzo.RTE.mazCoerce v14) (MAlonzo.RTE.mazCoerce v16)))
         (MAlonzo.RTE.mazCoerce
            (v13 (MAlonzo.RTE.mazCoerce v14) (MAlonzo.RTE.mazCoerce v16)
               (MAlonzo.RTE.mazCoerce v15)
               (MAlonzo.RTE.mazCoerce v17))))
d114 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = MAlonzo.RTE.mazIncompleteMatch name114
name52 = "Data.Product._,\8242_"
d52 = MAlonzo.RTE.mazCoerce (\ v0 -> \ v1 -> \ v2 -> \ v3 -> C15)
name36 = "Data.Product.\8707\8322"
d36 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d23 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce
            (\ v6 ->
               d23 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v2)
                 (MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v6)))
                 (MAlonzo.RTE.mazCoerce (v5 (MAlonzo.RTE.mazCoerce v6))))))
name180 = "Data.Product.uncurry\8242"
d180
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           \ v2 ->
             \ v3 ->
               \ v4 ->
                 \ v5 ->
                   d170 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce (\ v6 -> v4))
                     (MAlonzo.RTE.mazCoerce (\ v6 -> v5)))
name15 = "Data.Product.\931._,_"
name134 = "Data.Product._-\215-_"
d134 v0 v1 v2 v3 v4 v5 v6 v7
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
            (d44 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce v7))
name6 = "Data.Product.\931"
d6 a0 a1 a2 a3 = ()
 
data T6 a0 a1 = C15 a0 a1
name57 = "Data.Product.\8707!"
d57 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d23 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v0)))))
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce
            (\ v6 ->
               d44 (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce v0)))))
                 (MAlonzo.RTE.mazCoerce (v5 (MAlonzo.RTE.mazCoerce v6)))
                 (MAlonzo.RTE.mazCoerce ()))))
name67 = "Data.Product.,_"
d67 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (C15 (MAlonzo.RTE.mazCoerce v4) (MAlonzo.RTE.mazCoerce v5))
name19 = "Data.Product.\931-syntax"
d19 = MAlonzo.RTE.mazCoerce d6
name170 = "Data.Product.uncurry"
d170 v0 v1 v2 v3 v4 v5 v6 (C15 v7 v8)
  = MAlonzo.RTE.mazCoerce
      (v6 (MAlonzo.RTE.mazCoerce v7) (MAlonzo.RTE.mazCoerce v8))
d170 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazIncompleteMatch name170
name13 = "Data.Product.\931.proj\8321"
d13 (C15 v0 v1) = MAlonzo.RTE.mazCoerce v0
d13 v0 = MAlonzo.RTE.mazIncompleteMatch name13
name157 = "Data.Product.curry"
d157 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (v6
         (MAlonzo.RTE.mazCoerce
            (C15 (MAlonzo.RTE.mazCoerce v7) (MAlonzo.RTE.mazCoerce v8))))
name125 = "Data.Product.swap"
d125 v0 v1 v2 v3 (C15 v4 v5)
  = MAlonzo.RTE.mazCoerce
      (C15 (MAlonzo.RTE.mazCoerce v5) (MAlonzo.RTE.mazCoerce v4))
d125 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name125
name44 = "Data.Product._\215_"
d44 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d19 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (\ v4 -> v3)))
name23 = "Data.Product.\8707"
d23
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           \ v2 ->
             d6 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))
name14 = "Data.Product.\931.proj\8322"
d14 (C15 v0 v1) = MAlonzo.RTE.mazCoerce v1
d14 v0 = MAlonzo.RTE.mazIncompleteMatch name14
name94 = "Data.Product.map"
d94 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 (C15 v10 v11)
  = MAlonzo.RTE.mazCoerce
      (C15 (MAlonzo.RTE.mazCoerce (v8 (MAlonzo.RTE.mazCoerce v10)))
         (MAlonzo.RTE.mazCoerce
            (v9 (MAlonzo.RTE.mazCoerce v10) (MAlonzo.RTE.mazCoerce v11))))
d94 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = MAlonzo.RTE.mazIncompleteMatch name94
name145 = "Data.Product._-,-_"
d145 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d113 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce
            (d6 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v6)
               (MAlonzo.RTE.mazCoerce (\ v10 -> v7))))
         (MAlonzo.RTE.mazCoerce v8)
         (MAlonzo.RTE.mazCoerce C15)
         (MAlonzo.RTE.mazCoerce v9))
name80 = "Data.Product.<_,_>"
d80 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazCoerce
      (C15 (MAlonzo.RTE.mazCoerce (v6 (MAlonzo.RTE.mazCoerce v8)))
         (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v8))))
name27 = "Data.Product.\8708"
d27 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.d3
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce
            (d23 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
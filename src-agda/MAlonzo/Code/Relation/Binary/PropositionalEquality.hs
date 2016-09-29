{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.PropositionalEquality where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Unit.NonEta
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified
       MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed
import qualified MAlonzo.Code.Relation.Binary.Indexed.Core
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
name66 = "Relation.Binary.PropositionalEquality.preorder"
d66 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.C729 (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (d64 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name98 = "Relation.Binary.PropositionalEquality._._.isEquivalence"
d98 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d86
         (MAlonzo.RTE.mazCoerce v4))
name133
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect-on-steroids.Reveal_is_"
d133 a0 a1 a2 a3 = ()
 
newtype T133 a0 = C139 a0
name101 = "Relation.Binary.PropositionalEquality._._.sym"
d101 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d90
         (MAlonzo.RTE.mazCoerce v4))
name100 = "Relation.Binary.PropositionalEquality._._.reflexive"
d100 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d89
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v4))
name116
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect.Inspect"
d116 a0 a1 a2 = ()
 
data T116 a0 a1 = C122 a0 a1
name191
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._.relTo"
name111 = "Relation.Binary.PropositionalEquality.\8594-to-\10230"
d111
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           \ v2 ->
             \ v3 ->
               \ v4 ->
                 d90 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                   (MAlonzo.RTE.mazCoerce v2)
                   (MAlonzo.RTE.mazCoerce v3)
                   (MAlonzo.RTE.mazCoerce
                      (MAlonzo.Code.Relation.Binary.Indexed.Core.C182
                         (MAlonzo.RTE.mazCoerce
                            (\ v5 ->
                               MAlonzo.Code.Relation.Binary.d65 (MAlonzo.RTE.mazCoerce v4)))
                         (MAlonzo.RTE.mazCoerce
                            (\ v5 ->
                               \ v6 ->
                                 MAlonzo.Code.Relation.Binary.d66 (MAlonzo.RTE.mazCoerce v4)))
                         (MAlonzo.RTE.mazCoerce
                            (MAlonzo.Code.Relation.Binary.Indexed.Core.C149
                               (MAlonzo.RTE.mazCoerce
                                  (\ v5 ->
                                     MAlonzo.Code.Relation.Binary.d69 (MAlonzo.RTE.mazCoerce v4)))
                               (MAlonzo.RTE.mazCoerce
                                  (\ v5 ->
                                     \ v6 ->
                                       MAlonzo.Code.Relation.Binary.d71 (MAlonzo.RTE.mazCoerce v4)))
                               (MAlonzo.RTE.mazCoerce
                                  (\ v5 ->
                                     \ v6 ->
                                       \ v7 ->
                                         MAlonzo.Code.Relation.Binary.d72
                                           (MAlonzo.RTE.mazCoerce v4))))))))
name102 = "Relation.Binary.PropositionalEquality._._.trans"
d102 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d91
         (MAlonzo.RTE.mazCoerce v4))
name198
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._\8773\10216_\10217_"
d198 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d187 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.d17
               (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v5)))
         (MAlonzo.RTE.mazCoerce v6))
name54 = "Relation.Binary.PropositionalEquality.proof-irrelevance"
d54 v0 v1 v2 v3 (MAlonzo.Code.Relation.Binary.Core.C256)
  (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d54 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name54
name230
  = "Relation.Binary.PropositionalEquality.\8704-extensionality"
d230 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d236 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce
            (v2 (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce (\ v7 -> ()))
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name185
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._._IsRelatedTo_"
d185 a0 a1 a2 a3 = ()
name105 = "Relation.Binary.PropositionalEquality._.cong\8242"
d105 v0 v1 v2 v3 v4 v5 v6 v7
  (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d88
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v6)
         (MAlonzo.RTE.mazCoerce (v5 (MAlonzo.RTE.mazCoerce v6))))
d105 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = MAlonzo.RTE.mazIncompleteMatch name105
name216
  = "Relation.Binary.PropositionalEquality.extensionality-for-lower-levels"
d216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.d79
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                           (MAlonzo.RTE.mazCoerce v0)))))))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                           (MAlonzo.RTE.mazCoerce
                              (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                                 (MAlonzo.RTE.mazCoerce v0)))))))
               (MAlonzo.RTE.mazCoerce ())
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.C10
                       (MAlonzo.RTE.mazCoerce
                          (v7
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.C10
                       (MAlonzo.RTE.mazCoerce
                          (v8
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))))
         (MAlonzo.RTE.mazCoerce
            (\ v10 ->
               MAlonzo.Code.Relation.Binary.Core.d252
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v0)))
                 (MAlonzo.RTE.mazCoerce ())
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                             (MAlonzo.RTE.mazCoerce v1)))
                       (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v5)
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 ->
                             MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                               (MAlonzo.RTE.mazCoerce v3)
                               (MAlonzo.RTE.mazCoerce (v6 (MAlonzo.RTE.mazCoerce v11)))))
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 -> \ v12 -> v6 (MAlonzo.RTE.mazCoerce v11)))
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 ->
                             \ v12 -> MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v12)))
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                                   (MAlonzo.RTE.mazCoerce v0)))
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                                   (MAlonzo.RTE.mazCoerce v1)))
                             (MAlonzo.RTE.mazCoerce v5)
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v0)
                                     (MAlonzo.RTE.mazCoerce v2)
                                     (MAlonzo.RTE.mazCoerce v5)))
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   \ v12 ->
                                     MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                                       (MAlonzo.RTE.mazCoerce v3)
                                       (MAlonzo.RTE.mazCoerce
                                          (v6
                                             (MAlonzo.RTE.mazCoerce
                                                (MAlonzo.Code.Level.d9
                                                   (MAlonzo.RTE.mazCoerce v12)))))))
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   \ v12 ->
                                     MAlonzo.Code.Level.C10
                                       (MAlonzo.RTE.mazCoerce
                                          (v7
                                             (MAlonzo.RTE.mazCoerce
                                                (MAlonzo.Code.Level.d9
                                                   (MAlonzo.RTE.mazCoerce v12)))))))
                             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Level.C10)))))
                 (MAlonzo.RTE.mazCoerce
                    (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                             (MAlonzo.RTE.mazCoerce v1)))
                       (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v5)
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 ->
                             MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                               (MAlonzo.RTE.mazCoerce v3)
                               (MAlonzo.RTE.mazCoerce (v6 (MAlonzo.RTE.mazCoerce v11)))))
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 -> \ v12 -> v6 (MAlonzo.RTE.mazCoerce v11)))
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 ->
                             \ v12 -> MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v12)))
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                                   (MAlonzo.RTE.mazCoerce v0)))
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                                   (MAlonzo.RTE.mazCoerce v1)))
                             (MAlonzo.RTE.mazCoerce v5)
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v0)
                                     (MAlonzo.RTE.mazCoerce v2)
                                     (MAlonzo.RTE.mazCoerce v5)))
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   \ v12 ->
                                     MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                                       (MAlonzo.RTE.mazCoerce v3)
                                       (MAlonzo.RTE.mazCoerce
                                          (v6
                                             (MAlonzo.RTE.mazCoerce
                                                (MAlonzo.Code.Level.d9
                                                   (MAlonzo.RTE.mazCoerce v12)))))))
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   \ v12 ->
                                     MAlonzo.Code.Level.C10
                                       (MAlonzo.RTE.mazCoerce
                                          (v8
                                             (MAlonzo.RTE.mazCoerce
                                                (MAlonzo.Code.Level.d9
                                                   (MAlonzo.RTE.mazCoerce v12)))))))
                             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Level.C10)))))))
         (MAlonzo.RTE.mazCoerce
            (d23
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                           (MAlonzo.RTE.mazCoerce
                              (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                                 (MAlonzo.RTE.mazCoerce v0)))))))
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v0)))
               (MAlonzo.RTE.mazCoerce ())
               (MAlonzo.RTE.mazCoerce ())
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                             (MAlonzo.RTE.mazCoerce v1)))
                       (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v5)
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 ->
                             MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                               (MAlonzo.RTE.mazCoerce v3)
                               (MAlonzo.RTE.mazCoerce (v6 (MAlonzo.RTE.mazCoerce v11)))))
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 -> \ v12 -> v6 (MAlonzo.RTE.mazCoerce v11)))
                       (MAlonzo.RTE.mazCoerce
                          (\ v11 ->
                             \ v12 -> MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v12)))
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Function.d19 (MAlonzo.RTE.mazCoerce v0)
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                                   (MAlonzo.RTE.mazCoerce v0)))
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                                   (MAlonzo.RTE.mazCoerce v1)))
                             (MAlonzo.RTE.mazCoerce v5)
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v0)
                                     (MAlonzo.RTE.mazCoerce v2)
                                     (MAlonzo.RTE.mazCoerce v5)))
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   \ v12 ->
                                     MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                                       (MAlonzo.RTE.mazCoerce v3)
                                       (MAlonzo.RTE.mazCoerce
                                          (v6
                                             (MAlonzo.RTE.mazCoerce
                                                (MAlonzo.Code.Level.d9
                                                   (MAlonzo.RTE.mazCoerce v12)))))))
                             (MAlonzo.RTE.mazCoerce (\ v11 -> v10))
                             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Level.C10)))))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.C10
                       (MAlonzo.RTE.mazCoerce
                          (v7
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.C10
                       (MAlonzo.RTE.mazCoerce
                          (v8
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))))
         (MAlonzo.RTE.mazCoerce
            (v4
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v0)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v5)))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v3)
                       (MAlonzo.RTE.mazCoerce
                          (v6
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.C10
                       (MAlonzo.RTE.mazCoerce
                          (v7
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
               (MAlonzo.RTE.mazCoerce
                  (\ v10 ->
                     MAlonzo.Code.Level.C10
                       (MAlonzo.RTE.mazCoerce
                          (v8
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Function.d19
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                           (MAlonzo.RTE.mazCoerce v0)))
                     (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                           (MAlonzo.RTE.mazCoerce v1)))
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v0)
                           (MAlonzo.RTE.mazCoerce v2)
                           (MAlonzo.RTE.mazCoerce v5)))
                     (MAlonzo.RTE.mazCoerce
                        (\ v10 ->
                           MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce
                                (v6
                                   (MAlonzo.RTE.mazCoerce
                                      (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))
                             (MAlonzo.RTE.mazCoerce
                                (v7
                                   (MAlonzo.RTE.mazCoerce
                                      (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))
                             (MAlonzo.RTE.mazCoerce
                                (v8
                                   (MAlonzo.RTE.mazCoerce
                                      (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
                     (MAlonzo.RTE.mazCoerce
                        (\ v10 ->
                           \ v11 ->
                             MAlonzo.Code.Relation.Binary.Core.d252
                               (MAlonzo.RTE.mazCoerce
                                  (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                                     (MAlonzo.RTE.mazCoerce v1)))
                               (MAlonzo.RTE.mazCoerce
                                  (MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                                     (MAlonzo.RTE.mazCoerce v3)
                                     (MAlonzo.RTE.mazCoerce
                                        (v6
                                           (MAlonzo.RTE.mazCoerce
                                              (MAlonzo.Code.Level.d9
                                                 (MAlonzo.RTE.mazCoerce v10)))))))
                               (MAlonzo.RTE.mazCoerce
                                  (MAlonzo.Code.Level.C10
                                     (MAlonzo.RTE.mazCoerce
                                        (v7
                                           (MAlonzo.RTE.mazCoerce
                                              (MAlonzo.Code.Level.d9
                                                 (MAlonzo.RTE.mazCoerce v10)))))))
                               (MAlonzo.RTE.mazCoerce
                                  (MAlonzo.Code.Level.C10
                                     (MAlonzo.RTE.mazCoerce
                                        (v8
                                           (MAlonzo.RTE.mazCoerce
                                              (MAlonzo.Code.Level.d9
                                                 (MAlonzo.RTE.mazCoerce v10)))))))))
                     (MAlonzo.RTE.mazCoerce
                        (\ v10 ->
                           d23 (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v3)
                                   (MAlonzo.RTE.mazCoerce v1)))
                             (MAlonzo.RTE.mazCoerce
                                (v6
                                   (MAlonzo.RTE.mazCoerce
                                      (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))
                             (MAlonzo.RTE.mazCoerce
                                (MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v1)
                                   (MAlonzo.RTE.mazCoerce v3)
                                   (MAlonzo.RTE.mazCoerce
                                      (v6
                                         (MAlonzo.RTE.mazCoerce
                                            (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
                             (MAlonzo.RTE.mazCoerce MAlonzo.Code.Level.C10)
                             (MAlonzo.RTE.mazCoerce
                                (v7
                                   (MAlonzo.RTE.mazCoerce
                                      (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))
                             (MAlonzo.RTE.mazCoerce
                                (v8
                                   (MAlonzo.RTE.mazCoerce
                                      (MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10)))))))
                     (MAlonzo.RTE.mazCoerce
                        (MAlonzo.Code.Function.d19
                           (MAlonzo.RTE.mazCoerce
                              (MAlonzo.Code.Agda.Primitive.d8 (MAlonzo.RTE.mazCoerce v2)
                                 (MAlonzo.RTE.mazCoerce v0)))
                           (MAlonzo.RTE.mazCoerce v0)
                           (MAlonzo.RTE.mazCoerce v1)
                           (MAlonzo.RTE.mazCoerce
                              (MAlonzo.Code.Level.d4 (MAlonzo.RTE.mazCoerce v0)
                                 (MAlonzo.RTE.mazCoerce v2)
                                 (MAlonzo.RTE.mazCoerce v5)))
                           (MAlonzo.RTE.mazCoerce (\ v10 -> v5))
                           (MAlonzo.RTE.mazCoerce
                              (\ v10 ->
                                 \ v11 ->
                                   MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v1)
                                     (MAlonzo.RTE.mazCoerce (v6 (MAlonzo.RTE.mazCoerce v11)))
                                     (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v11)))
                                     (MAlonzo.RTE.mazCoerce (v8 (MAlonzo.RTE.mazCoerce v11)))))
                           (MAlonzo.RTE.mazCoerce (\ v10 -> v9))
                           (MAlonzo.RTE.mazCoerce
                              (\ v10 ->
                                 MAlonzo.Code.Level.d9 (MAlonzo.RTE.mazCoerce v10))))))))))
name72 = "Relation.Binary.PropositionalEquality._\8594-setoid_"
d72 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.Equality.d103 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.d77
               (MAlonzo.RTE.mazCoerce
                  (d56 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v3)))
               (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v2))))
name56 = "Relation.Binary.PropositionalEquality.setoid"
d56 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.C738 (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d25
               (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1))))
name168
  = "Relation.Binary.PropositionalEquality.Reveal_\183_is_.[_]"
name99 = "Relation.Binary.PropositionalEquality._._.refl"
d99 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d88
         (MAlonzo.RTE.mazCoerce v4))
name147
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect-on-steroids.inspect"
d147 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (C139
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256))
name186
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._._\8718"
d186 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.EqReasoning.d19
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (d56 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name122
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect.Inspect._with-\8801_"
name90 = "Relation.Binary.PropositionalEquality.:\8594-to-\928"
d90 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Function.Equality.C151 (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce
            (d105 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5))))
name189
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._._\8776\10216\10217_"
d189
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 -> MAlonzo.Code.Relation.Binary.PreorderReasoning.d46)
name13 = "Relation.Binary.PropositionalEquality.subst\8322"
d13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  (MAlonzo.Code.Relation.Binary.Core.C256)
  (MAlonzo.Code.Relation.Binary.Core.C256) v10
  = MAlonzo.RTE.mazCoerce v10
d13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = MAlonzo.RTE.mazIncompleteMatch name13
name60 = "Relation.Binary.PropositionalEquality.decSetoid"
d60 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.C790 (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.C783
               (MAlonzo.RTE.mazCoerce
                  (MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d25
                     (MAlonzo.RTE.mazCoerce v0)
                     (MAlonzo.RTE.mazCoerce v1)))
               (MAlonzo.RTE.mazCoerce v2))))
name236 = "Relation.Binary.PropositionalEquality.with-235"
d236 v0 v1 v2 v3 v4 v5 v6 (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d236 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazIncompleteMatch name236
name188
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._._\8776\10216_\10217_"
d188 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.EqReasoning.d21
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (d56 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name23 = "Relation.Binary.PropositionalEquality.cong"
d23 v0 v1 v2 v3 v4 v5 v6 (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d23 v0 v1 v2 v3 v4 v5 v6 v7 = MAlonzo.RTE.mazIncompleteMatch name23
name167
  = "Relation.Binary.PropositionalEquality.Reveal_\183_is_.eq"
d167 (C168 v0) = MAlonzo.RTE.mazCoerce v0
d167 v0 = MAlonzo.RTE.mazIncompleteMatch name167
name46 = "Relation.Binary.PropositionalEquality.cong\8322"
d46 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  (MAlonzo.Code.Relation.Binary.Core.C256)
  (MAlonzo.Code.Relation.Binary.Core.C256)
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d46 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = MAlonzo.RTE.mazIncompleteMatch name46
name158 = "Relation.Binary.PropositionalEquality.Reveal_\183_is_"
d158 a0 a1 a2 a3 a4 a5 a6 = ()
 
newtype T158 a0 = C168 a0
name126
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect.inspect"
d126 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (C122 (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256))
name190
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._.begin_"
d190
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 -> MAlonzo.Code.Relation.Binary.PreorderReasoning.d30)
name97 = "Relation.Binary.PropositionalEquality._._.Carrier"
d97 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d84
         (MAlonzo.RTE.mazCoerce v4))
name33 = "Relation.Binary.PropositionalEquality.cong-app"
d33 v0 v1 v2 v3 v4 v5 (MAlonzo.Code.Relation.Binary.Core.C256) v6
  = MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256
d33 v0 v1 v2 v3 v4 v5 v6 v7 = MAlonzo.RTE.mazIncompleteMatch name33
name81 = "Relation.Binary.PropositionalEquality._\8791_"
d81 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.d66
         (MAlonzo.RTE.mazCoerce
            (d72 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name64 = "Relation.Binary.PropositionalEquality.isPreorder"
d64
  = MAlonzo.RTE.mazCoerce
      (\ v0 ->
         \ v1 ->
           MAlonzo.Code.Relation.Binary.C704
             (MAlonzo.RTE.mazCoerce
                (MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d25
                   (MAlonzo.RTE.mazCoerce v0)
                   (MAlonzo.RTE.mazCoerce v1)))
             (MAlonzo.RTE.mazCoerce
                (\ v2 ->
                   \ v3 ->
                     MAlonzo.Code.Function.d34 (MAlonzo.RTE.mazCoerce v0)
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
                             (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce v2)
                             (MAlonzo.RTE.mazCoerce v3)))))
             (MAlonzo.RTE.mazCoerce
                (MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d9
                   (MAlonzo.RTE.mazCoerce v0)
                   (MAlonzo.RTE.mazCoerce v1))))
name96 = "Relation.Binary.PropositionalEquality._._._\8776_"
d96 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Indexed.Core.d85
         (MAlonzo.RTE.mazCoerce v4))
name192
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._._IsRelatedTo_.relTo"
name176 = "Relation.Binary.PropositionalEquality.inspect"
d176 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (C168
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Relation.Binary.Core.C256))
name203 = "Relation.Binary.PropositionalEquality.Extensionality"
d203 v0 v1 = MAlonzo.RTE.mazCoerce ()
name187
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._._._\8764\10216_\10217_"
d187 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.EqReasoning.d20
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce
            (d56 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name139
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect-on-steroids.Reveal_is_.[_]"
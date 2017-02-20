{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Nat.Base where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Nullary
name75 = "Data.Nat.Base.GeneralisedArithmetic.add"
d75 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (d65 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
name27 = "Data.Nat.Base._<_"
d27 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d7 (MAlonzo.RTE.mazCoerce (C6 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce v1))
name30 = "Data.Nat.Base._\8805_"
d30 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d7 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v0))
name14 = "Data.Nat.Base._+_"
d14 (C4) v0 = MAlonzo.RTE.mazCoerce v0
d14 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_14 (C6 v0) v1
          = MAlonzo.RTE.mazCoerce
              (C6
                 (MAlonzo.RTE.mazCoerce
                    (d14 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_1_14 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name14
name33 = "Data.Nat.Base._>_"
d33 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d27 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v0))
name49 = "Data.Nat.Base._\8804\8242_"
d49 a0 a1 = ()
 
data T49 a0 a1 = C51
               | C54 a0 a1
name65 = "Data.Nat.Base.fold"
d65 v0 v1 v2 (C4) = MAlonzo.RTE.mazCoerce v1
d65 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d_1_65 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3))
  where d_1_65 v0 v1 v2 (C6 v3)
          = MAlonzo.RTE.mazCoerce
              (v2
                 (MAlonzo.RTE.mazCoerce
                    (d65 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                       (MAlonzo.RTE.mazCoerce v2)
                       (MAlonzo.RTE.mazCoerce v3))))
        d_1_65 v0 v1 v2 v3 = MAlonzo.RTE.mazIncompleteMatch name65
name39 = "Data.Nat.Base._\8814_"
d39 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.d3
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce
            (d27 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name7 = "Data.Nat.Base._\8804_"
d7 a0 a1 = ()
 
data T7 a0 a1 a2 = C9 a0
                 | C13 a0 a1 a2
name55 = "Data.Nat.Base._<\8242_"
d55 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d49 (MAlonzo.RTE.mazCoerce (C6 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce v1))
name23 = "Data.Nat.Base._*_"
d23 (C4) v0 = MAlonzo.RTE.mazCoerce C4
d23 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_23 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_23 (C6 v0) v1
          = MAlonzo.RTE.mazCoerce
              (d14 (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce
                    (d23 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_1_23 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name23
name42 = "Data.Nat.Base._\8817_"
d42 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.d3
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce
            (d30 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name58 = "Data.Nat.Base._\8805\8242_"
d58 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d49 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v0))
name90 = "Data.Nat.Base._\8852_"
d90 (C4) v0 = MAlonzo.RTE.mazCoerce v0
d90 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_90 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_90 (C6 v0) (C4)
          = MAlonzo.RTE.mazCoerce (C6 (MAlonzo.RTE.mazCoerce v0))
        d_1_90 v0 v1
          = MAlonzo.RTE.mazCoerce
              (d_2_90 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_2_90 (C6 v0) (C6 v1)
          = MAlonzo.RTE.mazCoerce
              (C6
                 (MAlonzo.RTE.mazCoerce
                    (d90 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_2_90 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name90
name45 = "Data.Nat.Base._\8815_"
d45 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.d3
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce
            (d33 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name13 = "Data.Nat.Base._\8804_.s\8804s"
name61 = "Data.Nat.Base._>\8242_"
d61 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d55 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v0))
name3 = "Data.Nat.Base.\8469"
d3 = ()
 
data T3 a0 = C4
           | C6 a0
name51 = "Data.Nat.Base._\8804\8242_.\8804\8242-refl"
name86 = "Data.Nat.Base._+\8910_"
d86 (C4) v0 = MAlonzo.RTE.mazCoerce v0
d86 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_86 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_86 (C6 v0) v1
          = MAlonzo.RTE.mazCoerce
              (C6
                 (MAlonzo.RTE.mazCoerce
                    (d86 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v0))))
        d_1_86 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name86
name6 = "Data.Nat.Base.\8469.suc"
name102 = "Data.Nat.Base.\8968_/2\8969"
d102 v0
  = MAlonzo.RTE.mazCoerce
      (d100 (MAlonzo.RTE.mazCoerce (C6 (MAlonzo.RTE.mazCoerce v0))))
name54 = "Data.Nat.Base._\8804\8242_.\8804\8242-step"
name9 = "Data.Nat.Base._\8804_.z\8804n"
name100 = "Data.Nat.Base.\8970_/2\8971"
d100 (C4) = MAlonzo.RTE.mazCoerce (mazIntegerToNat (0 :: Integer))
d100 v0
  = MAlonzo.RTE.mazCoerce (d_1_100 (MAlonzo.RTE.mazCoerce v0))
  where d_1_100 (C6 (C4))
          = MAlonzo.RTE.mazCoerce (mazIntegerToNat (0 :: Integer))
        d_1_100 v0
          = MAlonzo.RTE.mazCoerce (d_2_100 (MAlonzo.RTE.mazCoerce v0))
        d_2_100 (C6 (C6 v0))
          = MAlonzo.RTE.mazCoerce
              (C6 (MAlonzo.RTE.mazCoerce (d100 (MAlonzo.RTE.mazCoerce v0))))
        d_2_100 v0 = MAlonzo.RTE.mazIncompleteMatch name100
name36 = "Data.Nat.Base._\8816_"
d36 v0 v1
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Nullary.d3
         (MAlonzo.RTE.mazCoerce MAlonzo.Code.Agda.Primitive.d3)
         (MAlonzo.RTE.mazCoerce
            (d7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name84 = "Data.Nat.Base.pred"
d84 (C4) = MAlonzo.RTE.mazCoerce C4
d84 v0 = MAlonzo.RTE.mazCoerce (d_1_84 (MAlonzo.RTE.mazCoerce v0))
  where d_1_84 (C6 v0) = MAlonzo.RTE.mazCoerce v0
        d_1_84 v0 = MAlonzo.RTE.mazIncompleteMatch name84
name4 = "Data.Nat.Base.\8469.zero"
name95 = "Data.Nat.Base._\8851_"
d95 (C4) v0 = MAlonzo.RTE.mazCoerce C4
d95 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_95 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_95 (C6 v0) (C4) = MAlonzo.RTE.mazCoerce C4
        d_1_95 v0 v1
          = MAlonzo.RTE.mazCoerce
              (d_2_95 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_2_95 (C6 v0) (C6 v1)
          = MAlonzo.RTE.mazCoerce
              (C6
                 (MAlonzo.RTE.mazCoerce
                    (d95 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_2_95 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name95
name79 = "Data.Nat.Base.GeneralisedArithmetic.mul"
d79 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d65 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (v3 (MAlonzo.RTE.mazCoerce v5)))
         (MAlonzo.RTE.mazCoerce v4))
name18 = "Data.Nat.Base._\8760_"
d18 v0 (C4) = MAlonzo.RTE.mazCoerce v0
d18 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_18 (C4) (C6 v0) = MAlonzo.RTE.mazCoerce C4
        d_1_18 v0 v1
          = MAlonzo.RTE.mazCoerce
              (d_2_18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_2_18 (C6 v0) (C6 v1)
          = MAlonzo.RTE.mazCoerce
              (d18 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_2_18 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name18
 
{-# RULES
"mazNatToInteger-mazIntegerToNat" forall x .
                                  mazNatToInteger (mazIntegerToNat x) = x
"mazIntegerToNat-mazNatToInteger" forall x .
                                  mazIntegerToNat (mazNatToInteger x) = x
 #-}
 
{-# INLINE [2] mazNatToInteger #-}
 
{-# INLINE [2] mazIntegerToNat #-}
mazNatToInteger
  = \ x -> case x of { C4 -> 0 :: Integer; C6 x -> 1 + (mazNatToInteger (MAlonzo.RTE.mazCoerce x)) }
mazIntegerToNat
  = \ x -> if x <= (0 :: Integer) then C4 else C6 (MAlonzo.RTE.mazCoerce (mazIntegerToNat (x - 1)))
 
{-# RULES
"mazNatToInt-mazIntToNat" forall x . mazNatToInt (mazIntToNat x) =
                          x
"mazIntToNat-mazNatToInt" forall x . mazIntToNat (mazNatToInt x) =
                          x
 #-}
 
{-# INLINE [2] mazNatToInt #-}
 
{-# INLINE [2] mazIntToNat #-}
mazNatToInt
  = \ x -> case x of { C4 -> 0 :: Int; C6 x -> 1 + (mazNatToInt (MAlonzo.RTE.mazCoerce x)) }
mazIntToNat
  = \ x -> if x <= (0 :: Int) then C4 else C6 (MAlonzo.RTE.mazCoerce (mazIntToNat (x - 1)))
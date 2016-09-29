{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary where
import qualified Data.FFI
import qualified MAlonzo.RTE
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed.Core
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
name56 = "Relation.Binary.Preorder._.Eq.trans"
d56 v0
  = MAlonzo.RTE.mazCoerce
      (d25 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name568 = "Relation.Binary.DecTotalOrder.DTO.Eq._\8799_"
d568 v0
  = MAlonzo.RTE.mazCoerce
      (d534 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name312 = "Relation.Binary.IsStrictPartialOrder.Eq.trans"
d312 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d276
         (MAlonzo.RTE.mazCoerce (d304 (MAlonzo.RTE.mazCoerce v0))))
name72 = "Relation.Binary.Setoid._.trans"
d72 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d276
         (MAlonzo.RTE.mazCoerce (d67 (MAlonzo.RTE.mazCoerce v0))))
name840 = "Relation.Binary.recCon-NOT-PRINTED"
name584 = "Relation.Binary.DecTotalOrder._.isTotalOrder"
d584 v0
  = MAlonzo.RTE.mazCoerce
      (d465 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name152 = "Relation.Binary.IsPartialOrder._.Eq.sym"
d152 v0
  = MAlonzo.RTE.mazCoerce
      (d24 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name664 = "Relation.Binary.StrictTotalOrder._<_"
d664 (C1027 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d664 v0 = MAlonzo.RTE.mazIncompleteMatch name664
name552 = "Relation.Binary.DecTotalOrder._\8776_"
d552 (C959 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d552 v0 = MAlonzo.RTE.mazIncompleteMatch name552
name632 = "Relation.Binary.IsStrictTotalOrder._<?_"
d632 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Consequences.d192
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d629 (MAlonzo.RTE.mazCoerce v6))))
name376 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.trans"
d376 v0
  = MAlonzo.RTE.mazCoerce
      (d96 (MAlonzo.RTE.mazCoerce (d369 (MAlonzo.RTE.mazCoerce v0))))
name120 = "Relation.Binary.DecSetoid._.isEquivalence"
d120 v0
  = MAlonzo.RTE.mazCoerce
      (d67 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name648 = "Relation.Binary.IsStrictTotalOrder._.Eq.reflexive"
d648 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d310 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name216 = "Relation.Binary.IsDecPartialOrder.Eq._._\8799_"
d216 v0
  = MAlonzo.RTE.mazCoerce
      (d91 (MAlonzo.RTE.mazCoerce (d214 (MAlonzo.RTE.mazCoerce v0))))
name472 = "Relation.Binary.TotalOrder._.reflexive"
d472 v0
  = MAlonzo.RTE.mazCoerce
      (d444 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name360
  = "Relation.Binary.IsDecStrictPartialOrder.SPO.<-resp-\8776"
d360 v0
  = MAlonzo.RTE.mazCoerce
      (d307 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name616 = "Relation.Binary.IsStrictTotalOrder"
d616 a0 a1 a2 a3 a4 a5 = ()
 
data T616 a0 a1 a2 a3 = C978 a0 a1 a2 a3
name440 = "Relation.Binary.IsTotalOrder._.antisym"
d440 v0
  = MAlonzo.RTE.mazCoerce
      (d143 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name200 = "Relation.Binary.IsDecPartialOrder._\8804?_"
d200 (C828 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d200 v0 = MAlonzo.RTE.mazIncompleteMatch name200
name24 = "Relation.Binary.IsPreorder.Eq.sym"
d24 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d275
         (MAlonzo.RTE.mazCoerce (d18 (MAlonzo.RTE.mazCoerce v0))))
name536 = "Relation.Binary.IsDecTotalOrder.Eq._.refl"
d536 v0
  = MAlonzo.RTE.mazCoerce
      (d93 (MAlonzo.RTE.mazCoerce (d532 (MAlonzo.RTE.mazCoerce v0))))
name280 = "Relation.Binary.DecPoset.Eq._.isEquivalence"
d280 v0
  = MAlonzo.RTE.mazCoerce
      (d110 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name168 = "Relation.Binary.Poset.isPartialOrder"
d168 (C813 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d168 v0 = MAlonzo.RTE.mazIncompleteMatch name168
name680 = "Relation.Binary.StrictTotalOrder._.Eq.sym"
d680 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d639 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name504 = "Relation.Binary.IsDecTotalOrder"
d504 a0 a1 a2 a3 a4 a5 = ()
 
data T504 a0 a1 a2 = C947 a0 a1 a2
name248 = "Relation.Binary.DecPoset.DPO.Eq._\8799_"
d248 v0
  = MAlonzo.RTE.mazCoerce
      (d216 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name264 = "Relation.Binary.DecPoset._.preorder"
d264 v0
  = MAlonzo.RTE.mazCoerce
      (d181 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name8 = "Relation.Binary.IsPreorder"
d8 a0 a1 a2 a3 a4 a5 = ()
 
data T8 a0 a1 a2 = C704 a0 a1 a2
name520 = "Relation.Binary.IsDecTotalOrder.TO.isPartialOrder"
d520 v0
  = MAlonzo.RTE.mazCoerce
      (d437 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name600 = "Relation.Binary.DecTotalOrder.Eq._._\8799_"
d600 v0
  = MAlonzo.RTE.mazCoerce
      (d109 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name488 = "Relation.Binary.TotalOrder._.isPreorder"
d488 v0
  = MAlonzo.RTE.mazCoerce
      (d172 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name643 = "Relation.Binary.IsStrictTotalOrder._.<-resp-\8776"
d643 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d307
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name211 = "Relation.Binary.IsDecPartialOrder.PO._.Eq.sym"
d211 v0
  = MAlonzo.RTE.mazCoerce
      (d152 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name467 = "Relation.Binary.TotalOrder._.antisym"
d467 v0
  = MAlonzo.RTE.mazCoerce
      (d440 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name99 = "Relation.Binary.DecSetoid"
d99 a0 a1 = ()
 
data T99 a0 a1 a2 = C790 a0 a1 a2
name179 = "Relation.Binary.Poset._._.Eq.sym"
d179 v0
  = MAlonzo.RTE.mazCoerce
      (d152 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name947 = "Relation.Binary.recCon-NOT-PRINTED"
name691 = "Relation.Binary.StrictTotalOrder.Eq.refl"
d691 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d111
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name19 = "Relation.Binary.IsPreorder.reflexive"
d19 (C704 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d19 v0 = MAlonzo.RTE.mazIncompleteMatch name19
name675 = "Relation.Binary.StrictTotalOrder._.trans"
d675 v0
  = MAlonzo.RTE.mazCoerce
      (d628 (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v0))))
name419 = "Relation.Binary.DecStrictPartialOrder.Eq._.setoid"
d419 v0
  = MAlonzo.RTE.mazCoerce
      (d115 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name243 = "Relation.Binary.DecPoset.DPO.isPreorder"
d243 v0
  = MAlonzo.RTE.mazCoerce
      (d204 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name259 = "Relation.Binary.DecPoset._.Carrier"
d259 v0
  = MAlonzo.RTE.mazCoerce
      (d165 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name1027 = "Relation.Binary.recCon-NOT-PRINTED"
name515 = "Relation.Binary.IsDecTotalOrder._\8799_"
d515 (C947 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d515 v0 = MAlonzo.RTE.mazIncompleteMatch name515
name595 = "Relation.Binary.DecTotalOrder._._._._.Eq.trans"
d595 v0
  = MAlonzo.RTE.mazCoerce
      (d479 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name83 = "Relation.Binary.IsDecEquivalence"
d83 a0 a1 a2 a3 = ()
 
data T83 a0 a1 = C783 a0 a1
name483 = "Relation.Binary.TotalOrder._._\8804_"
d483 v0
  = MAlonzo.RTE.mazCoerce
      (d167 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name51 = "Relation.Binary.Preorder._.trans"
d51 v0
  = MAlonzo.RTE.mazCoerce
      (d20 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name563 = "Relation.Binary.DecTotalOrder.DTO.refl"
d563 v0
  = MAlonzo.RTE.mazCoerce
      (d522 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name307 = "Relation.Binary.IsStrictPartialOrder.<-resp-\8776"
d307 (C859 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d307 v0 = MAlonzo.RTE.mazIncompleteMatch name307
name67 = "Relation.Binary.Setoid.isEquivalence"
d67 (C738 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d67 v0 = MAlonzo.RTE.mazIncompleteMatch name67
name579 = "Relation.Binary.DecTotalOrder._.Carrier"
d579 v0
  = MAlonzo.RTE.mazCoerce
      (d462 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name403 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.refl"
d403 v0
  = MAlonzo.RTE.mazCoerce
      (d373 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name147 = "Relation.Binary.IsPartialOrder._.reflexive"
d147 v0
  = MAlonzo.RTE.mazCoerce
      (d19 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name35 = "Relation.Binary.Preorder"
d35 a0 a1 a2 = ()
 
data T35 a0 a1 a2 a3 = C729 a0 a1 a2 a3
name627 = "Relation.Binary.IsStrictTotalOrder.isEquivalence"
d627 (C978 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d627 v0 = MAlonzo.RTE.mazIncompleteMatch name627
name371 = "Relation.Binary.IsDecStrictPartialOrder.Eq._._\8799_"
d371 v0
  = MAlonzo.RTE.mazCoerce
      (d91 (MAlonzo.RTE.mazCoerce (d369 (MAlonzo.RTE.mazCoerce v0))))
name115 = "Relation.Binary.DecSetoid.setoid"
d115 v0
  = MAlonzo.RTE.mazCoerce
      (C738 (MAlonzo.RTE.mazCoerce (d105 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d106 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d110 (MAlonzo.RTE.mazCoerce v0))))
name870 = "Relation.Binary.recCon-NOT-PRINTED"
name358 = "Relation.Binary.IsDecStrictPartialOrder._<?_"
d358 (C898 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d358 v0 = MAlonzo.RTE.mazIncompleteMatch name358
name694 = "Relation.Binary.StrictTotalOrder.Eq.sym"
d694 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d113
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name438 = "Relation.Binary.IsTotalOrder.total"
d438 (C923 v0 v1) = MAlonzo.RTE.mazCoerce v1
d438 v0 = MAlonzo.RTE.mazIncompleteMatch name438
name198 = "Relation.Binary.IsDecPartialOrder.isPartialOrder"
d198 (C828 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d198 v0 = MAlonzo.RTE.mazIncompleteMatch name198
name454 = "Relation.Binary.TotalOrder"
d454 a0 a1 a2 = ()
 
data T454 a0 a1 a2 a3 = C932 a0 a1 a2 a3
name278 = "Relation.Binary.DecPoset.Eq._.Carrier"
d278 v0
  = MAlonzo.RTE.mazCoerce
      (d105 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name22 = "Relation.Binary.IsPreorder.Eq.refl"
d22 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d274
         (MAlonzo.RTE.mazCoerce (d18 (MAlonzo.RTE.mazCoerce v0))))
name790 = "Relation.Binary.recCon-NOT-PRINTED"
name534 = "Relation.Binary.IsDecTotalOrder.Eq._._\8799_"
d534 v0
  = MAlonzo.RTE.mazCoerce
      (d91 (MAlonzo.RTE.mazCoerce (d532 (MAlonzo.RTE.mazCoerce v0))))
name166 = "Relation.Binary.Poset._\8776_"
d166 (C813 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d166 v0 = MAlonzo.RTE.mazIncompleteMatch name166
name678 = "Relation.Binary.StrictTotalOrder._.Eq.refl"
d678 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d637 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name246 = "Relation.Binary.DecPoset.DPO.trans"
d246 v0
  = MAlonzo.RTE.mazCoerce
      (d207 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name518 = "Relation.Binary.IsDecTotalOrder.TO.antisym"
d518 v0
  = MAlonzo.RTE.mazCoerce
      (d440 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name262 = "Relation.Binary.DecPoset._.isPartialOrder"
d262 v0
  = MAlonzo.RTE.mazCoerce
      (d168 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name486 = "Relation.Binary.TotalOrder._.isEquivalence"
d486 v0
  = MAlonzo.RTE.mazCoerce
      (d171 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name310 = "Relation.Binary.IsStrictPartialOrder.Eq.reflexive"
d310 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d277 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce (d304 (MAlonzo.RTE.mazCoerce v6))))
name54 = "Relation.Binary.Preorder._.Eq.reflexive"
d54 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d23 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d43 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d44 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d45 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v3))))
name566 = "Relation.Binary.DecTotalOrder.DTO.trans"
d566 v0
  = MAlonzo.RTE.mazCoerce
      (d525 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name582 = "Relation.Binary.DecTotalOrder._.isPartialOrder"
d582 v0
  = MAlonzo.RTE.mazCoerce
      (d469 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name326 = "Relation.Binary.StrictPartialOrder._<_"
d326 (C870 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d326 v0 = MAlonzo.RTE.mazIncompleteMatch name326
name70 = "Relation.Binary.Setoid._.reflexive"
d70 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d277 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d65 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce (d66 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce (d67 (MAlonzo.RTE.mazCoerce v2))))
name662 = "Relation.Binary.StrictTotalOrder.Carrier"
d662 (C1027 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d662 v0 = MAlonzo.RTE.mazIncompleteMatch name662
name406 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.trans"
d406 v0
  = MAlonzo.RTE.mazCoerce
      (d376 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name150 = "Relation.Binary.IsPartialOrder._.Eq.refl"
d150 v0
  = MAlonzo.RTE.mazCoerce
      (d22 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name374 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.reflexive"
d374 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d94 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce (d369 (MAlonzo.RTE.mazCoerce v6))))
name118 = "Relation.Binary.DecSetoid._.Carrier"
d118 v0
  = MAlonzo.RTE.mazCoerce
      (d65 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name630 = "Relation.Binary.IsStrictTotalOrder.<-resp-\8776"
d630 (C978 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d630 v0 = MAlonzo.RTE.mazIncompleteMatch name630
name390 = "Relation.Binary.DecStrictPartialOrder._<_"
d390 (C910 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d390 v0 = MAlonzo.RTE.mazIncompleteMatch name390
name646 = "Relation.Binary.IsStrictTotalOrder._.trans"
d646 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d306
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name470 = "Relation.Binary.TotalOrder._.isPreorder"
d470 v0
  = MAlonzo.RTE.mazCoerce
      (d442 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name214 = "Relation.Binary.IsDecPartialOrder.Eq.isDecEquivalence"
d214 v0
  = MAlonzo.RTE.mazCoerce
      (C783 (MAlonzo.RTE.mazCoerce (d203 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d199 (MAlonzo.RTE.mazCoerce v0))))
name537 = "Relation.Binary.IsDecTotalOrder.Eq._.reflexive"
d537 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d94 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce (d532 (MAlonzo.RTE.mazCoerce v6))))
name281 = "Relation.Binary.DecPoset.Eq._.preorder"
d281 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d122 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v3))))
name25 = "Relation.Binary.IsPreorder.Eq.trans"
d25 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d276
         (MAlonzo.RTE.mazCoerce (d18 (MAlonzo.RTE.mazCoerce v0))))
name681 = "Relation.Binary.StrictTotalOrder._.Eq.trans"
d681 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d640 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name249 = "Relation.Binary.DecPoset.DPO.Eq.isDecEquivalence"
d249 v0
  = MAlonzo.RTE.mazCoerce
      (d214 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name265 = "Relation.Binary.DecPoset._.refl"
d265 v0
  = MAlonzo.RTE.mazCoerce
      (d173 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name521 = "Relation.Binary.IsDecTotalOrder.TO.isPreorder"
d521 v0
  = MAlonzo.RTE.mazCoerce
      (d442 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name601 = "Relation.Binary.DecTotalOrder.Eq._.Carrier"
d601 v0
  = MAlonzo.RTE.mazCoerce
      (d105 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name489 = "Relation.Binary.TotalOrder._.preorder"
d489 v0
  = MAlonzo.RTE.mazCoerce
      (d181 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name233 = "Relation.Binary.DecPoset.Carrier"
d233 (C840 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d233 v0 = MAlonzo.RTE.mazIncompleteMatch name233
name569 = "Relation.Binary.DecTotalOrder.DTO.Eq.isDecEquivalence"
d569 v0
  = MAlonzo.RTE.mazCoerce
      (d532 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name329 = "Relation.Binary.StrictPartialOrder._.<-resp-\8776"
d329 v0
  = MAlonzo.RTE.mazCoerce
      (d307 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name73 = "Relation.Binary.Setoid.isPreorder"
d73 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (C704
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d25
               (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce (d65 (MAlonzo.RTE.mazCoerce v2)))))
         (MAlonzo.RTE.mazCoerce
            (d70 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce (d72 (MAlonzo.RTE.mazCoerce v2))))
name585 = "Relation.Binary.DecTotalOrder._.poset"
d585 v0
  = MAlonzo.RTE.mazCoerce
      (d480 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name409 = "Relation.Binary.DecStrictPartialOrder.Eq.decSetoid"
d409 v0
  = MAlonzo.RTE.mazCoerce
      (C790 (MAlonzo.RTE.mazCoerce (d388 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d389 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d401 (MAlonzo.RTE.mazCoerce v0))))
name153 = "Relation.Binary.IsPartialOrder._.Eq.trans"
d153 v0
  = MAlonzo.RTE.mazCoerce
      (d25 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name665 = "Relation.Binary.StrictTotalOrder.isStrictTotalOrder"
d665 (C1027 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d665 v0 = MAlonzo.RTE.mazIncompleteMatch name665
name553 = "Relation.Binary.DecTotalOrder._\8804_"
d553 (C959 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d553 v0 = MAlonzo.RTE.mazIncompleteMatch name553
name633 = "Relation.Binary.IsStrictTotalOrder.isDecEquivalence"
d633 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (C783 (MAlonzo.RTE.mazCoerce (d627 (MAlonzo.RTE.mazCoerce v6)))
         (MAlonzo.RTE.mazCoerce
            (d631 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name121 = "Relation.Binary.DecSetoid._.isPreorder"
d121 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d73 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v2))))
name649 = "Relation.Binary.IsStrictTotalOrder._.Eq.sym"
d649 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d311
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name393 = "Relation.Binary.DecStrictPartialOrder.DSPO._<?_"
d393 v0
  = MAlonzo.RTE.mazCoerce
      (d358 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name217 = "Relation.Binary.IsDecPartialOrder.Eq._.isEquivalence"
d217 v0
  = MAlonzo.RTE.mazCoerce
      (d90 (MAlonzo.RTE.mazCoerce (d214 (MAlonzo.RTE.mazCoerce v0))))
name729 = "Relation.Binary.recCon-NOT-PRINTED"
name473 = "Relation.Binary.TotalOrder._.total"
d473 v0
  = MAlonzo.RTE.mazCoerce
      (d438 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name361 = "Relation.Binary.IsDecStrictPartialOrder.SPO.irrefl"
d361 v0
  = MAlonzo.RTE.mazCoerce
      (d305 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name105 = "Relation.Binary.DecSetoid.Carrier"
d105 (C790 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d105 v0 = MAlonzo.RTE.mazIncompleteMatch name105
name441 = "Relation.Binary.IsTotalOrder._.isEquivalence"
d441 v0
  = MAlonzo.RTE.mazCoerce
      (d145 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name388 = "Relation.Binary.DecStrictPartialOrder.Carrier"
d388 (C910 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d388 v0 = MAlonzo.RTE.mazIncompleteMatch name388
name644 = "Relation.Binary.IsStrictTotalOrder._.irrefl"
d644 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d305
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name468 = "Relation.Binary.TotalOrder._.isEquivalence"
d468 v0
  = MAlonzo.RTE.mazCoerce
      (d441 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name212 = "Relation.Binary.IsDecPartialOrder.PO._.Eq.trans"
d212 v0
  = MAlonzo.RTE.mazCoerce
      (d153 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name356
  = "Relation.Binary.IsDecStrictPartialOrder.isStrictPartialOrder"
d356 (C898 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d356 v0 = MAlonzo.RTE.mazIncompleteMatch name356
name180 = "Relation.Binary.Poset._._.Eq.trans"
d180 v0
  = MAlonzo.RTE.mazCoerce
      (d153 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name692 = "Relation.Binary.StrictTotalOrder.Eq.reflexive"
d692 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d112 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name276 = "Relation.Binary.DecPoset.Eq._._\8776_"
d276 v0
  = MAlonzo.RTE.mazCoerce
      (d106 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name20 = "Relation.Binary.IsPreorder.trans"
d20 (C704 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d20 v0 = MAlonzo.RTE.mazIncompleteMatch name20
name532 = "Relation.Binary.IsDecTotalOrder.Eq.isDecEquivalence"
d532 v0
  = MAlonzo.RTE.mazCoerce
      (C783 (MAlonzo.RTE.mazCoerce (d519 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d515 (MAlonzo.RTE.mazCoerce v0))))
name676 = "Relation.Binary.StrictTotalOrder._.Eq._\8799_"
d676 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d635 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name420 = "Relation.Binary.DecStrictPartialOrder.Eq._.sym"
d420 v0
  = MAlonzo.RTE.mazCoerce
      (d113 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name932 = "Relation.Binary.recCon-NOT-PRINTED"
name244 = "Relation.Binary.DecPoset.DPO.refl"
d244 v0
  = MAlonzo.RTE.mazCoerce
      (d205 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name260 = "Relation.Binary.DecPoset._.antisym"
d260 v0
  = MAlonzo.RTE.mazCoerce
      (d170 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name516 = "Relation.Binary.IsDecTotalOrder._\8804?_"
d516 (C947 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d516 v0 = MAlonzo.RTE.mazIncompleteMatch name516
name484 = "Relation.Binary.TotalOrder._.Carrier"
d484 v0
  = MAlonzo.RTE.mazCoerce
      (d165 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name564 = "Relation.Binary.DecTotalOrder.DTO.reflexive"
d564 v0
  = MAlonzo.RTE.mazCoerce
      (d523 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name52 = "Relation.Binary.Preorder._.\8764-resp-\8776"
d52 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d27 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d43 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d44 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d45 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v3))))
name580 = "Relation.Binary.DecTotalOrder._.antisym"
d580 v0
  = MAlonzo.RTE.mazCoerce
      (d467 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name324 = "Relation.Binary.StrictPartialOrder.Carrier"
d324 (C870 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d324 v0 = MAlonzo.RTE.mazIncompleteMatch name324
name148 = "Relation.Binary.IsPartialOrder._.trans"
d148 v0
  = MAlonzo.RTE.mazCoerce
      (d20 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name404 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.reflexive"
d404 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d374 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d388 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d389 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d390 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v3))))
name804 = "Relation.Binary.recCon-NOT-PRINTED"
name372
  = "Relation.Binary.IsDecStrictPartialOrder.Eq._.isEquivalence"
d372 v0
  = MAlonzo.RTE.mazCoerce
      (d90 (MAlonzo.RTE.mazCoerce (d369 (MAlonzo.RTE.mazCoerce v0))))
name628 = "Relation.Binary.IsStrictTotalOrder.trans"
d628 (C978 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d628 v0 = MAlonzo.RTE.mazIncompleteMatch name628
name367 = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.trans"
d367 v0
  = MAlonzo.RTE.mazCoerce
      (d312 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name111 = "Relation.Binary.DecSetoid._.refl"
d111 v0
  = MAlonzo.RTE.mazCoerce
      (d93 (MAlonzo.RTE.mazCoerce (d107 (MAlonzo.RTE.mazCoerce v0))))
name447 = "Relation.Binary.IsTotalOrder._._.Eq.refl"
d447 v0
  = MAlonzo.RTE.mazCoerce
      (d150 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name959 = "Relation.Binary.recCon-NOT-PRINTED"
name463 = "Relation.Binary.TotalOrder._\8776_"
d463 (C932 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d463 v0 = MAlonzo.RTE.mazIncompleteMatch name463
name207 = "Relation.Binary.IsDecPartialOrder.PO.trans"
d207 v0
  = MAlonzo.RTE.mazCoerce
      (d148 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name543 = "Relation.Binary.DecTotalOrder"
d543 a0 a1 a2 = ()
 
data T543 a0 a1 a2 a3 = C959 a0 a1 a2 a3
name175 = "Relation.Binary.Poset._.trans"
d175 v0
  = MAlonzo.RTE.mazCoerce
      (d148 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name687 = "Relation.Binary.StrictTotalOrder.Eq.Carrier"
d687 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d105
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name255 = "Relation.Binary.DecPoset.poset"
d255 v0
  = MAlonzo.RTE.mazCoerce
      (C813 (MAlonzo.RTE.mazCoerce (d233 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d234 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d235 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d242 (MAlonzo.RTE.mazCoerce v0))))
name527 = "Relation.Binary.IsDecTotalOrder.TO._._.Eq.refl"
d527 v0
  = MAlonzo.RTE.mazCoerce
      (d447 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name271 = "Relation.Binary.DecPoset._._._.Eq.sym"
d271 v0
  = MAlonzo.RTE.mazCoerce
      (d179 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name783 = "Relation.Binary.recCon-NOT-PRINTED"
name607 = "Relation.Binary.DecTotalOrder.Eq._.setoid"
d607 v0
  = MAlonzo.RTE.mazCoerce
      (d115 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name95 = "Relation.Binary.IsDecEquivalence._.sym"
d95 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d275
         (MAlonzo.RTE.mazCoerce (d90 (MAlonzo.RTE.mazCoerce v0))))
name495 = "Relation.Binary.TotalOrder._._._.Eq.reflexive"
d495 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d178 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v3))))
name239 = "Relation.Binary.DecPoset.DPO._\8804?_"
d239 v0
  = MAlonzo.RTE.mazCoerce
      (d200 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name575 = "Relation.Binary.DecTotalOrder.totalOrder"
d575 v0
  = MAlonzo.RTE.mazCoerce
      (C932 (MAlonzo.RTE.mazCoerce (d551 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d552 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d553 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d562 (MAlonzo.RTE.mazCoerce v0))))
name335 = "Relation.Binary.StrictPartialOrder._.Eq.sym"
d335 v0
  = MAlonzo.RTE.mazCoerce
      (d311 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name591 = "Relation.Binary.DecTotalOrder._.\8764-resp-\8776"
d591 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d475 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v3))))
name415
  = "Relation.Binary.DecStrictPartialOrder.Eq._.isEquivalence"
d415 v0
  = MAlonzo.RTE.mazCoerce
      (d110 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name671 = "Relation.Binary.StrictTotalOrder._.irrefl"
d671 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d644 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name559 = "Relation.Binary.DecTotalOrder.DTO.isEquivalence"
d559 v0
  = MAlonzo.RTE.mazCoerce
      (d519 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name639 = "Relation.Binary.IsStrictTotalOrder.Eq.sym"
d639 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d95
         (MAlonzo.RTE.mazCoerce
            (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name143 = "Relation.Binary.IsPartialOrder.antisym"
d143 (C804 v0 v1) = MAlonzo.RTE.mazCoerce v1
d143 v0 = MAlonzo.RTE.mazIncompleteMatch name143
name399 = "Relation.Binary.DecStrictPartialOrder.DSPO.trans"
d399 v0
  = MAlonzo.RTE.mazCoerce
      (d363 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name479 = "Relation.Binary.TotalOrder._._._.Eq.trans"
d479 v0
  = MAlonzo.RTE.mazCoerce
      (d450 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name242 = "Relation.Binary.DecPoset.DPO.isPartialOrder"
d242 v0
  = MAlonzo.RTE.mazCoerce
      (d198 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name258 = "Relation.Binary.DecPoset._._\8804_"
d258 v0
  = MAlonzo.RTE.mazCoerce
      (d167 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name514 = "Relation.Binary.IsDecTotalOrder.isTotalOrder"
d514 (C947 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d514 v0 = MAlonzo.RTE.mazIncompleteMatch name514
name594 = "Relation.Binary.DecTotalOrder._._._._.Eq.sym"
d594 v0
  = MAlonzo.RTE.mazCoerce
      (d478 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name738 = "Relation.Binary.recCon-NOT-PRINTED"
name482 = "Relation.Binary.TotalOrder._._\8776_"
d482 v0
  = MAlonzo.RTE.mazCoerce
      (d166 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name50 = "Relation.Binary.Preorder._.reflexive"
d50 v0
  = MAlonzo.RTE.mazCoerce
      (d19 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name562 = "Relation.Binary.DecTotalOrder.DTO.isTotalOrder"
d562 v0
  = MAlonzo.RTE.mazCoerce
      (d514 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name306 = "Relation.Binary.IsStrictPartialOrder.trans"
d306 (C859 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d306 v0 = MAlonzo.RTE.mazIncompleteMatch name306
name66 = "Relation.Binary.Setoid._\8776_"
d66 (C738 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d66 v0 = MAlonzo.RTE.mazIncompleteMatch name66
name578 = "Relation.Binary.DecTotalOrder._._\8804_"
d578 v0
  = MAlonzo.RTE.mazCoerce
      (d464 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name402
  = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.isEquivalence"
d402 v0
  = MAlonzo.RTE.mazCoerce
      (d372 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name146 = "Relation.Binary.IsPartialOrder._.refl"
d146 v0
  = MAlonzo.RTE.mazCoerce
      (d26 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name114 = "Relation.Binary.DecSetoid._.trans"
d114 v0
  = MAlonzo.RTE.mazCoerce
      (d96 (MAlonzo.RTE.mazCoerce (d107 (MAlonzo.RTE.mazCoerce v0))))
name898 = "Relation.Binary.recCon-NOT-PRINTED"
name210 = "Relation.Binary.IsDecPartialOrder.PO._.Eq.reflexive"
d210 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d151 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v6))))
name978 = "Relation.Binary.recCon-NOT-PRINTED"
name178 = "Relation.Binary.Poset._._.Eq.reflexive"
d178 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d151 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d165 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d166 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d167 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v3))))
name690 = "Relation.Binary.StrictTotalOrder.Eq.preorder"
d690 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d122 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name450 = "Relation.Binary.IsTotalOrder._._.Eq.trans"
d450 v0
  = MAlonzo.RTE.mazCoerce
      (d153 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name18 = "Relation.Binary.IsPreorder.isEquivalence"
d18 (C704 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d18 v0 = MAlonzo.RTE.mazIncompleteMatch name18
name530 = "Relation.Binary.IsDecTotalOrder.TO._._.Eq.trans"
d530 v0
  = MAlonzo.RTE.mazCoerce
      (d450 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name274 = "Relation.Binary.DecPoset.Eq.decSetoid"
d274 v0
  = MAlonzo.RTE.mazCoerce
      (C790 (MAlonzo.RTE.mazCoerce (d233 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d234 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d249 (MAlonzo.RTE.mazCoerce v0))))
name674 = "Relation.Binary.StrictTotalOrder._.isStrictPartialOrder"
d674 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name418 = "Relation.Binary.DecStrictPartialOrder.Eq._.reflexive"
d418 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d112 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v3))))
name597 = "Relation.Binary.DecTotalOrder.Eq.decSetoid"
d597 v0
  = MAlonzo.RTE.mazCoerce
      (C790 (MAlonzo.RTE.mazCoerce (d551 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d552 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d569 (MAlonzo.RTE.mazCoerce v0))))
name485 = "Relation.Binary.TotalOrder._.antisym"
d485 v0
  = MAlonzo.RTE.mazCoerce
      (d170 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name565 = "Relation.Binary.DecTotalOrder.DTO.total"
d565 v0
  = MAlonzo.RTE.mazCoerce
      (d524 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name309 = "Relation.Binary.IsStrictPartialOrder.Eq.refl"
d309 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d274
         (MAlonzo.RTE.mazCoerce (d304 (MAlonzo.RTE.mazCoerce v0))))
name53 = "Relation.Binary.Preorder._.Eq.refl"
d53 v0
  = MAlonzo.RTE.mazCoerce
      (d22 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name581 = "Relation.Binary.DecTotalOrder._.isEquivalence"
d581 v0
  = MAlonzo.RTE.mazCoerce
      (d468 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name325 = "Relation.Binary.StrictPartialOrder._\8776_"
d325 (C870 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d325 v0 = MAlonzo.RTE.mazIncompleteMatch name325
name69 = "Relation.Binary.Setoid._.refl"
d69 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d274
         (MAlonzo.RTE.mazCoerce (d67 (MAlonzo.RTE.mazCoerce v0))))
name405 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.sym"
d405 v0
  = MAlonzo.RTE.mazCoerce
      (d375 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name149 = "Relation.Binary.IsPartialOrder._.\8764-resp-\8776"
d149 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d27 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v6))))
name293 = "Relation.Binary.IsStrictPartialOrder"
d293 a0 a1 a2 a3 a4 a5 = ()
 
data T293 a0 a1 a2 a3 = C859 a0 a1 a2 a3
name373 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.refl"
d373 v0
  = MAlonzo.RTE.mazCoerce
      (d93 (MAlonzo.RTE.mazCoerce (d369 (MAlonzo.RTE.mazCoerce v0))))
name117 = "Relation.Binary.DecSetoid._._\8776_"
d117 v0
  = MAlonzo.RTE.mazCoerce
      (d66 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name629 = "Relation.Binary.IsStrictTotalOrder.compare"
d629 (C978 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d629 v0 = MAlonzo.RTE.mazIncompleteMatch name629
name389 = "Relation.Binary.DecStrictPartialOrder._\8776_"
d389 (C910 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d389 v0 = MAlonzo.RTE.mazIncompleteMatch name389
name133 = "Relation.Binary.IsPartialOrder"
d133 a0 a1 a2 a3 a4 a5 = ()
 
data T133 a0 a1 = C804 a0 a1
name645 = "Relation.Binary.IsStrictTotalOrder._.isEquivalence"
d645 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d304
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name469 = "Relation.Binary.TotalOrder._.isPartialOrder"
d469 v0
  = MAlonzo.RTE.mazCoerce
      (d437 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name357 = "Relation.Binary.IsDecStrictPartialOrder._\8799_"
d357 (C898 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d357 v0 = MAlonzo.RTE.mazIncompleteMatch name357
name181 = "Relation.Binary.Poset.preorder"
d181 v0
  = MAlonzo.RTE.mazCoerce
      (C729 (MAlonzo.RTE.mazCoerce (d165 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d166 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d167 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d172 (MAlonzo.RTE.mazCoerce v0))))
name693 = "Relation.Binary.StrictTotalOrder.Eq.setoid"
d693 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d115
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name437 = "Relation.Binary.IsTotalOrder.isPartialOrder"
d437 (C923 v0 v1) = MAlonzo.RTE.mazCoerce v0
d437 v0 = MAlonzo.RTE.mazIncompleteMatch name437
name277 = "Relation.Binary.DecPoset.Eq._._\8799_"
d277 v0
  = MAlonzo.RTE.mazCoerce
      (d109 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name677 = "Relation.Binary.StrictTotalOrder._.Eq.isEquivalence"
d677 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d636 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name421 = "Relation.Binary.DecStrictPartialOrder.Eq._.trans"
d421 v0
  = MAlonzo.RTE.mazCoerce
      (d114 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name165 = "Relation.Binary.Poset.Carrier"
d165 (C813 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d165 v0 = MAlonzo.RTE.mazIncompleteMatch name165
name245 = "Relation.Binary.DecPoset.DPO.reflexive"
d245 v0
  = MAlonzo.RTE.mazCoerce
      (d206 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name261 = "Relation.Binary.DecPoset._.isEquivalence"
d261 v0
  = MAlonzo.RTE.mazCoerce
      (d171 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name272 = "Relation.Binary.DecPoset._._._.Eq.trans"
d272 v0
  = MAlonzo.RTE.mazCoerce
      (d180 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name528 = "Relation.Binary.IsDecTotalOrder.TO._._.Eq.reflexive"
d528 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d448 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v6))))
name416 = "Relation.Binary.DecStrictPartialOrder.Eq._.preorder"
d416 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d122 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v3))))
name672 = "Relation.Binary.StrictTotalOrder._.isDecEquivalence"
d672 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name496 = "Relation.Binary.TotalOrder._._._.Eq.sym"
d496 v0
  = MAlonzo.RTE.mazCoerce
      (d179 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name240 = "Relation.Binary.DecPoset.DPO.antisym"
d240 v0
  = MAlonzo.RTE.mazCoerce
      (d202 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name592 = "Relation.Binary.DecTotalOrder._._._._.Eq.refl"
d592 v0
  = MAlonzo.RTE.mazCoerce
      (d476 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name336 = "Relation.Binary.StrictPartialOrder._.Eq.trans"
d336 v0
  = MAlonzo.RTE.mazCoerce
      (d312 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name480 = "Relation.Binary.TotalOrder.poset"
d480 v0
  = MAlonzo.RTE.mazCoerce
      (C813 (MAlonzo.RTE.mazCoerce (d462 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d463 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d464 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d469 (MAlonzo.RTE.mazCoerce v0))))
name304 = "Relation.Binary.IsStrictPartialOrder.isEquivalence"
d304 (C859 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d304 v0 = MAlonzo.RTE.mazIncompleteMatch name304
name48 = "Relation.Binary.Preorder._.isEquivalence"
d48 v0
  = MAlonzo.RTE.mazCoerce
      (d18 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name560 = "Relation.Binary.DecTotalOrder.DTO.isPartialOrder"
d560 v0
  = MAlonzo.RTE.mazCoerce
      (d520 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name400 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq._\8799_"
d400 v0
  = MAlonzo.RTE.mazCoerce
      (d371 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name112 = "Relation.Binary.DecSetoid._.reflexive"
d112 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d94 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d105 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce (d106 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce (d107 (MAlonzo.RTE.mazCoerce v2))))
name640 = "Relation.Binary.IsStrictTotalOrder.Eq.trans"
d640 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d96
         (MAlonzo.RTE.mazCoerce
            (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name464 = "Relation.Binary.TotalOrder._\8804_"
d464 (C932 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d464 v0 = MAlonzo.RTE.mazIncompleteMatch name464
name208 = "Relation.Binary.IsDecPartialOrder.PO.\8764-resp-\8776"
d208 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d149 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v6))))
name608 = "Relation.Binary.DecTotalOrder.Eq._.sym"
d608 v0
  = MAlonzo.RTE.mazCoerce
      (d113 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name96 = "Relation.Binary.IsDecEquivalence._.trans"
d96 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d276
         (MAlonzo.RTE.mazCoerce (d90 (MAlonzo.RTE.mazCoerce v0))))
name688 = "Relation.Binary.StrictTotalOrder.Eq.isDecEquivalence"
d688 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d107
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name176 = "Relation.Binary.Poset._.\8764-resp-\8776"
d176 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d149 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d165 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d166 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d167 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v3))))
name704 = "Relation.Binary.recCon-NOT-PRINTED"
name448 = "Relation.Binary.IsTotalOrder._._.Eq.reflexive"
d448 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d151 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v6))))
name251 = "Relation.Binary.DecPoset.DPO.Eq.refl"
d251 v0
  = MAlonzo.RTE.mazCoerce
      (d218 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name267 = "Relation.Binary.DecPoset._.trans"
d267 v0
  = MAlonzo.RTE.mazCoerce
      (d175 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name523 = "Relation.Binary.IsDecTotalOrder.TO.reflexive"
d523 v0
  = MAlonzo.RTE.mazCoerce
      (d444 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name91 = "Relation.Binary.IsDecEquivalence._\8799_"
d91 (C783 v0 v1) = MAlonzo.RTE.mazCoerce v1
d91 v0 = MAlonzo.RTE.mazIncompleteMatch name91
name859 = "Relation.Binary.recCon-NOT-PRINTED"
name603 = "Relation.Binary.DecTotalOrder.Eq._.isEquivalence"
d603 v0
  = MAlonzo.RTE.mazCoerce
      (d110 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name491 = "Relation.Binary.TotalOrder._.reflexive"
d491 v0
  = MAlonzo.RTE.mazCoerce
      (d174 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name235 = "Relation.Binary.DecPoset._\8804_"
d235 (C840 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d235 v0 = MAlonzo.RTE.mazIncompleteMatch name235
name571 = "Relation.Binary.DecTotalOrder.DTO.Eq.refl"
d571 v0
  = MAlonzo.RTE.mazCoerce
      (d536 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name59 = "Relation.Binary.Setoid"
d59 a0 a1 = ()
 
data T59 a0 a1 a2 = C738 a0 a1 a2
name587 = "Relation.Binary.DecTotalOrder._.refl"
d587 v0
  = MAlonzo.RTE.mazCoerce
      (d471 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name331 = "Relation.Binary.StrictPartialOrder._.isEquivalence"
d331 v0
  = MAlonzo.RTE.mazCoerce
      (d304 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name923 = "Relation.Binary.recCon-NOT-PRINTED"
name667 = "Relation.Binary.StrictTotalOrder._._<?_"
d667 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d632 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name411 = "Relation.Binary.DecStrictPartialOrder.Eq._._\8776_"
d411 v0
  = MAlonzo.RTE.mazCoerce
      (d106 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name43 = "Relation.Binary.Preorder.Carrier"
d43 (C729 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d43 v0 = MAlonzo.RTE.mazIncompleteMatch name43
name123 = "Relation.Binary.DecSetoid._.refl"
d123 v0
  = MAlonzo.RTE.mazCoerce
      (d69 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name635 = "Relation.Binary.IsStrictTotalOrder.Eq._\8799_"
d635 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d91
         (MAlonzo.RTE.mazCoerce
            (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name395 = "Relation.Binary.DecStrictPartialOrder.DSPO.<-resp-\8776"
d395 v0
  = MAlonzo.RTE.mazCoerce
      (d360 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name475 = "Relation.Binary.TotalOrder._.\8764-resp-\8776"
d475 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d446 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d462 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d463 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d464 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v3))))
name219 = "Relation.Binary.IsDecPartialOrder.Eq._.reflexive"
d219 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d94 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce (d214 (MAlonzo.RTE.mazCoerce v6))))
name107 = "Relation.Binary.DecSetoid.isDecEquivalence"
d107 (C790 v0 v1 v2) = MAlonzo.RTE.mazCoerce v2
d107 v0 = MAlonzo.RTE.mazIncompleteMatch name107
name363 = "Relation.Binary.IsDecStrictPartialOrder.SPO.trans"
d363 v0
  = MAlonzo.RTE.mazCoerce
      (d306 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name443 = "Relation.Binary.IsTotalOrder._.refl"
d443 v0
  = MAlonzo.RTE.mazCoerce
      (d146 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name203 = "Relation.Binary.IsDecPartialOrder.PO.isEquivalence"
d203 v0
  = MAlonzo.RTE.mazCoerce
      (d145 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name539 = "Relation.Binary.IsDecTotalOrder.Eq._.trans"
d539 v0
  = MAlonzo.RTE.mazCoerce
      (d96 (MAlonzo.RTE.mazCoerce (d532 (MAlonzo.RTE.mazCoerce v0))))
name283 = "Relation.Binary.DecPoset.Eq._.reflexive"
d283 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d112 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v3))))
name27 = "Relation.Binary.IsPreorder.\8764-resp-\8776"
d27 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Data.Product.C15
         (MAlonzo.RTE.mazCoerce
            (\ v7 ->
               \ v8 ->
                 \ v9 ->
                   \ v10 ->
                     \ v11 ->
                       d20 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v7)
                         (MAlonzo.RTE.mazCoerce v8)
                         (MAlonzo.RTE.mazCoerce v9)
                         (MAlonzo.RTE.mazCoerce v11)
                         (MAlonzo.RTE.mazCoerce
                            (d19 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v8)
                               (MAlonzo.RTE.mazCoerce v9)
                               (MAlonzo.RTE.mazCoerce v10)))))
         (MAlonzo.RTE.mazCoerce
            (\ v7 ->
               \ v8 ->
                 \ v9 ->
                   \ v10 ->
                     d20 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v9)
                       (MAlonzo.RTE.mazCoerce v8)
                       (MAlonzo.RTE.mazCoerce v7)
                       (MAlonzo.RTE.mazCoerce
                          (MAlonzo.Code.Function.d79 (MAlonzo.RTE.mazCoerce v1)
                             (MAlonzo.RTE.mazCoerce v2)
                             (MAlonzo.RTE.mazCoerce
                                (v4 (MAlonzo.RTE.mazCoerce v9) (MAlonzo.RTE.mazCoerce v8)))
                             (MAlonzo.RTE.mazCoerce
                                (\ v11 ->
                                   v5 (MAlonzo.RTE.mazCoerce v9) (MAlonzo.RTE.mazCoerce v8)))
                             (MAlonzo.RTE.mazCoerce
                                (d19 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v9)
                                   (MAlonzo.RTE.mazCoerce v8)))
                             (MAlonzo.RTE.mazCoerce
                                (d24 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v8)
                                   (MAlonzo.RTE.mazCoerce v9)
                                   (MAlonzo.RTE.mazCoerce v10))))))))
name683 = "Relation.Binary.StrictTotalOrder.decSetoid"
d683 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (C790 (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (d672 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name171 = "Relation.Binary.Poset._.isEquivalence"
d171 v0
  = MAlonzo.RTE.mazCoerce
      (d145 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name606 = "Relation.Binary.DecTotalOrder.Eq._.reflexive"
d606 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d112 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v3))))
name94 = "Relation.Binary.IsDecEquivalence._.reflexive"
d94 v0 v1 v2 v3 v4
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d277 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce (d90 (MAlonzo.RTE.mazCoerce v4))))
name238 = "Relation.Binary.DecPoset.DPO._\8799_"
d238 v0
  = MAlonzo.RTE.mazCoerce
      (d199 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name494 = "Relation.Binary.TotalOrder._._._.Eq.refl"
d494 v0
  = MAlonzo.RTE.mazCoerce
      (d177 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name574 = "Relation.Binary.DecTotalOrder.DTO.Eq.trans"
d574 v0
  = MAlonzo.RTE.mazCoerce
      (d539 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name334 = "Relation.Binary.StrictPartialOrder._.Eq.reflexive"
d334 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d310 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d324 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d325 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d326 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v3))))
name590 = "Relation.Binary.DecTotalOrder._.trans"
d590 v0
  = MAlonzo.RTE.mazCoerce
      (d474 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name414
  = "Relation.Binary.DecStrictPartialOrder.Eq._.isDecEquivalence"
d414 v0
  = MAlonzo.RTE.mazCoerce
      (d107 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name670 = "Relation.Binary.StrictTotalOrder._.compare"
d670 v0
  = MAlonzo.RTE.mazCoerce
      (d629 (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v0))))
name558 = "Relation.Binary.DecTotalOrder.DTO.antisym"
d558 v0
  = MAlonzo.RTE.mazCoerce
      (d518 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name46 = "Relation.Binary.Preorder.isPreorder"
d46 (C729 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d46 v0 = MAlonzo.RTE.mazIncompleteMatch name46
name126 = "Relation.Binary.DecSetoid._.trans"
d126 v0
  = MAlonzo.RTE.mazCoerce
      (d72 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name638 = "Relation.Binary.IsStrictTotalOrder.Eq.reflexive"
d638 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d94 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce
            (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name142 = "Relation.Binary.IsPartialOrder.isPreorder"
d142 (C804 v0 v1) = MAlonzo.RTE.mazCoerce v0
d142 v0 = MAlonzo.RTE.mazIncompleteMatch name142
name910 = "Relation.Binary.recCon-NOT-PRINTED"
name654 = "Relation.Binary.StrictTotalOrder"
d654 a0 a1 a2 = ()
 
data T654 a0 a1 a2 a3 = C1027 a0 a1 a2 a3
name398
  = "Relation.Binary.DecStrictPartialOrder.DSPO.isStrictPartialOrder"
d398 v0
  = MAlonzo.RTE.mazCoerce
      (d356 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name478 = "Relation.Binary.TotalOrder._._._.Eq.sym"
d478 v0
  = MAlonzo.RTE.mazCoerce
      (d449 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name366 = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.sym"
d366 v0
  = MAlonzo.RTE.mazCoerce
      (d311 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name110 = "Relation.Binary.DecSetoid._.isEquivalence"
d110 v0
  = MAlonzo.RTE.mazCoerce
      (d90 (MAlonzo.RTE.mazCoerce (d107 (MAlonzo.RTE.mazCoerce v0))))
name446 = "Relation.Binary.IsTotalOrder._.\8764-resp-\8776"
d446 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d149 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v6))))
name462 = "Relation.Binary.TotalOrder.Carrier"
d462 (C932 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d462 v0 = MAlonzo.RTE.mazIncompleteMatch name462
name206 = "Relation.Binary.IsDecPartialOrder.PO.reflexive"
d206 v0
  = MAlonzo.RTE.mazCoerce
      (d147 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name286 = "Relation.Binary.DecPoset.Eq._.trans"
d286 v0
  = MAlonzo.RTE.mazCoerce
      (d114 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name174 = "Relation.Binary.Poset._.reflexive"
d174 v0
  = MAlonzo.RTE.mazCoerce
      (d147 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name686 = "Relation.Binary.StrictTotalOrder.Eq._\8799_"
d686 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d109
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name254 = "Relation.Binary.DecPoset.DPO.Eq.trans"
d254 v0
  = MAlonzo.RTE.mazCoerce
      (d221 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name526 = "Relation.Binary.IsDecTotalOrder.TO.\8764-resp-\8776"
d526 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d446 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v6))))
name270 = "Relation.Binary.DecPoset._._._.Eq.reflexive"
d270 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d178 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v3))))
name369
  = "Relation.Binary.IsDecStrictPartialOrder.Eq.isDecEquivalence"
d369 v0
  = MAlonzo.RTE.mazCoerce
      (C783 (MAlonzo.RTE.mazCoerce (d362 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d357 (MAlonzo.RTE.mazCoerce v0))))
name113 = "Relation.Binary.DecSetoid._.sym"
d113 v0
  = MAlonzo.RTE.mazCoerce
      (d95 (MAlonzo.RTE.mazCoerce (d107 (MAlonzo.RTE.mazCoerce v0))))
name641 = "Relation.Binary.IsStrictTotalOrder.isStrictPartialOrder"
d641 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (C859 (MAlonzo.RTE.mazCoerce (d627 (MAlonzo.RTE.mazCoerce v6)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Consequences.d158
               (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce (d630 (MAlonzo.RTE.mazCoerce v6)))
               (MAlonzo.RTE.mazCoerce
                  (d639 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                     (MAlonzo.RTE.mazCoerce v2)
                     (MAlonzo.RTE.mazCoerce v3)
                     (MAlonzo.RTE.mazCoerce v4)
                     (MAlonzo.RTE.mazCoerce v5)
                     (MAlonzo.RTE.mazCoerce v6)))
               (MAlonzo.RTE.mazCoerce (d629 (MAlonzo.RTE.mazCoerce v6)))))
         (MAlonzo.RTE.mazCoerce (d628 (MAlonzo.RTE.mazCoerce v6)))
         (MAlonzo.RTE.mazCoerce (d630 (MAlonzo.RTE.mazCoerce v6))))
name465 = "Relation.Binary.TotalOrder.isTotalOrder"
d465 (C932 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d465 v0 = MAlonzo.RTE.mazIncompleteMatch name465
name209 = "Relation.Binary.IsDecPartialOrder.PO._.Eq.refl"
d209 v0
  = MAlonzo.RTE.mazCoerce
      (d150 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name609 = "Relation.Binary.DecTotalOrder.Eq._.trans"
d609 v0
  = MAlonzo.RTE.mazCoerce
      (d114 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name689 = "Relation.Binary.StrictTotalOrder.Eq.isEquivalence"
d689 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d110
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name177 = "Relation.Binary.Poset._._.Eq.refl"
d177 v0
  = MAlonzo.RTE.mazCoerce
      (d150 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name449 = "Relation.Binary.IsTotalOrder._._.Eq.sym"
d449 v0
  = MAlonzo.RTE.mazCoerce
      (d152 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name529 = "Relation.Binary.IsDecTotalOrder.TO._._.Eq.sym"
d529 v0
  = MAlonzo.RTE.mazCoerce
      (d449 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name417 = "Relation.Binary.DecStrictPartialOrder.Eq._.refl"
d417 v0
  = MAlonzo.RTE.mazCoerce
      (d111 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name673 = "Relation.Binary.StrictTotalOrder._.isEquivalence"
d673 v0
  = MAlonzo.RTE.mazCoerce
      (d627 (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v0))))
name497 = "Relation.Binary.TotalOrder._._._.Eq.trans"
d497 v0
  = MAlonzo.RTE.mazCoerce
      (d180 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name241 = "Relation.Binary.DecPoset.DPO.isEquivalence"
d241 v0
  = MAlonzo.RTE.mazCoerce
      (d203 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name257 = "Relation.Binary.DecPoset._._\8776_"
d257 v0
  = MAlonzo.RTE.mazCoerce
      (d166 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name593 = "Relation.Binary.DecTotalOrder._._._._.Eq.reflexive"
d593 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d477 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v3))))
name337 = "Relation.Binary.StrictPartialOrder.asymmetric"
d337 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Consequences.d9
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d324 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d325 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d326 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d333 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d332 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d330 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
name225 = "Relation.Binary.DecPoset"
d225 a0 a1 a2 = ()
 
data T225 a0 a1 a2 a3 = C840 a0 a1 a2 a3
name305 = "Relation.Binary.IsStrictPartialOrder.irrefl"
d305 (C859 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d305 v0 = MAlonzo.RTE.mazIncompleteMatch name305
name49 = "Relation.Binary.Preorder._.refl"
d49 v0
  = MAlonzo.RTE.mazCoerce
      (d26 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name561 = "Relation.Binary.DecTotalOrder.DTO.isPreorder"
d561 v0
  = MAlonzo.RTE.mazCoerce
      (d521 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name65 = "Relation.Binary.Setoid.Carrier"
d65 (C738 v0 v1 v2) = MAlonzo.RTE.mazCoerce v0
d65 v0 = MAlonzo.RTE.mazIncompleteMatch name65
name577 = "Relation.Binary.DecTotalOrder._._\8776_"
d577 v0
  = MAlonzo.RTE.mazCoerce
      (d463 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name401
  = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.isDecEquivalence"
d401 v0
  = MAlonzo.RTE.mazCoerce
      (d369 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name145 = "Relation.Binary.IsPartialOrder._.isEquivalence"
d145 v0
  = MAlonzo.RTE.mazCoerce
      (d18 (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v0))))
name252 = "Relation.Binary.DecPoset.DPO.Eq.reflexive"
d252 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d219 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d233 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d234 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d235 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v3))))
name524 = "Relation.Binary.IsDecTotalOrder.TO.total"
d524 v0
  = MAlonzo.RTE.mazCoerce
      (d438 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name268 = "Relation.Binary.DecPoset._.\8764-resp-\8776"
d268 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d176 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v3))))
name604 = "Relation.Binary.DecTotalOrder.Eq._.preorder"
d604 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d122 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v3))))
name492 = "Relation.Binary.TotalOrder._.trans"
d492 v0
  = MAlonzo.RTE.mazCoerce
      (d175 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name236 = "Relation.Binary.DecPoset.isDecPartialOrder"
d236 (C840 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d236 v0 = MAlonzo.RTE.mazIncompleteMatch name236
name316 = "Relation.Binary.StrictPartialOrder"
d316 a0 a1 a2 = ()
 
data T316 a0 a1 a2 a3 = C870 a0 a1 a2 a3
name828 = "Relation.Binary.recCon-NOT-PRINTED"
name572 = "Relation.Binary.DecTotalOrder.DTO.Eq.reflexive"
d572 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d537 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d551 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d552 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d553 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v3))))
name588 = "Relation.Binary.DecTotalOrder._.reflexive"
d588 v0
  = MAlonzo.RTE.mazCoerce
      (d472 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name332 = "Relation.Binary.StrictPartialOrder._.trans"
d332 v0
  = MAlonzo.RTE.mazCoerce
      (d306 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name668 = "Relation.Binary.StrictTotalOrder._._\8799_"
d668 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d631 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name412 = "Relation.Binary.DecStrictPartialOrder.Eq._._\8799_"
d412 v0
  = MAlonzo.RTE.mazCoerce
      (d109 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name44 = "Relation.Binary.Preorder._\8776_"
d44 (C729 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d44 v0 = MAlonzo.RTE.mazIncompleteMatch name44
name556 = "Relation.Binary.DecTotalOrder.DTO._\8799_"
d556 v0
  = MAlonzo.RTE.mazCoerce
      (d515 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name380 = "Relation.Binary.DecStrictPartialOrder"
d380 a0 a1 a2 = ()
 
data T380 a0 a1 a2 a3 = C910 a0 a1 a2 a3
name124 = "Relation.Binary.DecSetoid._.reflexive"
d124 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d70 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v2))))
name636 = "Relation.Binary.IsStrictTotalOrder.Eq.isEquivalence"
d636 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d90
         (MAlonzo.RTE.mazCoerce
            (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name396 = "Relation.Binary.DecStrictPartialOrder.DSPO.irrefl"
d396 v0
  = MAlonzo.RTE.mazCoerce
      (d361 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name476 = "Relation.Binary.TotalOrder._._._.Eq.refl"
d476 v0
  = MAlonzo.RTE.mazCoerce
      (d447 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name220 = "Relation.Binary.IsDecPartialOrder.Eq._.sym"
d220 v0
  = MAlonzo.RTE.mazCoerce
      (d95 (MAlonzo.RTE.mazCoerce (d214 (MAlonzo.RTE.mazCoerce v0))))
name364 = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.refl"
d364 v0
  = MAlonzo.RTE.mazCoerce
      (d309 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name444 = "Relation.Binary.IsTotalOrder._.reflexive"
d444 v0
  = MAlonzo.RTE.mazCoerce
      (d147 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name188 = "Relation.Binary.IsDecPartialOrder"
d188 a0 a1 a2 a3 a4 a5 = ()
 
data T188 a0 a1 a2 = C828 a0 a1 a2
name204 = "Relation.Binary.IsDecPartialOrder.PO.isPreorder"
d204 v0
  = MAlonzo.RTE.mazCoerce
      (d142 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name284 = "Relation.Binary.DecPoset.Eq._.setoid"
d284 v0
  = MAlonzo.RTE.mazCoerce
      (d115 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name428 = "Relation.Binary.IsTotalOrder"
d428 a0 a1 a2 a3 a4 a5 = ()
 
data T428 a0 a1 = C923 a0 a1
name172 = "Relation.Binary.Poset._.isPreorder"
d172 v0
  = MAlonzo.RTE.mazCoerce
      (d142 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name327 = "Relation.Binary.StrictPartialOrder.isStrictPartialOrder"
d327 (C870 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d327 v0 = MAlonzo.RTE.mazIncompleteMatch name327
name71 = "Relation.Binary.Setoid._.sym"
d71 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d275
         (MAlonzo.RTE.mazCoerce (d67 (MAlonzo.RTE.mazCoerce v0))))
name583 = "Relation.Binary.DecTotalOrder._.isPreorder"
d583 v0
  = MAlonzo.RTE.mazCoerce
      (d470 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name663 = "Relation.Binary.StrictTotalOrder._\8776_"
d663 (C1027 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d663 v0 = MAlonzo.RTE.mazIncompleteMatch name663
name407
  = "Relation.Binary.DecStrictPartialOrder.strictPartialOrder"
d407 v0
  = MAlonzo.RTE.mazCoerce
      (C870 (MAlonzo.RTE.mazCoerce (d388 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d389 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d390 (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce (d398 (MAlonzo.RTE.mazCoerce v0))))
name151 = "Relation.Binary.IsPartialOrder._.Eq.reflexive"
d151 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d23 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d142 (MAlonzo.RTE.mazCoerce v6))))
name551 = "Relation.Binary.DecTotalOrder.Carrier"
d551 (C959 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v0
d551 v0 = MAlonzo.RTE.mazIncompleteMatch name551
name119 = "Relation.Binary.DecSetoid._.indexedSetoid"
d119 v0
  = MAlonzo.RTE.mazCoerce
      (d77 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name631 = "Relation.Binary.IsStrictTotalOrder._\8799_"
d631 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Consequences.d168
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d629 (MAlonzo.RTE.mazCoerce v6))))
name375 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.sym"
d375 v0
  = MAlonzo.RTE.mazCoerce
      (d95 (MAlonzo.RTE.mazCoerce (d369 (MAlonzo.RTE.mazCoerce v0))))
name391
  = "Relation.Binary.DecStrictPartialOrder.isDecStrictPartialOrder"
d391 (C910 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d391 v0 = MAlonzo.RTE.mazIncompleteMatch name391
name647 = "Relation.Binary.IsStrictTotalOrder._.Eq.refl"
d647 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d309
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name471 = "Relation.Binary.TotalOrder._.refl"
d471 v0
  = MAlonzo.RTE.mazCoerce
      (d443 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name695 = "Relation.Binary.StrictTotalOrder.Eq.trans"
d695 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d114
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name199 = "Relation.Binary.IsDecPartialOrder._\8799_"
d199 (C828 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d199 v0 = MAlonzo.RTE.mazIncompleteMatch name199
name279 = "Relation.Binary.DecPoset.Eq._.isDecEquivalence"
d279 v0
  = MAlonzo.RTE.mazCoerce
      (d107 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name23 = "Relation.Binary.IsPreorder.Eq.reflexive"
d23 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d277 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce (d18 (MAlonzo.RTE.mazCoerce v6))))
name535 = "Relation.Binary.IsDecTotalOrder.Eq._.isEquivalence"
d535 v0
  = MAlonzo.RTE.mazCoerce
      (d90 (MAlonzo.RTE.mazCoerce (d532 (MAlonzo.RTE.mazCoerce v0))))
name167 = "Relation.Binary.Poset._\8804_"
d167 (C813 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d167 v0 = MAlonzo.RTE.mazIncompleteMatch name167
name679 = "Relation.Binary.StrictTotalOrder._.Eq.reflexive"
d679 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d638 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v3))))
name247 = "Relation.Binary.DecPoset.DPO.\8764-resp-\8776"
d247 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d208 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d233 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d234 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d235 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v3))))
name519 = "Relation.Binary.IsDecTotalOrder.TO.isEquivalence"
d519 v0
  = MAlonzo.RTE.mazCoerce
      (d441 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name263 = "Relation.Binary.DecPoset._.isPreorder"
d263 v0
  = MAlonzo.RTE.mazCoerce
      (d172 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name599 = "Relation.Binary.DecTotalOrder.Eq._._\8776_"
d599 v0
  = MAlonzo.RTE.mazCoerce
      (d106 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name487 = "Relation.Binary.TotalOrder._.isPartialOrder"
d487 v0
  = MAlonzo.RTE.mazCoerce
      (d168 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name311 = "Relation.Binary.IsStrictPartialOrder.Eq.sym"
d311 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d275
         (MAlonzo.RTE.mazCoerce (d304 (MAlonzo.RTE.mazCoerce v0))))
name55 = "Relation.Binary.Preorder._.Eq.sym"
d55 v0
  = MAlonzo.RTE.mazCoerce
      (d24 (MAlonzo.RTE.mazCoerce (d46 (MAlonzo.RTE.mazCoerce v0))))
name567 = "Relation.Binary.DecTotalOrder.DTO.\8764-resp-\8776"
d567 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d526 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d551 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d552 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d553 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v3))))
name554 = "Relation.Binary.DecTotalOrder.isDecTotalOrder"
d554 (C959 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v3
d554 v0 = MAlonzo.RTE.mazIncompleteMatch name554
name122 = "Relation.Binary.DecSetoid._.preorder"
d122 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d74 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v2))))
name650 = "Relation.Binary.IsStrictTotalOrder._.Eq.trans"
d650 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d312
         (MAlonzo.RTE.mazCoerce
            (d641 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
name394 = "Relation.Binary.DecStrictPartialOrder.DSPO._\8799_"
d394 v0
  = MAlonzo.RTE.mazCoerce
      (d357 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name474 = "Relation.Binary.TotalOrder._.trans"
d474 v0
  = MAlonzo.RTE.mazCoerce
      (d445 (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v0))))
name218 = "Relation.Binary.IsDecPartialOrder.Eq._.refl"
d218 v0
  = MAlonzo.RTE.mazCoerce
      (d93 (MAlonzo.RTE.mazCoerce (d214 (MAlonzo.RTE.mazCoerce v0))))
name362
  = "Relation.Binary.IsDecStrictPartialOrder.SPO.isEquivalence"
d362 v0
  = MAlonzo.RTE.mazCoerce
      (d304 (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v0))))
name106 = "Relation.Binary.DecSetoid._\8776_"
d106 (C790 v0 v1 v2) = MAlonzo.RTE.mazCoerce v1
d106 v0 = MAlonzo.RTE.mazIncompleteMatch name106
name442 = "Relation.Binary.IsTotalOrder._.isPreorder"
d442 v0
  = MAlonzo.RTE.mazCoerce
      (d142 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name202 = "Relation.Binary.IsDecPartialOrder.PO.antisym"
d202 v0
  = MAlonzo.RTE.mazCoerce
      (d143 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name538 = "Relation.Binary.IsDecTotalOrder.Eq._.sym"
d538 v0
  = MAlonzo.RTE.mazCoerce
      (d95 (MAlonzo.RTE.mazCoerce (d532 (MAlonzo.RTE.mazCoerce v0))))
name282 = "Relation.Binary.DecPoset.Eq._.refl"
d282 v0
  = MAlonzo.RTE.mazCoerce
      (d111 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name26 = "Relation.Binary.IsPreorder.refl"
d26 v0
  = MAlonzo.RTE.mazCoerce
      (\ v1 ->
         d19 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
           (MAlonzo.RTE.mazCoerce v1)
           (MAlonzo.RTE.mazCoerce
              (d22 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
name682 = "Relation.Binary.StrictTotalOrder.strictPartialOrder"
d682 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (C870 (MAlonzo.RTE.mazCoerce (d662 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d663 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d664 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce
            (d674 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name170 = "Relation.Binary.Poset._.antisym"
d170 v0
  = MAlonzo.RTE.mazCoerce
      (d143 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name250 = "Relation.Binary.DecPoset.DPO.Eq.isEquivalence"
d250 v0
  = MAlonzo.RTE.mazCoerce
      (d217 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name266 = "Relation.Binary.DecPoset._.reflexive"
d266 v0
  = MAlonzo.RTE.mazCoerce
      (d174 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name522 = "Relation.Binary.IsDecTotalOrder.TO.refl"
d522 v0
  = MAlonzo.RTE.mazCoerce
      (d443 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name346 = "Relation.Binary.IsDecStrictPartialOrder"
d346 a0 a1 a2 a3 a4 a5 = ()
 
data T346 a0 a1 a2 = C898 a0 a1 a2
name90 = "Relation.Binary.IsDecEquivalence.isEquivalence"
d90 (C783 v0 v1) = MAlonzo.RTE.mazCoerce v0
d90 v0 = MAlonzo.RTE.mazIncompleteMatch name90
name602 = "Relation.Binary.DecTotalOrder.Eq._.isDecEquivalence"
d602 v0
  = MAlonzo.RTE.mazCoerce
      (d107 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name490 = "Relation.Binary.TotalOrder._.refl"
d490 v0
  = MAlonzo.RTE.mazCoerce
      (d173 (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v0))))
name234 = "Relation.Binary.DecPoset._\8776_"
d234 (C840 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v1
d234 v0 = MAlonzo.RTE.mazIncompleteMatch name234
name570 = "Relation.Binary.DecTotalOrder.DTO.Eq.isEquivalence"
d570 v0
  = MAlonzo.RTE.mazCoerce
      (d535 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name74 = "Relation.Binary.Setoid.preorder"
d74 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (C729 (MAlonzo.RTE.mazCoerce (d65 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce
            (MAlonzo.Code.Relation.Binary.Core.d252 (MAlonzo.RTE.mazCoerce v0)
               (MAlonzo.RTE.mazCoerce (d65 (MAlonzo.RTE.mazCoerce v2)))))
         (MAlonzo.RTE.mazCoerce (d66 (MAlonzo.RTE.mazCoerce v2)))
         (MAlonzo.RTE.mazCoerce
            (d73 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2))))
name586 = "Relation.Binary.DecTotalOrder._.preorder"
d586 v0
  = MAlonzo.RTE.mazCoerce
      (d489 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name330 = "Relation.Binary.StrictPartialOrder._.irrefl"
d330 v0
  = MAlonzo.RTE.mazCoerce
      (d305 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name397
  = "Relation.Binary.DecStrictPartialOrder.DSPO.isEquivalence"
d397 v0
  = MAlonzo.RTE.mazCoerce
      (d362 (MAlonzo.RTE.mazCoerce (d391 (MAlonzo.RTE.mazCoerce v0))))
name477 = "Relation.Binary.TotalOrder._._._.Eq.reflexive"
d477 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d448 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d462 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d463 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d464 (MAlonzo.RTE.mazCoerce v3)))
         (MAlonzo.RTE.mazCoerce (d465 (MAlonzo.RTE.mazCoerce v3))))
name221 = "Relation.Binary.IsDecPartialOrder.Eq._.trans"
d221 v0
  = MAlonzo.RTE.mazCoerce
      (d96 (MAlonzo.RTE.mazCoerce (d214 (MAlonzo.RTE.mazCoerce v0))))
name365
  = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.reflexive"
d365 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d310 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce (d356 (MAlonzo.RTE.mazCoerce v6))))
name109 = "Relation.Binary.DecSetoid._._\8799_"
d109 v0
  = MAlonzo.RTE.mazCoerce
      (d91 (MAlonzo.RTE.mazCoerce (d107 (MAlonzo.RTE.mazCoerce v0))))
name445 = "Relation.Binary.IsTotalOrder._.trans"
d445 v0
  = MAlonzo.RTE.mazCoerce
      (d148 (MAlonzo.RTE.mazCoerce (d437 (MAlonzo.RTE.mazCoerce v0))))
name205 = "Relation.Binary.IsDecPartialOrder.PO.refl"
d205 v0
  = MAlonzo.RTE.mazCoerce
      (d146 (MAlonzo.RTE.mazCoerce (d198 (MAlonzo.RTE.mazCoerce v0))))
name285 = "Relation.Binary.DecPoset.Eq._.sym"
d285 v0
  = MAlonzo.RTE.mazCoerce
      (d113 (MAlonzo.RTE.mazCoerce (d274 (MAlonzo.RTE.mazCoerce v0))))
name173 = "Relation.Binary.Poset._.refl"
d173 v0
  = MAlonzo.RTE.mazCoerce
      (d146 (MAlonzo.RTE.mazCoerce (d168 (MAlonzo.RTE.mazCoerce v0))))
name685 = "Relation.Binary.StrictTotalOrder.Eq._\8776_"
d685 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d106
         (MAlonzo.RTE.mazCoerce
            (d683 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3))))
name253 = "Relation.Binary.DecPoset.DPO.Eq.sym"
d253 v0
  = MAlonzo.RTE.mazCoerce
      (d220 (MAlonzo.RTE.mazCoerce (d236 (MAlonzo.RTE.mazCoerce v0))))
name525 = "Relation.Binary.IsDecTotalOrder.TO.trans"
d525 v0
  = MAlonzo.RTE.mazCoerce
      (d445 (MAlonzo.RTE.mazCoerce (d514 (MAlonzo.RTE.mazCoerce v0))))
name269 = "Relation.Binary.DecPoset._._._.Eq.refl"
d269 v0
  = MAlonzo.RTE.mazCoerce
      (d177 (MAlonzo.RTE.mazCoerce (d255 (MAlonzo.RTE.mazCoerce v0))))
name93 = "Relation.Binary.IsDecEquivalence._.refl"
d93 v0
  = MAlonzo.RTE.mazCoerce
      (MAlonzo.Code.Relation.Binary.Core.d274
         (MAlonzo.RTE.mazCoerce (d90 (MAlonzo.RTE.mazCoerce v0))))
name605 = "Relation.Binary.DecTotalOrder.Eq._.refl"
d605 v0
  = MAlonzo.RTE.mazCoerce
      (d111 (MAlonzo.RTE.mazCoerce (d597 (MAlonzo.RTE.mazCoerce v0))))
name493 = "Relation.Binary.TotalOrder._.\8764-resp-\8776"
d493 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d176 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (d480 (MAlonzo.RTE.mazCoerce v3))))
name573 = "Relation.Binary.DecTotalOrder.DTO.Eq.sym"
d573 v0
  = MAlonzo.RTE.mazCoerce
      (d538 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name333 = "Relation.Binary.StrictPartialOrder._.Eq.refl"
d333 v0
  = MAlonzo.RTE.mazCoerce
      (d309 (MAlonzo.RTE.mazCoerce (d327 (MAlonzo.RTE.mazCoerce v0))))
name77 = "Relation.Binary.Setoid.indexedSetoid"
d77 v0
  = MAlonzo.RTE.mazCoerce
      (\ v1 ->
         \ v2 ->
           MAlonzo.Code.Relation.Binary.Indexed.Core.C182
             (MAlonzo.RTE.mazCoerce (\ v3 -> d65 (MAlonzo.RTE.mazCoerce v0)))
             (MAlonzo.RTE.mazCoerce
                (\ v3 -> \ v4 -> d66 (MAlonzo.RTE.mazCoerce v0)))
             (MAlonzo.RTE.mazCoerce
                (MAlonzo.Code.Relation.Binary.Indexed.Core.C149
                   (MAlonzo.RTE.mazCoerce (\ v3 -> d69 (MAlonzo.RTE.mazCoerce v0)))
                   (MAlonzo.RTE.mazCoerce
                      (\ v3 -> \ v4 -> d71 (MAlonzo.RTE.mazCoerce v0)))
                   (MAlonzo.RTE.mazCoerce
                      (\ v3 -> \ v4 -> \ v5 -> d72 (MAlonzo.RTE.mazCoerce v0))))))
name589 = "Relation.Binary.DecTotalOrder._.total"
d589 v0
  = MAlonzo.RTE.mazCoerce
      (d473 (MAlonzo.RTE.mazCoerce (d575 (MAlonzo.RTE.mazCoerce v0))))
name669 = "Relation.Binary.StrictTotalOrder._.<-resp-\8776"
d669 v0
  = MAlonzo.RTE.mazCoerce
      (d630 (MAlonzo.RTE.mazCoerce (d665 (MAlonzo.RTE.mazCoerce v0))))
name413 = "Relation.Binary.DecStrictPartialOrder.Eq._.Carrier"
d413 v0
  = MAlonzo.RTE.mazCoerce
      (d105 (MAlonzo.RTE.mazCoerce (d409 (MAlonzo.RTE.mazCoerce v0))))
name157 = "Relation.Binary.Poset"
d157 a0 a1 a2 = ()
 
data T157 a0 a1 a2 a3 = C813 a0 a1 a2 a3
name45 = "Relation.Binary.Preorder._\8764_"
d45 (C729 v0 v1 v2 v3) = MAlonzo.RTE.mazCoerce v2
d45 v0 = MAlonzo.RTE.mazIncompleteMatch name45
name813 = "Relation.Binary.recCon-NOT-PRINTED"
name557 = "Relation.Binary.DecTotalOrder.DTO._\8804?_"
d557 v0
  = MAlonzo.RTE.mazCoerce
      (d516 (MAlonzo.RTE.mazCoerce (d554 (MAlonzo.RTE.mazCoerce v0))))
name125 = "Relation.Binary.DecSetoid._.sym"
d125 v0
  = MAlonzo.RTE.mazCoerce
      (d71 (MAlonzo.RTE.mazCoerce (d115 (MAlonzo.RTE.mazCoerce v0))))
name637 = "Relation.Binary.IsStrictTotalOrder.Eq.refl"
d637 v0 v1 v2 v3 v4 v5 v6
  = MAlonzo.RTE.mazCoerce
      (d93
         (MAlonzo.RTE.mazCoerce
            (d633 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5)
               (MAlonzo.RTE.mazCoerce v6))))
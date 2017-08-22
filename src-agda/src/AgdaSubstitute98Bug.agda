open import Agda.Primitive

infixr 5 _,_
record Pair
  {a} (A : Set a) {b} (B : Set b)
  : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B

data Constraint
  {a} {A : Set a} (x : A)
  : Set where
  instance _ : Constraint x

record Outer
  l {a} {A : Set a} (x : A)
  : Set (lsuc l) where
  constructor #
  field type : Set l

record Inner
  {l} {a} {A : Set a} (x : A) {{_ : Constraint x}} (outer : Outer l x)
  : Set l where
  field value : Outer.type outer

module Class
  {l} {a} {A : Set a} (x : A) (C : Set l)
  where
  class = Inner x (# C)
  method : {{_ : class}} → C
  method {{INSTANCE}} = Inner.value INSTANCE

module Beekeeper
  {i} {I : Set i}
  (A : I -> Set)
  (B : I -> Set)
  (x : I)
  = Class (x , A , B)
          (A x -> B x)

module Indexed
  {a b b?} {I : Set}
  {A : I -> Set a}
  (mkA : ∀ {x} -> A x)
  (B : I -> Set b)
  (toB : ∀ {x} -> A x -> B x)
  (B? : ∀ {x} -> B x -> Set b?)
  = Class ((λ {x} -> toB {x}) , (λ {x} -> B? {x}))
          (∀ {x} -> B? (toB (mkA {x})))

module Unindexed
  {a b}
  {A : Set a}
  (mkA : A)
  {B : Set b}
  (toB : A -> B)
  (B? : B -> Set)
  = Class (mkA , toB , B?)
          (B? (toB mkA))

module _
  {a b} {I : Set}
  {A : I -> Set a}
  {mkA : ∀ {x} -> A x}
  {B : I -> Set b}
  {toB : ∀ {x} -> A x -> B x}
  {B? : ∀ {x} -> B x -> Set}
  {{_ : Indexed.class mkA B toB B?}}
  where
  postulate
    instance iToUnindexed : ∀ {x} -> Unindexed.class (mkA {x}) toB B?

postulate
  I : Set

data A
  a (x : I)
  : Set a where
  mkA : A a x

record B
  b (x : I)
  : Set (lsuc b) where
  field ?? : Set b
open B public

postulate
  toB : ∀ {a b x} -> A a x -> B b x
  instance
    iIndexedAB : ∀ {a b} -> Indexed.class (mkA {a}) (B b) toB (B.??)
  b : Level
  x : I
  myB : B b x

error : myB .??
error = Beekeeper.method _ _ _ _ _
-- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:98

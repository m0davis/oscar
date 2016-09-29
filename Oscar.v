Require Import Containers.MapInterface.
Require Import Containers.OrderedType.

Inductive Free (f : Type -> Type) (a : Type) :=
| Pure : a -> Free f a
| Join : forall x, (x -> Free f a) -> f x -> Free f a.

Print FMap.

Print All.
Print empty.
Print dict.
Eval compute in empty bool.
Check empty bool.
Check FMap.empty

Eval compute in is_empty bool (empty bool).

Eval compute in mem 2 (add 2 false (empty bool)).

Theorem a : mem 2 (add 2 false (empty bool)) = true.

Definition Match' {K} {H: OrderedType K} {F: FMap K H}
           (binds : F} : F
           
           ( : F := add 

(**)

Class Opposite A :=
  {
    opp : A -> A
  }.

Print Opposite.

Instance on : Opposite nat :=
  {
    opp x := 99 - x
  }.

Instance ob : Opposite bool  :=
  {
    opp := negb
  }.

Eval unfold opp in opp 3.

Definition op {A} `{opa : Opposite A} (x : A) := opp x.

Print op.

Eval compute in op nat.
Eval compute in op 3.

Definition op' on (opa : Opposite on) (x : on) := opp x.


Print op'.

Eval compute in op' bool ob true.
Eval compute in op 3.

Class Opposite' A := opp' : A -> A.

Print Opposite.
Print Opposite'.


Definition f := fun x => x + 1.

Check f 1.

Check f.

Eval compute in f 1.

Section x.
  Variables x y : nat.
  Section x.
    Variable z : nat.
    Parameter w : nat.
    Let Z := z.
    Definition W := w.
    Definition X := x.
  End x.
End x.  

Print All.

Print X.
Print W.

Eval compute in X W.

Check w.

Check _=_.

Require Import Containers.MapInterface.
Require Import Containers.OrderedType.

Print FMap.

Eval compute in add 2 true (empty bool).

Check add 2 true (empty bool).

Section SSSS.
  Variable S : Type.

  Definition 
  
Check OrderedType bool.

Definition bar : FMap nat := add 2 true (empty bool).



Check  (empty bool).
 


Definition foo := add 2 true (empty bool).

Generalizable All Variables.

Definition eMap := empty.

Definition testMap `{OrderedType key} `{FMap key} {elt : Type} m := empty.

                                                       

Require Import Containers.MapList.
Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make Nat_as_OT.

Definition map_nat_nat: Type := M.t nat.

Definition find k (m: map_nat_nat) := M.find k m.

Definition update (p: nat * nat) (m: map_nat_nat) :=
  M.add (fst p) (snd p) m.

Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ).

Example ex1: find 3 [1 |-> 2, 3 |-> 4] = Some 4.
Proof. reflexivity. Qed.

Example ex2: find 5 [1 |-> 2, 3 |-> 4] = None.
Proof. reflexivity. Qed.

Eval compute in M.add 2 3 (M.empty nat).

Module M1 := FMapAVL.Make Nat_as_OT.

Eval compute in M.add 2 3 (M1.empty nat).




                *)

(*
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Structures.DecidableTypeEx.

Module M := FMapWeakList.Make(Nat_as_DT).

Eval compute in M.add 2 3 (M.empty nat).
*)


Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Peano_dec.

Set Implicit Arguments.

Inductive Compare2 (X : Type) (lt eq : X -> X -> Prop) (x y : X) : Type :=
  | LT : lt x y -> Compare2 lt eq x y
  | EQ : eq x y -> Compare2 lt eq x y
  | GT : lt y x -> Compare2 lt eq x y.

Module Nat_as_OT <: UsualOrderedType.

  Definition t := nat.

  Definition eq := @eq nat.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Definition compare x y : Compare2 lt eq x y.

  Definition eq_dec := eq_nat_dec.

End Nat_as_OT.


Module Nat_as_MDT <: MiniDecidableType.
  Definition t := nat.
  Definition eq_dec : forall x y : t, {x=y}+{~x=y}.
End Nat_as_MDT.

Module Nat_as_UDT := Equalities.Make_UDT(Nat_as_MDT).

Module WL := FMapWeakList.Make(Nat_as_UDT).
Module M := FMapWeakList.Make(Nat_as_DT).

Eval compute in M.add 2 3 (M.empty nat).

Eval compute in WL.add 2 3 (WL.empty nat).


Module Type TOP.
  Parameter t : Type.
  Parameter add : t -> t -> t.
End TOP.

Module Make (X: TOP).
  Definition t := X.t.
End Make.

Module T : TOP.
  Definition t := nat.
  Definition add a b := a + b.
End T.

Module B := Make T.

Eval compute in B.add 2 3.

Module Bottom1 <: TOP.
  Definition t := nat.
  Definition add a b := a + b.
  Definition x := add 1 2.
  Print x.
End Bottom1.

Definition y := Bottom1.x.

Print y.

Lemma yx : y = Bottom1.x.
  reflexivity.
Qed.

Lemma y3 : y = 3.
  auto.
Qed.

Lemma x4 : Bottom1.add 3 5 = 8.
  auto.
Qed.

Definition asdf := Bottom1.add.

Check asdf.

Eval compute in asdf 1 2.

Eval compute in Bottom1.add 3 4.

Definition asd3 := Bottom1.add 6 7.


Eval simpl (1 + 2).
Print Bottom1.

Print Bottom1.x.

.Check 1.
Check nat.
Check Set.
Print Set.
Print nat.
Let x := Bottom1.add 1 2.
Module Bottom2 <: TOP with Definition t := Set.
  Definition add a b := a + b.
End Bottom2.

Let x := Bottom.add 1 2.

End Bottom.

Print nat.

Print Bottom.

  Check add 1 2 empty.

Module ASDF.

  Import WL.

  Definition asdf := add 1 2 empty.

Definition asdf := WL.add 1 2 WL.empty.


Import DecidableType.
  Definition t := nat.
  Definition eq (x y : nat) := x = y.
End DT.
    with Definition t := nat .


Module DT : DecidableType with Definition eq (x y : t) := x = y.
    with  .
                                          
  Theorem eq_refl : forall x, eq x x.
    intros.
    unfold eq.
    reflexivity.
  Qed.
  Theorem eq_sym
  
End DT.
Print DT.

Module M := Make DT.


Module Z_as_OT <: OrderedType.
  Definition t := Z.
  Definition eq (x y:Z) := (x=y).
  Definition lt (x y:Z) := (x<y).
End Z_as_OT.


Module OT := OrderedType.

Module SN := S OT.

Print Raw.



Module RawN := Raw OrderedType where t := nat.

Check Raw(nat).equal.

Print Term Sord.Sig.

Check WSFun.empty.

Definition formula := Free list.



Inductive Map (A : Set) (B : Set) :=
| Empty : Map A B
| Insert : A -> B -> Map A B -> Map A B.



Definition Map (a : Set) (b : Set) : a -> b ≔ fun 

                                           
Definition Match' := 

Definition Match := Match' .

Definition Match pat exp = Match' := .


Definition Free_rect := 
  fun (f : Type -> Type) (a : Type) (P : Free f a -> Type)
      (f0 : forall a0 : a, P (Pure f a a0))
      (f1 : forall (x : Type) (f1 : x -> Free f a),
              (forall x0 : x, P (f1 x0)) -> forall f2 : f x, P (Join f a x f1 f2)) =>
    fix F (f2 : Free f a) : P f2 :=
  match f2 as f3 return (P f3) with
    | Pure y => f0 y
    | Join x f3 y => f1 x f3 (fun x0 : x => F (f3 x0)) y
  end
  : forall (f : Type -> Type) (a : Type) (P : Free f a -> Type),
      (forall a0 : a, P (Pure f a a0)) ->
      (forall (x : Type) (f1 : x -> Free f a),
         (forall x0 : x, P (f1 x0)) -> forall f2 : f x, P (Join f a x f1 f2)) ->
      forall f2 : Free f a, P f2
                         
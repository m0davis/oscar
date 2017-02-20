Inductive list (E : Type) : Type :=
| Nil : list E
| Cons : E -> list E -> list E.

Inductive nat : Type :=
| Base : nat
| Succ : nat -> nat.

Fixpoint member {E : Set} (e : E) (l : list E) : Prop :=
  match l with
    | Nil => False
    | Cons e' l' => IF (e = e') then True else member e l'
  end.

Theorem m0 : member Base (Cons nat Base (Nil nat)).
  unfold member.
  left.
  auto.
Qed.

Theorem m1 : member (Succ Base) (Cons nat (Succ Base) (Nil nat)).
  unfold member.
  left.
  auto.
Qed.

Theorem mall : forall (n : nat), member n (Cons nat n (Nil nat)).
  unfold member.
  left.
  auto.
Qed.

Theorem nEGeneral : forall (n : nat), n = n.
  auto.
Qed.

Theorem mallGeneral : forall (n : nat) (l : list nat), member n (Cons nat n l).
  intros.
  unfold member.
  left.
  auto.
Qed.
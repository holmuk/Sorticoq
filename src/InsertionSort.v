Require Import List Orders.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Sorticoq.SortedList.
Import ListNotations.

Module InsertionSort (Import O: UsualOrderedTypeFull').

Include (OrderedTypeFacts O).

Definition A := O.t.

Fixpoint Insert (l: list A) x : list A :=
  match l with
  | [] => [x]
  | h::t => match (O.compare x h) with
    | Lt => x::l
    | _ => h::(Insert t x)
    end
  end.

Definition InsertionSort (l: list A) :=
  @fold_right (list A) A (fun x y => Insert y x) [] l.

Hint Resolve perm_skip perm_swap.
Hint Constructors LocallySorted.
Hint Extern 1 (?x <= ?y) => apply le_lteq; OrderTac.order.

Ltac convert_compare :=
  repeat match goal with
  | H: compare ?x ?y = Lt |- _ => apply compare_lt_iff in H
  | H: compare ?x ?y = Gt |- _ => apply compare_gt_iff in H
  | H: compare ?x ?y = Eq |- _ => apply compare_eq in H
  end.

Lemma Permute: forall l x,
  Permutation (x::l) (Insert l x).
Proof.
  induction l; simpl; auto.
  intros. destruct (compare _ _);
  specialize IHl with x; transitivity (a::x::l); auto.
Qed.

Lemma InsertionSort_Permutation: forall l,
  Permutation l (InsertionSort l).
Proof.
  induction l; simpl; auto.
  transitivity (a::(InsertionSort l)); auto.
  apply Permute.
Qed.

Lemma Insert_LocallySorted: forall l a,
  LocallySorted le l -> LocallySorted le (Insert l a).
Proof.
  induction 1; [simpl | simpl | ]; auto.
  - destruct (compare a a0) eqn:E; convert_compare; subst; auto.
  - simpl in *. destruct (compare _ _) eqn:R1;
    destruct (compare a a0) eqn:R2; convert_compare; subst; auto.
Qed.

Lemma InsertionSort_LocallySorted: forall l,
  LocallySorted le (InsertionSort l).
Proof.
  induction l; simpl; auto.
  apply Insert_LocallySorted; auto.
Qed.

Corollary InsertionSort_Sorted: forall l,
  Sorted le (InsertionSort l).
Proof.
  intros; apply Sorted_LocallySorted_iff.
  apply InsertionSort_LocallySorted.
Qed.

Theorem InsertionSort_is_sorting_algo:
  is_sorting_algo le InsertionSort.
Proof.
  unfold is_sorting_algo; intros; split.
  - apply InsertionSort_Permutation.
  - apply InsertionSort_Sorted.
Qed.

End InsertionSort.

(**
   An example
*)

Require Import ZArith.

Module Import ZSort := InsertionSort Z.

Example SortingExample: [2%Z; 4%Z; 4%Z; 6%Z; 8%Z] =
  (InsertionSort [4%Z; 2%Z; 8%Z; 4%Z; 6%Z]).
Proof.
  compute. reflexivity.
Qed.

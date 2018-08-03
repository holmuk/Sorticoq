Require Import List Orders Nat.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Sorticoq.SortedList.
Import ListNotations.

Module SelectionSort (Import O: UsualOrderedTypeFull').

Include (OrderedTypeFacts O).

Definition A := O.t.

Fixpoint SelectMin (l: list A) (d: A) : A :=
  match l with
  | [] => d
  | h::t => let y := (SelectMin t h) in match (O.compare d y) with
    | Lt => d
    | _ => y
    end
  end.

Fixpoint delete (x: A) (l: list A) : list A :=
  match l with
  | [] => []
  | h::t => match (O.compare x h) with
    | Eq => t
    | _ => h::(delete x t)
    end
  end.

Fixpoint SelectionSortHelp (l: list A) (n: nat) : list A :=
  match l, n with
  | [], _ => []
  | _, 0 => l
  | h::t, S n' => let y := (SelectMin t h) in
    y::(SelectionSortHelp (delete y l) n')
  end.

Definition SelectionSort (l: list A) :=
  SelectionSortHelp l (length l).

Hint Constructors LocallySorted.
Hint Extern 1 (?x <= ?y) => apply le_lteq; OrderTac.order.

Ltac convert_compare :=
  repeat match goal with
  | H: compare ?x ?y = Lt |- _ => apply compare_lt_iff in H
  | H: compare ?x ?y = Gt |- _ => apply compare_gt_iff in H
  | H: compare ?x ?y = Eq |- _ => apply compare_eq in H
  end.

Lemma le_trans: @transitive O.t le.
Proof.
  unfold transitive.
  intros. apply le_lteq in H. apply le_lteq in H0.
  apply le_lteq. intuition; order.
Qed.

Lemma SelectMin_is_min: forall l a,
  forall x, In x (a::l) -> (SelectMin l a) <= x.
Proof.
  intro l; induction l; intros; simpl; auto.
  - inversion H; auto. inversion H0.
  - simpl in H. destruct H as [H | [H | H]];
    remember (compare _ _) as c; symmetry in Heqc; destruct c; convert_compare;
    subst; auto;
    try match goal with
    | |- SelectMin l ?x <= ?y => apply IHl
    | H: ?x < ?y |- ?x <= ?z => apply (le_trans x y z)
    end; simpl; auto; apply IHl; simpl; auto.
Qed.

Ltac do_compare :=
  let C := fresh in let eqnC := fresh in remember (compare _ _) as C eqn:eqnC;
  symmetry in eqnC; destruct C; convert_compare.

Lemma SelectMin_In: forall l a,
  In (SelectMin l a) (a::l).
Proof.
  intro l; induction l; simpl; auto.
  intros; do_compare; auto.
  simpl in IHl. auto.
Qed.

Lemma SelectMin_In2: forall l a,
  (SelectMin l a) <> a ->
  In (SelectMin l a) l.
Proof.
  intros. assert (In (SelectMin l a) (a::l)) by apply SelectMin_In.
  destruct H0. rewrite <- H0 in H. contradiction. exact H0.
Qed.

Lemma delete_length: forall l a,
  In a l ->
  S (length (delete a l)) = length l.
Proof.
  intro l; induction l; simpl; intros; auto.
  - contradiction.
  - do_compare; auto; intuition; try order.
  all: simpl; apply eq_S; apply IHl; assumption.
Qed.

Lemma delete_Permutation: forall l a,
  In a l ->
  Permutation l (a::delete a l).
Proof.
  induction l; intros; simpl in *.
  - contradiction.
  - do_compare; intuition; subst; try order; auto.
    all: transitivity (a::a0::delete a0 l); auto; apply perm_swap.
Qed.

Opaque delete.

Lemma SelectionSort_Permutation_t: forall l n,
  length l = n -> Permutation l (SelectionSort l).
Proof.
  intros; generalize dependent l.
  induction n; unfold SelectionSort; intros; auto.
  - apply length_zero_iff_nil in H. subst. auto.
  - destruct l eqn: E; simpl; auto.
    assert (length (delete (SelectMin l0 a) (a::l0)) = length l0).
      assert (Hy: In (SelectMin l0 a) (a::l0)) by apply SelectMin_In; simpl in Hy.
      Transparent delete. simpl. do_compare; intuition; try order;
      simpl; apply delete_length; assumption.
    rewrite <- H0.
    change (SelectionSortHelp ?l (length ?l)) with (SelectionSort l).
    transitivity (SelectMin l0 a :: (delete (SelectMin l0 a) (a::l0))).
    apply delete_Permutation. apply SelectMin_In.
    constructor. apply IHn. rewrite H0. simpl in H. auto.
Qed.

Lemma SelectionSort_Permutation: forall l,
  Permutation l (SelectionSort l).
Proof.
  intros. apply (SelectionSort_Permutation_t l (length l)). reflexivity.
Qed.

Hint Extern 2 (Permutation (SelectionSort ?l) ?l) =>
  apply Permutation_sym; apply SelectionSort_Permutation.

Lemma delete_length2: forall l a,
  SelectMin l a <> a ->
  length (a :: delete (SelectMin l a) l) = length l.
Proof.
  intros. simpl; apply delete_length.
  apply SelectMin_In2; assumption.
Qed.

Lemma In_delete: forall l a x,
  In x (delete a l) -> In x l.
Proof.
  induction l; simpl; auto; intros; do_compare; auto.
  all: simpl in H; intuition; apply IHl in H0; auto.
Qed.

Lemma SelectionSort_LocallySorted_t: forall l n,
  length l = n -> LocallySorted le (SelectionSort l).
Proof.
  intros; generalize dependent l.
  induction n; unfold SelectionSort; intros; simpl; auto.
  + apply length_zero_iff_nil in H. subst; simpl; auto.
  + destruct l. inversion H. simpl.
  do_compare;
  try assert (length (a::(delete (SelectMin l a) l)) = length l) by
      (apply delete_length2; order);
  repeat (match goal with
  | |- context[SelectionSortHelp ?x (length ?x)] =>
    change (SelectionSortHelp ?l (length ?l)) with (SelectionSort l)
  | H: context[SelectionSortHelp ?x (length ?x)] |- _ =>
    change (SelectionSortHelp ?l (length ?l)) with (SelectionSort l) in H
  | |- LocallySorted le (SelectMin ?l ?x :: _) =>
    apply LocallySorted_hd_relation; intros
  | |- SelectMin ?l ?a <= ?x =>
    apply SelectMin_is_min
  | H: length ?x = length ?l |- context[length l] =>
    rewrite <- H
  | H: length ?x = length ?l |- _ =>
    try match goal with
    | H2: In ?t (SelectionSortHelp x (length l)) |- _ =>
      rewrite <- H in H2
    end
  end; auto).
  - apply Permutation_in with (l' := l) in H0; simpl; auto.
  - apply Permutation_in with (l' := (a::delete (SelectMin l a) l)) in H2; simpl; auto.
    simpl in H2; intuition. apply In_delete in H3. auto.
  - apply IHn. rewrite H0. auto.
  - apply Permutation_in with (l' := (a::delete (SelectMin l a) l)) in H2; simpl; auto.
    simpl in H2; intuition. apply In_delete in H3. auto.
  - apply IHn. rewrite H0. auto.
Qed.

Lemma SelectionSort_LocallySorted: forall l,
  LocallySorted le (SelectionSort l).
Proof.
  intros. apply SelectionSort_LocallySorted_t with (n:=length l). reflexivity.
Qed.

Lemma SelectionSort_is_sorting_algo:
  is_sorting_algo le SelectionSort.
Proof.
  unfold is_sorting_algo; intros; split.
  - apply SelectionSort_Permutation.
  - apply Sorted_LocallySorted_iff. apply SelectionSort_LocallySorted.
Qed.

End SelectionSort.

(**
   An example
*)

Require Import ZArith.

Module Import ZSort := SelectionSort Z.

Example SortingExample: [2%Z; 4%Z; 4%Z; 6%Z; 8%Z] =
  (SelectionSort [4%Z; 2%Z; 8%Z; 4%Z; 6%Z]).
Proof.
  compute. reflexivity.
Qed.
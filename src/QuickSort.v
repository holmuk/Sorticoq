Require Import List Orders Nat.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Sorticoq.SortedList.
Import ListNotations.

Module QuickSort (Import O: UsualOrderedTypeFull').

Include (OrderedTypeFacts O).

Definition A := O.t.

Definition LtEqList (l: list A) (a: A) : list A :=
  @fold_right (list A) A (fun x l' => match O.compare x a with
  | Gt => l'
  | _ => x::l'
  end) [] l.

Definition GtList (l: list A) (a: A) : list A :=
  @fold_right (list A) A (fun x l' => match O.compare x a with
  | Gt => x::l'
  | _ => l'
  end) [] l.

Fixpoint QuickSortHelp (l: list A) (help: nat) : list A :=
  match l, help with
  | [], _ => []
  | _, 0 => l
  | p::t, S n => (QuickSortHelp (LtEqList t p) n) ++ [p] ++
    (QuickSortHelp (GtList t p) n)
  end.

Definition QuickSort (l: list A) : list A :=
  QuickSortHelp l (length l).

Hint Extern 1 (?x <= ?y) => apply le_lteq; OrderTac.order.

Ltac convert_compare :=
  repeat match goal with
  | H: compare ?x ?y = Lt |- _ => apply compare_lt_iff in H
  | H: compare ?x ?y = Gt |- _ => apply compare_gt_iff in H
  | H: compare ?x ?y = Eq |- _ => apply compare_eq in H
  end.

Ltac do_compare :=
  let C := fresh in let eqnC := fresh in remember (compare _ _) as C eqn:eqnC;
  symmetry in eqnC; destruct C; convert_compare.

Lemma LtEqList_works: forall l a,
  forall x, In x (LtEqList l a) -> x <= a.
Proof.
  induction l; intros; simpl in H.
  - contradiction.
  - do_compare; simpl in H; intuition.
Qed.

Lemma GtList_works: forall l a,
  forall x, In x (GtList l a) -> a < x.
Proof.
  induction l; intros; simpl in H.
  - contradiction.
  - do_compare; simpl in H; intuition.
    order.
Qed.

Lemma LtEqList_length: forall l a,
  (length (LtEqList l a) <= length l)%nat.
Proof.
  induction l; intros; simpl; auto.
  do_compare; simpl; intuition.
Qed.

Lemma GtList_length: forall l a,
  (length (GtList l a) <= length l)%nat.
Proof.
  induction l; intros; simpl; auto.
  do_compare; simpl; intuition.
Qed.

Lemma LtEqGt_Permutation: forall l a,
  Permutation l (LtEqList l a ++ GtList l a).
Proof.
  induction l; simpl; intros; auto.
  do_compare; simpl; try constructor; auto.
  apply Permutation_cons_app; auto.
Qed.

Lemma QuickSortHelp_Permutation: forall l n,
  (length l <= n)%nat -> Permutation l (QuickSortHelp l n).
Proof.
  intros; generalize dependent l; induction n.
  all: intros; simpl; destruct l; auto.
  simpl in H.
  assert (Permutation (LtEqList l a) (QuickSortHelp (LtEqList l a) n)).
    apply IHn. transitivity (length l). apply LtEqList_length. intuition.
  assert (Permutation (GtList l a) (QuickSortHelp (GtList l a) n)).
    apply IHn. transitivity (length l). apply GtList_length. intuition.
  transitivity ((LtEqList l a) ++ a::(GtList l a)).
  - apply Permutation_cons_app.
    apply LtEqGt_Permutation.
  - apply Permutation_add_inside; auto.
Qed.

Lemma QuickSort_Permutation: forall l,
  Permutation l (QuickSort l).
Proof.
  unfold QuickSort. intros.
  apply QuickSortHelp_Permutation with (n:=length l); auto.
Qed.

Lemma in_qert_last: forall {A:Type} l a,
  @In A (@last A (a::l) a) (a::a::l).
Proof.
  intros. induction l; intuition.
  destruct l; simpl in *; intuition.
Qed.

Ltac proof_QSH_LtEqGt_LS :=
  match goal with
  | H: forall l : _, _ |- _ => apply H; transitivity (length l);
  [try apply LtEqList_length; try apply GtList_length | intuition]
  end.

Ltac proof_QSH_Perm l :=
  apply QuickSortHelp_Permutation; transitivity (length l);
  [try apply LtEqList_length; try apply GtList_length | intuition].

Lemma QuickSortHelp_is_LocallySorted: forall l n,
  (length l <= n)%nat -> LocallySorted le (QuickSortHelp l n).
Proof.
  intros; generalize dependent l.
  induction n; intros; simpl.
  - destruct l; simpl in H; intuition.
    inversion H.
  - destruct l; auto. simpl in H.
    assert (LocallySorted le (QuickSortHelp (LtEqList l a) n)).
      proof_QSH_LtEqGt_LS.
    assert (LocallySorted le (QuickSortHelp (GtList l a) n)).
      proof_QSH_LtEqGt_LS.
    assert (PermGt: Permutation (GtList l a) (QuickSortHelp (GtList l a) n)).
      proof_QSH_Perm l.
    assert (PermLtEq: Permutation (LtEqList l a) (QuickSortHelp (LtEqList l a) n)).
      proof_QSH_Perm l.
    destruct (QuickSortHelp (GtList l a) n) eqn:QSgt;
    destruct (QuickSortHelp (LtEqList l a) n) eqn:QSle.
    + simpl; auto.
    + assert (a0::l0 = removelast (a0::l0) ++ [last (a0::l0) a0]).
        apply app_removelast_last. intuition. inversion H2.
      rewrite H2. rewrite <- app_assoc. apply LocallySorted_end.
      * remember (removelast _ ++ [last _ _]).
        rewrite <- H2. rewrite <- QSle.
        proof_QSH_LtEqGt_LS.
      * apply Permutation_sym in PermLtEq.
        assert (In (last (a0::l0) a0) (a0::a0::l0)) by apply in_qert_last.
        destruct H3. rewrite <- H3.
        apply Permutation_in with (x:=a0) in PermLtEq.
        apply LtEqList_works in PermLtEq; intuition. intuition.
        apply Permutation_in with (x:=(last (a0::l0) a0)) in PermLtEq.
        apply LtEqList_works in PermLtEq; auto. auto.
    + apply LocallySorted_sum; auto.
      apply Permutation_sym in PermGt.
      apply Permutation_in with (x:=a0) in PermGt.
      * simpl; auto.
      * intuition.
      * apply Permutation_sym in PermGt.
        apply Permutation_in with (x:=a0) in PermGt.
        apply GtList_works in PermGt. intuition. intuition.
    + apply LocallySorted_sum; auto.
      * assert (a1::l1 = removelast (a1::l1) ++ [last (a1::l1) a1]).
          apply app_removelast_last. intuition. inversion H2.
        rewrite H2. rewrite <- app_assoc. apply LocallySorted_end.
        remember (removelast _ ++ [last _ _]).
        rewrite <- H2. rewrite <- QSle. proof_QSH_LtEqGt_LS.
        apply Permutation_sym in PermLtEq.
        assert (In (last (a1::l1) a1) (a1::a1::l1)) by apply in_qert_last.
        destruct H3. rewrite <- H3.
        apply Permutation_in with (x:=a1) in PermLtEq.
        apply LtEqList_works in PermLtEq. auto. intuition.
        apply Permutation_in with (x:=(last (a1::l1) a1)) in PermLtEq.
        apply LtEqList_works in PermLtEq. auto. auto.
      * assert (Permutation (GtList l a) (QuickSortHelp (GtList l a) n)).
          proof_QSH_Perm l.
        apply Permutation_sym in H2.
        apply Permutation_in with (x:=a0) in H2.
        apply GtList_works in H2. intuition.
        rewrite QSgt. intuition.
Qed.

Lemma QuickSort_LocallySorted: forall l,
  LocallySorted le (QuickSort l).
Proof.
  intros. unfold QuickSort. apply QuickSortHelp_is_LocallySorted with (n:=length l).
  auto.
Qed.

Theorem QuickSort_is_sorting_algo:
  is_sorting_algo le QuickSort.
Proof.
  unfold is_sorting_algo; intros; split.
  - apply QuickSort_Permutation.
  - apply Sorted_LocallySorted_iff. apply QuickSort_LocallySorted.
Qed.

End QuickSort.

Require Import ZArith.

Module Import ZSort := QuickSort Z.

Eval compute in QuickSort [4%Z; 2%Z; 8%Z; 4%Z; 6%Z].

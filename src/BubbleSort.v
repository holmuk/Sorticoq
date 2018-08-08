Require Import List Orders.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Structures.GenericMinMax.
Require Import Sorticoq.SortedList.
Import ListNotations.

Module BubbleSort (Import O: UsualOrderedTypeFull').

Include (OrderedTypeFacts O).

Module MinMax := GenericMinMax O.
Import MinMax.

Module Props := (UsualMinMaxProperties O MinMax).
Import Props.

Definition A := O.t.

Definition max_of_list_t (l: list A) x : A :=
  @fold_right A A max x l.

Lemma max_of_list_t_ge_def: forall l x,
  x <= max_of_list_t l x.
Proof.
  intros; induction l; simpl in *; intros.
  - apply le_lteq. order.
  - rewrite max_le_iff; intuition.
Qed.

Hint Resolve perm_skip perm_swap.
Hint Constructors LocallySorted.
Hint Extern 1 (?x <= ?y) => apply le_lteq; OrderTac.order.

Lemma max_of_list_t_ok: forall l x,
  forall x', In x' l -> x' <= max_of_list_t l x.
Proof.
  intros. induction l.
  - inversion H.
  - simpl. rewrite max_le_iff.
    destruct H; subst; auto.
Qed.

Fixpoint bubble_step (l: list A) x : list A :=
  match l with
  | nil => [x]
  | h::t => match O.compare x h with
    | Gt => h::(bubble_step t x)
    | _ => x::(bubble_step t h)
    end
  end.

Lemma bubble_step_not_nil: forall l x,
  bubble_step l x <> [].
Proof.
  intros l x H.
  destruct l; simpl in *. inversion H.
  destruct (compare x a); inversion H.
Qed.

Lemma last_l: forall (l: list A) x a,
  l <> [] -> last (a::l) x = last l x.
Proof.
  induction l; intuition.
Qed.

Lemma max_niv: forall l x,
  max x (max_of_list_t l x) = max_of_list_t l x.
Proof.
  intros. induction l; simpl.
  - apply max_id.
  - rewrite max_assoc; rewrite (max_comm x a).
    rewrite <- max_assoc; change (gmax compare) with max.
    rewrite IHl. reflexivity.
Qed.

Lemma max_rev: forall l x a,
  max x (max_of_list_t l a) = max a (max_of_list_t l x).
Proof.
  intros. induction l; simpl.
  - apply max_comm.
  - do 2 rewrite max_assoc. rewrite (max_comm x a0).
    rewrite (max_comm a a0). do 2 rewrite <- max_assoc.
    change (gmax compare) with max.
    rewrite IHl. reflexivity.
Qed.

Lemma max_lt: forall l x a,
  a < x ->
  max x (max_of_list_t l a) = max_of_list_t l x.
Proof.
  intros. induction l; simpl.
  - apply max_l. apply le_lteq. auto.
  - rewrite max_assoc. rewrite (max_comm x a0).
    rewrite <- max_assoc. change (gmax compare) with max.
    rewrite IHl. reflexivity.
Qed.

Ltac convert_compare :=
  repeat match goal with
  | H: compare ?x ?y = Lt |- _ => apply compare_lt_iff in H
  | H: compare ?x ?y = Gt |- _ => apply compare_gt_iff in H
  | H: compare ?x ?y = Eq |- _ => apply compare_eq in H
  end.

Ltac do_compare :=
  let C := fresh in let eqnC := fresh in remember (compare _ _) as C eqn:eqnC;
  symmetry in eqnC; destruct C; convert_compare.

Lemma bubble_step_bubbles: forall l x x',
  last (bubble_step l x) x' = max_of_list_t l x.
Proof.
  induction l; intuition.
  simpl (max_of_list_t _ _).
  assert (forall x, bubble_step l x <> []) by apply bubble_step_not_nil.
  simpl; do_compare.
  all: match goal with
  | |- last (?a :: bubble_step _ ?x) _ = _ =>
    specialize H with x; apply (last_l _ x' a) in H; rewrite H; rewrite IHl;
    symmetry; subst
  end.
  - apply max_niv.
  - apply max_lt; auto.
  - rewrite max_rev; apply max_lt; auto.
Qed.

Lemma bubble_step_length: forall l a,
  length (bubble_step l a) = length (a::l).
Proof.
  induction l; intros. intuition.
  simpl; do_compare; simpl; rewrite IHl; auto.
Qed.

Lemma bubble_step_permute: forall l a,
  Permutation (a::l) (bubble_step l a).
Proof.
  induction l; intros; auto.
  simpl. do_compare; auto.
  transitivity (a::a0::l); auto.
Qed.

Require Import Omega.

Fixpoint bubble_sort_m (l: list A) (m: nat) : list A :=
  match l, m with
  | nil, _ => nil
  | _, 0 => nil
  | h::t, S m' => let l' := (bubble_step t h) in
    (bubble_sort_m (removelast l') m') ++ [last l' h]
  end.

Definition bubble_sort (l: list A) :=
  bubble_sort_m l (length l).

Ltac stupid_list :=
  intro Y; inversion Y.

Lemma removelast_end: forall (l: list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros. rewrite removelast_app. ssimpl_list. reflexivity.
  stupid_list.
Qed.

Lemma permute_omg: forall (l: list A) a,
  Permutation (l) (removelast (l ++ [a])).
Proof.
  intros; rewrite removelast_end; auto.
Qed.

Lemma removelast_len: forall l a,
  length (removelast (bubble_step l a)) = length l.
Proof.
  intros.
  assert (bubble_step l a <> []) by apply bubble_step_not_nil.
  apply exists_last in H. inversion H; inversion X. rewrite H0.
  rewrite removelast_end. apply f_equal with (f:=@length A) in H0.
  rewrite bubble_step_length in H0. rewrite app_length in H0; simpl in H0.
  intuition.
Qed.

Lemma permute: forall n l,
  length l = n -> Permutation l (bubble_sort l).
Proof.
  induction n; intros.
  - apply length_zero_iff_nil in H; subst; auto.
  - destruct l; simpl; auto.
    unfold bubble_sort in *. simpl.
    specialize IHn with (removelast (bubble_step l a)).
    rewrite removelast_len in IHn. simpl in H. apply eq_add_S in H.
    apply IHn in H.
    transitivity (removelast (bubble_step l a) ++ [last (bubble_step l a) a]).
    + assert (bubble_step l a <> []) by apply bubble_step_not_nil.
      apply app_removelast_last with (d:=a) in H0. rewrite <- H0.
      apply bubble_step_permute.
    + apply Permutation_app_tail. assumption.
Qed.

Corollary bubble_sort_permute: forall l,
  Permutation l (bubble_sort l).
Proof.
  intros; apply (permute (length l) _); reflexivity.
Qed.

Lemma bubble_sort_not_nil: forall l,
  l <> [] -> bubble_sort l <> [].
Proof.
  intros. destruct l; try contradiction.
  unfold bubble_sort; simpl. intro Y.
  apply app_eq_nil in Y. destruct Y. inversion H1.
Qed.

Include (OTF_to_TTLB O).
Lemma le_trans:
  Transitive le.
Proof.
  unfold Transitive. intros. rewrite <- leb_le in *.
  unfold is_true in *. unfold leb in *; repeat do_compare; subst; auto; order.
Qed.

Hint Resolve le_trans.

Lemma In_removelast: forall {A:Type} l x,
  @In A x (removelast l) -> In x l.
Proof.
  intros. destruct l; auto.
  assert (a::l <> []) by stupid_list.
  apply app_removelast_last with (d:=a) in H0. rewrite H0.
  apply in_or_app; auto.
Qed.

Lemma BubbleSortHelp_is_LocallySorted: forall l n,
  length l = n ->
    LocallySorted le (bubble_sort_m l n).
Proof.
  intros; generalize dependent l;
  induction n; intros.
  - apply length_zero_iff_nil in H. subst; simpl. auto.
  - destruct l; simpl in *. inversion H.
    assert (length (removelast (bubble_step l a)) = n).
      transitivity (length l).
      apply removelast_len. auto.
    apply LocallySorted_end_relation; auto.
    intros. rewrite <- H0 in H1.
    change (bubble_sort_m ?x (length ?x)) with (bubble_sort x) in H1.
    rewrite bubble_step_bubbles.
    assert (Permutation (bubble_sort (removelast (bubble_step l a))) (removelast (bubble_step l a))).
      apply Permutation_sym; apply bubble_sort_permute.
    apply Permutation_in with (x:=t0)in H2; auto.
    apply In_removelast in H2.
    assert (Permutation (bubble_step l a) (a::l)).
      apply Permutation_sym; apply bubble_step_permute.
    apply Permutation_in with (x:=t0) in H3; auto.
    destruct H3; subst.
    apply max_of_list_t_ge_def.
    apply max_of_list_t_ok; auto.
Qed.

Lemma BubbleSort_LocallySorted: forall l,
  LocallySorted le (bubble_sort l).
Proof.
  intros. apply BubbleSortHelp_is_LocallySorted. auto.
Qed.

End BubbleSort.

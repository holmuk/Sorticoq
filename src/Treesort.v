Require Import Nat List Bool PeanoNat Orders.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Sorticoq.SortedList.
Require Import Sorticoq.BinaryTree.
Import ListNotations.

Module TreeSort (Import O: UsualOrderedTypeFull').
(*
Module Bdefs := UsualOrderedTypeFull'_to_BinaryTree O.
Import Bdefs.
*)
Include (BinaryTree_over_OrderedType O).

Fixpoint makeBST (l: list A) : BinaryTree :=
  match l with
  | nil => BT_nil
  | h::t => BST_Insert (makeBST t) h
  end.

Lemma makeBST_ok: forall x (l: list A),
  In_tree x (makeBST l) <-> In x l.
Proof.
  split; intros; induction l; simpl in *;
    [inversion H |  idtac | inversion H | idtac ].
  - apply In_tree_insert in H; intuition.
  - apply In_insert_cond; intuition.
Qed.

Definition Treesort (l: list A) : list A :=
  BT_get_list (makeBST l).

Lemma Treesort_is_LocallySorted: forall l,
  LocallySorted lte (Treesort l).
Proof.
  intros. apply BST_is_LocallySorted.
  induction l; simpl; auto.
  apply Insert_not_change_BSTSP. assumption.
Qed.

Lemma Treesort_Permutation: forall l,
  Permutation l (Treesort l).
Proof.
  induction l; simpl; auto.
  unfold Treesort in *. simpl.
  remember (BST_Insert _ a) as Tr. symmetry in HeqTr.
  apply BST_Insert_emplace in HeqTr. destruct HeqTr as [e1 [e2 [H' H'']]].
  rewrite <- H'. rewrite <- H'' in IHl.
  simpl. apply Permutation_cons_app. auto.
Qed.

Theorem Treesort_is_sorting_algo:
  is_sorting_algo lte Treesort.
Proof.
  unfold is_sorting_algo. split.
  - apply Treesort_Permutation.
  - apply Sorted_LocallySorted_iff. apply Treesort_is_LocallySorted.
Qed.

End TreeSort.

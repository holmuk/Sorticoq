Require Import Nat List Bool PeanoNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sorting.Sorted.
Require Import Sorticoq.SortedList.
Require Import Sorticoq.BinaryTree.
Import ListNotations.

Parameter A:Type.
Parameter lte: relation A.
Parameter lte_bool: A -> A -> bool.

Parameter lte_trans: transitive _ lte.
Parameter lte_total: total _ lte.

Parameter lte_to_bool: forall x y,
  lte x y <-> lte_bool x y = true.

Parameter lte_to_eq: forall x y,
  (lte x y) /\ (lte y x) -> x = y.

Module BTForSortDef <: BinaryTree.BinaryTreeParameters.
Definition Node_type := A.
Definition lte := lte.
Definition lte_bool := lte_bool.
Definition lte_to_bool := lte_to_bool.
Definition lte_total := lte_total.
Definition lte_trans := lte_trans.
Definition lte_to_eq := lte_to_eq.
End BTForSortDef.

Module BTForSort := BinaryTreeDef BTForSortDef.
Import BTForSort.

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

Lemma Treesort_not_change_In: forall x l,
  In x l <-> In x (Treesort l).
Proof.
  split; intros; unfold Treesort in *.
  - apply In_tree_In_equivalence.
    apply makeBST_ok. assumption.
  - apply In_tree_In_equivalence in H.
    apply makeBST_ok. assumption.
Qed.

Definition is_sorting_algo {A: Type} (R: relation A) (f: list A -> list A) :=
  forall l, Sorted R (f l) /\
    forall x, In x l <-> In x (f l).

Theorem Treesort_is_sorting_algo:
  is_sorting_algo lte Treesort.
Proof.
  unfold is_sorting_algo. split.
  - apply Sorted_LocallySorted_iff. apply Treesort_is_LocallySorted.
  - intros x. revert l. revert x. apply Treesort_not_change_In.
Qed.

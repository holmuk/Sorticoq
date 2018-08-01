Require Import Nat List Bool Setoid.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Sorting.Sorted.
Require Import Sorticoq.SortedList.
Import ListNotations.

(**
  Strictly speaking, the relation should be a total preorder relation.
  It's possible to derive [[comparison]] from total preorder laws.
*)

Definition total (A: Type) (R: relation A) :=
  forall (x y:A), R x y \/ R y x.

Module Type BinaryTreeParameters.
Parameter Node_type:Type.

Parameter lte: relation Node_type.
Parameter lte_bool: Node_type -> Node_type -> bool.

Parameter lte_trans: transitive _ lte.
Parameter lte_total: total _ lte.

Parameter lte_to_bool: forall x y,
  lte x y <-> lte_bool x y = true.

Parameter lte_to_eq: forall x y,
  (lte x y) /\ (lte y x) -> x = y.

End BinaryTreeParameters.

(**
  Our general Binary Tree definition
*)

Module BinaryTreeDef (BTP: BinaryTreeParameters).
Import BTP.

Lemma lte_refl: reflexive _ lte.
Proof.
  red; intros.
  assert (forall x y, lte x y \/ lte y x) by apply lte_total.
  specialize H with x x. intuition.
Qed.

Add Relation Node_type lte
  reflexivity proved by lte_refl
  transitivity proved by lte_trans
as lte_rel.

Definition lt (x y: Node_type) := ~ lte y x.
Definition eq (x y: Node_type) := (lte x y) /\ (lte y x).

Definition compare (x y: Node_type) :=
  match lte_bool x y with
  | true =>
    match lte_bool y x with
    | true => Eq
    | false => Gt
    end
  | false => Lt
  end.

Lemma lte_change: forall (x y: Node_type),
  ~ lte x y -> lte y x.
Proof.
  intros.
  assert (forall x y, lte x y \/ lte y x) by apply lte_total.
  specialize H0 with x y. intuition.
Qed.

Inductive BinaryTree : Type :=
  | BT_nil: BinaryTree
  | BT_tr:  Node_type -> BinaryTree -> BinaryTree -> BinaryTree.

Inductive BinaryTree_eq : BinaryTree -> BinaryTree -> Prop :=
  | BTE_nil1:
    BinaryTree_eq BT_nil BT_nil
  | BTE_nil2: forall t1 t1' t2 t2' x y,
    BinaryTree_eq t1 t1' ->
    BinaryTree_eq t2 t2' ->
    x = y ->
    BinaryTree_eq (BT_tr x t1 t2) (BT_tr y t1' t2').

Hint Constructors BinaryTree_eq.

Lemma BT_eq_eq_equivalence: forall (A B: BinaryTree),
  A = B <-> BinaryTree_eq A B.
Proof.
  split.
  - intros; subst; induction B; auto.
  - induction 1; subst; auto.
Qed.

(**
  Tree in-order traverse
*)

Fixpoint In_order_traverse (BT: BinaryTree) (f: Node_type -> Node_type) : list Node_type :=
  match BT with
  | BT_nil => nil
  | BT_tr x t1 t2 =>
    (In_order_traverse t1 f) ++ [f x] ++ (In_order_traverse t2 f)
  end.

Definition BT_get_list (BT: BinaryTree) := In_order_traverse BT (fun x:Node_type => x).

Lemma In_order_traverse_of_tree: forall rval t1 t2 f,
  In_order_traverse (BT_tr rval t1 t2) f =
  In_order_traverse t1 f ++ [f rval] ++ In_order_traverse t2 f.
Proof.
  reflexivity.
Qed.

(**
  In for tree
*)

Inductive In_tree: Node_type -> BinaryTree -> Prop :=
  | In_tree_e: forall x t1 t2,
    In_tree x (BT_tr x t1 t2)
  | In_tree_r: forall x y t1 t2,
    In_tree x t2 ->
    In_tree x (BT_tr y t1 t2)
  | In_tree_l: forall x y t1 t2,
    In_tree x t1 ->
    In_tree x (BT_tr y t1 t2).

Hint Constructors In_tree.

Hint Unfold BT_get_list : BT_Hintbase.
Hint Rewrite In_order_traverse_of_tree : BT_Hintbase.

Ltac clone H :=
  let eq := fresh in let Heq := fresh in
  remember H as eq eqn:Heq; clear Heq.

Ltac clone_as H Eq :=
  let Heq := fresh in
  remember H as Eq eqn:Heq; clear Heq.

Tactic Notation "clone" hyp(H) :=
  clone H.

Tactic Notation "clone" hyp(H) "as" ident(Eq) :=
  clone_as H Eq.

Ltac gen_clear H :=
  generalize H; clear H.

Ltac In_help :=
  autounfold with BT_Hintbase in *;
  autorewrite with BT_Hintbase in *;
  simpl in *;
  repeat (match goal with
  | H: In ?x (_ ++ _) |- _ => apply in_app_or in H; destruct H
  | H: In ?x (_::_) |- _ => simpl in H; destruct H
  end; subst).

Hint Extern 3 (In ?x (_ ++ _)) => apply in_or_app; intuition.

Ltac tree_induction :=
  intros;
  match goal with
  | BT: BinaryTree |- _ =>
    match goal with
    | H: ?P BT |- _ => induction H
    | H: ?P ?x BT |- _ => induction H
    end || induction BT
  end; subst; simpl in *.

Lemma In_tree_In_equivalence: forall x BT,
  In_tree x BT <-> In x (BT_get_list BT).
Proof.
  split; intros; tree_induction; In_help; intuition.
Qed.

(** ** Binary Search Tree
  We introduce two types of BSTs: the Weak BST and the Strong BST, which is the normal BST
*)

Inductive BST_WeakProperty: BinaryTree -> Prop :=
  | BSTWP_nil:
    BST_WeakProperty BT_nil
  | BSTWP_tr: forall x1 t1 t1' x2 t2 t2' rval,
    BST_WeakProperty (BT_tr x1 t1 t1') ->
    BST_WeakProperty (BT_tr x2 t2 t2') ->
    lte x1 rval -> lte rval x2 ->
    BST_WeakProperty (BT_tr rval (BT_tr x1 t1 t1') (BT_tr x2 t2 t2'))
  | BSTWP_rnil: forall x1 t1 t1' rval,
    BST_WeakProperty (BT_tr x1 t1 t1') ->
    lte x1 rval ->
    BST_WeakProperty (BT_tr rval (BT_tr x1 t1 t1') BT_nil)
  | BSTWP_lnil: forall x2 t2 t2' rval,
    BST_WeakProperty (BT_tr x2 t2 t2') ->
    lte rval x2 ->
    BST_WeakProperty (BT_tr rval BT_nil (BT_tr x2 t2 t2'))
  | BSTWP_dnil: forall rval,
    BST_WeakProperty (BT_tr rval BT_nil BT_nil).

Inductive BST_StrongProperty: BinaryTree -> Prop :=
  | BSTSP_nil:
    BST_StrongProperty BT_nil
  | BSTSP_tr: forall rval t1 t2,
    BST_StrongProperty t1 -> (forall x, In_tree x t1 -> lte x rval) ->
    BST_StrongProperty t2 -> (forall x, In_tree x t2 -> lte rval x) ->
    BST_StrongProperty (BT_tr rval t1 t2).

Hint Constructors BST_WeakProperty BST_StrongProperty.

(**
  Now we can introduce some useful tactics
*)

Ltac solve_if :=
  let Eq := fresh in
  match goal with
  | |- context[if ?B then _ else _] =>
    match goal with
    | Eq: B = ?b |- _ => match type of b with | bool => rewrite Eq end
    end || destruct B eqn:Eq
  | H: context[if ?B then _ else _] |- _ =>
    match goal with
    | Eq: B = ?b |- _ => match type of b with | bool => rewrite Eq end
    end || destruct B eqn:Eq
  end.

(**
  Tactics to solve lte
  *)

Ltac find_lte_true x y :=
  let P := BST_WeakProperty in
  match goal with
  | H: P (BT_tr y (BT_tr x _ _) _ ) |- _ =>
    inversion H; clear H
  | H: P (BT_tr x _ (BT_tr y _ _) ) |- _ =>
    inversion H; clear H
  | H: lte x y |- _ => idtac
  end; subst; auto.

Ltac lte_bool_change :=
  repeat match goal with
  | H: lte_bool _ _ = true |- _ =>
    apply lte_to_bool in H
  | H: lte_bool _ _ = false |- _ =>
    apply not_true_iff_false in H; rewrite <- lte_to_bool in H
  end.

Ltac change_False_rep :=
  repeat match goal with
  | H: ?X -> False |- _ => change (X -> False) with (~ X) in H
  end.

Ltac lte_solve :=
  try lte_bool_change;
  try change_False_rep;
  match goal with
  | H: ~ lte ?y ?x |- lte ?x ?y  => apply lte_change
  | H: lte ?x ?z |- lte ?x ?y => find_lte_true z y; transitivity z
  | H: lte ?z ?y |- lte ?x ?y => find_lte_true x z; transitivity z
  | [H: ~ lte ?x ?y, H2: ~ lte ?y ?x |- _ ] =>
    apply lte_change in H; contradiction
  | [H: lte ?x ?y, H2: ~ lte ?x ?y |- _] => contradiction
  end; auto.

(**
  Get info from definitions
  *)

Ltac get_info_BSTWP :=
  try repeat constructor; auto;
  let P := BST_WeakProperty in
  try match goal with
    | [H: P (BT_tr ?val ?T ?T') |- P ?T] => inversion H
    | [H: P (BT_tr ?val ?T' ?T) |- P ?T] => inversion H
  end; subst; auto.

Ltac get_info_BSTSP :=
  let P := BST_StrongProperty in
  repeat match goal with
  | H: P (BT_tr _ _ _) |- _ => inversion H; gen_clear H; subst
  end; intros; firstorder.

(**
  And a stupid tactic, which is able to solve a lot of lemmas about BST
*)

Ltac general_solve_tac Hint :=
  repeat solve_if; auto;
  try match goal with
  | |- BST_WeakProperty _ => repeat constructor
  | |- BST_StrongProperty _ => repeat constructor
  end;
  repeat (
  match goal with
  | H: In_tree _ (BT_tr _ _ _) |- _ => inversion_clear H
  | H: In_tree _ BT_nil |- _ => inversion H
  | H: _ \/ _  |- _ => destruct H
  | H: _ <-> _ |- _ => destruct H
  | H: ?P -> ?Q |- _ =>
    match goal with
    | H': P |- _ =>
      let eq := fresh in clone_as H eq; apply H in H';
      move H at top;
      gen_clear H'
    end
  end; subst; auto; try Hint); try lte_solve; try discriminate; try Hint.

Tactic Notation "general_solve" :=
  general_solve_tac idtac.

Tactic Notation "general_solve" "using" tactic(tacname) :=
  general_solve_tac tacname.

(**
  Some obvious properties
*)

Lemma BST_StrongProperty_subtree: forall rval t1 t2,
  BST_StrongProperty (BT_tr rval t1 t2) ->
  BST_StrongProperty t1 /\ BST_StrongProperty t2.
Proof.
  tree_induction; get_info_BSTSP.
Qed.

Lemma BST_WeakProperty_subtree: forall rval t1 t2,
  BST_WeakProperty (BT_tr rval t1 t2) ->
  BST_WeakProperty t1 /\ BST_WeakProperty t2.
Proof.
  tree_induction; get_info_BSTWP.
Qed.

Lemma BST_Property_strong_impl_weak: forall BT,
  BST_StrongProperty BT -> BST_WeakProperty BT.
Proof.
  tree_induction; try destruct t1, t2; auto.
Qed.

(**
  Some obvious lemmas
  *)

Lemma BST_WeakProperty_lefttree_left: forall rval t2 rval' t1' t2',
  BST_WeakProperty (BT_tr rval (BT_tr rval' t1' t2') t2) ->
  BST_WeakProperty (BT_tr rval t1' t2).
Proof.
  intros; inversion H; destruct t1'.
  all: get_info_BSTWP; lte_solve.
Qed.

Lemma BST_WeakProperty_righttree_right: forall rval t1 rval' t1' t2',
  BST_WeakProperty (BT_tr rval t1 (BT_tr rval' t1' t2')) ->
  BST_WeakProperty (BT_tr rval t1 t2').
Proof.
  intros; inversion H; destruct t2'.
  all: get_info_BSTWP; lte_solve.
Qed.

Lemma BST_StrongProperty_righttree_left: forall rval t1 rval' t1' t2',
  BST_StrongProperty (BT_tr rval t1 (BT_tr rval' t1' t2')) ->
  BST_StrongProperty (BT_tr rval t1 t1').
Proof.
  intros; get_info_BSTSP.
Qed.

Lemma BST_StrongProperty_lefttree_right: forall rval t2 rval' t1' t2',
  BST_StrongProperty (BT_tr rval (BT_tr rval' t1' t2') t2) ->
  BST_StrongProperty (BT_tr rval t2' t2).
Proof.
  intros; get_info_BSTSP.
Qed.

Lemma BST_StrongProperty_left_tree: forall rval t1 t2,
  BST_StrongProperty (BT_tr rval t1 t2) ->
  (forall x, In_tree x t1 -> lte x rval).
Proof.
  intros; get_info_BSTSP.
Qed.

Lemma BST_StrongProperty_right_tree: forall rval t1 t2,
  BST_StrongProperty (BT_tr rval t1 t2) ->
  (forall x, In_tree x t2 -> lte rval x).
Proof.
  intros; get_info_BSTSP.
Qed.

(**
  Just search
  *)

Fixpoint BST_Search (BT: BinaryTree) (k: Node_type) : option Node_type :=
  match BT with
  | BT_nil => None
  | BT_tr r t1 t2 =>
    match compare k r with
    | Eq => Some r
    | Lt => BST_Search t1 k
    | Gt => BST_Search t2 k
    end
  end.

Inductive BST_indInsert : BinaryTree -> Node_type -> BinaryTree -> Prop :=
  | BSTi_nil: forall k,
    BST_indInsert BT_nil k (BT_tr k BT_nil BT_nil)
  | BSTi_lte: forall k r t t' t2,
    lte k r ->
    BST_indInsert t k t' ->
    BST_indInsert (BT_tr r t t2) k (BT_tr r t' t2)
  | BSTi_gt: forall k r t t2 t2',
    ~ lte k r ->
    BST_indInsert t2 k t2' ->
    BST_indInsert (BT_tr r t t2) k (BT_tr r t t2').

Hint Constructors BST_indInsert.

Fixpoint BST_Insert (BT: BinaryTree) (k: Node_type) : BinaryTree :=
  match BT with
  | BT_nil => BT_tr k BT_nil BT_nil
  | BT_tr r t1 t2 =>
    if (lte_bool k r) then BT_tr r (BST_Insert t1 k) t2 else
      BT_tr r t1 (BST_Insert t2 k)
  end.

Lemma BST_Insert_eq: forall BT BT' k,
  BST_indInsert BT k BT' <-> BST_Insert BT k = BT'.
Proof.
  split; intros.
  - induction H; simpl;
    general_solve using (rewrite IHBST_indInsert; reflexivity).
  - generalize dependent BT'.
    induction BT; intros.
    + subst. constructor.
    + simpl in *; solve_if; lte_bool_change; rewrite <- H; auto.
Qed.

Lemma Insert_not_change_BSTWP: forall k (BT: BinaryTree),
  BST_WeakProperty BT ->
  BST_WeakProperty (BST_Insert BT k).
Proof.
  tree_induction; general_solve; auto.
  change_False_rep. auto.
  lte_bool_change. auto.
  all: lte_bool_change; auto.
Qed.

Lemma In_tree_insert: forall k x (BT: BinaryTree),
  (In_tree x (BST_Insert BT k) ->
  x = k \/ In_tree x BT).
Proof.
  tree_induction; general_solve.
  all: firstorder.
Qed.

(*
Ltac solve_in :=
  repeat (rewrite In_tree_In_equivalence in *; unfold BT_get_list in *;
    In_help; try solve_if; auto).
*)

Lemma In_insert_cond: forall x n (BT: BinaryTree),
  (x = n) \/ In_tree x BT ->
  In_tree x (BST_Insert BT n).
Proof.
  tree_induction; general_solve.
Qed.

Lemma In_insert: forall x (BT: BinaryTree),
  In_tree x (BST_Insert BT x).
Proof.
  intros.
  apply In_insert_cond; auto.
Qed.

Fixpoint BST_InsertMintree (BT:BinaryTree) (What: BinaryTree) : BinaryTree :=
  match BT with
  | BT_nil => What
  | BT_tr r t1 t2 => BT_tr r (BST_InsertMintree t1 What) t2
  end.

Definition isNilBT (BT: BinaryTree) : bool :=
  match BT with
  | BT_nil => true
  | _ => false
  end.

Fixpoint BST_Delete (BT: BinaryTree) (k: Node_type) : BinaryTree :=
  match BT with
  | BT_nil => BT_nil
  | BT_tr r t1 t2 =>
    if (lte_bool k r) then BT_tr r (BST_Delete t1 k) t2 else
      if (lte_bool r k) then BT_tr r t1 (BST_Delete t2 k) else
        if andb (isNilBT t1) (isNilBT t2) then
          BT_nil
        else if (isNilBT t2) then
          t1
        else if (isNilBT t1) then
          t2
        else
          BST_InsertMintree t2 t1
  end.

Lemma In_tree_delete: forall x k (BT: BinaryTree),
  In_tree x (BST_Delete BT k) ->
  In_tree x BT.
Proof.
  tree_induction; general_solve.
Qed.

Hint Resolve In_tree_insert In_tree_delete.

Ltac tree_solve_in :=
  try repeat (match goal with (* Second step, use insert/delete *)
  | H: In_tree ?x (BST_Insert ?T ?k) |- _ => apply In_tree_insert in H; destruct H; subst
  | H: In_tree ?x (BST_Delete ?T ?k) |- _ => apply In_tree_delete in H; destruct H; subst
  end); try lte_solve; auto.

Ltac specialize_spec :=
   match goal with
  | H: forall x:?T, _ -> ?R x ?Y |- ?R ?Z ?Y =>
    match type of Z with | T => specialize H with Z end
  | H: forall x:?T, _ -> ?R x |- ?R ?Z =>
    match type of Z with | T => specialize H with Z end
  end.

Lemma BST_Insert_nil: forall t k,
  BST_Insert t k = BT_nil -> False.
Proof.
  intros.
  destruct t; simpl in H. inversion H.
  solve_if; inversion H.
Qed.

Lemma Insert_not_change_BSTSP: forall k (BT: BinaryTree),
  BST_StrongProperty BT ->
  BST_StrongProperty (BST_Insert BT k).
Proof.
  intros; induction BT; simpl; try solve_if; auto.
  all: repeat constructor; intros; general_solve; inversion H; auto.
  apply In_tree_insert in H1; destruct H1.
    subst. lte_bool_change. auto.
    subst. auto.
  apply In_tree_insert in H1; destruct H1.
    subst. lte_bool_change. apply lte_change in H0; auto.
    subst. auto.
Qed.

Fixpoint BST_Minimum (BT:BinaryTree) : option Node_type :=
  match BT with
  | BT_tr r t _ => match t with
    | BT_nil => Some r
    | _ => BST_Minimum t
    end
  | _ => None
  end.

Fixpoint BST_Maximum (BT:BinaryTree) : option Node_type :=
  match BT with
  | BT_tr r _ t => match t with
    | BT_nil => Some r
    | _ => BST_Maximum t
    end
  | _ => None
  end.

Lemma Delete_not_change_BSTWP: forall k (BT: BinaryTree),
  BST_WeakProperty BT ->
  BST_WeakProperty (BST_Delete BT k).
Proof.
  tree_induction; general_solve.
Qed.

Lemma Delete_not_change_BSTSP: forall k (BT: BinaryTree),
  BST_StrongProperty BT ->
  BST_StrongProperty (BST_Delete BT k).
Proof.
  tree_induction; general_solve.
  all: repeat constructor; get_info_BSTSP.
  all: tree_solve_in.
Qed.

Lemma BST_Maximum_not_nil: forall (BT: BinaryTree),
  BT = BT_nil <->
  BST_Maximum BT = None.
Proof.
  tree_induction; split; intros.
  all: general_solve.
Qed.

Lemma BST_Minimum_not_nil: forall (BT: BinaryTree),
  BT = BT_nil <->
  BST_Minimum BT = None.
Proof.
  tree_induction; split; intros; general_solve.
Qed.

Lemma BST_Maximum_not_nil2: forall (BT: BinaryTree),
  BT <> BT_nil <->
  BST_Maximum BT <> None.
Proof.
  split; intros; unfold not in *; intros; apply H;
  apply BST_Maximum_not_nil in H0; assumption.
Qed.

Lemma BST_Maximum_not_nil_tr: forall n t1 t2,
  exists x, BST_Maximum (BT_tr n t1 t2) = Some x.
Proof.
  intros.
  remember (BT_tr n t1 t2) as Tree; symmetry in HeqTree.
  destruct (BST_Maximum _) eqn:F. eauto.
  apply BST_Maximum_not_nil in F. rewrite F in HeqTree. inversion HeqTree.
Qed.

Lemma BST_Minimum_not_nil_tr: forall n t1 t2,
  exists x, BST_Minimum (BT_tr n t1 t2) = Some x.
Proof.
  intros.
  remember (BT_tr n t1 t2) as Tree; symmetry in HeqTree.
  destruct (BST_Minimum _) eqn:F. eexists. reflexivity.
  apply BST_Minimum_not_nil in F. rewrite F in HeqTree. inversion HeqTree.
Qed.

Lemma BST_Minimum_ok_hderror: forall (BT: BinaryTree),
  BST_WeakProperty BT ->
  BST_Minimum BT = hd_error (In_order_traverse BT (fun x:_ => x)).
Proof.
  induction 1; simpl; try reflexivity;
  simpl in *;
  destruct (In_order_traverse t1 _); simpl in *; assumption.
Qed.

Lemma BST_Maximum_ok_hderror: forall (BT: BinaryTree),
  BST_WeakProperty BT ->
  BST_Maximum BT = hd_error( rev( In_order_traverse BT (fun x:_ => x))).
Proof.
  induction 1; simpl; try reflexivity;
  simpl in *; try rewrite IHBST_WeakProperty2; try rewrite IHBST_WeakProperty; simpl;
  do 2 (repeat multimatch goal with
  | |- context[?x::?l] => match l with
    | nil => idtac
    | _ => change (x::l) with ([x] ++ l)
    end
  end; repeat rewrite rev_app_distr; simpl).
  - destruct (rev (In_order_traverse t2' _)); simpl; auto.
  - reflexivity.
  - destruct (rev (In_order_traverse t2' _)); simpl; reflexivity.
Qed.

Lemma BT_get_list_nil: forall (BT: BinaryTree),
  BT_get_list BT = [] <-> BT = BT_nil.
Proof.
  split; intros.
  - destruct BT eqn:eq; auto.
    destruct (BT_tr _ _ _) eqn:eq2; auto.
    unfold BT_get_list in H. inversion H.
    assert ([] <> In_order_traverse b3 (fun x: _ => x) ++ n0::In_order_traverse b4 (fun x:_ => x)) by apply app_cons_not_nil.
    symmetry in H1. contradiction.
  - subst. constructor.
Qed.

Lemma BST_WeakProperty_max: forall rval t t1,
  BST_WeakProperty (BT_tr rval t t1) ->
  exists x, (BST_Maximum (BT_tr rval t t1) = Some x) /\
  (exists m, BT_get_list (BT_tr rval t t1) = m ++ [x]).
Proof.
  intros. unfold BT_get_list.
  do 2 clone H. apply BST_Maximum_ok_hderror in H.
  remember (In_order_traverse (BT_tr rval t t1) _) as l; symmetry in Heql.
  assert (exists x, BST_Maximum (BT_tr rval t t1) = Some x) by apply BST_Maximum_not_nil_tr.
  destruct H2. exists x. split; auto.
  rewrite H in H2.
  destruct (rev l) eqn:Eql; inversion H2.
  subst. exists (rev l0).
  apply (@f_equal (list Node_type) (list Node_type) (@rev Node_type) _ _) in Eql.
  rewrite rev_involutive in Eql. rewrite Eql.
  simpl. reflexivity.
Qed.

Lemma BST_WeakProperty_min: forall rval t t1,
  BST_WeakProperty (BT_tr rval t t1) ->
  exists x, (BST_Minimum (BT_tr rval t t1) = Some x) /\
  (exists m, BT_get_list (BT_tr rval t t1) = x::m).
Proof.
  intros. unfold BT_get_list.
  do 2 clone H. apply BST_Minimum_ok_hderror in H.
  remember (In_order_traverse (BT_tr rval t t1) _) as l; symmetry in Heql.
  assert (exists x, BST_Minimum (BT_tr rval t t1) = Some x) by apply BST_Minimum_not_nil_tr.
  destruct H2. exists x. split; auto.
  rewrite H in H2.
  destruct l eqn:Eql; inversion H2.
  subst. exists l0. reflexivity.
Qed.

Lemma BST_root_in_tree: forall rval t1 t2,
  In rval (BT_get_list (BT_tr rval t1 t2)).
Proof.
  intros. unfold BT_get_list in *.
  rewrite In_order_traverse_of_tree.  simpl.
  apply in_or_app; right. simpl. left. reflexivity.
Qed.

Lemma BST_Maximum_in_tree: forall t x,
  BST_Maximum t = Some x ->
  In_tree x t.
Proof.
  intros.
  induction t; inversion H.
  destruct t2; inversion H1; intuition.
Qed.

Lemma BST_Minimum_in_tree: forall t x,
  BST_Minimum t = Some x ->
  In_tree x t.
Proof.
  intros.
  induction t; inversion H.
  destruct t1; inversion H1; intuition.
Qed.

(* Tree is sorted *)

Lemma BST_is_LocallySorted: forall (BT: BinaryTree),
  BST_StrongProperty BT ->
  LocallySorted lte (BT_get_list BT).
Proof.
  intros; induction H; try constructor; unfold BT_get_list in *.
  rewrite In_order_traverse_of_tree.
  clone H. clone H1.
  apply BST_Property_strong_impl_weak in H.
  apply BST_Property_strong_impl_weak in H1.
  destruct t1, t2; simpl in *; try constructor.
  - apply BST_WeakProperty_min in H1; unfold BT_get_list in *; firstorder.
    simpl in H5. rewrite H5 in *.
    apply LocallySorted_begin; auto.
    apply BST_Minimum_in_tree in H1. firstorder.
  - apply BST_WeakProperty_max in H; unfold BT_get_list in *; firstorder.
    simpl in H5. rewrite H5 in *.
    rewrite app_assoc_reverse; simpl.
    apply LocallySorted_end; auto.
    apply BST_Maximum_in_tree in H. firstorder.
  - apply BST_WeakProperty_min in H1.
    apply BST_WeakProperty_max in H. unfold BT_get_list in *; firstorder.
    apply BST_Maximum_in_tree in H.
    apply BST_Minimum_in_tree in H1.
    simpl in H5; rewrite H5 in *.
    simpl in H6; rewrite H6 in *.
    rewrite app_assoc_reverse. simpl.
    apply LocallySorted_sum; firstorder.
    apply LocallySorted_begin; firstorder.
Qed.

End BinaryTreeDef.
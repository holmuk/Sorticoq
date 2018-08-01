(**
  sublist
  first_n and drop_n functions
*)

Require Import Nat PeanoNat Arith Omega.
Require Import List.

Import ListNotations.

Fixpoint first_n {T: Type} (n: nat) (l: list T): list T :=
  match n, l with
  | O, _ => nil
  | _, nil => nil
  | S n', x::l' => cons x (first_n n' l')
  end.

Fixpoint drop_n {T: Type} (n: nat) (l: list T) : list T :=
  match n, l with
  | O, l' => l'
  | n', nil => nil
  | S n', x::l' => (drop_n n' l')
  end.

Lemma first_n_of_nil: forall (T: Type) n,
  @first_n T n [] = [].
Proof.
  intros. destruct n; reflexivity.
Qed.

Lemma drop_n_of_nil: forall (T: Type) n,
  @drop_n T n [] = [].
Proof.
  intros. destruct n; reflexivity.
Qed.

Lemma app_first_drop: forall n (T: Type) (l: list T),
  first_n n l ++ drop_n n l = l.
Proof.
  intros.
  generalize dependent n.
  induction l; intros; destruct n; simpl; try reflexivity.
  + apply f_equal. intuition.
Qed.

Lemma rev_first_drop_rev: forall n (T: Type) (l: list T),
  rev ( drop_n n l ) ++ rev ( first_n n l ) = rev l.
Proof.
  intros.
  rewrite <- rev_app_distr.
  apply f_equal.
  apply app_first_drop.
Qed.

(**
  relations between length and first_n/drop_n
*)

Lemma first_length: forall (T: Type) (l: list T),
  first_n (length l) l = l.
Proof.
  intros. induction l; try reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma drop_length: forall (T: Type) (l: list T),
  drop_n (length l) l = [].
Proof.
  intros. induction l; try reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma length_drop_first: forall n (T: Type) (l: list T),
  length (first_n n l) + length (drop_n n l) = length l.
Proof.
  intros.
  rewrite <- app_length. rewrite app_first_drop.
  reflexivity.
Qed.

Hint Rewrite first_n_of_nil drop_n_of_nil app_first_drop : first_drop_rewrite.
Hint Rewrite rev_first_drop_rev : first_drop_rewrite.
Hint Rewrite first_length drop_length length_drop_first : first_drop_rewrite.

Ltac simpl_first_drop :=
  autorewrite with first_drop_rewrite in *; simpl in *.

(**
  Lemmas with (in)equalities
*)

Lemma first_n_nil: forall n (T: Type) (l: list T),
  (n = 0) \/ (l = nil) <-> first_n n l = nil.
Proof.
  split; intros.
  - destruct H; subst; auto.
    destruct n; subst; auto.
  - destruct n; destruct l; subst; auto.
    inversion H.
Qed.

Lemma first_n_not_nil: forall n (T: Type) (l: list T),
  (n <> 0) /\ (l <> nil) <-> first_n n l <> nil.
Proof.
  intros. rewrite <- first_n_nil. intuition.
Qed.

Lemma drop_n_nil: forall n (T: Type) (l: list T),
  (length l <= n) <-> drop_n n l = [].
Proof.
  split; intros.
  - generalize dependent l. induction n; intros.
    + inversion H. simpl_first_drop; auto.
    + destruct l; auto.
      apply IHn. simpl in H. apply le_S_n. assumption.
  - generalize dependent n. induction l; simpl; intuition.
    destruct n.
    + inversion H.
    + apply le_n_S. apply IHl. rewrite <- H. reflexivity.
Qed.

Lemma drop_n_not_nil: forall n (T: Type) (l: list T),
  (n < length l) <-> drop_n n l <> [].
Proof.
  intros. rewrite <- drop_n_nil. intuition.
Qed.

Lemma length_of_first: forall n (T: Type) (l: list T),
  n <= length l ->
  length (first_n n l) = n.
Proof.
  intros. generalize dependent l.
  induction n; simpl; auto.
  intros. destruct l; simpl. inversion H.
  apply eq_S. apply IHn. simpl in H. intuition.
Qed.

Lemma drop_cat: forall (T: Type) (l l': list T) n,
  n <= length l ->
  drop_n n l ++ l' = drop_n n (l ++ l').
Proof.
  intros. generalize dependent l'; generalize dependent l; induction n; auto.
  intros.
  destruct l eqn:eqL, l' eqn: eqL'; ssimpl_list; auto.
  simpl in H. inversion H. simpl. apply IHn. intuition.
Qed.

Lemma first_drop_rel: forall n (T: Type) (l: list T),
  n <= length l ->
  rev (first_n n l) = drop_n (length l - n) (rev l).
Proof.
  intros. generalize dependent l.
  induction n; simpl; auto; intros.
  - rewrite Nat.sub_0_r. symmetry. apply drop_n_nil. simpl_list. auto.
  - destruct l; simpl in *; auto.
    apply le_S_n in H. apply IHn in H. rewrite H. 
    rewrite drop_cat; auto. simpl_list.
    apply Nat.le_sub_l.
Qed.

Lemma length_of_drop: forall n (T: Type) (l: list T),
  n <= length l ->
  length (drop_n n l) = length l - n.
Proof.
  intros.
  remember H as H2; clear HeqH2.
  assert (n = length l - (length l - n)) by omega.
  assert (length (rev l) - n <= length (rev l)) by omega.
  apply first_drop_rel in H1.
  assert (l = rev (rev l)) by (rewrite rev_involutive; reflexivity).
  rewrite H0. rewrite H3. rewrite rev_length. rewrite <- H1.
  simpl_list. rewrite length_of_first. rewrite <- H0. reflexivity.
  simpl_list. omega.
Qed.
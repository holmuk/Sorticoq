(*
 * Math Auxillary
 * The background for simple 'nat' lemmas.
*)

Require Import Omega.

Lemma div2_less_x: forall x,
  (1 < x) -> x/2 < x.
Proof.
  intros. apply Nat.div_lt; omega.
Qed.

Lemma x_lt_2x: forall x,
  (1 <= x) -> x < 2*x.
Proof.
  intros. omega.
Qed.


Lemma div2_rep: forall n m,
  m = n/2 -> 2*m = n \/ 2*m + 1 = n.
Proof.
  intros.
  assert (2 <> 0) by auto.
  assert (Nat.Even (n) \/ Nat.Odd (n)) by apply Nat.Even_or_Odd.
  destruct H1; inversion H1.
  - rewrite H2 in H. apply Nat.div_mul with (a:=x) in H0.
    rewrite Nat.mul_comm in H. rewrite H0 in H. subst. auto.
  - apply (Nat.div_add_l x _ 1) in H0.
    rewrite H2 in H. rewrite Nat.mul_comm in H. rewrite H0 in H. simpl in H.
    omega.
Qed.

Lemma div2_plus_mod2_lt_x: forall x,
  (1 < x) -> (x / 2) + (x mod 2) < x.
Proof.
  intros.
  assert (x = 2*(x/2) + (x mod 2)) by (apply Nat.div_mod; intuition).
  induction x.
  - inversion H.
  - remember (S x mod 2) as Sxm2.
    remember (S x / 2) as Sxd2.
    rewrite H0.
    apply Nat.add_lt_mono_r.
    assert (1 <= Sxd2) by (rewrite HeqSxd2; apply Nat.div_le_lower_bound; intuition).
    apply x_lt_2x. assumption.
Qed.

Lemma xpy_div2_plus_mod2_lt_y: forall x y,
  (2*x + 1 < y) -> (x + y)/2 + (x + y) mod 2 < y.
Proof.
  intros.
  assert (Nat.Even (x + y) \/ Nat.Odd (x + y)) by apply Nat.Even_or_Odd.
  destruct H0; inversion H0; rewrite H1.
  - rewrite Nat.mul_comm. rewrite Nat.div_mul. rewrite Nat.mod_mul.
    rewrite <- plus_n_O.
    omega. discriminate. discriminate.
  - rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.add_mod.
    rewrite Nat.mod_mul. simpl. omega.
    discriminate. discriminate. discriminate.
Qed.

Lemma mod2_plus_div2_neq_zero: forall x,
  (x <> 0) -> x/2 + x mod 2 <> 0.
Proof.
  intros. unfold not. intros.
  apply Nat.eq_add_0 in H0.
  destruct H0.
  apply Nat.div_small_iff in H0; auto.
  apply Nat.mod_small in H0. rewrite H0 in H1.
  contradiction.
Qed.

Lemma mod2_plus_div2_eq_x: forall x,
  (x < 2) -> x/2 + x mod 2 = x.
Proof.
  intros.
  apply Nat.div_small_iff in H; auto. rewrite H. rewrite plus_O_n.
  apply Nat.mod_small.
  apply Nat.div_small_iff in H; auto.
Qed.

Lemma mod2_plus_div2_eq_zero: forall x,
  x/2 + x mod 2 = 0 -> (x = 0).
Proof.
  intros.
  apply plus_is_O in H. destruct H.
  assert (2 <> 0) by auto.
  apply Nat.div_small_iff with (a:=x) in H1.
  apply Nat.div_exact in H0; omega.
Qed.

Lemma pow_lt_max: forall x y,
  2 ^ x <= 2 ^ (max x y).
Proof.
  intros.
  destruct (max x y) eqn:meq; simpl.
  - destruct x, y; simpl; auto; inversion meq.
  - rewrite <- plus_n_O.
    assert (forall x, x + x = 2*x) by (intros; omega).
    rewrite H; clear H.
    rewrite <- Nat.pow_succ_r'.
    apply Nat.pow_le_mono_r; auto.
    inversion meq. apply Max.le_max_l.
Qed.

Hint Rewrite Nat.add_0_r Nat.sub_0_r : arith_simple.

Ltac arith_help :=
  try match goal with
  | H: ?x + ?y = 0 |- _ =>
    apply plus_is_O in H; destruct H
  end;
  autorewrite with arith_simple in *.

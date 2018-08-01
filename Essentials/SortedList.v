Require Import Nat List Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Relations.Relation_Definitions.
Import ListNotations.

Lemma LocallySorted_begin: forall {A:Type} {R:relation A} l x y,
  LocallySorted R (x::l) ->
  R y x ->
  LocallySorted R (y::x::l).
Proof.
  intros; constructor; auto.
Qed.

Lemma LocallySorted_end: forall {A:Type} {R:relation A} l x y,
  LocallySorted R (l ++ [x]) ->
  R x y ->
  LocallySorted R (l ++ [x; y]).
Proof.
  intros.
  induction l; simpl in *.
  - repeat constructor; auto.
  - inversion H. symmetry in H3. apply app_eq_nil in H3; destruct H3. inversion H3.
    rewrite H2 in *.
    apply IHl in H3. change (l ++ [x; y]) with (l ++ [x] ++ [y]) in *.
    rewrite app_assoc in *. rewrite <- H2 in *. simpl in H3.
    change (a::(b::l0) ++ [y]) with (a::b::(l0 ++ [y])).
    constructor; auto.
Qed.

Lemma LocallySorted_sum: forall {A:Type} {R:relation A} a b l l',
  LocallySorted R (l ++ [a]) -> LocallySorted R (b::l') ->
  R a b ->
  LocallySorted R (l ++ [a;b] ++ l').
Proof.
  intros.
  induction l, l'; simpl.
  - repeat constructor; auto.
  - constructor; auto.
  - simpl in H. inversion H. symmetry in H4. apply app_eq_nil in H4. destruct H4. inversion H4.
    subst. rewrite H3 in H4.
    apply IHl in H4. simpl in H4.
    change (l ++ [a;b]) with (l ++ [a] ++ [b]) in *. rewrite app_assoc in *.
    rewrite <- H3 in *.
    change (a0::(b0::l0) ++ [b]) with (a0::b0::(l0 ++ [b])). constructor.
    simpl in H4. auto. auto.
  - simpl in H. inversion H. symmetry in H4. apply app_eq_nil in H4. destruct H4. inversion H4.
    subst. rewrite H3 in H4. apply IHl in H4. simpl in H4.
    change (l ++ a :: b :: a1 :: l') with (l ++ [a] ++ b :: a1 :: l') in *.
    rewrite app_assoc in *. rewrite <- H3 in *.
    simpl in *. constructor; auto.
Qed.

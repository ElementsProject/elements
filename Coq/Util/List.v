Require Export Coq.Lists.List.
Require Import ZArith.

Lemma repeat_S_tail {A} : forall (a : A) n, repeat a n ++ (a :: nil) = repeat a (S n).
Proof.
intros a.
induction n;[reflexivity|].
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma rev_repeat {A} : forall (a : A) n, rev (repeat a n) = repeat a n.
Proof.
intros a.
induction n;[reflexivity|].
simpl.
rewrite IHn, repeat_S_tail.
reflexivity.
Qed.

Lemma firstn_app_3 {A} (l1 l2 : list A) :
  firstn (length l1) (l1 ++ l2) = l1.
Proof.
rewrite <- (Plus.plus_0_r (length l1)), firstn_app_2; cbn.
apply app_nil_r.
Qed.

Lemma skipn_all {A} (l : list A) : skipn (length l) l = nil.
Proof.
apply (app_inv_head (firstn (length l) l)).
rewrite firstn_skipn, firstn_all, app_nil_r; auto.
Qed.

Lemma skipn_all2 {A} n (l : list A) : length l <= n -> skipn n l = nil.
Proof.
intros Hn.
apply (app_inv_head (firstn n l)).
rewrite firstn_skipn, firstn_all2, app_nil_r; auto.
Qed.

Lemma skipn_app {A} (n : nat) : forall (l1 l2 : list A),
       skipn n (l1 ++ l2) = skipn n l1 ++ skipn (n - length l1) l2.
Proof.
induction n.
 reflexivity.
destruct l1.
 reflexivity.
apply IHn.
Qed.

Lemma skipn_app_2 {A} (n : nat) : forall (l1 l2 : list A),
       skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof.
intros l1 l2.
rewrite skipn_app, Minus.minus_plus, skipn_all2; auto with arith.
Qed.

Lemma skipn_app_3 {A} (l1 l2 : list A) :
  skipn (length l1) (l1 ++ l2) = l2.
Proof.
apply (app_inv_head l1).
rewrite <- (firstn_app_3 l1 l2) at 1.
apply firstn_skipn.
Qed.

Definition N_sum : list N -> N := fold_right N.add 0%N.

Definition Z_sum : list Z -> Z := fold_right Z.add 0%Z.
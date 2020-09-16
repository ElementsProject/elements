Require Import ZArith.

Set Implicit Arguments.

(* In order to compute, this needs to be transparent *)
Definition natDiff : forall n m, {i | i + n = m} + {i | i + m = n}.
Proof.
assert (H0 : forall n, n + 0 = n).
 induction n.
  reflexivity.
 simpl; rewrite IHn; reflexivity.
assert (HS : forall n m, n + S m = S (n + m)).
 induction n; intros m.
  reflexivity.
 simpl; rewrite IHn; reflexivity.
induction n.
intros m.
left.
exists m.
apply H0.
induction m.
 right.
 exists (S n).
 apply H0.
case (IHn m); intros [i Hi].
 left.
 exists i.
 rewrite <- Hi.
 apply HS.
right.
exists i.
rewrite <- Hi.
apply HS.
Defined.

Lemma Zmod_div (x y : Z) : (x mod y / y = 0)%Z.
Proof.
destruct y as [|y|y].
- apply Zdiv_0_r.
- apply Zdiv_small.
  apply Zmod_pos_bound.
  reflexivity.
- rewrite <- Zdiv_opp_opp.
  apply Zdiv_small.
  rewrite Z.opp_nonneg_nonpos, <- Z.opp_lt_mono.
  destruct (Zmod_neg_bound x (Z.neg y));[reflexivity|auto].
Qed.

Lemma two_power_nat_le n m : n <= m -> (two_power_nat n <= two_power_nat m)%Z.
Proof.
repeat rewrite two_power_nat_equiv.
auto using Z.pow_le_mono_r with zarith.
Qed.

Lemma two_power_nat_plus n m : (two_power_nat (n + m) = two_power_nat n * two_power_nat m)%Z.
Proof.
repeat rewrite two_power_nat_equiv.
rewrite inj_plus, Z.pow_add_r; auto with zarith.
Qed.


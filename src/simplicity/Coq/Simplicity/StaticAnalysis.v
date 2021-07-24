Require Import NArith.
Require Import Simplicity.Util.List.

Require Import Simplicity.Alg.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Translate.
Require Import Simplicity.Ty.

Set Implicit Arguments.

Local Open Scope N_scope.

Module StateShape.
(* In this section we prove that executing Simplicity programs on the Bit
 * Machine starting from *any* state, preserves the shape of the state if it
 * doesn't crash or halt.
 * Although spec allows for starting from the Halted state, any program
 * starting from the Halted state must end in the Halted state, which will
 * violating the assumptions of spec that it doesn't end in the Halted state.
 * Hence this scenario vacuously sastifies the spec.
 *)

Definition spec {A B : Ty} (p : Naive.Program_ty A B) :=
  forall s0 (s1 : RunState),
   s0 >>- p ->> s1 ->
   stateShape s0 = stateShape s1.

Lemma iden_spec {A : Ty} : spec (A:=A) iden.
Proof.
intros s0 s1.
apply stateShape_copy.
Qed.

Lemma comp_spec {A B C : Ty} (s : Naive.Program_ty A B) (t : Naive.Program_ty B C) :
 spec s -> spec t -> spec (comp s t) .
Proof.
intros Hs Ht s0 s5 Hs05.
simpl in Hs05.
apply seq_complete in Hs05.
destruct Hs05 as [s4 Hs04 Hs45].
apply seq_complete in Hs04.
destruct Hs04 as [s3 Hs03 Hs34].
apply seq_complete in Hs03.
destruct Hs03 as [s2 Hs02 Hs23].
apply seq_complete in Hs02.
destruct Hs02 as [s1 Hs01 Hs12].
pose (inv := dropFrame_complete Hs45);inversion inv as [s4' s5' Hs45'|]; clear inv Hs45.
subst s4; subst s5.
apply Ht in Hs34.
destruct s3 as [|s3];[discriminate|].
pose (inv := moveFrame_complete Hs23);inversion inv as [s2' s3' Hs23'|]; clear inv Hs23.
subst s2; subst s3.
apply Hs in Hs12.
destruct s1 as [|s1];[discriminate|].
pose (inv := newFrame_complete Hs01);inversion inv as [s0' s1' Hs01'|]; clear inv Hs01.
subst s0; subst s1.
revert Hs12 Hs34.
inversion_clear Hs01'.
inversion_clear Hs23'.
inversion_clear Hs45'.
clear.
unfold stateShape, runStateShape; cbn.
do 2 inversion 1.
reflexivity.
Qed.

Lemma unit_spec {A : Ty} : spec (A:=A) unit.
Proof.
intros x y Hxy.
cbn in Hxy.
apply nop_complete in Hxy.
congruence.
Qed.

Lemma injl_spec {A B C : Ty} (t : Naive.Program_ty A B) :
 spec t -> spec (injl (C:=C) t).
Proof.
intros Ht s0 s3 Hs03.
simpl in Hs03.
apply seq_complete in Hs03.
destruct Hs03 as [s2 Hs02 Hs23].
apply seq_complete in Hs02.
destruct Hs02 as [s1 Hs01 Hs12].
rewrite (stateShape_write Hs01).
rewrite (stateShape_skip Hs12).
apply (Ht _ _ Hs23).
Qed.

Lemma injr_spec {A B C : Ty} (t : Naive.Program_ty A C) :
 spec t -> spec (injr (B:=B) t).
Proof.
intros Ht s0 s3 Hs03.
simpl in Hs03.
apply seq_complete in Hs03.
destruct Hs03 as [s2 Hs02 Hs23].
apply seq_complete in Hs02.
destruct Hs02 as [s1 Hs01 Hs12].
rewrite (stateShape_write Hs01).
rewrite (stateShape_skip Hs12).
apply (Ht _ _ Hs23).
Qed.

Lemma bump_spec {A B : Ty} (t : Naive.Program_ty A B) n (Ht : spec t) x (y : RunState) :
 x >>- bump n t ->> y ->
 stateShape x = stateShape y.
Proof.
unfold bump.
intros Hxy.
apply seq_complete in Hxy.
destruct Hxy as [s2 Hxs2 Hs2y].
apply seq_complete in Hxs2.
destruct Hxs2 as [s1 Hxs1 Hs1s2].
rewrite (stateShape_fwd Hxs1).
destruct s2 as [|s2].
 pose (inv := runHalt (trace Hs2y));inversion inv.
rewrite (Ht _ _ Hs1s2).
apply (stateShape_bwd Hs2y).
Qed.

Lemma case_spec {A B C D : Ty} (s : Naive.Program_ty (A * C) D) (t : Naive.Program_ty (B * C) D) :
 spec s -> spec t -> spec (case s t).
Proof.
intros Hs Ht x y Hxy.
simpl in Hxy.
remember (Running y) as y'.
revert Heqy'; pattern x; pattern y; revert x y' Hxy.
apply choice_complete;[intros x y' [|] Hb Hxy ->|discriminate];
eauto using bump_spec.
Qed.

Lemma pair_spec {A B C : Ty} (s : Naive.Program_ty A B) (t : Naive.Program_ty A C) :
 spec s -> spec t -> spec (pair s t).
Proof.
intros Hs Ht x z Hxz.
simpl in Hxz.
apply seq_complete in Hxz.
destruct Hxz as [y Hxy Hyz].
destruct y as [|y].
 pose (inv := runHalt (trace Hyz));inversion inv.
rewrite (Hs _ _ Hxy).
apply (Ht _ _ Hyz).
Qed.

Lemma take_spec {A B C : Ty} (t : Naive.Program_ty A C) :
 spec t -> spec (take (B:=B) t).
Proof.
auto.
Qed.

Lemma drop_spec {A B C : Ty} (t : Naive.Program_ty B C) :
 spec t -> spec (drop (A:=A) t).
Proof.
intros Ht x y; cbn.
apply bump_spec.
assumption.
Qed.

Lemma Core_spec {A B : Ty} (t : forall {alg : Core.Algebra}, alg A B) (Ht : Core.Parametric (@t)) :
 forall s0 (s1 : RunState),
 s0 >>- @t Naive.translate ->> s1 ->
 stateShape s0 = stateShape s1.
Proof.
refine (Ht _ _ (Core.Parametric.Pack (_ : Core.Parametric.class (fun A B x (_:Naive.Program_ty A B) => @spec A B x)))).
constructor; intros.
- apply iden_spec.
- apply comp_spec; assumption.
- apply unit_spec.
- apply injl_spec; assumption.
- apply injr_spec; assumption.
- apply case_spec; assumption.
- apply pair_spec; assumption.
- apply take_spec; assumption.
- apply drop_spec; assumption.
Qed.

Lemma StateSize A B (p : Naive.Program_ty A B) (Hp : spec p) s0 s1 :
  s0 >>- p ->> s1 -> stateSize s1 <= stateSize s0.
Proof.
intros H01.
destruct s1 as [|s1];[apply N.le_0_l|].
unfold stateSize.
rewrite (Hp _ _ H01).
reflexivity.
Qed.

End StateShape.

Module MaximumMemory.

Definition bound_ty (A B : Ty) := N.

Definition extraMemoryBound_class : Core.class bound_ty :=
  {| Core.iden A := 0
   ; Core.comp A B C s t := N.of_nat (bitSize B) + N.max s t
   ; Core.unit A := 0
   ; Core.injl A B C t := t
   ; Core.injr A B C t := t
   ; Core.case A B C D s t := N.max s t
   ; Core.pair A B C s t := N.max s t
   ; Core.take A B C t := t
   ; Core.drop A B C t := t
   |}.

Canonical Structure extraMemoryBound : Core.Algebra :=
  Core.Pack bound_ty extraMemoryBound_class.

Definition MemoryBound {A B : Ty} (t : bound_ty A B) x : N := stateSize x + t.

Definition spec {A B : Ty} (p : Naive.Program_ty A B) (mt : bound_ty A B)  :=
  forall x y (tr : x >>- p ->> y),
   maximumMemoryResidence (trace tr) <= MemoryBound mt x.

Lemma iden_spec {A : Ty} : spec iden (iden (A:=A)).
Proof.
intros x y tr.
unfold MemoryBound.
cbn in *.
rewrite MMR_copy, N.add_0_r.
reflexivity.
Qed.

Lemma comp_spec {A B C : Ty} (ps : Naive.Program_ty A B) (pt : Naive.Program_ty B C) ms mt:
 spec ps ms -> spec pt mt -> StateShape.spec ps -> StateShape.spec pt -> spec (comp ps pt) (comp ms mt).
Proof.
intros Hs Ht Ss St s0 s5 tr05.
unfold MemoryBound.
cbn in *.
destruct (seq_complete tr05) as [s4 tr04 tr45].
rewrite (MMR_seq tr04 tr45 tr05).
destruct (seq_complete tr04) as [s3 tr03 tr34].
rewrite (MMR_seq tr03 tr34 tr04).
destruct (seq_complete tr03) as [s2 tr02 tr23].
rewrite (MMR_seq tr02 tr23 tr03).
destruct (seq_complete tr02) as [s1 tr01 tr12].
rewrite (MMR_seq tr01 tr12 tr02).
rewrite N.add_assoc.
rewrite MMR_newFrame, MMR_moveFrame, MMR_dropFrame.
transitivity (stateSize s1 + N.max ms mt).
 rewrite <- N.add_max_distr_l; do 2 rewrite <- N.max_assoc.
 apply N.max_le_compat.
  apply N.max_lub;[apply N.le_add_r|apply (Hs _ _ tr12)].
 transitivity (stateSize s2 + mt).
  replace (stateSize s2) with (stateSize s3).
   transitivity (N.max (stateSize s3) (maximumMemoryResidence (trace tr34))).
    rewrite N.max_assoc.
    apply N.max_lub;[reflexivity|].
    etransitivity;[apply (StateShape.StateSize St tr34)|apply N.le_max_l].
   apply N.max_lub;[apply N.le_add_r|apply (Ht _ _ tr34)].
  destruct (moveFrame_complete tr23) as [s2 s3 T23|];[|reflexivity].
  inversion T23;cbn.
  rewrite fullWriteFrame_size.
  ring.
 apply N.add_le_mono_r.
 apply (StateShape.StateSize Ss tr12).
apply N.add_le_mono_r.
destruct (newFrame_complete tr01) as [s0 s1 T01|];[apply N.eq_le_incl|apply N.le_0_l].
inversion T01; cbn.
ring.
Qed.

Lemma unit_spec {A : Ty} : spec unit (unit (A:=A)).
Proof.
intros x y tr.
unfold MemoryBound.
cbn in *.
destruct (trace_subproof _); cbn.
rewrite N.add_0_r.
reflexivity.
Qed.

Lemma injl_spec {A B C : Ty} (pt : Naive.Program_ty A B) mt :
 spec pt mt -> spec (injl pt) (injl (C:=C) mt).
Proof.
intros Ht s0 s3 tr03.
unfold MemoryBound.
cbn in *.
destruct (seq_complete tr03) as [s2 tr02 tr23].
rewrite (MMR_seq tr02 tr23 tr03).
destruct (seq_complete tr02) as [s1 tr01 tr12].
rewrite (MMR_seq tr01 tr12 tr02).
rewrite MMR_write, MMR_skip.
unfold stateSize.
rewrite (stateShape_write tr01), N.max_id, (stateShape_skip tr12).
apply N.max_lub.
 apply N.le_add_r.
apply Ht.
Qed.

Lemma injr_spec {A B C : Ty} (pt : Naive.Program_ty A C) mt :
 spec pt mt -> spec (injr pt) (injr (B:=B) mt).
Proof.
intros Ht s0 s3 tr03.
unfold MemoryBound.
cbn in *.
destruct (seq_complete tr03) as [s2 tr02 tr23].
rewrite (MMR_seq tr02 tr23 tr03).
destruct (seq_complete tr02) as [s1 tr01 tr12].
rewrite (MMR_seq tr01 tr12 tr02).
rewrite MMR_write, MMR_skip.
unfold stateSize.
rewrite (stateShape_write tr01), N.max_id, (stateShape_skip tr12).
apply N.max_lub.
 apply N.le_add_r.
apply Ht.
Qed.

Lemma bump_spec {A B : Ty} (pt : Naive.Program_ty A B) mt (Ht : spec pt mt) x y n (tr : x >>- bump n pt ->> y) :
   maximumMemoryResidence (trace tr) <= MemoryBound mt x.
Proof.
unfold bump in tr.
destruct (seq_complete tr) as [s2 tr02 tr23].
rewrite (MMR_seq tr02 tr23).
destruct (seq_complete tr02) as [s1 tr01 tr12].
rewrite (MMR_seq tr01 tr12).
rewrite MMR_bwd, MMR_fwd.
unfold MemoryBound, stateSize.
rewrite (stateShape_fwd tr01).
rewrite (N.max_comm (stateShapeSize _)), <- N.max_assoc, N.max_l.
 apply Ht.
apply MMR_bounds.
Qed.

Lemma case_spec {A B C D : Ty} (ps : Naive.Program_ty (A * C) D) (pt : Naive.Program_ty (B * C) D) ms mt :
 spec ps ms -> spec pt mt -> spec (case ps pt) (case ms mt).
Proof.
intros Hs Ht s0 s1 tr01.
unfold MemoryBound.
cbn in *.
rewrite <- N.add_max_distr_l.
generalize tr01.
pattern s0; pattern s1.
revert s0 s1 tr01.
apply choice_complete.
 intros s0 s1 [|] Heq tr tr01.
  rewrite <- (trace_right tr tr01);[|assumption].
  etransitivity;[apply bump_spec;apply Ht|apply N.le_max_r].
 rewrite <- (trace_left tr tr01);[|assumption].
 etransitivity;[apply bump_spec;apply Hs|apply N.le_max_l].
unfold runProgram, choice;cbn.
intros tr01.
destruct (trace_subproof _); cbn.
apply N.le_0_l.
Qed.

Lemma pair_spec {A B C : Ty} (ps : Naive.Program_ty A B) (pt : Naive.Program_ty A C) ms mt :
  spec ps ms -> spec pt mt -> StateShape.spec ps -> spec (pair ps pt) (pair ms mt).
Proof.
intros Hs Ht Ss s0 s2 tr02.
unfold MemoryBound.
cbn in *.
destruct (seq_complete tr02) as [s1 tr01 tr12].
rewrite (MMR_seq tr01 tr12 tr02).
rewrite <- N.add_max_distr_l.
apply N.max_le_compat.
 apply Hs.
etransitivity;[apply Ht|].
apply N.add_le_mono_r.
apply (StateShape.StateSize Ss tr01).
Qed.

Lemma take_spec {A B C : Ty} (pt : Naive.Program_ty A C) mt :
 spec pt mt -> spec (take pt) (take (B:=B) mt).
Proof.
auto.
Qed.

Lemma drop_spec {A B C : Ty} (pt : Naive.Program_ty B C) mt :
 spec pt mt -> spec (drop pt) (drop (A:=A) mt).
Proof.
intros Ht x n Hp;cbn.
apply (bump_spec Ht Hp).
Qed.

Lemma Core_spec  {A B : Ty} (t : forall {alg : Core.Algebra}, alg A B) (Ht : Core.Parametric (@t)) :
  spec t t.
Proof.
pose (R A B (x : Naive.Program_ty A B) y := StateShape.spec x /\ spec x y).
cut (R A B (t _) (t _));[intros [spec1 spec2]; auto|]. 
refine (Ht _ _ (Core.Parametric.Pack (_ : Core.Parametric.class R))).
constructor; unfold R; intros; split.
- apply StateShape.iden_spec.
- apply iden_spec.
- apply StateShape.comp_spec; tauto.
- apply comp_spec; tauto.
- apply StateShape.unit_spec.
- apply unit_spec.
- apply StateShape.injl_spec; tauto.
- apply injl_spec; tauto.
- apply StateShape.injr_spec; tauto.
- apply injr_spec; tauto.
- apply StateShape.case_spec; tauto.
- apply case_spec; tauto.
- apply StateShape.pair_spec; tauto.
- apply pair_spec; tauto.
- apply StateShape.take_spec; tauto.
- apply take_spec; tauto.
- apply StateShape.drop_spec; tauto.
- apply drop_spec; tauto.
Qed.

Definition CellBound {A B : Ty} (t : bound_ty A B) : N := N.of_nat (bitSize A) + N.of_nat (bitSize B) + t.

Lemma CellBound_correct {A B : Ty} (t : forall {alg : Core.Algebra}, alg A B) (Ht : Core.Parametric (@t)) a y
  (tr : fillContext emptyCtx (Naive.LocalStateBegin t a) >>- @t Naive.translate ->> y) :
  maximumMemoryResidence (trace tr) <= CellBound t.
Proof.
etransitivity;[apply (Core_spec Ht tr)|].
unfold MemoryBound, CellBound, stateSize, stateShapeSize; cbn.
rewrite app_nil_r, encode_length, N.add_0_r, <- plus_n_O.
reflexivity.
Qed.

End MaximumMemory.

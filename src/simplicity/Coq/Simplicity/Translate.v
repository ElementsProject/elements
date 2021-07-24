Require Import PeanoNat.
Require Import Simplicity.Util.List.
Require Import Simplicity.Util.Thrist.

Require Import Simplicity.Alg.
Require Import Simplicity.BitMachine.
Require Import Simplicity.Ty.

Set Implicit Arguments.

Local Open Scope ty_scope.
Local Open Scope mc_scope.
Local Open Scope semantic_scope.

Fixpoint bitSize (X : Ty) : nat :=
match X with
| Unit => 0
| Sum A B => 1 + max (bitSize A) (bitSize B)
| Prod A B => bitSize A + bitSize B
end.

(* We take advantage that x - y = 0 when x <= y for natural numbers. *)
Definition padL (X Y : Ty) : nat := bitSize Y - bitSize X.
Definition padR (X Y : Ty) : nat := bitSize X - bitSize Y.

Lemma padL_bitSize (X Y : Ty) : (padL X Y + bitSize X = max (bitSize X) (bitSize Y))%nat.
Proof.
unfold padL.
apply Nat.max_case_strong; intros HXY.
- rewrite <- Nat.sub_0_le in HXY.
  rewrite HXY.
  reflexivity.
- rewrite Nat.sub_add; auto.
Qed.

Lemma padR_bitSize (X Y : Ty) : (padR X Y + bitSize Y = max (bitSize X) (bitSize Y))%nat.
Proof.
unfold padR.
apply Nat.max_case_strong; intros HXY.
- rewrite Nat.sub_add; auto.
- rewrite <- Nat.sub_0_le in HXY.
  rewrite HXY.
  reflexivity.
Qed.

Fixpoint encode {X : Ty} : X -> list Cell :=
match X with
| Unit => fun _ => nil
| Sum A B => fun ab =>
  match ab with
  | inl a => Some false :: repeat None (padL A B) ++ encode a
  | inr b => Some true  :: repeat None (padR A B) ++ encode b
  end
| Prod A B => fun ab =>
  let (a, b) := ab in encode a ++ encode b
end.

Lemma encode_length {X : Ty} : forall x : X, length (encode x) = bitSize X.
Proof.
induction X.
- reflexivity.
- intros [a|b]; cbn; rewrite app_length, repeat_length;
  [rewrite IHX1, padL_bitSize | rewrite IHX2, padR_bitSize];
  reflexivity.
- intros [a b]; cbn.
  rewrite app_length, IHX1, IHX2.
  reflexivity.
Qed.

Module Naive.

Definition Program_ty (A B : Ty) := Program.

Definition translate_class : Core.class Program_ty :=
  {| Core.iden A := copy (bitSize A)
   ; Core.comp A B C ps pt := newFrame (bitSize B) ;;; ps ;;; moveFrame ;;; pt ;;; dropFrame
   ; Core.unit A := nop
   ; Core.injl A B C pt := write false ;;; skip (padL B C) ;;; pt
   ; Core.injr A B C pt := write true ;;; skip (padR B C) ;;; pt
   ; Core.case A B C D ps pt := bump (1 + padL A B) ps ||| bump (1 + padR A B) pt
   ; Core.pair A B C ps pt := ps ;;; pt
   ; Core.take A B C pt := pt
   ; Core.drop A B C pt := bump (bitSize A) pt
   |}.

Canonical Structure translate : Core.Algebra := Core.Pack Program_ty translate_class.

Definition LocalStateBegin {A B : Ty} (t : Arrow A B) (a : A) :=
  {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |}.

Definition LocalStateEnd {A B : Ty} (t : Arrow A B) (a : A) :=
  {| readLocalState := encode a; writeLocalState := fullWriteFrame (encode (t a)) |}.

Definition spec {A B : Ty} (p : Program_ty A B) (t : Arrow A B)  :=
  forall a ctx, fillContext ctx (LocalStateBegin t a) >>- p ->> fillContext ctx (LocalStateEnd t a).

Lemma iden_spec {A : Ty} : spec (A:=A) iden iden.
Proof.
intros a ctx; cbn.
unfold LocalStateBegin, LocalStateEnd.
rewrite <- (encode_length a).
apply copy_correct.
Qed.

Lemma comp_spec {A B C : Ty} (s : Arrow A B) (t : Arrow B C) ps pt :
 spec ps s -> spec pt t ->
 spec (comp ps pt) (comp s t) .
Proof.
intros Hs Ht a ctx.
unfold LocalStateBegin, LocalStateEnd.
destruct ctx as [irf arf awf iwf].
repeat eapply seq_correct.
- apply newFrame_correct.
- cbn.
  pose (ctx0 := {| inactiveReadFrames := irf
                 ; activeReadFrame := arf
                 ; activeWriteFrame := newWriteFrame 0
                 ; inactiveWriteFrames :=
                   {| writeData := writeData awf
                    ; writeEmpty := bitSize C + writeEmpty awf
                    |} :: iwf
                 |}).
  rewrite (plus_n_O (bitSize B)).
  apply (Hs a ctx0).
- unfold fillContext; cbn.
  rewrite app_nil_r.
  apply moveFrame_correct.
- cbn.
  pose (ctx0 := {| inactiveReadFrames := {| prevData := prevData arf; nextData := encode a ++ nextData arf |} :: irf
                 ; activeReadFrame := setFrame nil
                 ; activeWriteFrame := awf
                 ; inactiveWriteFrames := iwf
                 |}).
  rewrite <- (app_nil_r (encode (s a))).
  apply (Ht (s a) ctx0).
- unfold fillContext; cbn.
  rewrite app_nil_r.
  apply dropFrame_correct.
Qed.

Lemma unit_spec {A : Ty} : spec (A:=A) unit unit.
Proof.
intros a ctx.
apply nop_correct.
Qed.

Lemma injl_spec {A B C : Ty} (t : Arrow A B) pt :
 spec pt t ->
 spec (injl pt) (injl (C:=C) t).
Proof.
intros Ht a ctx.
repeat eapply seq_correct.
- pose (ls1 := {| readLocalState := encode a; writeLocalState := newWriteFrame (max (bitSize B) (bitSize C)) |}).
  pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame 1 |}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
  rewrite <- context_action.
  apply write_correct.
- rewrite context_action.
  unfold appendLocalState; cbn.
  rewrite <- padL_bitSize.
  pose (ls1 := {| readLocalState := encode a; writeLocalState := {| writeData := Some false :: nil; writeEmpty := bitSize B |}|}).
  pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame (padL B C)|}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
  rewrite <- context_action.
  apply skip_correct.
- rewrite context_action.
  unfold appendLocalState; cbn.
  rewrite <- (app_nil_r (encode a)), <- (Plus.plus_0_r (bitSize B)).
  pose (ls1 := {| readLocalState := nil; writeLocalState := fullWriteFrame (Some false :: repeat None (padL B C))|}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
  unfold LocalStateEnd, fullWriteFrame; cbn.
  rewrite <- (app_nil_r (encode a)), rev_app_distr, <- app_assoc.
  change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState ls1 (LocalStateEnd t a))).
  do 2 rewrite <- context_action.
  apply Ht.
Qed.

Lemma injr_spec {A B C : Ty} (t : Arrow A C) pt :
 spec pt t ->
 spec (injr pt) (injr (B:=B) t).
Proof.
intros Ht a ctx.
repeat eapply seq_correct.
- pose (ls1 := {| readLocalState := encode a; writeLocalState := newWriteFrame (max (bitSize B) (bitSize C)) |}).
  pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame 1 |}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
  rewrite <- context_action.
  apply write_correct.
- rewrite context_action.
  unfold appendLocalState; cbn.
  rewrite <- padR_bitSize.
  pose (ls1 := {| readLocalState := encode a; writeLocalState := {| writeData := Some true :: nil; writeEmpty := bitSize C |}|}).
  pose (ls2 := {| readLocalState := nil; writeLocalState := newWriteFrame (padR B C)|}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 ls2)).
  rewrite <- context_action.
  apply skip_correct.
- rewrite context_action.
  unfold appendLocalState; cbn.
  rewrite <- (app_nil_r (encode a)), <- (Plus.plus_0_r (bitSize C)).
  pose (ls1 := {| readLocalState := nil; writeLocalState := fullWriteFrame (Some true :: repeat None (padR B C))|}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
  unfold LocalStateEnd, fullWriteFrame; cbn.
  rewrite <- (app_nil_r (encode a)), rev_app_distr, <- app_assoc.
  change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState ls1 (LocalStateEnd t a))).
  do 2 rewrite <- context_action.
  apply Ht.
Qed.

Lemma caseL_spec {A B C D : Ty} (s : Arrow (A * C) D) (t : Arrow (B * C) D) ps pt :
 spec ps s ->
 forall (a : A) (c : C) ctx,
  fillContext ctx (LocalStateBegin (case s t) (inl a, c))
   >>- bump (1 + padL A B) ps ||| bump (1 + padR A B) pt ->>
  fillContext ctx (LocalStateEnd (case s t) (inl a, c)).
Proof.
intros Hs a c ctx.
apply choice_left_correct;[reflexivity|].
unfold LocalStateBegin, LocalStateEnd; cbn.
rewrite <- app_assoc.
rewrite <- (@repeat_length Cell None (padL A B)) at 1.
set (prefix := Some false :: repeat None (padL A B)).
pose (ls2 := {| readLocalState := prefix; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState (LocalStateBegin s (a,c)) ls2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState (LocalStateEnd s (a,c)) ls2)).
repeat rewrite <- context_action.
change (fillContext _ _) at 1 with (fillReadFrame (fillContext ctx (LocalStateBegin s (a,c))) {| prevData := nil; nextData := prefix |}).
change (fillContext _ _) at 2 with (fillReadFrame (fillContext ctx (LocalStateEnd s (a,c))) {| prevData := nil; nextData := prefix |}).
apply bump_correct.
apply (Hs _ (fillReadFrame ctx {| prevData := rev (prefix); nextData := nil |})).
Qed.

Lemma caseR_spec {A B C D : Ty} (s : Arrow (A * C) D) (t : Arrow (B * C) D) ps pt :
 spec pt t ->
 forall (b : B) (c : C) ctx,
  fillContext ctx (LocalStateBegin (case s t) (inr b, c))
   >>- bump (1 + padL A B) ps ||| bump (1 + padR A B) pt ->>
  fillContext ctx (LocalStateEnd (case s t) (inr b, c)).
Proof.
intros Ht b c ctx.
apply choice_right_correct;[reflexivity|].
unfold LocalStateBegin, LocalStateEnd; cbn.
rewrite <- app_assoc.
rewrite <- (@repeat_length Cell None (padR A B)) at 1.
set (prefix := Some true :: repeat None (padR A B)).
pose (ls2 := {| readLocalState := prefix; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState (LocalStateBegin t (b,c)) ls2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState (LocalStateEnd t (b,c)) ls2)).
repeat rewrite <- context_action.
change (fillContext _ _) at 1 with (fillReadFrame (fillContext ctx (LocalStateBegin t (b,c))) {| prevData := nil; nextData := prefix |}).
change (fillContext _ _) at 2 with (fillReadFrame (fillContext ctx (LocalStateEnd t (b,c))) {| prevData := nil; nextData := prefix |}).
apply bump_correct.
apply (Ht _ (fillReadFrame ctx {| prevData := rev (prefix); nextData := nil |})).
Qed.

Lemma case_spec {A B C D : Ty} (s : Arrow (A * C) D) (t : Arrow (B * C) D) ps pt :
 spec ps s -> spec pt t ->
 spec (case ps pt) (case s t).
Proof.
intros Hs Ht [[a|b] c] ctx.
- apply caseL_spec; assumption.
- apply caseR_spec; assumption.
Qed.

Lemma pair_spec {A B C : Ty} (s : Arrow A B) (t : Arrow A C) ps pt :
 spec ps s -> spec pt t ->
 spec (pair ps pt) (pair s t).
Proof.
intros Hs Ht a ctx.
unfold LocalStateBegin, LocalStateEnd.
eapply seq_correct.
- rewrite <- (app_nil_r (encode a)) at 1.
  pose (ls1 := {| readLocalState := nil; writeLocalState := newWriteFrame (bitSize C) |}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin s a))).
  rewrite <- context_action.
  apply Hs.
- rewrite context_action.
  unfold appendLocalState, fullWriteFrame; cbn.
  rewrite (app_nil_r (rev _)), <- (Plus.plus_0_r (bitSize C)), rev_app_distr.
  rewrite <- (app_nil_r (encode a)) at 2.
  pose (ls1 := {| readLocalState := nil; writeLocalState := fullWriteFrame (encode (s a)) |}).
  change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
  change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState ls1 (LocalStateEnd t a))).
  do 2 rewrite <- context_action.
  apply Ht.
Qed.

Lemma take_spec {A B C : Ty} (t : Arrow A C) pt :
 spec pt t ->
 spec (take pt) (take (B:=B) t).
Proof.
intros Ht [a b] ctx.
unfold LocalStateBegin, LocalStateEnd, fullWriteFrame; cbn.
rewrite <- (Plus.plus_0_r (bitSize C)), <- (app_nil_r (rev _)).
pose (ls1 := {| readLocalState := encode b; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState ls1 (LocalStateBegin t a))).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState ls1 (LocalStateEnd t a))).
do 2 rewrite <- context_action.
apply Ht.
Qed.

Lemma drop_spec {A B C : Ty} (t : Arrow B C) pt :
 spec pt t ->
 spec (drop pt) (drop (A:=A) t).
Proof.
intros Ht [a b] ctx; cbn.
pose (ls2 := {| readLocalState := encode a; writeLocalState := newWriteFrame 0 |}).
change (fillContext _ _) at 1 with (fillContext ctx (appendLocalState (LocalStateBegin t b) ls2)).
change (fillContext _ _) at 2 with (fillContext ctx (appendLocalState (LocalStateEnd t b) ls2)).
repeat rewrite <- context_action.
change (fillContext _ _) at 1 with (fillReadFrame (fillContext ctx (LocalStateBegin t b)) {| prevData := nil; nextData := encode a |}).
change (fillContext _ _) at 2 with (fillReadFrame (fillContext ctx (LocalStateEnd t b)) {| prevData := nil; nextData := encode a |}).
rewrite <- (encode_length a).
apply bump_correct.
apply (Ht _ (fillReadFrame ctx {| prevData := rev (encode a); nextData := nil |})).
Qed.

Theorem translate_correct {A B : Ty} (t : forall {alg : Core.Algebra}, alg A B) (Ht : Core.Parametric (@t)) :
 forall a ctx,
 fillContext ctx {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |}
  >>- @t translate ->>
 fillContext ctx {| readLocalState := encode a; writeLocalState := fullWriteFrame (encode (|[ t ]| a)) |}.
refine (Ht _ _ (Core.Parametric.Pack (_ : Core.Parametric.class (@spec)))).
constructor; clear; intros.
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

End Naive.
Canonical Structure Naive.translate.

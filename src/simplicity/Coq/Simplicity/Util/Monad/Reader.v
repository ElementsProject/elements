Require Import Logic.FunctionalExtensionality.

Require Import Simplicity.Util.Monad.
Local Open Scope monad_scope.

Definition ReaderT E (M : Type -> Type) A := E -> M A.

Section ReaderT_CIMonad.

Variable E : Type.
Variable M : CIMonad.

Definition ReaderT_eta A (a : A) : ReaderT E M A :=
fun _ => eta a.

Definition ReaderT_bind A B (f : A -> ReaderT E M B) (x : ReaderT E M A) :
  ReaderT E M B :=
fun e => bind (fun a => f a e) (x e).

Definition ReaderT_CIMonad_class : CIMonad.class (ReaderT E M).
exists ReaderT_eta ReaderT_bind.
- abstract (
  intros A B f0 f1 Hf a;
  extensionality e;
  unfold ReaderT_bind; rewrite !bind_def;
  apply f_equal;
  apply map_ext; intros a0;
  rewrite Hf;
  reflexivity).
- abstract (
  intros A x;
  extensionality e;
  unfold ReaderT_bind; rewrite bind_def, <- kleisli_comp_def;
  apply kleisli_compl).
- abstract (
  intros A B f a;
  extensionality e;
  unfold ReaderT_bind; rewrite bind_def;
  unfold ReaderT_eta; rewrite <- kleisli_comp_def, kleisli_compr;
  reflexivity).
- abstract (
  intros A B C g f x;
  extensionality e;
  unfold ReaderT_bind; rewrite !bind_def;
  rewrite <- (kleisli_comp_def (fun a : A => f a e)), <- kleisli_comp_def;
  rewrite <- kleisli_comp_assoc, !kleisli_comp_def;
  reflexivity).
- abstract (
  intros A B [x y];
  extensionality e;
  unfold ReaderT_bind, ReaderT_eta; cbn;
  rewrite !bind_def;
  repeat (rewrite <- map_comp, <- (kleisli_comp_def eta), kleisli_compl);
  pose (f0 (p : A * M B) := bind (fun b => eta (fst p, b)) (snd p));
  rewrite <- (map_comp f0 (fun p => (fst p, snd p e)));
  rewrite (map_comp (fun p => (fst p, snd p e)) ((fun a : A => (a, y)))); cbn;
  pose (f1 (p : M A * B) := bind (fun a => eta (a, snd p)) (fst p));
  rewrite <- (map_comp f1 (fun p => (fst p e, snd p)));
  rewrite (map_comp (fun p => (fst p e, snd p)) (pair x)); cbn;
  rewrite (map_ext _ strength) by
   (intros [a y0]; unfold f0; rewrite bind_def;
    rewrite <- map_comp, <- (kleisli_comp_def eta), kleisli_compl;
    reflexivity);
  rewrite (map_ext _ strength') by
   (intros [a y0]; unfold f1; rewrite bind_def;
    rewrite <- map_comp, <- (kleisli_comp_def eta), kleisli_compl;
    reflexivity);
  rewrite <- !kleisli_comp_def;
  apply phi_phi').
- abstract (
  intros A x;
  extensionality e;
  unfold ReaderT_bind, ReaderT_eta; cbn;
  rewrite !bind_def;
  repeat (rewrite <- map_comp, <- (kleisli_comp_def eta), kleisli_compl);
  pose (f0 (p : A * M A) := bind (fun b => eta (fst p, b)) (snd p));
  rewrite <- (map_comp f0 (fun p => (fst p, snd p e)));
  rewrite (map_comp (fun p => (fst p, snd p e)) ((fun a : A => (a, x)))); cbn;
  rewrite (map_ext _ strength) by
   (intros [a y0]; unfold f0; rewrite bind_def;
    rewrite <- map_comp, <- (kleisli_comp_def eta), kleisli_compl;
    reflexivity);
  rewrite <- kleisli_comp_def;
  apply phi_diag).
Defined.

End ReaderT_CIMonad.
Canonical Structure ReaderT_CIMonad E (M : CIMonad) :=
  CIMonad.Pack (ReaderT E M) (ReaderT_CIMonad_class E M).

Section ReaderT_CIMonadZero.

Variable E : Type.
Variable M : CIMonadZero.

Definition ReaderT_mzero A : ReaderT E M A := fun _ => mzero.

Definition ReaderT_MonadZero_mixin : MonadZero.mixin (ReaderT_CIMonad E M).
exists ReaderT_mzero.
- abstract (
  intros A B f;
  extensionality e;
  change (map f mzero = mzero :> M B);
  apply mzero_natural).
- abstract (
  intros A B C f a;
  extensionality e;
  change ((kzero <-< (fun a => f a e)) a = kzero a :> M C);
  apply kleisli_comp_zerol).
- abstract (
  intros A B C f a;
  extensionality e;
  change (((fun b => f b e) <-< kzero) a = kzero a :> M C);
  apply kleisli_comp_zeror).
Defined.

End ReaderT_CIMonadZero.
Canonical Structure ReaderT_CIMonadZero E (M : CIMonadZero) :=
  MonadZero.Pack (ReaderT E M) (ReaderT_MonadZero_mixin E M).

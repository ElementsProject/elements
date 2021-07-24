Require Import Simplicity.Util.Monad.

Set Implicit Arguments.

Local Open Scope monad_scope.

Definition option_join {A} (x : option (option A)) : option A :=
match x with
| None => None
| Some x => x
end.

Definition option_bind {A B} (f : A -> option B) (x : option A) : option B :=
option_join (option_map f x).

Lemma option_bind_ext {A B} (f1 f2 : A -> option B) :
  (forall a, f1 a = f2 a) -> forall x, option_bind f1 x = option_bind f2 x.
Proof.
intros H [|];[apply H|reflexivity].
Qed.

Definition option_CIMonad_class : CIMonad.class option.
exists @Some @option_bind; try abstract (intros; try destruct x; try reflexivity).
- abstract (auto using option_bind_ext).
- abstract (intros; destruct p as [[|] [|]]; reflexivity).
Defined.

Canonical Structure option_CIMonad := CIMonad.Pack option option_CIMonad_class.

Definition option_MonadZero_mixin : MonadZero.mixin option_CIMonad.
exists @None; try abstract (intros; try reflexivity).
abstract (intros; unfold kleisliComp; cbn; destruct (f a); reflexivity).
Defined.

Canonical Structure option_Monad_Zero := MonadZero.Pack option option_MonadZero_mixin.

Definition optionZero {M : CIMonadZero} {A} (x : option A) : M A :=
match x with
| None => mzero
| Some a => eta a
end.

Lemma optionZero_natural {M :CIMonadZero} {A B} (f : A -> B) x :
  map f (optionZero x) = optionZero (map f x) :> M B.
Proof.
destruct x; cbn.
- apply eta_natural.
- apply mzero_natural.
Qed.

Lemma optionZero_mu {M :CIMonadZero} {A} x :
  optionZero (mu x) = mu (map optionZero (optionZero x)) :> M A.
Proof.
destruct x as [x|]; cbn.
- rewrite <- kleisli_comp_def, kleisli_compr.
  reflexivity.
- rewrite mzero_natural.
  symmetry.
  apply mu_mzero.
Qed.

Lemma optionZero_phi {M :CIMonadZero} {A B} x y :
  optionZero (phi x y) = phi (optionZero x) (optionZero y) :> M (A * B)%type.
Proof.
destruct x as [a|]; destruct y as [b|]; cbn; try reflexivity;
first [rewrite phi_eta|rewrite phi_mzerol|rewrite phi_mzeror];
reflexivity.
Qed.

(* TODO: move these into CIMonad when needed.
Definition option_ap {A B} (f : option (A -> B)) : option A -> option B :=
option_bind (fun a => option_map (fun f => f a) f).

Definition option_map2 {A B C} (f : A -> B -> C) (x : option A) : option B -> option C :=
option_ap (option_map f x).
*)

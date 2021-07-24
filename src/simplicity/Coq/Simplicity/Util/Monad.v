Require Import Simplicity.Util.PackedClass.
Import Coq.Strings.String.StringSyntax.

Set Implicit Arguments.

Local Open Scope type_scope.
Declare Scope monad_scope.

(* Commutative and Idempotnent Monads *)
Module CIMonad.

(* Eventually we will need the functional extensionality axoim, but let's try
 * to delay that as long as possible.  The alternative is to use Setoid / PERs
 * but that would seem to entail writing an entirely new standard library.
 *)
Record class (M : Type -> Type) := Class
{ eta : forall {A}, A -> M A
; bind : forall {A B}, (A -> M B) -> M A -> M B
; map := (fun A B f => bind (fun a => eta (f a))) : forall {A B}, (A -> B) -> M A -> M B
; kleisliComp := (fun A B C g f a => bind g (f a)) : forall {A B C}, (B -> M C) -> (A -> M B) -> A -> M C
; strength := (fun A B p => map (pair (fst p)) (snd p)) : forall {A B}, A * M B -> M (A * B)
; strength' := (fun A B p => map (fun a => pair a (snd p)) (fst p)) : forall {A B}, M A * B -> M (A * B)
; _ : forall {A B} (f0 f1: A -> M B), (forall a, f0 a = f1 a) -> forall a, bind f0 a = bind f1 a
; _ : forall {A} (x : M A), bind eta x = x
; _ : forall {A B} (f : A -> M B) (a : A), bind f (eta a) = f a
; _ : forall {A B C} (g : B -> M C) (f : A -> M B) (x : M A),
        bind g (bind f x) = bind (fun a => bind g (f a)) x
; _ : forall {A B} (p : M A * M B), kleisliComp strength strength' p = kleisliComp strength' strength p
; _ : forall {A} (x : M A), kleisliComp strength strength' (pair x x) = map (fun a => pair a a) x
}.

Structure type := Pack { domain :> Type -> Type; class_of : class domain }.
Arguments Pack : clear implicits.

Module Theory.

Section Context.

Context {M : type}.

Definition eta {A} (a : A) := eta (class_of M) a.
Definition bind {A B} (f : A -> M B) := bind (class_of M) f.
Definition map {A B} (f : A -> B) := map (class_of M) f.
Definition kleisliComp {A B C} (g : B -> M C) (f : A -> M B) :=
  kleisliComp (class_of M) g f.
Definition strength {A B} (p : A * M B) := strength (class_of M) p.
Definition strength' {A B} (p : M A * B) := strength' (class_of M) p.
Definition mu {A} (x : M (M A)) : M A := bind (fun y => y) x.

Infix "<-<" := kleisliComp (at level 40, left associativity).

Definition phi {A B} (x : M A) (y : M B) : M (A * B) := (strength <-< strength') (pair x y).
Definition phi' {A B} (x : M A) (y : M B) : M (A * B) := (strength' <-< strength) (pair x y).

Lemma bind_def {A B} (f : A -> M B) (x : M A) :
  bind f x = mu (map f x).
Proof.
unfold mu, map.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
rewrite bind_assoc.
apply bind_ext; intros a.
rewrite bind_right.
reflexivity.
Qed.

Lemma kleisli_comp_def {A B C} (g : B -> M C) (f : A -> M B) (a : A) :
  (g <-< f) a = mu (map g (f a)).
Proof.
apply bind_def.
Qed.

Lemma kleisli_compl {A B} (f : A -> M B) (a : A) :
  (eta <-< f) a = f a.
Proof.
unfold kleisliComp.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_left.
Qed.

Lemma kleisli_compr {A B} (f : A -> M B) (a : A) :
  (f <-< eta) a = f a.
Proof.
unfold kleisliComp.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma kleisli_comp_assoc {A B C D}
  (h : C -> M D) (g : B -> M C) (f : A -> M B) (a : A) :
  ((h <-< g) <-< f) a = (h <-< (g <-< f)) a.
Proof.
unfold kleisliComp.
unfold bind, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
erewrite (bind_assoc _ _ _ h g);reflexivity.
Qed.

Lemma eta_natural {A B} (f : A -> B) (a : A) :
  map f (eta a) = eta (f a).
Proof.
unfold map, eta; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma mu_natural {A B} (f : A -> B) (x : M (M A)) :
  map f (mu x) = mu (map (map f) x).
Proof.
unfold map, mu, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
repeat rewrite bind_assoc.
apply bind_ext; intros y.
rewrite bind_right.
reflexivity.
Qed.

Lemma map_ext {A B} (f0 f1 : A -> B) (Hf : forall a, f0 a = f1 a) (x : M A) :
  map f0 x = map f1 x.
Proof.
unfold map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_ext.
congruence.
Qed.

Lemma map_comp {A B C} (g : B -> C) (f : A -> B) (x : M A) : map g (map f x) = map (fun a => g (f a)) x.
Proof.
unfold map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
rewrite bind_assoc.
apply bind_ext.
intros.
apply bind_right.
Qed.

Lemma strength_eta {A B} (a : A) (b : B) : strength (a, eta b) = eta (a, b).
Proof.
unfold strength, eta, map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma strength'_eta {A B} (a : A) (b : B) : strength' (eta a, b) = eta (a, b).
Proof.
unfold strength', eta, map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply bind_right.
Qed.

Lemma phi_eta {A B} (a : A) (b : B) : phi (eta a) (eta b) = eta (a, b).
Proof.
unfold phi.
rewrite kleisli_comp_def, strength'_eta, <- kleisli_comp_def.
rewrite kleisli_compr.
apply strength_eta.
Qed.

Lemma phi_phi' {A B} (a : M A) (b : M B) : phi a b = phi' a b.
Proof.
unfold phi, phi', kleisliComp, strength, strength', eta, map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply (comm _ _ (a,b)).
Qed.

Lemma phi_diag {A} (a : M A) : phi a a = map (fun x => (x,x)) a.
Proof.
unfold phi, kleisliComp, strength, strength', eta, map, bind; destruct (class_of M) as [eta0 bind0 map0 kleisliComp0 strength0 strength'0 bind_ext bind_left bind_right bind_assoc comm idem]; cbn.
apply (idem _ a).
Qed.

End Context.
End Theory.
End CIMonad.
Export CIMonad.Theory.
Notation CIMonad := CIMonad.type.
Coercion CIMonad.domain : CIMonad >-> Funclass.
Infix "<-<" := kleisliComp (at level 40, left associativity) : monad_scope.
Arguments kleisliComp {M A B C} g f : simpl never.
Arguments map {M A B} f : simpl never.
Local Open Scope monad_scope.

Definition Identity (A : Type) : Type := A.

Definition Identity_CIMonad_class : CIMonad.class Identity.
exists (fun A a => a) (fun A B f => f); auto.
Defined.

Canonical Structure Identity_CIMonad := CIMonad.Pack Identity Identity_CIMonad_class.

(* Monad with zero *)
Module MonadZero.

Record mixin (M : CIMonad) := Mixin
{ mzero : forall {A}, M A
; kzero := (fun A B a => mzero) : forall {A B}, A -> M B
; _ : forall {A B} (f : A -> B), map f mzero = mzero
; _ : forall {A B C} (f : A -> M B) (a : A), (kzero <-< f) a = kzero a :> M C
; _ : forall {A B C} (f : B -> M C) (a : A), (f <-< kzero) a = kzero a
}.

Record class (M : Type -> Type) := Class
{ base :> CIMonad.class M
; ext :> mixin (CIMonad.Pack M base)
}.

Structure type := _Pack { domain :> Type -> Type; class_of : class domain }.

Definition packager F M0 (mz0 : mixin M0) :=
 [find M  | CIMonad.domain M ~ F | "is not a CIMonad" ]
 [find cM | CIMonad.class_of M0 ~ cM ]
 [find mz | mz ~ mz0 | "is not the right mixin" ]
 @_Pack F (@Class F cM mz).

Notation Pack F mz := (@packager F _ mz _ id _ id _ id).  

Canonical Structure to_Monad (M : type) : CIMonad := CIMonad.Pack M (class_of M).

Module Theory.

Section Context.

Context {M : type}.

Definition mzero {A} := mzero (class_of M) : M A.
Definition kzero {A B} := kzero (class_of M) : A -> M B.

Lemma mzero_natural {A B} (f : A -> B) :
  map f mzero = mzero.
Proof.
unfold mzero; destruct M as [M0 [Monad_class0 [mzero0 kzero natural kzerol kzeror]]]; cbn.
apply natural.
Qed.

Lemma kleisli_comp_zerol {A B C} (f : A -> M B) (a : A) :
  (kzero <-< f) a = kzero a :> M C.
Proof.
unfold kzero; destruct M as [M0 [Monad_class0 [mzero0 kzero natural kzerol kzeror]]]; cbn.
apply kzerol.
Qed.

Lemma kleisli_comp_zeror {A B C} (f : B -> M C) (a : A) :
  (f <-< kzero) a = kzero a.
Proof.
unfold kzero; destruct M as [M0 [Monad_class0 [mzero0 kzero natural kzerol kzeror]]]; cbn.
apply kzeror.
Qed.

Lemma mu_mzero {A} : mu mzero = mzero :> M A.
Proof.
cbn; change (@mzero (M A)) with (@kzero (M A) (M A) mzero).
unfold mu.
rewrite bind_def, <- kleisli_comp_def.
rewrite kleisli_comp_zeror; reflexivity.
Qed.

Lemma mu_eta_mzero {A} : mu (eta mzero) = mzero :> M A.
Proof.
cbn; change (@mzero A) with (@kzero (M A) A mzero).
unfold mu.
rewrite bind_def, <- kleisli_comp_def.
rewrite kleisli_compr; reflexivity.
Qed.

Lemma phi_mzeror {A B} (x : M B) : phi mzero x = mzero :> M (A * B).
Proof.
unfold phi.
rewrite kleisli_comp_def.
change (mu (map strength (map (fun a => pair a x) mzero)) = mzero :> M (A * B)).
repeat rewrite mzero_natural.
apply mu_mzero.
Qed.

Lemma phi_mzerol {A B} (x : M A) : phi x mzero = mzero :> M (A * B).
Proof.
unfold phi.
rewrite kleisli_comp_def.
change (mu (map strength (map (fun a => pair a mzero) x)) = mzero :> M (A * B)).
rewrite map_comp.
erewrite map_ext;[|intros; apply mzero_natural].
change x with ((fun y => y) x).
rewrite <- kleisli_comp_def.
apply kleisli_comp_zerol.
Qed.

End Context.
End Theory.
End MonadZero.
Notation CIMonadZero := MonadZero.type.
Canonical Structure MonadZero.to_Monad.
Coercion MonadZero.to_Monad : CIMonadZero >-> CIMonad.
Export MonadZero.Theory.

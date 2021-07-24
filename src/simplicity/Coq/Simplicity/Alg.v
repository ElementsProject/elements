Require Import Simplicity.Util.Monad.
Require Import Simplicity.Util.Option.
Require Import Simplicity.Util.PackedClass.
Import Coq.Strings.String.StringSyntax.

Require Import Simplicity.Ty.
Require Import Simplicity.Digest.
Require Simplicity.Core.

Set Implicit Arguments.
Local Open Scope ty_scope.
Local Open Scope monad_scope.
Declare Scope term_scope.
Declare Scope semantic_scope.

Module Core.

Record class (term : Ty -> Ty -> Type) := Class
{ iden : forall {A}, term A A
; comp : forall {A B C}, term A B -> term B C -> term A C
; unit : forall {A}, term A Unit
; injl : forall {A B C}, term A B -> term A (B + C)
; injr : forall {A B C}, term A C -> term A (B + C)
; case : forall {A B C D}, term (A * C) D -> term (B * C) D -> term ((A + B) * C) D
; pair : forall {A B C}, term A B -> term A C -> term A (B * C)
; take : forall {A B C}, term A C -> term (A * B) C
; drop : forall {A B C}, term B C -> term (A * B) C
}.

Structure Algebra := Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.
Arguments Pack : clear implicits.

Module Combinators.

Definition iden {A} {alg : Algebra} : alg A A := iden (class_of alg).
Definition comp {A B C} {alg : Algebra} : alg A B -> alg B C -> alg A C := comp (class_of alg).
Definition unit {A} {alg : Algebra} : alg A Unit := unit (class_of alg).
Definition injl {A B C} {alg : Algebra} : alg A B -> alg A (B + C) := injl (class_of alg).
Definition injr {A B C} {alg : Algebra} : alg A C -> alg A (B + C) := injr (class_of alg).
Definition case {A B C D} {alg : Algebra} : alg (A * C) D -> alg (B * C) D -> alg ((A + B) * C) D := case (class_of alg).
Definition pair {A B C} {alg : Algebra} : alg A B -> alg A C -> alg A (B * C) := pair (class_of alg).
Definition take {A B C} {alg : Algebra} : alg A C -> alg (A * B) C := take (class_of alg).
Definition drop {A B C} {alg : Algebra} : alg B C -> alg (A * B) C := drop (class_of alg).

Definition elimS {A B C D} {alg : Algebra} (r : alg A (B + C)) (s : alg B D) (t : alg C D) : alg A D :=
  comp (pair r unit) (case (take s) (take t)).
Definition copair {A B C} {alg : Algebra} : alg A C -> alg B C -> alg (A + B) C :=
  elimS iden.
Definition swapS {A B} {alg : Algebra} : alg (A + B) (B + A) :=
  copair (injr iden) (injl iden).
Definition swapP {A B} {alg : Algebra} : alg (A * B) (B * A) :=
  pair (drop iden) (take iden).

Notation "s &&& t" := (pair s t) (at level 70, right associativity) : term_scope.
Notation "s >>> t" := (comp s t) (at level 90, right associativity) : term_scope.

Notation "'H'" := iden : term_scope.
Notation "'O' x" := (take x) (at level 0, right associativity) : term_scope.
Notation "'I' x" := (drop x) (at level 0, right associativity) : term_scope.

End Combinators.

Module Parametric.
Import Combinators.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A, rel iden (@iden A _)
 ; _ : forall A B C s1 s2 t1 t2 (Hs : rel s1 s2) (Ht : rel t1 t2), rel (comp s1 t1) (@comp A B C _ s2 t2)
 ; _ : forall A, rel unit (@unit A _)
 ; _ : forall A B C t1 t2 (Ht : rel t1 t2), rel (injl t1) (@injl A B C _ t2)
 ; _ : forall A B C t1 t2 (Ht : rel t1 t2), rel (injr t1) (@injr A B C _ t2)
 ; _ : forall A B C D s1 s2 t1 t2 (Hs : rel s1 s2) (Ht : rel t1 t2), rel (case s1 t1) (@case A B C D _ s2 t2)
 ; _ : forall A B C s1 s2 t1 t2 (Hs : rel s1 s2) (Ht : rel t1 t2), rel (pair s1 t1) (@pair A B C _ s2 t2)
 ; _ : forall A B C t1 t2 (Ht : rel t1 t2), rel (take t1) (@take A B C _ t2)
 ; _ : forall A B C t1 t2 (Ht : rel t1 t2), rel (drop t1) (@drop A B C _ t2)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall {alg : Algebra}, alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B x y.

Definition Parametric {A B} (x : forall {alg : Algebra}, alg A B) : Prop := Reynolds (@x) (@x).
End Reynolds.

Section CoreTerm.
Import Combinators.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Fixpoint eval {A B} (x : Simplicity.Core.Term A B) {alg : Algebra} : alg A B :=
match x in Simplicity.Core.Term A B return alg A B with
| Simplicity.Core.iden => iden
| Simplicity.Core.comp s t => comp (eval s) (eval t)
| Simplicity.Core.unit => unit
| Simplicity.Core.injl t => injl (eval t)
| Simplicity.Core.injr t => injr (eval t)
| Simplicity.Core.case s t => case (eval s) (eval t)
| Simplicity.Core.pair s t => pair (eval s) (eval t)
| Simplicity.Core.take t => take (eval t)
| Simplicity.Core.drop t => drop (eval t)
end.

Lemma eval_Parametric {A B} (x : Simplicity.Core.Term A B) : Parametric (@eval A B x).
Proof.
intros alg1 alg2 [R []].
induction x; simpl; auto.
Qed.

Definition Term_mixin : class Simplicity.Core.Term :=
  {| Core.iden := @Simplicity.Core.iden
   ; Core.comp := @Simplicity.Core.comp
   ; Core.unit := @Simplicity.Core.unit
   ; Core.injl := @Simplicity.Core.injl
   ; Core.injr := @Simplicity.Core.injr
   ; Core.case := @Simplicity.Core.case
   ; Core.pair := @Simplicity.Core.pair
   ; Core.take := @Simplicity.Core.take
   ; Core.drop := @Simplicity.Core.drop
   |}.

Canonical Structure Term : Algebra := Pack Simplicity.Core.Term Term_mixin.

Lemma eval_Term {A B} (x : Simplicity.Core.Term A B) : eval x = x.
Proof.
induction x; cbn; congruence.
Qed.

Lemma term_eval {A B} (x : forall alg : Algebra, alg A B) (Hx : Parametric x) (alg : Algebra) :
  x alg = eval (x Term).
Proof.
refine (Hx _ _ (@Parametric.Pack Term alg (fun a b x y => y = eval x) _)); constructor;
intros; simpl; congruence.
Qed.

End CoreTerm.

End Core.
Export Core.Combinators.
Coercion Core.domain : Core.Algebra >-> Funclass.
Coercion Core.Parametric.rel : Core.Parametric.Rel >-> Funclass.
Canonical Structure Core.Term.

Lemma iden_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A} : R A A iden iden.
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma comp_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R B C t1 t2 -> R A C (comp s1 t1) (comp s2 t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma unit_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A} : R A Unit unit unit.
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma injl_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R A B t1 t2 -> R A (B + C) (injl t1) (injl t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma injr_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R A (B + C) (injr t1) (injr t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma case_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C D} s1 s2 t1 t2 : R (A * C) D s1 s2 -> R (B * C) D t1 t2 -> R ((A + B) * C) D (case s1 t1) (case s2 t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma pair_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A B s1 s2 -> R A C t1 t2 -> R A (B * C) (pair s1 t1) (pair s2 t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma take_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R A C t1 t2 -> R (A * B) C (take t1) (take t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Lemma drop_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} t1 t2 : R B C t1 t2 -> R (A * B) C (drop t1) (drop t2).
Proof.
destruct R as [R []].
cbn; auto.
Qed.

Create HintDb parametricity discriminated.
Hint Immediate iden_Parametric : parametricity.
Hint Resolve comp_Parametric : parametricity.
Hint Immediate unit_Parametric : parametricity.
Hint Resolve injl_Parametric : parametricity.
Hint Resolve injr_Parametric : parametricity.
Hint Resolve case_Parametric : parametricity.
Hint Resolve pair_Parametric : parametricity.
Hint Resolve take_Parametric : parametricity.
Hint Resolve drop_Parametric : parametricity.

Lemma elimS_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C D} r1 r2 s1 s2 t1 t2 : R A (B + C) r1 r2 -> R B D s1 s2 -> R C D t1 t2
                             -> R A D (elimS r1 s1 t1) (elimS r2 s2 t2).
Proof.
unfold elimS.
auto with parametricity.
Qed.
Hint Resolve elimS_Parametric : parametricity.

Lemma copair_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B C} s1 s2 t1 t2 : R A C s1 s2 -> R B C t1 t2
                     -> R (A + B) C (copair s1 t1) (copair s2 t2).
Proof.
unfold copair.
auto with parametricity.
Qed.
Hint Resolve copair_Parametric : parametricity.

Lemma swapS_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B} : R (A + B) (B + A) swapS swapS.
Proof.
unfold swapS.
auto with parametricity.
Qed.
Hint Resolve swapS_Parametric : parametricity.

Lemma swapP_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B} : R (A * B) (B * A) swapP swapP.
Proof.
unfold swapP.
auto with parametricity.
Qed.
Hint Resolve swapP_Parametric : parametricity.

Section CoreSem.

Definition FunSem_mixin : Core.class Arrow :=
  {| Core.iden A a := a
   ; Core.comp A B C s t (a : A) := t (s a)
   ; Core.unit A _ := tt
   ; Core.injl A B C t a := inl (t a)
   ; Core.injr A B C t a := inr (t a)
   ; Core.case A B C D s t p := let (ab, c) := p in
      match ab with
      | inl a => s (a, c)
      | inr b => t (b, c)
      end
   ; Core.pair A B C s t a := (s a, t a)
   ; Core.take A B C t ab := t (fst ab)
   ; Core.drop A B C t ab := t (snd ab)
   |}.

Definition CoreSem_mixin (M : CIMonad) : Core.class (Kleisli M) :=
  {| Core.iden A a := eta a
   ; Core.comp A B C s t (a : A) := (t <-< s) a
   ; Core.unit A _ := eta tt
   ; Core.injl A B C t a := map inl (t a)
   ; Core.injr A B C t a := map inr (t a)
   ; Core.case A B C D s t p := let (ab, c) := p in
      match ab with
      | inl a => s (a, c)
      | inr b => t (b, c)
      end
   ; Core.pair A B C s t a := phi (s a) (t a)
   ; Core.take A B C t ab := t (fst ab)
   ; Core.drop A B C t ab := t (snd ab)
   |}.

End CoreSem.
Canonical Structure CoreFunSem : Core.Algebra := Core.Pack Arrow FunSem_mixin.
Canonical Structure CoreSem (M : CIMonad) : Core.Algebra :=
  Core.Pack (Kleisli M) (CoreSem_mixin M).

Notation "|[ x ]|^ M" := (x : Kleisli M _ _) (at level 0, M at level 0) : semantic_scope.
Notation "|[ x ]|" := (x : Arrow _ _) : semantic_scope.

Local Open Scope semantic_scope.
Local Open Scope monad_scope.

Lemma CoreFunSem_correct {A B} {t : forall {alg : Core.Algebra}, alg A B} (Ht : Core.Parametric (@t)) :
 forall a, Simplicity.Core.eval t a = |[ t ]| a.
Proof.
set (R A B (x : Simplicity.Core.Term A B) (y : Arrow A B) := forall a, Simplicity.Core.eval x a = |[ y ]| a).
refine (Ht _ _ (Core.Parametric.Pack (_ : Core.Parametric.class R))).
constructor; unfold R; clear; intros; cbn; try destruct a as [[a|b] c];
 try rewrite Hs; try rewrite Ht; try reflexivity.
Qed.

Lemma CoreSem_initial {M : CIMonad} {A B} {t : forall {alg : Core.Algebra}, alg A B} (Ht : Core.Parametric (@t)) :
  forall a, |[ t ]|^M a = eta (|[ t ]| a).
Proof.
set (R A B (x : Kleisli M A B) (y : Arrow A B) := forall a, |[ x ]|^M a = eta (|[ y ]| a)).
refine (Ht _ _ (Core.Parametric.Pack (_ : Core.Parametric.class R))).
constructor; unfold R; clear; intros; cbn.
- reflexivity.
- rewrite kleisli_comp_def, Hs, <- kleisli_comp_def.
  rewrite kleisli_compr; apply Ht.
- reflexivity.
- rewrite Ht; apply eta_natural.
- rewrite Ht; apply eta_natural.
- destruct a as [[a|b] c]; [apply Hs|apply Ht].
- rewrite Hs, Ht.
  apply phi_eta.
- apply Ht.
- apply Ht.
Qed.

Section Generic.

Fixpoint scribe {A B : Ty} : B -> forall {alg : Core.Algebra}, alg A B :=
match B with
| Unit => fun _ _ => unit
| Sum BL BR => fun b =>
  match b with
  | inl l => fun _ => injl (scribe l)
  | inr r => fun _ => injr (scribe r)
  end
| Prod B1 B2 => fun b _ => pair (scribe (fst b)) (scribe (snd b))
end.

Lemma scribe_correct {A B : Ty} (a : A) (b : B) : |[scribe b]| a = b.
Proof.
induction B;[destruct b as [] | destruct b as [b|b] | destruct b as [b0 b1]]; cbn;
try rewrite IHB1; try rewrite IHB2; reflexivity.
Qed.

End Generic.

Lemma scribe_Parametric {alg1 alg2 : Core.Algebra} (R : Core.Parametric.Rel alg1 alg2)
  {A B : Ty} (b : B) : R A B (scribe b) (scribe b).
Proof.
induction B;[|destruct b as [b|b] |]; cbn;
auto with parametricity.
Qed.
Hint Immediate scribe_Parametric : parametricity.


Module Assertion.

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ assertl : forall {A B C D}, term (A * C) D -> hash256 -> term ((A + B) * C) D
; assertr : forall {A B C D}, hash256 -> term (B * C) D -> term ((A + B) * C) D
; fail : forall {A B}, (hash256 * hash256) -> term A B
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> Core.class term
; ext  :> mixin term
}.

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (a0 : mixin dom) :=
 [find c  | Core.domain c ~ dom | "is not a Core algebra" ]
 [find cc | Core.class_of c ~ cc ]
 [find a  | a ~ a0 | "is not the right mixin" ]
 @_Pack dom (@Class dom cc a).

Notation Pack dom a := (@packager dom a _ id _ id _ id).

Canonical Structure toCore (alg : Algebra) : Core.Algebra := Core.Pack alg (class_of alg).

Module Combinators.

Definition assertl {A B C D} {alg : Algebra} : alg (A * C) D -> hash256 -> alg ((A + B) * C) D := assertl (class_of alg).
Definition assertr {A B C D} {alg : Algebra} : hash256 -> alg (B * C) D -> alg ((A + B) * C) D := assertr (class_of alg).
Definition fail {A B} {alg : Algebra} : (hash256 * hash256) -> alg A B := fail (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B C D s1 s2 th, rel s1 s2 -> rel (assertl s1 th) (@assertl A B C D _ s2 th)
 ; _ : forall A B C D sh t1 t2, rel t1 t2 -> rel (assertr sh t1) (@assertr A B C D _ sh t2)
 ; _ : forall A B hh, rel (fail hh) (@fail A B _ hh)
 }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Core.Parametric.class (@rel)
 ; ext :> mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.
End Reynolds.

End Assertion.
Export Assertion.Combinators.
Coercion Assertion.domain : Assertion.Algebra >-> Funclass.
Coercion Assertion.toCore : Assertion.Algebra >-> Core.Algebra.
Coercion Assertion.base : Assertion.class >-> Core.class.
Coercion Assertion.ext : Assertion.class >-> Assertion.mixin.
Coercion Assertion.Parametric.rel : Assertion.Parametric.Rel >-> Funclass.
Canonical Structure Assertion.toCore.

Lemma assertl_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.Parametric.Rel alg1 alg2)
  {A B C D} s1 s2 th : R (A * C) D s1 s2 -> R ((A + B) * C) D (assertl s1 th) (assertl s2 th).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.

Lemma assertr_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.Parametric.Rel alg1 alg2)
  {A B C D} sh t1 t2 : R (B * C) D t1 t2 -> R ((A + B) * C) D (assertr sh t1) (assertr sh t2).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.

Lemma fail_Parametric {alg1 alg2 : Assertion.Algebra} (R : Assertion.Parametric.Rel alg1 alg2)
  {A B} hh : R A B (fail hh) (fail hh).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.

Hint Resolve assertl_Parametric : parametricity.
Hint Resolve assertr_Parametric : parametricity.
Hint Immediate fail_Parametric : parametricity.

Section AssertionSem.

Definition AssertionSem_mixin (M : CIMonadZero) : Assertion.mixin (Kleisli M) :=
  {| Assertion.assertl A B C D s _ (p : tySem ((A + B) * C)):= let (ab, c) := p in
      match ab with
      | inl a => s (a, c)
      | inr b => mzero
      end
   ; Assertion.assertr A B C D _ t p := let (ab, c) := p in
      match ab with
      | inl a => mzero
      | inr b => t (b, c)
      end
   ; Assertion.fail A B _ := kzero
   |}.

End AssertionSem.
Canonical Structure AssertionSem (M : CIMonadZero) : Assertion.Algebra :=
  Assertion.Pack (Kleisli M) (AssertionSem_mixin M).

Lemma AssertionSem_initial {M : CIMonadZero} {A B} {t : forall {alg : Assertion.Algebra}, alg A B} (Ht : Assertion.Parametric (@t)) :
  forall (a : A), |[ t ]|^M a = optionZero (|[ t ]|^option a).
Proof.
set (R := fun A B (x : AssertionSem M A B) (y : AssertionSem option_Monad_Zero A B) =>
          forall a : A, x a = optionZero (y a)).
refine (Ht _ _ (Assertion.Parametric.Pack (_ : Assertion.Parametric.class R)));
repeat constructor; unfold R; clear; try reflexivity; cbn.
- intros A B C s1 s2 t1 t2 Hs Ht a.
  symmetry; rewrite kleisli_comp_def.
  rewrite optionZero_mu, optionZero_natural, map_comp, <- optionZero_natural, <- Hs.
  erewrite map_ext;[|intros;symmetry;apply Ht].
  rewrite <- kleisli_comp_def.
  reflexivity.
- intros A B C t1 t2 Ht a.
  rewrite Ht; apply optionZero_natural.
- intros A B C t1 t2 Ht a.
  rewrite Ht; apply optionZero_natural.
- intros A B C D s1 s2 t1 t2 Hs Ht [[a|b] c]; [apply Hs|apply Ht].
- intros A B C s1 s2 t1 t2 Hs Ht a.
  rewrite Hs, Ht.
  symmetry; apply optionZero_phi.
- intros A B C t1 t2 Ht a.
  apply Ht.
- intros A B C t1 t2 Ht a.
  apply Ht.
- intros A B C D s1 s2 h Hs [[a|b] c]; [apply Hs|reflexivity].
- intros A B C D h t1 t2 Ht [[a|b] c]; [reflexivity|apply Ht].
Qed.

Module Witness.

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ witness : forall {A B : Ty}, B -> term A B }.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> Core.class term
; ext  :> mixin term
}.

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (a0 : mixin dom) :=
 [find c  | Core.domain c ~ dom | "is not a Core algebra" ]
 [find cc | Core.class_of c ~ cc ]
 [find a  | a ~ a0 | "is not the right mixin" ]
 @_Pack dom (@Class dom cc a).

Notation Pack dom a := (@packager dom a _ id _ id _ id).

Canonical Structure toCore (alg : Algebra) : Core.Algebra := Core.Pack alg (class_of alg).

Module Combinators.

Definition witness {A B : Ty} {alg : Algebra} : B -> alg A B := witness (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B b, rel (witness b) (@witness A B _ b) }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Core.Parametric.class (@rel)
 ; ext :> mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.
End Reynolds.

End Witness.
Export Witness.Combinators.
Coercion Witness.domain : Witness.Algebra >-> Funclass.
Coercion Witness.toCore : Witness.Algebra >-> Core.Algebra.
Coercion Witness.base : Witness.class >-> Core.class.
Coercion Witness.ext : Witness.class >-> Witness.mixin.
Coercion Witness.Parametric.rel : Witness.Parametric.Rel >-> Funclass.
Canonical Structure Witness.toCore.

Lemma witness_Parametric {alg1 alg2 : Witness.Algebra} (R : Witness.Parametric.Rel alg1 alg2)
  {A B} b : R A B (witness b) (witness b).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.
Hint Immediate witness_Parametric : parametricity.

Section WitnessSem.

Definition WitnessFunSem_mixin : Witness.mixin Arrow :=
  {| Witness.witness A B b a := b |}.

Definition WitnessSem_mixin (M : CIMonad) : Witness.mixin (Kleisli M) :=
  {| Witness.witness A B b a := eta b |}.

End WitnessSem.
Canonical Structure WitnessFunSem : Witness.Algebra := Witness.Pack Arrow WitnessFunSem_mixin.
Canonical Structure WitnessSem (M : CIMonad) : Witness.Algebra :=
  Witness.Pack (Kleisli M) (WitnessSem_mixin M).

Lemma WitnessSem_initial {M : CIMonad} {A B} {t : forall {alg : Witness.Algebra}, alg A B} (Ht : Witness.Parametric (@t)) :
  forall a, |[ t ]|^M a = eta (|[ t ]| a).
Proof.
set (R A B (x : Kleisli M A B) (y : Arrow A B) := forall a, |[ x ]|^M a = eta (|[ y ]| a)).
refine (Ht _ _ (Witness.Parametric.Pack (_ : Witness.Parametric.class R))).
do 2 constructor; unfold R; clear; intros; cbn.
- reflexivity.
- rewrite kleisli_comp_def, Hs, <- kleisli_comp_def.
  rewrite kleisli_compr; apply Ht.
- reflexivity.
- rewrite Ht; apply eta_natural.
- rewrite Ht; apply eta_natural.
- destruct a as [[a|b] c]; [apply Hs|apply Ht].
- rewrite Hs, Ht.
  apply phi_eta.
- apply Ht.
- apply Ht.
- reflexivity.
Qed.

Module AssertionWitness.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> Assertion.class term
; ext  :> Witness.mixin term
}.

Definition base2 term (c : class term) : Witness.class term := Witness.Class (base c) (ext c).

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom :=
 [find a  | Assertion.domain a ~ dom | "is not a Assertion algebra" ]
 [find ac | Assertion.class_of a ~ ac ]
 [find w  | Witness.domain w ~ dom | "is not a Witness algebra" ]
 [find wm | Witness.ext (Witness.class_of w) ~ wm ]
 @_Pack dom (@Class dom ac wm).

Notation Pack dom := (@packager dom _ id _ id _ id _ id).

Canonical Structure toCore (alg : Algebra) : Core.Algebra := Core.Pack alg (class_of alg).
Canonical Structure toAssertion (alg : Algebra) : Assertion.Algebra := Assertion.Pack alg (class_of alg).
Canonical Structure toWitness (alg : Algebra) : Witness.Algebra := Witness.Pack alg (class_of alg).

Module Parametric.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Assertion.Parametric.class (@rel)
 ; ext :> Witness.Parametric.mixin (@rel)
 }.

Record Rel (alg1 alg2 : Algebra) := Pack
 { rel :> forall {A B}, alg1 A B -> alg2 A B -> Prop
 ; class_of : class (@rel)
 }.

End Parametric.

Section Reynolds.
Local Coercion Parametric.rel : Parametric.Rel >-> Funclass.

Definition Reynolds {A B} (x y : forall (alg : Algebra), alg A B) : Prop :=
  forall alg1 alg2 (R : Parametric.Rel alg1 alg2), R A B (x alg1) (y alg2).

Definition Parametric {A B} (x : forall (alg : Algebra), alg A B) : Prop := Reynolds x x.
End Reynolds.

End AssertionWitness.
Coercion AssertionWitness.domain : AssertionWitness.Algebra >-> Funclass.
Coercion AssertionWitness.toAssertion : AssertionWitness.Algebra >-> Assertion.Algebra.
Coercion AssertionWitness.toWitness : AssertionWitness.Algebra >-> Witness.Algebra.
Coercion AssertionWitness.base : AssertionWitness.class >-> Assertion.class.
Coercion AssertionWitness.base2 : AssertionWitness.class >-> Witness.class.
Coercion AssertionWitness.Parametric.rel : AssertionWitness.Parametric.Rel >-> Funclass.
Canonical Structure AssertionWitness.toCore.
Canonical Structure AssertionWitness.toAssertion.
Canonical Structure AssertionWitness.toWitness.

Canonical Structure AssertionWitnessSem (M : CIMonadZero) : AssertionWitness.Algebra :=
  AssertionWitness.Pack (Kleisli M).

Lemma AssertionWitnessSem_initial {M : CIMonadZero} {A B} {t : forall {alg : AssertionWitness.Algebra}, alg A B} (Ht : AssertionWitness.Parametric (@t)) :
  forall (a : A), |[ t ]|^M a = optionZero (|[ t ]|^option a).
Proof.
set (R := fun A B (x : AssertionSem M A B) (y : AssertionSem option_Monad_Zero A B) =>
          forall a : A, x a = optionZero (y a)).
refine (Ht _ _ (AssertionWitness.Parametric.Pack (_ : AssertionWitness.Parametric.class R))).
repeat constructor; unfold R; clear; try reflexivity; cbn.
- intros A B C s1 s2 t1 t2 Hs Ht a.
  symmetry; rewrite kleisli_comp_def.
  rewrite optionZero_mu, optionZero_natural, map_comp, <- optionZero_natural, <- Hs.
  erewrite map_ext;[|intros;symmetry;apply Ht].
  rewrite <- kleisli_comp_def.
  reflexivity.
- intros A B C t1 t2 Ht a.
  rewrite Ht; apply optionZero_natural.
- intros A B C t1 t2 Ht a.
  rewrite Ht; apply optionZero_natural.
- intros A B C D s1 s2 t1 t2 Hs Ht [[a|b] c]; [apply Hs|apply Ht].
- intros A B C s1 s2 t1 t2 Hs Ht a.
  rewrite Hs, Ht.
  symmetry; apply optionZero_phi.
- intros A B C t1 t2 Ht a.
  apply Ht.
- intros A B C t1 t2 Ht a.
  apply Ht.
- intros A B C D s1 s2 h Hs [[a|b] c]; [apply Hs|reflexivity].
- intros A B C D h t1 t2 Ht [[a|b] c]; [reflexivity|apply Ht].
Qed.

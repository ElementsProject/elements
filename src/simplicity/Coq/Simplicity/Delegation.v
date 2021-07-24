Require Import Simplicity.Util.PackedClass.
Import Coq.Strings.String.StringSyntax.

Require Import Simplicity.Alg.
Require Import Simplicity.MerkleRoot.
Require Import Simplicity.Ty.
Require Import Simplicity.Word.

Set Implicit Arguments.
Local Open Scope ty_scope.
Local Open Scope term_scope.

Module Delegation.

Record mixin (term : Ty -> Ty -> Type) := Mixin
{ disconnect : forall {A B C D},
    term (Word256 * A) (B * C) -> term C D -> term A (B * D)
}.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> Witness.class term
; ext  :> mixin term
}.

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom (d0 : mixin dom) :=
 [find w  | Witness.domain w ~ dom | "is not a Witness algebra" ]
 [find wc | Witness.class_of w ~ wc ]
 [find d  | d ~ d0 | "is not the right mixin" ]
 @_Pack dom (@Class dom wc d).

Notation Pack dom d := (@packager dom d _ id _ id _ id).

Canonical Structure toCore (alg : Algebra) : Core.Algebra := Core.Pack alg (class_of alg).
Canonical Structure toWitness (alg : Algebra) : Witness.Algebra := Witness.Pack alg (class_of alg).

Module Combinators.

Definition disconnect {A B C D : Ty} {alg : Algebra} : alg (Word256 * A) (B * C) -> alg C D -> alg A (B * D) :=
  disconnect (class_of alg).

End Combinators.

Module Parametric.
Import Combinators.

Record mixin {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { _ : forall A B C D s1 s2 t1 t2 (Hs : rel s1 s2) (Ht : rel t1 t2), rel (disconnect s1 t1) (@disconnect A B C D _ s2 t2) }.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> Witness.Parametric.class (@rel)
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

End Delegation.
Export Delegation.Combinators.
Coercion Delegation.domain : Delegation.Algebra >-> Funclass.
Coercion Delegation.toWitness : Delegation.Algebra >-> Witness.Algebra.
Coercion Delegation.base : Delegation.class >-> Witness.class.
Coercion Delegation.ext : Delegation.class >-> Delegation.mixin.
Coercion Delegation.Parametric.rel : Delegation.Parametric.Rel >-> Funclass.
Canonical Structure Delegation.toCore.
Canonical Structure Delegation.toWitness.

Lemma disconnect_Parametric {alg1 alg2 : Delegation.Algebra} (R : Delegation.Parametric.Rel alg1 alg2)
  {A B C D} s1 s2 t1 t2 : R (Word256 * A) (B * C) s1 s2 -> R C D t1 t2 -> R A (B * D) (disconnect s1 t1) (disconnect s2 t2).
Proof.
destruct R as [R [Rb []]].
cbn; auto.
Qed.
Hint Resolve disconnect_Parametric : parametricity.

Module AssertionDelegation.

Record class (term : Ty -> Ty -> Type) := Class
{ base :> AssertionWitness.class term
; ext  :> Delegation.mixin term
}.
Definition base2 term (c : class term) := Delegation.Class (base c) (ext c).

Structure Algebra := _Pack { domain :> Ty -> Ty -> Type; class_of : class domain }.

Definition packager dom :=
 [find aw  | AssertionWitness.domain aw ~ dom | "is not a AssertionWitness algebra" ]
 [find awc | AssertionWitness.class_of aw ~ awc ]
 [find d  | Delegation.domain d ~ dom | "is not a Delegation algebra" ]
 [find dm | Delegation.ext (Delegation.class_of d) ~ dm ]
 @_Pack dom (@Class dom awc dm).

Notation Pack dom := (@packager dom _ id _ id _ id _ id).

Canonical Structure toCore (alg : Algebra) : Core.Algebra := Core.Pack alg (class_of alg).
Canonical Structure toAssertion (alg : Algebra) : Assertion.Algebra := Assertion.Pack alg (class_of alg).
Canonical Structure toWitness (alg : Algebra) : Witness.Algebra := Witness.Pack alg (class_of alg).
Canonical Structure toAssertionWitness (alg : Algebra) : AssertionWitness.Algebra := AssertionWitness.Pack alg.
Canonical Structure toDelegation (alg : Algebra) : Delegation.Algebra := Delegation.Pack alg (class_of alg).

Module Parametric.

Record class {alg1 alg2 : Algebra} (rel : forall {A B}, alg1 A B -> alg2 A B -> Prop) :=
 { base :> AssertionWitness.Parametric.class (@rel)
 ; ext :> Delegation.Parametric.mixin (@rel)
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

End AssertionDelegation.
Coercion AssertionDelegation.domain : AssertionDelegation.Algebra >-> Funclass.
Coercion AssertionDelegation.toAssertionWitness : AssertionDelegation.Algebra >-> AssertionWitness.Algebra.
Coercion AssertionDelegation.toDelegation : AssertionDelegation.Algebra >-> Delegation.Algebra.
Coercion AssertionDelegation.base : AssertionDelegation.class >-> AssertionWitness.class.
Coercion AssertionDelegation.base2 : AssertionDelegation.class >-> Delegation.class.
Coercion AssertionDelegation.Parametric.rel : AssertionDelegation.Parametric.Rel >-> Funclass.
Canonical Structure AssertionDelegation.toCore.
Canonical Structure AssertionDelegation.toAssertion.
Canonical Structure AssertionDelegation.toWitness.
Canonical Structure AssertionDelegation.toAssertionWitness.
Canonical Structure AssertionDelegation.toDelegation.

Section MerkleRoot.

Let disconnectTag := Eval vm_compute in commitmentTag "disconnect".

Definition CommitmentRoot_Delegation_mixin : Delegation.mixin CommitmentRoot :=
 {| Delegation.disconnect A B C D s _ := compress_half disconnectTag s |}.

End MerkleRoot.
Canonical Structure CommitmentRoot_Delegation_alg : Delegation.Algebra :=
  Delegation.Pack CommitmentRoot CommitmentRoot_Delegation_mixin.
Canonical Structure CommitmentRoot_AssertionDelegation_alg : AssertionDelegation.Algebra :=
  AssertionDelegation.Pack CommitmentRoot.

Section Delegator.

Record Delegator (Arrow : Ty -> Ty -> Type) (A B : Ty) :=
{ delegatorRoot : CommitmentRoot A B
; runDelegator : Arrow A B
}.

Definition CoreDelegator_mixin (alg : Core.Algebra) : Core.class (Delegator alg) :=
  {| Core.iden A := {| delegatorRoot := iden
                     ; runDelegator := iden |}
   ; Core.comp A B C s t := {| delegatorRoot := comp (delegatorRoot s) (delegatorRoot t)
                             ; runDelegator := comp (runDelegator s) (runDelegator t)
                             |}
   ; Core.unit A := {| delegatorRoot := unit
                     ; runDelegator := unit |}
   ; Core.injl A B C t := {| delegatorRoot := injl (delegatorRoot t)
                           ; runDelegator := injl (runDelegator t)
                           |}
   ; Core.injr A B C t := {| delegatorRoot := injr (delegatorRoot t)
                           ; runDelegator := injr (runDelegator t)
                           |}
   ; Core.case A B C D s t := {| delegatorRoot := case (delegatorRoot s) (delegatorRoot t)
                               ; runDelegator := case (runDelegator s) (runDelegator t)
                               |}
   ; Core.pair A B C s t := {| delegatorRoot := pair (delegatorRoot s) (delegatorRoot t)
                             ; runDelegator := pair (runDelegator s) (runDelegator t)
                             |}
   ; Core.take A B C t := {| delegatorRoot := take (delegatorRoot t)
                           ; runDelegator := take (runDelegator t)
                           |}
   ; Core.drop A B C t := {| delegatorRoot := drop (delegatorRoot t)
                           ; runDelegator := drop (runDelegator t)
                           |}
   |}.

Definition AssertionDelegator_mixin (alg : Assertion.Algebra) : Assertion.mixin (Delegator alg) :=
  {| Assertion.assertl A B C D s ht := {| delegatorRoot := assertl (delegatorRoot s) ht
                                       ; runDelegator := assertl (runDelegator s) ht
                                       |}
   ; Assertion.assertr A B C D hs t := {| delegatorRoot := assertr hs (delegatorRoot t)
                                       ; runDelegator := assertr hs (runDelegator t)
                                       |}
   ; Assertion.fail A B h := {| delegatorRoot := fail h
                              ; runDelegator := @fail A B alg h
                              |}
   |}.

Definition WitnessDelegator_mixin (alg : Witness.Algebra) : Witness.mixin (Delegator alg) :=
  {| Witness.witness A B b := {| delegatorRoot := witness b
                               ; runDelegator := witness b
                               |}
   |}.

Definition DelegationDelegator_mixin (alg : Core.Algebra) : Delegation.mixin (Delegator alg) :=
  {| Delegation.disconnect A B C D s t :=
     {| delegatorRoot := @disconnect A B C D _ (delegatorRoot s) (delegatorRoot t)
      ; runDelegator := scribe (from_hash256 (delegatorRoot t)) &&& iden
                    >>> runDelegator s >>> take iden &&& drop (runDelegator t)
      |}
   |}.

End Delegator.

Canonical Structure CoreDelegator (alg : Core.Algebra) : Core.Algebra :=
  Core.Pack (Delegator alg) (CoreDelegator_mixin alg).
Canonical Structure AssertionDelegator (alg : Assertion.Algebra) : Assertion.Algebra :=
  Assertion.Pack (Delegator alg) (AssertionDelegator_mixin alg).
Canonical Structure WitnessDelegator (alg : Witness.Algebra) : Witness.Algebra :=
  Witness.Pack (Delegator alg) (WitnessDelegator_mixin alg).
Canonical Structure AssertionWitnessDelegator (alg : AssertionWitness.Algebra) : AssertionWitness.Algebra :=
  AssertionWitness.Pack (Delegator alg).
Canonical Structure DelegationDelegator (alg : Witness.Algebra) : Delegation.Algebra :=
  Delegation.Pack (Delegator alg) (DelegationDelegator_mixin alg).
Canonical Structure AssertionDelegationDelegator (alg : AssertionWitness.Algebra) : AssertionDelegation.Algebra :=
  AssertionDelegation.Pack (Delegator alg).

Lemma delegatorRoot_correctness A B (t : forall alg : AssertionDelegation.Algebra, alg A B)
  (Ht : AssertionDelegation.Parametric t) alg : delegatorRoot (t (AssertionDelegationDelegator alg)) = t _.
Proof.
set (R := fun A B (x : Delegator alg A B) (y : CommitmentRoot A B) => delegatorRoot x = y).
refine (Ht _ _ (AssertionDelegation.Parametric.Pack (_ : AssertionDelegation.Parametric.class R))).
repeat constructor; unfold R; clear; intros; cbn; repeat f_equal; assumption.
Qed.

Lemma runDelegator_correctness A B (t : forall alg : AssertionWitness.Algebra, alg A B)
  (Ht : AssertionWitness.Parametric t) alg : runDelegator (t (AssertionWitnessDelegator alg)) = t alg.
Proof.
set (R := fun A B (x : Delegator alg A B) (y : alg A B) => runDelegator x = y).
refine (Ht _ _ (AssertionWitness.Parametric.Pack (_ : AssertionWitness.Parametric.class R))).
repeat constructor; unfold R; clear; intros; cbn; repeat f_equal; assumption.
Qed.

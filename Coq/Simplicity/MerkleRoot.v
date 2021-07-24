Require Import List.
Require Import Coq.Strings.String.
Import Coq.Strings.Ascii.AsciiSyntax.

Require Import Simplicity.Alg.
Require Export Simplicity.Digest.
Require Import Simplicity.Ty.

Set Implicit Arguments.

Import ListNotations.

Definition tag (ws : list string) :=
 let str := concat (String "031" EmptyString) ws in
 let tagDigest := normalizeHash (stringHash str) in
  normalizeHash (compress sha256_iv tagDigest tagDigest).

Definition prefix := ["Simplicity-Draft"%string].
Definition typePrefix := prefix ++ ["Type"%string].
Definition commitmentPrefix := prefix ++ ["Commitment"%string].
Definition identityPrefix := prefix ++ ["Identity"%string].

Section TypeRoot.

Let typeTag tg := tag (typePrefix ++ [tg]).

Let unitTag := Eval vm_compute in typeTag "unit".
Let sumTag := Eval vm_compute in typeTag "sum".
Let prodTag := Eval vm_compute in typeTag "prod".

Definition typeRootAlg : tyAlg hash256 :=
{| unitA := unitTag
 ; sumA  := compress sumTag
 ; prodA := compress prodTag
 |}.

End TypeRoot.

(* :TODO: memoize the computation of type roots. *)
Definition typeRoot : Ty -> hash256 := tyCata typeRootAlg.

Definition commitmentTag tg := tag (commitmentPrefix ++ [tg]).

Section CommitmentRoot.

Let idenTag := Eval vm_compute in commitmentTag "iden".
Let compTag := Eval vm_compute in commitmentTag "comp".
Let unitTag := Eval vm_compute in commitmentTag "unit".
Let injlTag := Eval vm_compute in commitmentTag "injl".
Let injrTag := Eval vm_compute in commitmentTag "injr".
Let caseTag := Eval vm_compute in commitmentTag "case".
Let pairTag := Eval vm_compute in commitmentTag "pair".
Let takeTag := Eval vm_compute in commitmentTag "take".
Let dropTag := Eval vm_compute in commitmentTag "drop".
Let failTag := Eval vm_compute in commitmentTag "fail".
Let witnessTag := Eval vm_compute in commitmentTag "witness".

Definition CommitmentRoot (A B:Ty) := hash256.

Definition commitmentRoot {A B} (x : CommitmentRoot A B) : hash256 := x.

Definition CommitmentRoot_Core_mixin : Core.class CommitmentRoot :=
 {| Core.iden A := idenTag
  ; Core.comp A B C hs ht := compress compTag hs ht
  ; Core.unit A := unitTag
  ; Core.injl A B C ht := compress_half injlTag ht
  ; Core.injr A B C ht := compress_half injrTag ht
  ; Core.case A B C D hs ht := compress caseTag hs ht
  ; Core.pair A B C hs ht := compress pairTag hs ht
  ; Core.take A B C ht := compress_half takeTag ht
  ; Core.drop A B C ht := compress_half dropTag ht
  |}.

Definition CommitmentRoot_Assertion_mixin : Assertion.mixin CommitmentRoot :=
 {| Assertion.assertl A B C D hs ht := compress caseTag hs ht
  ; Assertion.assertr A B C D hs ht := compress caseTag hs ht
  ; Assertion.fail A B h := compress failTag (fst h) (snd h)
  |}.

Definition CommitmentRoot_Witness_mixin : Witness.mixin CommitmentRoot :=
 {| Witness.witness A B b := witnessTag |}.

End CommitmentRoot.

Canonical Structure CommitmentRoot_Core_alg : Core.Algebra :=
  Core.Pack CommitmentRoot CommitmentRoot_Core_mixin.

Canonical Structure CommitmentRoot_Assertion_alg : Assertion.Algebra :=
  Assertion.Pack CommitmentRoot CommitmentRoot_Assertion_mixin.

Canonical Structure CommitmentRoot_Witness_alg : Witness.Algebra :=
  Witness.Pack CommitmentRoot CommitmentRoot_Witness_mixin.

Canonical Structure CommitmentRoot_AssertionWitness_alg : AssertionWitness.Algebra :=
  AssertionWitness.Pack CommitmentRoot.

Definition identityRootTag := tag identityPrefix.

Section IdentityRoot.

Definition IdentityRoot (A B:Ty) := hash256.

Definition identityRoot {A B} (x : IdentityRoot A B) : hash256 :=
  compress (compress_half identityRootTag x) (typeRoot A) (typeRoot B).

Definition IdentityRoot_Core_mixin : Core.class IdentityRoot := CommitmentRoot_Core_mixin.

Definition IdentityRoot_Assertion_mixin : Assertion.mixin IdentityRoot := CommitmentRoot_Assertion_mixin.

End IdentityRoot.

Canonical Structure IdentityRoot_Core_alg : Core.Algebra :=
  Core.Pack IdentityRoot IdentityRoot_Core_mixin.

Canonical Structure IdentityRoot_Assertion_alg : Assertion.Algebra :=
  Assertion.Pack IdentityRoot IdentityRoot_Assertion_mixin.

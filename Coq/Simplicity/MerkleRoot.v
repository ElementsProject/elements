Require Import List.
Require Import Coq.Strings.String.
Import Coq.Strings.Ascii.AsciiSyntax.

Require Import Simplicity.Alg.
Require Export Simplicity.Digest.
Require Import Simplicity.Ty.

Set Implicit Arguments.

Import ListNotations.

(* TODO remove when we update to lastest version of Coq.Strings.String *)
(** *** Concatenating lists of strings *)

(** [concat sep sl] concatenates the list of strings [sl], inserting
    the separator string [sep] between each. *)

Local Fixpoint concat (sep : string) (ls : list string) :=
  match ls with
  | nil => EmptyString
  | cons x nil => x
  | cons x xs => (x ++ sep ++ concat sep xs)%string
end.

Definition tag (ws : list string) :=
 let str := concat (String "031" EmptyString) ws in
   fun (_precondition : length str - 55 = 0) => normalizeHash (stringHash str).

Definition prefix := ["Simplicity"%string].
Definition typePrefix := prefix ++ ["Type"%string].
Definition commitmentPrefix := prefix ++ ["Commitment"%string].
Definition witnessPrefix := prefix ++ ["Witness"%string].

Section TypeRoot.

Notation typeTag tg := (tag (typePrefix ++ [tg%string]) refl_equal).

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

Notation commitmentTag tg := (tag (commitmentPrefix ++ [tg%string]) refl_equal).

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

Notation witnessTag tg := (tag (witnessPrefix ++ [tg%string]) refl_equal).

Section WitnessRoot.

Let idenTag := Eval vm_compute in witnessTag "iden".
Let compTag := Eval vm_compute in witnessTag "comp".
Let unitTag := Eval vm_compute in witnessTag "unit".
Let injlTag := Eval vm_compute in witnessTag "injl".
Let injrTag := Eval vm_compute in witnessTag "injr".
Let caseTag := Eval vm_compute in witnessTag "case".
Let pairTag := Eval vm_compute in witnessTag "pair".
Let takeTag := Eval vm_compute in witnessTag "take".
Let dropTag := Eval vm_compute in witnessTag "drop".
Let assertlTag := Eval vm_compute in witnessTag "assertl".
Let assertrTag := Eval vm_compute in witnessTag "assertr".
Let failTag := Eval vm_compute in witnessTag "fail".

Definition WitnessRoot (A B:Ty) := hash256.

Definition witnessRoot {A B} (x : WitnessRoot A B) : hash256 := x.

Definition WitnessRoot_Core_mixin : Core.class WitnessRoot :=
 {| Core.iden A := compress_half idenTag (typeRoot A)
  ; Core.comp A B C hs ht := compress (compress (compress_half compTag (typeRoot A))
                                                (typeRoot B) (typeRoot C))
                                       hs ht
  ; Core.unit A := compress_half unitTag (typeRoot A)
  ; Core.injl A B C ht := compress (compress injlTag (typeRoot A) (typeRoot B))
                                   (typeRoot C) ht
  ; Core.injr A B C ht := compress (compress injrTag (typeRoot A) (typeRoot B))
                                   (typeRoot C) ht
  ; Core.case A B C D hs ht := compress (compress (compress caseTag (typeRoot A) (typeRoot B))
                                                  (typeRoot C) (typeRoot D))
                                        hs ht
  ; Core.pair A B C hs ht := compress (compress (compress_half pairTag (typeRoot A))
                                                (typeRoot B) (typeRoot C))
                                      hs ht
  ; Core.take A B C ht := compress (compress takeTag (typeRoot A) (typeRoot B))
                                   (typeRoot C) ht
  ; Core.drop A B C ht := compress (compress dropTag (typeRoot A) (typeRoot B))
                                   (typeRoot C) ht
  |}.

Definition WitnessRoot_Assertion_mixin : Assertion.mixin WitnessRoot :=
 {| Assertion.assertl A B C D hs ht := compress (compress (compress assertlTag (typeRoot A) (typeRoot B))
                                                          (typeRoot C) (typeRoot D))
                                                hs ht
  ; Assertion.assertr A B C D hs ht := compress (compress (compress assertrTag (typeRoot A) (typeRoot B))
                                                          (typeRoot C) (typeRoot D))
                                                hs ht
  ; Assertion.fail A B h := compress failTag (fst h) (snd h)
  |}.

End WitnessRoot.

Canonical Structure WitnessRoot_Core_alg : Core.Algebra :=
  Core.Pack WitnessRoot WitnessRoot_Core_mixin.

Canonical Structure WitnessRoot_Assertion_alg : Assertion.Algebra :=
  Assertion.Pack WitnessRoot WitnessRoot_Assertion_mixin.

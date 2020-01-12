Require Import Simplicity.Ty.
Require Import Simplicity.Alg.

Set Implicit Arguments.

Local Open Scope ty_scope.
Local Open Scope term_scope.

Notation Bit := (Unit + Unit).
Notation "'Bit.zero'" := (inl tt).
Notation "'Bit.one'" := (inr tt).

Definition toBool (b : Bit) :=
match b with
| inl _ => false
| inr _ => true
end.

Definition fromBool (b : bool) := if b then Bit.one else Bit.zero.

Section Definitions.

Definition false {A} {term : Core.Algebra} : term A Bit := injl unit.
Definition true {A} {term : Core.Algebra} : term A Bit := injr unit.

Definition cond {A B} {term : Core.Algebra} (thn els : term A B) : term (Bit * A) B :=
  case (drop els) (drop thn).

Definition ch {A} {term : Core.Algebra} : term (Bit * (A * A)) A :=
  cond (O H) (I H).

Definition not {A} {term : Core.Algebra} (t : term A Bit) : term A Bit :=
  t &&& unit >>> cond false true.

Definition and {A} {term : Core.Algebra} (s t : term A Bit) : term A Bit :=
  s &&& iden >>> cond t false.

Definition or {A} {term : Core.Algebra} (s t : term A Bit) : term A Bit :=
  s &&& iden >>> cond true t.

Definition xor3 {term : Core.Algebra} : term (Bit * (Bit * Bit)) Bit :=
  cond (cond iden (not iden)) (cond (not iden) iden).

Definition maj {term : Core.Algebra} : term (Bit * (Bit * Bit)) Bit :=
  cond (cond true iden) (cond iden false).

End Definitions.

Lemma false_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A} : R A Bit false false.
Proof.
unfold false.
auto with parametricity.
Qed.
Hint Immediate false_Parametric : parametricity.

Lemma true_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A} : R A Bit true true.
Proof.
unfold true.
auto with parametricity.
Qed.
Hint Immediate true_Parametric : parametricity.

Lemma cond_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A B} s1 s2 t1 t2 : R A B s1 s2 -> R A B t1 t2 -> R (Bit * A) B (cond s1 t1) (cond s2 t2).
Proof.
unfold cond.
auto with parametricity.
Qed.
Hint Resolve cond_Parametric : parametricity.

Lemma ch_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A} : R _ A ch ch.
Proof.
unfold ch.
auto with parametricity.
Qed.
Hint Immediate ch_Parametric : parametricity.

Lemma not_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A} t1 t2 : R A Bit t1 t2 -> R A Bit (not t1) (not t2).
Proof.
unfold not.
auto with parametricity.
Qed.
Hint Resolve not_Parametric : parametricity.

Lemma and_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A} s1 s2 t1 t2 : R A Bit s1 s2 -> R A Bit t1 t2 -> R A Bit (and s1 t1) (and s2 t2).
Proof.
unfold and.
auto with parametricity.
Qed.
Hint Resolve and_Parametric : parametricity.

Lemma or_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {A} s1 s2 t1 t2 : R A Bit s1 s2 -> R A Bit t1 t2 -> R A Bit (or s1 t1) (or s2 t2).
Proof.
unfold or.
auto with parametricity.
Qed.
Hint Resolve or_Parametric : parametricity.

Lemma xor3_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  : R _ _ xor3 xor3.
Proof.
unfold xor3.
auto with parametricity.
Qed.
Hint Immediate xor3_Parametric : parametricity.

Lemma maj_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  : R _ _ maj maj.
Proof.
unfold maj.
auto with parametricity.
Qed.
Hint Immediate maj_Parametric : parametricity.
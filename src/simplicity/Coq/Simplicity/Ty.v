Set Primitive Projections.
Set Implicit Arguments.

Declare Scope ty_scope.

Inductive Ty : Set :=
| Unit : Ty
| Sum  : Ty -> Ty -> Ty
| Prod : Ty -> Ty -> Ty.
Bind Scope ty_scope with Ty.

Fixpoint tySem (X : Ty) : Set :=
match X with
| Unit => Datatypes.unit
| Sum A B => tySem A + tySem B
| Prod A B => tySem A * tySem B
end.

Notation "A + B" := (Sum A B) : ty_scope.
Notation "A * B" := (Prod A B) : ty_scope.
Coercion tySem : Ty >-> Sortclass.

Definition Arrow (A B : Ty) := A -> B.
Definition Kleisli (M : Type -> Type) (A B : Ty) := A -> M B.

Record tyAlg (A : Set) : Set :=
{ unitA : A
; sumA  : A -> A -> A
; prodA : A -> A -> A
}.

Fixpoint tyCata A (alg : tyAlg A) (t : Ty) : A :=
match t with
| Unit => unitA alg
| Sum tl tr => sumA alg (tyCata alg tl) (tyCata alg tr)
| Prod t1 t2 => prodA alg (tyCata alg t1) (tyCata alg t2)
end.

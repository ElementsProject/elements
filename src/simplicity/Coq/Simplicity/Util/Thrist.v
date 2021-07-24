Module Thrist.

Declare Scope thrist_scope.

Inductive T {A} (P : A -> A -> Type) (z:A) : A -> Type :=
| nil : T P z z
| cons : forall x y, P x y -> T P z y -> T P z x.

Fixpoint append {A : Type} {P : A -> A -> Type} {x y z} (thr1 : T P y x) : T P z y -> T P z x :=
match thr1 with
| nil _ _ => fun thr2 => thr2
| cons _ _ _ _ hd tl => fun thr2 => cons _ _ _ _ hd (append tl thr2)
end.

End Thrist.
Bind Scope thrist_scope with Thrist.T.

Local Open Scope thrist_scope.

Notation "'Thrst' P x y" := (Thrist.T P y x) (at level 0, P at level 0, x at level 0, y at level 0).
Notation "x <| y" := (Thrist.cons _ _ _ _ x y) (at level 30) : thrist_scope.
Notation "x |><| y" := (Thrist.append x y) (at level 30)  : thrist_scope.
Notation "[]" := (Thrist.nil _ _ ) : thrist_scope.
Notation "x |> y" := (x |><| (y <| [])) (at level 30) : thrist_scope.

Definition eq_nil {A : Type} {P : A -> A -> Type} {x y} (Hxy : x = y) : Thrst P x y :=
match Hxy with
| eq_refl => []
end.

Lemma thrist_app_nil {A : Type} {P : A -> A -> Type} {x y} (thr : Thrst P x y) :
  thr |><| [] = thr.
Proof.
induction thr.
 reflexivity.
cbn.
rewrite IHthr.
reflexivity.
Qed.

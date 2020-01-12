Require Import Simplicity.Ty.

Set Implicit Arguments.

Inductive Term : Ty -> Ty -> Set :=
| iden : forall {A}, Term A A
| comp : forall {A B C}, Term A B -> Term B C -> Term A C
| unit : forall {A}, Term A Unit
| injl : forall {A B C}, Term A B -> Term A (Sum B C)
| injr : forall {A B C}, Term A C -> Term A (Sum B C)
| case : forall {A B C D},
    Term (Prod A C) D -> Term (Prod B C) D -> Term (Prod (Sum A B) C) D
| pair : forall {A B C}, Term A B -> Term A C -> Term A (Prod B C)
| take : forall {A B C}, Term A C -> Term (Prod A B) C
| drop : forall {A B C}, Term B C -> Term (Prod A B) C.

Fixpoint eval {A B} (x : Term A B) : tySem A -> tySem B :=
match x in Term A B return tySem A -> tySem B with
| iden => fun a => a
| comp s t => fun a => eval t (eval s a)
| unit => fun _ => tt
| injl t => fun a => inl (eval t a)
| injr t => fun a => inr (eval t a)
| case s t => fun p => let (ab, c) := p in
    match ab with
    | inl a => eval s (a, c)
    | inr b => eval t (b, c)
    end
| pair s t => fun a => (eval s a, eval t a)
| take t => fun ab => eval t (fst ab)
| drop t => fun ab => eval t (snd ab)
end.

Section Completeness.

Fixpoint scribe {A B : Ty} : B -> Term A B :=
match B with
| Unit => fun _ => unit
| Sum BL BR => fun b =>
  match b with
  | inl l => injl (scribe l)
  | inr r => injr (scribe r)
  end
| Prod B1 B2 => fun b => pair (scribe (fst b)) (scribe (snd b))
end.

Lemma scribe_correct (A B : Ty) (a : A) (b : B) : eval (scribe b) a = b.
Proof.
induction B.
- destruct b; reflexivity.
- destruct b as [b|b];cbn;f_equal;auto.
- destruct b as [b0 b1];cbn;f_equal;auto.
Qed.

Fixpoint reifyProd {A B C : Ty} : (A -> Term B C) -> Term (Prod A B) C :=
match A with
| Unit => fun f => drop (f tt)
| Sum AL AR => fun f => case (reifyProd (fun al => f (inl al)))
                             (reifyProd (fun ar => f (inr ar)))
| Prod A1 A2 => fun f => comp (pair (take (take iden))
                                    (pair (take (drop iden)) (drop iden)))
                         (reifyProd (fun a1 => reifyProd (fun a2 => f (a1, a2))))
end.

Lemma reifyProd_correct : forall (A B C : Ty) (f : A -> Term B C) (a : A) (b : B),
  eval (reifyProd f) (a, b) = eval (f a) b.
Proof.
intros A.
induction A; intros B C f a b.
- destruct a; reflexivity.
- destruct a as [a|a];cbn;[rewrite IHA1|rewrite IHA2];reflexivity.
- destruct a as [a1 a2];cbn;rewrite IHA1, IHA2;reflexivity.
Qed.

Fixpoint reify {A B : Ty} : (A -> B) -> Term A B :=
match A with
| Unit => fun f => scribe (f tt)
| Sum AL AR => fun f => comp (pair iden unit)
                             (case (take (reify (fun al => f (inl al))))
                                   (take (reify (fun ar => f (inr ar)))))
| Prod A1 A2 => fun f => reifyProd (fun a1 => reify (fun a2 => f (a1, a2)))
end.

Lemma reify_correct (A B : Ty) (f : A -> B) (a : A) : eval (reify f) a = f a.
Proof.
induction A.
- destruct a; cbn; apply scribe_correct.
- destruct a as [a|a];cbn;[apply IHA1|apply IHA2].
- destruct a as [a0 a1]; cbn; rewrite reifyProd_correct; apply IHA2.
Qed.

Theorem Simplicity_Completeness : forall (A B : Ty) (f : A -> B),
  { t : Term A B | forall a, eval t a = f a }.
Proof.
intros A B f.
exists (reify f).
apply reify_correct.
Defined.

End Completeness.
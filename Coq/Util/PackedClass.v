Require Import Coq.Strings.String.

(* Assia Mahboubi, Enrico Tassi.  Canonical Structures for the working Coq user.  2013.
 * <hal-00816703v1> https://hal.inria.fr/hal-00816703v1
 *)

Inductive phantom {T : Type} (t : T) : Type := Phantom.

Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string) :=
  phantom t1 -> phantom t2.

Definition id {T} {t : T} (x : phantom t) := x.

Notation "[find v | t1 ~ t2 ] p" := (fun v (_ : unify t1 t2 None) => p) (at level 50, v ident, only parsing).
Notation "[find v | t1 ~ t2 | msg ] p" := (fun v (_ : unify t1 t2 (Some msg)) => p) (at level 50, v ident, only parsing).
Notation "'Error : t : msg" := (unify _ t (Some msg)) (at level 50, format "''Error'  :  t  :  msg").
Open Scope string_scope.
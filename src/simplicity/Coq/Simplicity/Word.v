Require Import Logic.Eqdep_dec.
Require Import List.
Require Import ZArith.
Require Import Simplicity.Util.Arith.
Require Import Lia.
Require compcert.lib.Integers.

Require Import Simplicity.Ty.
Require Import Simplicity.Alg.
Require Import Simplicity.Bit.
Require Import Simplicity.Digest.
Set Implicit Arguments.

Local Set Keyed Unification.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.

Fixpoint Word (n : nat) :=
match n with
| 0 => Bit
| S n => let rec := Word n in Prod rec rec
end.

Module ToZ.

Record class T := Class
  { bitSize : nat
  ; toZ : T -> Z
  ; fromZ : Z -> T
  ; from_toZ : forall (v : T), fromZ (toZ v) = v
  ; to_fromZ : forall (z : Z), toZ (fromZ z) = Zmod z (two_power_nat bitSize)
  }.

Structure type := Pack { obj :> Ty; class_of : class obj }.
Arguments Pack : clear implicits.

Module Theory.

Section Context.

Context {T : type}.

Definition bitSize : nat := bitSize (class_of T).
Definition toZ : obj T -> Z := toZ (class_of T).
Definition fromZ : Z -> obj T := fromZ (class_of T).

Lemma from_toZ (v : T) : fromZ (toZ v) = v.
Proof.
unfold fromZ, toZ.
destruct (class_of T); auto.
Qed.

Lemma to_fromZ (z : Z) : toZ (fromZ z : T) = Zmod z (two_power_nat bitSize).
Proof.
unfold fromZ, toZ, bitSize.
destruct (class_of T); auto.
Qed.

Lemma toZ_mod (v : T) : toZ v = Zmod (toZ v) (two_power_nat bitSize).
Proof.
rewrite <- from_toZ at 1.
apply to_fromZ.
Qed.

Lemma galois (v : T) (z : Z) : v = fromZ z <-> eqm (two_power_nat bitSize) (toZ v) z.
Proof.
unfold eqm.
split.
- intros ->.
  rewrite to_fromZ.
  rewrite Z.mod_mod;[reflexivity|].
  rewrite two_power_nat_equiv.
  auto using  Z.pow_nonzero with zarith.
- unfold eqm.
  rewrite <- 2!to_fromZ, from_toZ.
  rewrite <- from_toZ at 2.
  intros ->.
  rewrite from_toZ.
  reflexivity.
Qed.

End Context.
Arguments bitSize : clear implicits.
End Theory.
End ToZ.
Export ToZ.Theory.
Coercion ToZ.obj : ToZ.type >-> Ty.

Section BitToZ.

Let BitToZ (v : Bit) : Z :=
match v with
| Bit.zero => 0%Z
| Bit.one => 1%Z
end.

Let BitFromZ (z : Z) : Bit :=
if Z.odd z then Bit.one else Bit.zero.

Lemma Bit_from_toZ (v : Bit) : BitFromZ (BitToZ v) = v.
Proof.
destruct v as [[] | []]; reflexivity.
Qed.

Lemma Bit_to_fromZ (z : Z) : BitToZ (BitFromZ z) = Zmod z (two_power_nat 1).
Proof.
unfold BitFromZ.
rewrite (Zmod_odd z).
destruct (Z.odd z); reflexivity.
Qed.

Definition BitToZ_Class := ToZ.Class 1 BitToZ BitFromZ Bit_from_toZ Bit_to_fromZ.
End BitToZ.
Canonical Structure BitToZ : ToZ.type := ToZ.Pack Bit BitToZ_Class.

Section PairToZ.
Context {a b : ToZ.type}.

Let PairBitSize : nat := bitSize a + bitSize b.

Let PairToZ (v : a * b) : Z :=
let (va, vb) := v in
 toZ va * two_power_nat (bitSize b) +
 toZ vb.

Let PairFromZ (z : Z) : a * b :=
( fromZ (z / two_power_nat (bitSize b))
, fromZ z
).

Lemma Pair_from_toZ (v : a * b) : PairFromZ (PairToZ v) = v.
Proof.
destruct v as [va vb].
cbn; unfold PairFromZ.
assert (Hb : two_power_nat (bitSize b) <> 0%Z).
 rewrite two_power_nat_equiv.
 apply Z.pow_nonzero; auto with zarith.
f_equal.
- rewrite Z_div_plus_full_l by auto.
  rewrite <- (from_toZ vb), to_fromZ.
  rewrite Zmod_div, Z.add_0_r.
  apply from_toZ.
- rewrite <- (from_toZ (fromZ _ )), to_fromZ.
  rewrite Zplus_comm, Z_mod_plus_full.
  rewrite <- toZ_mod.
  apply from_toZ.
Qed.

Lemma Pair_to_fromZ (z : Z) : PairToZ (PairFromZ z) = Zmod z (two_power_nat PairBitSize).
Proof.
assert (H2 : forall n, (0 < Zpower_nat 2 n)%Z).
 intros n.
 rewrite Zpower_nat_Z.
 auto using Z.pow_pos_nonneg with zarith.
assert (H2' : forall n, (Zpower_nat 2 n <> 0)%Z).
 intros n.
 generalize (H2 n).
 lia.
unfold PairBitSize.
rewrite two_power_nat_correct, Zpower_nat_is_exp.
rewrite Zmult_comm, Z.rem_mul_r by auto; cbn.
rewrite 2!to_fromZ; rewrite !two_power_nat_correct.
rewrite Zplus_comm, Zmult_comm; reflexivity.
Qed.

Definition PairToZ_Class :=
  ToZ.Class PairBitSize PairToZ PairFromZ Pair_from_toZ Pair_to_fromZ.

End PairToZ.
Canonical Structure PairToZ (a b : ToZ.type) : ToZ.type := ToZ.Pack (a * b) PairToZ_Class.

Lemma toZ_Pair {A B : ToZ.type} (a : A) (b : B) :
  @toZ (PairToZ A B) (a, b) = (toZ a * two_power_nat (bitSize B) + toZ b)%Z.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Lemma bitSize_Pair (A B : ToZ.type) :
  bitSize (PairToZ A B) = (bitSize A + bitSize B)%nat.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Fixpoint WordToZ_Class {n : nat} : ToZ.class (Word n) :=
match n with
| 0 => BitToZ_Class
| (S m) => @PairToZ_Class (ToZ.Pack _ WordToZ_Class) (ToZ.Pack _ WordToZ_Class)
end.

Canonical Structure WordToZ (n : nat) : ToZ.type := ToZ.Pack (Word n) WordToZ_Class.

Notation Word8 := (Word 3).
Notation Word16 := (Word 4).
Notation Word32 := (Word 5).
Notation Word64 := (Word 6).
Notation Word256 := (Word 8).
Notation Word512 := (Word 9).

Lemma bitSize_Word n :
  Z.of_nat (bitSize (WordToZ n)) = two_power_nat n.
Proof.
induction n.
 reflexivity.
cbn.
rewrite Nat2Z.inj_add, IHn, two_power_nat_S.
ring.
Qed.

Lemma testbitToZLo {n} (ahi alo : Word n) i (Hi : (i < two_power_nat n)%Z) :
  Z.testbit (toZ ((ahi, alo) : Word (S n))) i = Z.testbit (toZ alo) i.
Proof.
rewrite (toZ_Pair ahi alo), two_power_nat_equiv, <- (Z.mod_pow2_bits_low _ _ _ Hi),
        bitSize_Word, Zplus_comm, Z_mod_plus_full.
auto using Z.mod_pow2_bits_low.
Qed.

Lemma testbitToZHi {n} (ahi alo : Word n) i (Hi : (two_power_nat n <= i)%Z) :
  Z.testbit (toZ ((ahi, alo) : Word (S n))) i = Z.testbit (toZ ahi) (i - two_power_nat n).
Proof.
rewrite <- bitSize_Word in *.
replace i with (i - Z.of_nat (bitSize (WordToZ n)) + Z.of_nat (bitSize (WordToZ n)))%Z at 1 by ring.
rewrite (toZ_Pair ahi alo), two_power_nat_equiv, <- Z.div_pow2_bits,
        Zplus_comm, Z_div_plus, (toZ_mod alo), two_power_nat_equiv, Zmod_div, Z.add_0_l;
auto using Z.lt_gt, Z.pow_pos_nonneg with zarith.
Qed.

Definition to_hash256 (h : Word256) : hash256 :=
  let '(((h0,h1),(h2,h3)),((h4,h5),(h6,h7))) := h in
    Hash256 (List.map (fun x : Word32 => Integers.Int.repr (toZ x))
              [h0;h1;h2;h3;h4;h5;h6;h7])
            refl_equal.

Definition from_hash256 (l : hash256) : Word256 :=
match map (fun x => fromZ (Integers.Int.unsigned x) : Word32) (hash256_reg l) with
| [h0;h1;h2;h3;h4;h5;h6;h7] => (((h0,h1),(h2,h3)),((h4,h5),(h6,h7)))
| _ => fromZ 0%Z
end.

Lemma from_to_hash256 (h : Word256) : from_hash256 (to_hash256 h) = h.
Proof.
assert (H32 : forall x : Word32, (0 <= toZ x <= Integers.Int.max_unsigned)%Z).
 intros x.
 change Integers.Int.max_unsigned with (Z.pred Integers.Int.modulus).
 rewrite <- Z.lt_le_pred, toZ_mod.
 apply Z.mod_pos_bound.
 reflexivity.
destruct h as [[[h0 h1][h2 h3]][[h4 h5][h6 h7]]]; cbn -[Word toZ fromZ].
repeat rewrite Integers.Int.unsigned_repr by auto.
repeat rewrite from_toZ.
reflexivity.
Qed.

Lemma to_from_hash256 (h : hash256) : to_hash256 (from_hash256 h) = h.
Proof.
destruct h as [[|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|h8 h]]]]]]]]] Hh]; try discriminate.
simpl.
rewrite !to_fromZ.
change (two_power_nat (bitSize (WordToZ 5))) with Integers.Int.modulus.
rewrite <- !Integers.Int.unsigned_repr_eq, !Integers.Int.repr_unsigned.
elim Hh using K_dec_set;[decide equality|].
reflexivity.
Qed.

Section Definitions.

Section Arith.

Fixpoint zero {n : nat} {A} {term : Core.Algebra} : term A (Word n) :=
match n with
| 0 => false
| S n => zero &&& zero
end.

Definition adderBit {term : Core.Algebra} : term (Bit * Bit) (Bit * Bit) :=
  cond (iden &&& not iden) (false &&& iden).

Definition fullAdderBit {term : Core.Algebra} : term (Bit * (Bit * Bit)) (Bit * Bit) :=
  let add := adderBit in
    drop add &&& O H
>>> O O H &&& (O I H &&& I H >>> add)
>>> cond true O H &&& I I H.

Definition buildFullAdder {W} {term : Core.Algebra} (rec : term (Bit * (W * W)) (Bit * W)) :
  term (Bit * ((W * W) * (W * W))) (Bit * (W * W)) :=
    drop (O O H &&& I O H) &&& (O H &&& drop (O I H &&& I I H) >>> rec)
>>> I I H &&& (I O H &&& O H >>> rec)
>>> I O H &&& (I I H &&& O H).

Fixpoint fullAdder {n : nat} {term : Core.Algebra} : term (Bit * (Word n * Word n)) (Bit * Word n) :=
match n with
| 0 => fullAdderBit
| S n => buildFullAdder fullAdder
end.

Definition adder {n : nat} {term : Core.Algebra} : term (Word n * Word n) (Bit * Word n) :=
match n with
| 0 => adderBit
| S n => false &&& iden >>> fullAdder
end.

Definition fullMultiplierBit {term : Core.Algebra} : term ((Bit * Bit) * (Bit * Bit)) (Word 1) :=
    take (cond iden false) &&& drop iden
>>> fullAdderBit.

Definition buildFullMultiplier {W} {term : Core.Algebra} (rec : term ((W * W) * (W * W)) (W * W)) :
  term (((W * W) * (W * W)) * ((W * W) * (W * W))) (((W * W) * (W * W))) :=
    take (O O H &&& (I O H &&& O I H))
&&& ((take (O O H &&& I I H) &&& drop (O O H &&& I O H) >>> rec)
&&& (take (O I H &&& I I H) &&& drop (O I H &&& I I H) >>> rec))
>>> take (O H &&& I O H)
&&& (drop (O O H &&& I I H) &&& (O I H &&& drop (O I H &&& I O H) >>> rec))
>>> (O H &&& drop (I O H &&& O O H) >>> rec) &&& drop (I I H &&& O I H).

Fixpoint fullMultiplier {n : nat} {term : Core.Algebra} : term ((Word n * Word n) * (Word n * Word n)) (Word (S n)) :=
match n with
| 0 => fullMultiplierBit
| S n => buildFullMultiplier fullMultiplier
end.

Definition multiplier {n : nat} {term : Core.Algebra} : term (Word n * Word n) (Word (S n)) :=
   iden &&& (zero &&& zero) >>> fullMultiplier.

End Arith.

Section BitVector.

Definition buildBitwiseTri {W} {term : Core.Algebra} (rec : term (W * (W * W)) W) :
  term ((W * W) * ((W * W) * (W * W))) (W * W) :=
    (O O H &&& (I O O H &&& I I O H) >>> rec)
&&& (O I H &&& (I O I H &&& I I I H) >>> rec).

Fixpoint bitwiseTri {n : nat} {term : Core.Algebra} (op : term (Bit * (Bit * Bit)) Bit) :
  term (Word n * (Word n * Word n)) (Word n) :=
match n with
| 0 => op
| S n => buildBitwiseTri (bitwiseTri op)
end.

Fixpoint subseq0_le {n m} {term : Core.Algebra} : term (Word n) (Word (m + n)) :=
match m with
| 0 => iden
| S m => zero &&& subseq0_le 
end.

Fixpoint subseq0_ge {n m} {term : Core.Algebra} : term (Word (m + n)) (Word n) :=
match m with
| 0 => iden
| S m => drop subseq0_ge
end.

Definition subseq0 {n m} {term : Core.Algebra} : term (Word n) (Word m) :=
match natDiff n m with
| inl (exist _ i Hi) => eq_rect _ (fun x => term (Word n) (Word x)) subseq0_le _ Hi
| inr (exist _ i Hi) => eq_rect _ (fun x => term (Word x) (Word m)) subseq0_ge _ Hi
end.

Fixpoint subseqBit {n} (z:Z) {term : Core.Algebra} : term Bit (Word n) :=
match n with
| 0 => match (Z.eq_dec z 0)%Z with
       | Specif.left _ => iden
       | Specif.right _ => false
       end
| S n => subseqBit (z + two_power_nat n) &&& subseqBit z
end.

Fixpoint subseqPair {n m} (z:Z) {term : Core.Algebra} (rec : forall {m}, Z -> term (Word n) (Word m)) : term (Word (S n)) (Word m) :=
match (Z.eq_dec z 0)%Z with
| Specif.left _ => subseq0
| Specif.right _ =>
  match Z_lt_le_dec z (two_power_nat n) with
  | Specif.right _ =>
    match Z_lt_le_dec z (two_power_nat (S n)) with
    | Specif.right _ => zero
    | Specif.left _ => take (rec (z - two_power_nat n)%Z)
    end
  | Specif.left Hz0 =>
    match Z_lt_le_dec (two_power_nat n) (z + two_power_nat m) with
    | Specif.right _ => 
      match Z_lt_le_dec 0 (z + two_power_nat m) with
      | Specif.right _ => zero
      | Specif.left _ => drop (rec z)
      end
    | Specif.left Hz1 =>
      match m return ((two_power_nat n < z + two_power_nat m)%Z -> term (Word (S n)) (Word m)) with
      | 0 => fun Hz1 => False_rect _ (Zlt_not_le _ _ Hz0 (Zlt_succ_le _ _ Hz1))
      | S m => fun _ => subseqPair (z + two_power_nat m) (@rec) &&& subseqPair z (@rec)
      end Hz1
    end
  end
end.

Fixpoint subseq {n m} (z:Z) {term : Core.Algebra} : term (Word n) (Word m) :=
match n with
| 0 => subseqBit z
| S n => subseqPair z (fun m z => @subseq n m z term)
end.

Definition shift {n} (z:Z) {term : Core.Algebra} : term (Word n) (Word n) := subseq z.

Fixpoint subseqWrap0_le {n m} {term : Core.Algebra} : term (Word n) (Word (m + n)) :=
match m with
| 0 => iden
| S m => let rec := subseqWrap0_le in rec &&& rec
end.

Definition subseqWrap0 {n m} {term : Core.Algebra} : term (Word n) (Word m) :=
match natDiff n m with
| inl (exist _ i Hi) => eq_rect _ (fun x => term (Word n) (Word x)) subseqWrap0_le _ Hi
| inr (exist _ i Hi) => eq_rect _ (fun x => term (Word x) (Word m)) subseq0_ge _ Hi
end.

Fixpoint subseqWrapPair {n m} (z:Z) {term : Core.Algebra} (rec : forall {m}, Z -> term (Word n) (Word m)) : term (Word (S n)) (Word m) :=
let z := (z mod (two_power_nat (S n)))%Z in (* shadow old value of z to take it out of scope *)
match (Z.eq_dec z 0)%Z with
| Specif.left _ => subseqWrap0
| Specif.right _ =>
  match (Z_lt_le_dec z (two_power_nat n)) with
  | Specif.left _ =>
    match m with
    | 0 => drop (rec z)
    | S m =>
      match Z_lt_le_dec (two_power_nat n) (z + two_power_nat (S m)) with
      | Specif.right _ => drop (rec z)
      | Specif.left _ => subseqWrapPair (z + two_power_nat m) (@rec) &&&  subseqWrapPair z (@rec)
      end
    end
  | Specif.right _ => 
    match m with
    | 0 => take (rec (z - two_power_nat n)%Z)
    | S m =>
      match Z_lt_le_dec (two_power_nat (S n)) (z + two_power_nat (S m)) with
      | Specif.left _ => subseqWrapPair (z + two_power_nat m) (@rec) &&& subseqWrapPair z (@rec)
      | Specif.right _ => take (rec (z - two_power_nat n)%Z)
      end
    end
  end
end.

Fixpoint subseqWrap {n m} (z:Z) {term : Core.Algebra} : term (Word n) (Word m) :=
match n with
| 0 => subseqWrap0
| S n => subseqWrapPair z (fun m z => @subseqWrap n m z term)
end.

Definition rotate {n} (z:Z) {term : Core.Algebra} : term (Word n) (Word n) := subseqWrap z.

End BitVector.

End Definitions.

Section Specifications.

Lemma zero_correct n (A : Ty) (a : A) : toZ (|[zero (n:=n)]| a) = 0%Z.
Proof.
induction n; cbn;[|rewrite IHn];reflexivity.
Qed.

Lemma fullAdder_correct n : forall (a b : Word n) (c : Bit),
  (toZ (|[fullAdder]| (c, (a, b))) = toZ a + toZ b  + toZ c)%Z.
Proof.
induction n. { intros [[] | []] [[] | []] [[] | []]; reflexivity. }
intros [ahi alo] [bhi blo] c.
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo).
set (C := two_power_nat _).
transitivity ((toZ ahi + toZ bhi) * C + (toZ alo + toZ blo + toZ c))%Z;[|ring].
rewrite <- IHn.
destruct (|[fullAdder]| (c, (alo, blo))) as [c0 rlo]; clear alo blo c.
cbn [fst snd].
rewrite (toZ_Pair c0 rlo).
fold C.
transitivity ((toZ ahi + toZ bhi + toZ c0) * C + toZ rlo)%Z;[|ring].
rewrite <- IHn.
destruct (|[fullAdder]| (c0, (ahi, bhi))) as [c1 rhi]; clear ahi bhi c0.
cbn [fst snd].
rewrite (toZ_Pair c1 rhi); fold C.
rewrite (toZ_Pair c1 _).
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
rewrite (toZ_Pair rhi rlo); fold C.
ring.
Qed.

Lemma adder_correct n : forall (a b : Word n),
  (toZ (|[adder]| (a, b)) = toZ a + toZ b)%Z.
destruct n. { intros [[] | []] [[] | []]; reflexivity. }
unfold adder.
generalize (S n); clear n; intros n a b.
cbn -[toZ].
rewrite fullAdder_correct.
cbn.
ring.
Qed.

Lemma fullMultiplier_correct n : forall (a b c d : Word n),
  (toZ (|[fullMultiplier]| ((a, b), (c, d))) = toZ a * toZ b + toZ c + toZ d)%Z.
Proof.
induction n. { intros [[] | []] [[] | []] [[] | []] [[] | []]; reflexivity. }
intros [ahi alo] [bhi blo] [chi clo] [dhi dlo].
cbn -[toZ]; fold tySem; fold (tySem Bit).
rewrite (toZ_Pair ahi alo), (toZ_Pair bhi blo), (toZ_Pair chi clo), (toZ_Pair dhi dlo).
set (C := two_power_nat _).
transitivity ((toZ ahi * C + toZ alo) * toZ bhi * C +
 ((toZ ahi * toZ blo + toZ chi + toZ dhi) * C) + (toZ alo * toZ blo + toZ clo + toZ dlo))%Z;
 [|ring].
rewrite <- 2!IHn.
destruct (|[fullMultiplier]| ((alo, blo), (clo, dlo))) as [c0 rOO]; clear clo dlo.
destruct (|[fullMultiplier]| ((ahi, blo), (chi, dhi))) as [c1 c2]; clear chi dhi blo.
cbn [fst snd].
rewrite (toZ_Pair c1 c2), (toZ_Pair c0 rOO); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c1) * C * C +
 (toZ bhi * toZ alo + toZ c2 + toZ c0) * C + toZ rOO)%Z;
 [|ring].
rewrite <- IHn.
destruct (|[fullMultiplier]| ((bhi, alo), (c2, c0))) as [c3 rOI]; clear c2 c0 alo.
cbn [fst snd].
rewrite (toZ_Pair c3 rOI); fold C.
transitivity ((toZ ahi * toZ bhi + toZ c3 + toZ c1) * C * C + toZ rOI * C + toZ rOO)%Z;
 [|ring].
rewrite <- IHn.
destruct (|[fullMultiplier]| ((ahi, bhi), (c3, c1))) as [rII rIO]; clear c3 c1 ahi bhi.
rewrite (@toZ_Pair (WordToZ (S n)) (WordToZ (S n))), (toZ_Pair rOI rOO); fold C.
rewrite (bitSize_Pair (WordToZ n) (WordToZ n)).
rewrite two_power_nat_correct, Zpower_nat_is_exp, <- two_power_nat_correct; fold C.
set (X := toZ _); ring.
Qed.

Lemma multiplier_correct n : forall (a b : Word n),
  (toZ (|[multiplier]| (a, b)) = toZ a * toZ b)%Z.
Proof.
intros a b.
cbn -[toZ].
rewrite fullMultiplier_correct, zero_correct.
ring.
Qed.

Definition TrinarySpec {n} (f : bool -> bool -> bool -> bool) (term : Arrow (Word n * (Word n * Word n)) (Word n)) :=
  forall (x y z : Word n) i, (Z.testbit (toZ (term (x,(y,z)))) i = f (Z.testbit (toZ x) i) (Z.testbit (toZ y) i) (Z.testbit (toZ z) i))%Z.

Lemma bitwiseTri_correct {n} (f : bool -> bool -> bool -> bool) (op : Arrow (Bit * (Bit * Bit)) Bit)
    (Hf : f Datatypes.false Datatypes.false Datatypes.false = Datatypes.false)
    (Hop : (forall (a b c : Bit), toBool (op (a,(b,c))) = f (toBool a) (toBool b) (toBool c))) :
  forall (a b c : Word n) i, (Z.testbit (toZ (bitwiseTri op (a,(b,c)))) i = f (Z.testbit (toZ a) i) (Z.testbit (toZ b) i) (Z.testbit (toZ c) i))%Z.
Proof.
induction n.
 intros a b c i.
 simpl (bitwiseTri op).
 assert (to01 : (forall (b : Bit), Z.testbit (toZ b) i = if toBool b then Z.testbit 1 i else Z.testbit 0 i)%Z) by
  (intros [[] | []]; reflexivity).
 repeat rewrite to01.
 rewrite Hop; clear - Hf.
 destruct (toBool a);
 destruct (toBool b);
 destruct (toBool c);
 destruct i; cbn; try rewrite Hf; try reflexivity;
 destruct (f _ _ _) in |- *; reflexivity.
intros [ahi alo] [bhi blo] [chi clo] i.
destruct (Z_lt_le_dec i (two_power_nat n)) as [Hi|Hi]; cbn;
[repeat rewrite (testbitToZLo _ _ Hi)
|repeat rewrite (testbitToZHi _ _ Hi)
]; auto.
Qed.

Let subseqSpec n m z (t : Arrow (Word n) (Word m)) :=
  forall x i, (0 <= i < two_power_nat m)%Z -> Z.testbit (toZ (t x)) i = Z.testbit (toZ x) (i + z)%Z.

Lemma subseq0_ge_correct n m : subseqSpec (m + n) n 0 subseq0_ge.
Proof.
intros x i Hi; clear - Hi.
rewrite Z.add_0_r.
induction m.
 reflexivity.
destruct x as [xhi xlo]; simpl.
rewrite testbitToZLo.
 apply IHm; assumption.
eapply Z.lt_le_trans;[apply Hi|].
auto using two_power_nat_le with arith.
Qed.

Lemma subseq0_le_correct n m : subseqSpec n (m + n) 0 subseq0_le.
Proof.
intros x i Hi; clear - Hi.
rewrite Z.add_0_r.
induction m.
 reflexivity.
simpl.
destruct (Z_lt_le_dec i (two_power_nat (m + n))) as [Hi0|Hi0].
- rewrite testbitToZLo by auto.
  apply IHm; tauto.
- rewrite testbitToZHi by auto.
  rewrite zero_correct, Z.bits_0, toZ_mod, two_power_nat_equiv.
  rewrite Z.mod_pow2_bits_high;[reflexivity|].
  split;[auto with zarith|].
  rewrite bitSize_Word.
  etransitivity;[|apply Hi0].
  auto using two_power_nat_le with arith.
Qed.

Lemma subseq0_correct n m : subseqSpec n m 0 subseq0.
Proof.
unfold subseq0.
destruct natDiff as [[i <-] | [i <-]]; cbn;
[apply subseq0_le_correct
|apply subseq0_ge_correct].
Qed.

Lemma subseqBit_correct n z : subseqSpec 0 n z (subseqBit z).
Proof.
intros x; clear.
revert z; induction n; intros z i Hi; simpl.
 change (two_power_nat 0) with 1%Z in Hi.
 replace i with 0%Z by auto with zarith; clear Hi.
 destruct Z.eq_dec as [->|Hz];[reflexivity|].
 destruct x as [[] | []];cbn;[rewrite Z.bits_0; reflexivity|].
 destruct (not_Zeq _ _ Hz) as [Hz0|Hz0];
 [rewrite Z.testbit_neg_r
 |rewrite Z.bits_above_log2];
 auto with zarith.
destruct (Z_lt_le_dec i (two_power_nat n)) as [Hi0|Hi0].
- rewrite testbitToZLo by auto.
  apply IHn; auto with zarith.
- rewrite two_power_nat_S in Hi.
  rewrite testbitToZHi, IHn by auto with zarith.
  f_equal; ring.
Qed.

Lemma subseqPair_correct n m z rec (Hrec : forall m z, subseqSpec n m z (rec m z)) :
  subseqSpec (S n) m z (subseqPair z rec).
Proof.
unfold subseqSpec in *.
revert z; induction m; intros z [xhi xlo] i Hi; cbn -[toZ zero subseq0 Word];
(destruct Z.eq_dec as [->|];[apply subseq0_correct; auto|]);
 repeat destruct Z_lt_le_dec; try rewrite zero_correct;
 try solve
 [destruct Zlt_not_le
 |rewrite testbitToZLo;[apply Hrec|]; auto with zarith
 |rewrite Z.bits_0, Z.testbit_neg_r; auto with zarith
 |rewrite testbitToZHi, <- Z.add_sub_assoc;[apply Hrec|]; auto with zarith
 |rewrite Z.bits_0, toZ_mod, two_power_nat_equiv, bitSize_Word, Z.mod_pow2_bits_high;
   rewrite <- bitSize_Word in *;
   auto with zarith].
destruct (Z_lt_le_dec i (two_power_nat m)) as [Hi0|Hi0].
- rewrite (testbitToZLo _ _ Hi0), IHm; auto with zarith.
- rewrite two_power_nat_S in Hi.
  rewrite (testbitToZHi _ _ Hi0), IHm by auto with zarith.
  f_equal; ring.
Qed.

Lemma subseq_correct n : forall m z, subseqSpec n m z (subseq z).
Proof.
induction n; intros; cbn;
auto using subseqBit_correct, subseqPair_correct.
Qed.

Lemma shift_correct n z (x : Word n) i (Hi : (0 <= i < two_power_nat n)%Z) :
  Z.testbit (toZ (|[shift z]| x)) i = Z.testbit (toZ x) (i + z)%Z.
Proof.
exact (subseq_correct n z x Hi).
Qed.

Let subseqWrapSpec n m z (t : Arrow (Word n) (Word m)) :=
  forall x i, (0 <= i < two_power_nat m)%Z ->
  Z.testbit (toZ (t x)) i = Z.testbit (toZ x) (Zmod (i + z) (two_power_nat  n)).

Lemma subseqWrap0_ge_correct n m : subseqWrapSpec (m + n) n 0 subseq0_ge.
Proof.
intros x i Hi.
rewrite Z.mod_small;[apply subseq0_ge_correct|split]; auto with zarith.
apply Z.lt_le_trans with (two_power_nat n);
auto using two_power_nat_le with zarith.
Qed.

Lemma subseqWrap0_le_correct n m : subseqWrapSpec n (m + n) 0 subseqWrap0_le.
Proof.
intros x i Hi; clear - Hi.
rewrite Z.add_0_r.
revert i Hi; induction m; intros i Hi.
 rewrite Z.mod_small; auto.
simpl.
destruct (Z_lt_le_dec i (two_power_nat (m + n))) as [Hi0|Hi0]; simpl in *.
 rewrite testbitToZLo by auto.
 apply IHm; tauto.
rewrite two_power_nat_S in Hi.
rewrite testbitToZHi, IHm by auto with zarith.
rewrite two_power_nat_plus.
replace (i - two_power_nat m * two_power_nat n)%Z with (i + (- two_power_nat m) * two_power_nat n)%Z by ring.
rewrite Z_mod_plus_full.
reflexivity.
Qed.

Lemma subseqWrap0_correct n m : subseqWrapSpec n m 0 subseqWrap0.
Proof.
unfold subseqWrap0.
destruct natDiff as [[i <-] | [i <-]]; cbn;
[apply subseqWrap0_le_correct
|apply subseqWrap0_ge_correct].
Qed.

Lemma subseqWrapBit_correct n z : subseqWrapSpec 0 n z subseqWrap0.
Proof.
intros x i; rewrite Z.mod_1_r; revert x i.
unfold subseqWrap0.
destruct natDiff as [[i0 <-] | [i0 Hi0]]; cbn -[Word Z.testbit toZ].
 intros x i Hi; rewrite plus_0_r in Hi.
 revert i Hi; induction i0; intros i Hi.
  change (two_power_nat 0) with 1%Z in Hi.
  replace i with 0%Z by auto with zarith.
  reflexivity.
 simpl.
 destruct (Z_lt_le_dec i (two_power_nat i0)) as [Hi0|Hi0]; simpl in *.
  rewrite testbitToZLo by (rewrite plus_0_r; auto with zarith).
  apply IHi0; auto with zarith.
 rewrite two_power_nat_S in Hi.
 rewrite testbitToZHi by (rewrite plus_0_r; auto with zarith).
 apply IHi0; rewrite plus_0_r; auto with zarith.
rewrite <- Hi0; cbn.
rewrite Nat.eq_add_0 in Hi0.
destruct Hi0 as [Hi0 Hn].
rewrite Hi0, Hn.
change (two_power_nat 0) with 1%Z.
intros x i Hi.
replace i with 0%Z by auto with zarith.
reflexivity.
Qed.

Lemma subseqWrapPair_correct n m z rec (Hrec : forall m z, subseqWrapSpec n m z (rec m z)) :
  subseqWrapSpec (S n) m z (subseqWrapPair z rec).
Proof.
assert (Hpos : (0 < two_power_nat (S n))%Z).
 rewrite two_power_nat_equiv; auto using Z.pow_pos_nonneg with zarith.
assert (Hlt : (two_power_nat n <= two_power_nat (S n))%Z)
 by auto using two_power_nat_le with arith.
intros x i Hi.
rewrite <- Zplus_mod_idemp_r.
revert z x i Hi; induction m; intros z [xhi xlo] i Hi; cbn -[toZ zero subseqWrap0 Word];
 assert (Hz' := Z.mod_pos_bound z (two_power_nat (S n)) Hpos); 
 set (z':=Zmod z (two_power_nat (S n))) in *;
(destruct Z.eq_dec as [->|];[apply subseqWrap0_correct; auto|]);
 repeat destruct Z_lt_le_dec; simpl;
 change (two_power_nat 0) with 1%Z in *;
 solve
 [rewrite Z.mod_small, Hrec, testbitToZLo, Z.mod_small; auto with zarith
 |rewrite Z.mod_small, Hrec, testbitToZHi, <- Z.add_sub_assoc, Z.mod_small;
   repeat rewrite two_power_nat_S in *; auto with zarith
 |destruct (Z_lt_le_dec i (two_power_nat m)) as [Hi0|Hi0];
  [rewrite (testbitToZLo _ _ Hi0), IHm, Zplus_mod_idemp_r; auto with zarith
  |repeat rewrite two_power_nat_S in *; rewrite (testbitToZHi _ _ Hi0), IHm, Zplus_mod_idemp_r by auto with zarith
  ]; do 2 f_equal; ring
 ].
Qed.

Lemma subseqWrap_correct n : forall m z, subseqWrapSpec n m z (subseqWrap z).
Proof.
induction n; intros; cbn -[subseqWrap0];
auto using subseqWrapBit_correct, subseqWrapPair_correct.
Qed.

Lemma rotate_correct n z (x : Word n) i (Hi : (0 <= i < two_power_nat n)%Z) :
  Z.testbit (toZ (|[rotate z]| x)) i = Z.testbit (toZ x) (Zmod (i + z) (two_power_nat n))%Z.
Proof.
exact (subseqWrap_correct n z x Hi).
Qed.

End Specifications.

Lemma zero_Parametric {n A} {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R A (Word n) zero zero.
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Immediate zero_Parametric : parametricity.

Lemma adderBit_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ _ adderBit adderBit.
Proof.
unfold adderBit.
auto with parametricity.
Qed.
Hint Immediate adderBit_Parametric : parametricity.

Lemma fullAdderBit_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ _ fullAdderBit fullAdderBit.
Proof.
unfold fullAdderBit.
auto 10 with parametricity.
Qed.
Hint Immediate fullAdderBit_Parametric : parametricity.

Lemma buildFullAdder_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {W} t1 t2 : R _ (Bit * W) t1 t2 -> R _ _ (buildFullAdder t1) (buildFullAdder t2).
Proof.
unfold buildFullAdder.
auto 10 with parametricity.
Qed.
Hint Resolve buildFullAdder_Parametric : parametricity.

Lemma fullAdder_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ _ fullAdder (@fullAdder n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Immediate fullAdder_Parametric : parametricity.

Lemma adder_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ _ adder (@adder n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Immediate adder_Parametric : parametricity.

Lemma fullMultiplierBit_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) : R _ _ fullMultiplierBit fullMultiplierBit.
Proof.
unfold fullMultiplierBit.
auto with parametricity.
Qed.
Hint Immediate fullMultiplierBit_Parametric : parametricity.

Lemma buildFullMultiplier_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {W} t1 t2 : R _ (W * W) t1 t2 -> R _ _ (buildFullMultiplier t1) (buildFullMultiplier t2).
Proof.
unfold buildFullMultiplier.
auto 15 with parametricity.
Qed.
Hint Resolve buildFullMultiplier_Parametric : parametricity.

Lemma fullMultiplier_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ (Word n * Word n) fullMultiplier (@fullMultiplier n _).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Immediate fullMultiplier_Parametric : parametricity.

Lemma multiplier_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} : R _ _ multiplier (@multiplier n _).
Proof.
unfold multiplier.
simpl; auto with parametricity.
Qed.
Hint Immediate multiplier_Parametric : parametricity.

Lemma buildBitwiseTri_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {W} t1 t2 : R _ W t1 t2 -> R _ _ (buildBitwiseTri t1) (buildBitwiseTri t2).
Proof.
unfold buildBitwiseTri.
auto 10 with parametricity.
Qed.
Hint Resolve buildBitwiseTri_Parametric : parametricity.

Lemma bitwiseTri_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2)
  {n} op1 op2 : R _ _ op1 op2 -> R _ _ (bitwiseTri op1) (@bitwiseTri n _ op2).
Proof.
induction n; simpl; auto with parametricity.
Qed.
Hint Resolve bitwiseTri_Parametric : parametricity.

Lemma subseq0_Parametric {n m} {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word m) subseq0 subseq0.
Proof.
unfold subseq0.
destruct (natDiff n m) as [[i []] | [i []]];
 induction i; cbn; auto with parametricity.
Qed.
Hint Immediate subseq0_Parametric : parametricity.

Lemma subseqBit_Parametric {n} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ (Word n) (subseqBit z) (subseqBit z).
Proof.
revert z; induction n; cbn; intros z;
[destruct (Z.eq_dec _ _)|]; auto with parametricity.
Qed.
Hint Immediate subseqBit_Parametric : parametricity.

Lemma subseqPair_Parametric {n m} z {term1 term2 : Core.Algebra} rec1 rec2 (R : Core.Parametric.Rel term1 term2) :
  (forall m z, R (Word n) (Word m) (rec1 m z) (rec2 m z)) ->
  R (Word n * Word n) (Word m) (subseqPair z rec1) (subseqPair z rec2).
Proof.
change (R (Word n * Word n)) with (R (Word (S n))).
revert z; induction m; simpl subseqPair; intros z Hrec;
destruct (Z.eq_dec _ _) as [|];
repeat destruct Z_lt_le_dec;
repeat first [apply pair_Parametric
             |refine (drop_Parametric _ _ _ _)
             |refine (take_Parametric _ _ _ _)
             |destruct Zlt_not_le];
auto with parametricity.
Qed.
Hint Resolve subseqPair_Parametric : parametricity.

Lemma subseq_Parametric {n m} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word m) (subseq z) (subseq z).
Proof.
revert m z; induction n; simpl; auto with parametricity.
Qed.
Hint Immediate subseq_Parametric : parametricity.

Lemma shift_Parametric {n} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word n) (shift z) (shift z).
Proof.
unfold shift.
auto with parametricity.
Qed.
Hint Immediate shift_Parametric : parametricity.

Lemma subseqWrap0_Parametric {n m} {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word m) subseqWrap0 subseqWrap0.
Proof.
unfold subseqWrap0.
destruct (natDiff n m) as [[i []] | [i []]];
 induction i; cbn; auto with parametricity.
Qed.
Hint Immediate subseqWrap0_Parametric : parametricity.

Lemma subseqWrapPair_Parametric {n m} z {term1 term2 : Core.Algebra} rec1 rec2 (R : Core.Parametric.Rel term1 term2) :
  (forall m z, R (Word n) (Word m) (rec1 m z) (rec2 m z)) ->
  R (Word n * Word n) (Word m) (subseqWrapPair z rec1) (subseqWrapPair z rec2).
Proof.
change (R (Word n * Word n)) with (R (Word (S n))).
revert z; induction m; simpl subseqWrapPair; intros z Hrec;
destruct (Z.eq_dec _ _) as [|];
repeat (destruct Z_lt_le_dec);
repeat first [apply pair_Parametric
             |refine (drop_Parametric _ _ _ _)
             |refine (take_Parametric _ _ _ _)];
auto with parametricity.
Qed.
Hint Resolve subseqWrapPair_Parametric : parametricity.

Lemma subseqWrap_Parametric {n m} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word m) (subseqWrap z) (subseqWrap z).
Proof.
revert m z; induction n; simpl subseqWrap; auto with parametricity.
simpl; auto with parametricity.
Qed.
Hint Immediate subseqWrap_Parametric : parametricity.

Lemma rotate_Parametric {n} z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R (Word n) (Word n) (rotate z) (rotate z).
Proof.
unfold rotate.
auto with parametricity.
Qed.
Hint Immediate rotate_Parametric : parametricity.

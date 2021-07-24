Require Import ZArith.
Require Import List.
Require Import Lia.

Require sha.SHA256.
Require Import compcert.lib.Integers.
Global Unset Asymmetric Patterns. (* the VST library does a Global Set so we must unset it. *)
Import Coq.Strings.String.StringSyntax.

Require Import Simplicity.Alg.
Require Import Simplicity.Bit.
Require Import Simplicity.Digest.
Require Import Simplicity.Ty.
Require Import Simplicity.Word.

Set Implicit Arguments.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.

Local Tactic Notation "introLet" := match goal with
  |- context f [let N := ?V in (@?b N)] => let N0 := fresh N in set (N0 := V); let Y := eval cbv beta in (b N0) in let X := context f[Y] in change X
end.

Local Tactic Notation "clearLet" := match goal with
  |- context f [let N := ?V in (@?b N)] => let Y := eval cbv beta in (b V) in let X := context f[Y] in change X
end.

Definition repr_Block (b : Word512) : list int :=
  let (b0,b1) := b in
    hash256_reg (to_hash256 b0) ++ hash256_reg (to_hash256 b1).

Definition repr_Block_inv (l : list int) : Word512 :=
match l with
| [b0; b1; b2; b3; b4; b5; b6; b7;
   b8; b9; ba; bb; bc; bd; be; bf] =>
  (from_hash256 (Hash256 [b0; b1; b2; b3; b4; b5; b6; b7] refl_equal)
  ,from_hash256 (Hash256 [b8; b9; ba; bb; bc; bd; be; bf] refl_equal))
| _ => fromZ 0%Z
end.

Lemma repr_Block_inj (b : Word512) : repr_Block_inv (repr_Block b) = b.
Proof.
assert (H32 : forall x : Word32, (0 <= toZ x <= Int.max_unsigned)%Z).
 intros x.
 change Int.max_unsigned with (Z.pred Int.modulus).
 rewrite <- Z.lt_le_pred, toZ_mod.
 apply Z.mod_pos_bound.
 reflexivity.
destruct b as [[[[b0 b1][b2 b3]][[b4 b5][b6 b7]]]
               [[[b8 b9][ba bb]][[bc bd][be bf]]]].
simpl.
unfold from_hash256.
simpl map.
cbv iota beta.
repeat rewrite Int.unsigned_repr by auto.
repeat rewrite from_toZ.
reflexivity.
Qed.

Lemma repr_Block_length (b : Word512) : length (repr_Block b) = 16.
Proof.
destruct b as [b0 b1];cbn.
rewrite app_length, !hash256_len.
reflexivity.
Qed.

Section Definitions.

Definition scribe32 (z : Z) {A} {term : Core.Algebra} : term A Word32 :=
 scribe (fromZ z).

Definition add32 {term : Core.Algebra} : term (Word32 * Word32) Word32 := adder >>> I H.

Definition xor3Word32 {term : Core.Algebra} : term (Word32 * (Word32 * Word32)) Word32 := 
  bitwiseTri xor3.

Definition chWord32 {term : Core.Algebra} : term (Word32 * (Word32 * Word32)) Word32 := 
  bitwiseTri ch.

Definition majWord32 {term : Core.Algebra} : term (Word32 * (Word32 * Word32)) Word32 := 
  bitwiseTri maj.

Definition shift32 z {term : Core.Algebra} : term Word32 Word32 := 
  shift z.

Definition rotate32 z {term : Core.Algebra} : term Word32 Word32 := 
  rotate z.

Definition hashBlock {term : Core.Algebra} : term (Word256 * Word512) Word256 :=
let a32 := add32 in
let x32 := xor3Word32 in
let diag := O I H &&& I O H in
let odiag := O diag in
let idiag := I diag in
let bigDiag := O I I H &&& I O O H in
let part1Schedule := odiag &&& bigDiag in
let smallSigma0 := rotate32 7 &&& rotate32 18 &&& shift32 3 >>> x32 in
let smallSigma1 := rotate32 17 &&& rotate32 19 &&& shift32 10 >>> x32 in
let smallSigma := (O O O (O H &&& (I H >>> smallSigma0)) >>> a32)
             &&& (I (O O I H &&& (I I O H >>> smallSigma1)) >>> a32) >>> a32 in
let schedule := (O part1Schedule &&& (O idiag &&& (O I I I H &&& I (O O O H))))
           &&& (I part1Schedule &&& (I idiag &&& (I I I I H &&& smallSigma))) in
let bigSigma0 := rotate32 2 &&& rotate32 13 &&& rotate32 22 >>> x32 in
let bigSigma1 := rotate32 6 &&& rotate32 11 &&& rotate32 25 >>> x32 in
let t1 := (O H &&& I I O O O O H >>> a32) &&& I O (I (I I H &&& ((O O H >>> bigSigma1) &&& (O O H &&& diag >>> chWord32) >>> a32)) >>> a32) >>> a32 in
let t12 := O ((O I H &&& I H >>> majWord32) &&& (O (O H &&& (I H >>> bigSigma0)) >>> a32)) >>> a32 in
let t1d := O O O H &&& I O O H >>> a32 in
let part1Round := ((t1 &&& I O O O O H) &&& I O odiag)
             &&& I O (bigDiag &&& idiag) in
let part2Round := ((t12 &&& O O I H) &&& O I H)
              &&& ((t1d &&& I O I H) &&& I I H) in
let round := part1Round >>> part2Round in
let step := round &&& I I schedule in
let k0 := 1116352408%Z in
let ks :=    [ 1899447441; 3049323471; 3921009573;
   961987163 ; 1508970993; 2453635748; 2870763221;
   3624381080;  310598401;  607225278; 1426881987;
   1925078388; 2162078206; 2614888103; 3248222580;
   3835390401; 4022224774;  264347078;  604807628;
    770255983; 1249150122; 1555081692; 1996064986;
   2554220882; 2821834349; 2952996808; 3210313671;
   3336571891; 3584528711;  113926993;  338241895;
    666307205;  773529912; 1294757372; 1396182291;
   1695183700; 1986661051; 2177026350; 2456956037;
   2730485921; 2820302411; 3259730800; 3345764771;
   3516065817; 3600352804; 4094571909;  275423344;
    430227734;  506948616;  659060556;  883997877;
    958139571; 1322822218; 1537002063; 1747873779;
   1955562222; 2024104815; 2227730452; 2361852424;
   2428436474; 2756734187; 3204031479; 3329325298]%Z in
let compression := scribe32 k0 &&& iden >>> fold_right (fun k (rec : term (Word32 * (Word256 * Word512)) Word256) => scribe32 k &&& step >>> rec) round ks in
let collate (x : term Word256 Word32) := O x &&& I x >>> a32 in
  O H &&& compression >>>
    ((collate (O O O H) &&& collate (O O I H)) &&&
     (collate (O I O H) &&& collate (O I I H))) &&&
    ((collate (I O O H) &&& collate (I O I H)) &&&
     (collate (I I O H) &&& collate (I I I H))).

End Definitions.

Lemma add32_correct (x y : Word32) : 
  Int.repr (toZ (|[add32]| (x,y))) = Int.add (Int.repr (toZ x)) (Int.repr (toZ y)).
Proof.
rewrite coqlib3.add_repr.
change (_ (x, y)) with (|[I H]| (|[adder (n:=5)]| (x,y))).
rewrite <- (adder_correct _ x y).
destruct (|[adder (n:=5)]| (x,y)) as [c z].
rewrite toZ_Pair, two_power_nat_equiv.
rewrite <- Int.repr_unsigned, Int.unsigned_repr_eq.
rewrite Zplus_comm, Z_mod_plus_full.
rewrite toZ_mod.
reflexivity.
Qed.

Lemma xor3Word32_xor (x y z : Word32) :
  Int.repr (toZ (|[xor3Word32]| (x,(y,z)))) = Int.xor (Int.xor (Int.repr (toZ x)) (Int.repr (toZ y))) (Int.repr (toZ z)).
Proof.
apply Int.same_bits_eq; intros i Hi.
repeat rewrite Int.bits_xor by auto.
repeat rewrite Int.testbit_repr by auto.
set (f a b c := xorb (xorb a b) c).
apply (bitwiseTri_correct f);[|intros [[] | []] [[] | []] [[] | []]];
reflexivity.
Qed.

Lemma chWord32_Ch (x y z : Word32) :
  Int.repr (toZ (|[chWord32]| (x,(y,z)))) = SHA256.Ch (Int.repr (toZ x)) (Int.repr (toZ y)) (Int.repr (toZ z)).
Proof.
apply Int.same_bits_eq; intros i Hi.
unfold SHA256.Ch.
rewrite Int.bits_xor by auto.
repeat rewrite Int.bits_and by auto.
rewrite Int.bits_not by auto.
repeat rewrite Int.testbit_repr by auto.
set (f a b c := xorb (a && b) (negb a && c)).
apply (bitwiseTri_correct f);[|intros [[] | []] [[] | []] [[] | []]];
reflexivity.
Qed.

Lemma majWord32_Maj (x y z : Word32) :
  Int.repr (toZ (|[majWord32]| (x,(y,z)))) = SHA256.Maj (Int.repr (toZ x)) (Int.repr (toZ y)) (Int.repr (toZ z)).
Proof.
apply Int.same_bits_eq; intros i Hi.
unfold SHA256.Maj.
repeat rewrite Int.bits_xor by auto.
repeat rewrite Int.bits_and by auto.
repeat rewrite Int.testbit_repr by auto.
set (f a b c := xorb (xorb (a && c) (b && c)) (a && b)).
apply (bitwiseTri_correct f);[|intros [[] | []] [[] | []] [[] | []]];
reflexivity.
Qed.

Lemma shift32_correct z (Hz : (0 <= z <= Int.max_unsigned)%Z) (x : Word32) :
  Int.repr (toZ (|[shift32 z]| x)) = general_lemmas.Shr z (Int.repr (toZ x)).
Proof.
unfold general_lemmas.Shr.
apply Int.same_bits_eq; intros i Hi.
rewrite Int.testbit_repr by assumption.
rewrite Int.bits_shru by assumption.
unfold shift32.
rewrite shift_correct by assumption.
rewrite Int.unsigned_repr by assumption.
destruct (Coqlib.zlt _ _) as [Hiz|Hiz].
 rewrite Int.testbit_repr by lia.
 reflexivity.
rewrite toZ_mod, two_power_nat_equiv.
apply Z.mod_pow2_bits_high.
clear - Hiz.
cbn in *.
lia.
Qed.

Lemma rotate32_correct z (x : Word32) :
  Int.repr (toZ (|[rotate32 z]| x)) = SHA256.Rotr z (Int.repr (toZ x)).
Proof.
unfold SHA256.Rotr.
apply Int.same_bits_eq; intros i Hi.
rewrite Int.bits_ror by assumption.
rewrite Int.testbit_repr by assumption.
rewrite Int.testbit_repr by (apply Z_mod_lt; constructor).
unfold rotate32.
rewrite rotate_correct by assumption.
rewrite Int.unsigned_repr_eq, <- (Zplus_mod_idemp_r (z mod Int.modulus))%Z, <- Znumtheory.Zmod_div_mod; try constructor.
 rewrite Zplus_mod_idemp_r.
 reflexivity.
apply Znumtheory.Zmod_divide; auto with zarith.
Qed.

Lemma hashBlock_correct (h : Word256) (b : Word512) :
 to_hash256 (|[hashBlock]| (h, b)) = SHA256.hash_block (to_hash256 h) (repr_Block b) :> SHA256.registers.
Proof.
cbv beta delta [hashBlock].
do 7 clearLet.
do 6 introLet.
do 5 clearLet.
do 6 introLet.
simpl.
change (|[O H &&& compression]| (h, b)) with (h, |[compression]| (h,b)).
unfold SHA256.hash_block.
replace (SHA256.Round (to_hash256 h) (SHA256.nthi (repr_Block b)) 63) with
  (hash256_reg (to_hash256 (|[compression]| (h,b)))).
 destruct (|[compression]| (h,b)) as [[[h'0 h'1][h'2 h'3]][[h'4 h'5][h'6 h'7]]].
 destruct h as [[[h0 h1][h2 h3]][[h4 h5][h6 h7]]].
 simpl.
 rewrite <- !add32_correct.
 reflexivity.
clear collate.
pose (ks' := k0::ks).
pose (fr := fold_right (fun (k rec : Arrow (Word256 * Word512) (Word256 * Word512)) => rec >>> k) H (map (fun k => scribe32 k &&& H >>> step) (rev ks'))).
replace (|[compression]| (h,b)) with
  (|[fr >>> O H]| (h, b)); revgoals.
 unfold fr, compression, ks'; clear fr compression ks'.
 clearbody ks.
 rewrite <- fold_symmetric by reflexivity.
 rewrite <- fold_left_rev_right, map_rev, rev_involutive.
 simpl fold_right at 1.
 set (fr0 := fold_right comp _ _);fold (Word256) in fr0.
 set (fr1 := fold_right _ _ _).
 unfold comp; simpl.
 match goal with
  |- _ = fr1 ?p => generalize p
 end;
 intros p;change (tySem (Word32*(Word256*Word512))) in p;revert p.
 clear h b.
 induction ks;[reflexivity|].
 intros p.
 unfold fr0.
 simpl fold_right at 1.
 unfold comp; simpl; rewrite IHks.
 destruct p as [k [h b]].
 unfold fr1, comp; simpl; f_equal.
 unfold pair; simpl.
 unfold scribe32; rewrite !scribe_correct.
 reflexivity.
cut  (to_hash256 (fst (|[fr]| (h, b))) = SHA256.Round (to_hash256 h) (SHA256.nthi (repr_Block b)) 63 :> SHA256.registers
   /\ repr_Block (snd (|[fr]| (h, b))) = map (fun n => SHA256.W (SHA256.nthi (repr_Block b)) (Z.of_nat n)) (seq (Z.to_nat (63 + 1)) 16)).
 intros [<- _].
 reflexivity.
revert fr.
rewrite <- (firstn_all ks').
change (length ks') with (Z.to_nat (63 + 1)).
cut (63 < 64)%Z;[|lia].
apply SHA256.Round_ind.
 intros t Ht _ _ fr; unfold fr.
 replace (Z.to_nat _) with 0 by
  (destruct t as [|t|t];try discriminate;destruct t;reflexivity).
 split.
  reflexivity.
 cbn.
 repeat (rewrite SHA256.W_equation; cbn).
 destruct b as [[[[b0 b1][b2 b3]][[b4 b5][b6 b7]]]
                [[[b8 b9][ba bb]][[bc bd][be bf]]]].
 reflexivity.
intros t Ht Hzlt IH Ht0.
assert (Ht1 : (t - 1 < 64)%Z) by lia.
specialize (IH Ht1).
rewrite Z.sub_add in IH.
pose (kt := nth (Z.to_nat t) ks' 0%Z).
assert (Ht2 : Z.to_nat t < length ks').
 change (Z.to_nat t < Z.to_nat 64).
 rewrite <- Z2Nat.inj_lt; lia.
replace (firstn (Z.to_nat (t + 1)) ks') with (firstn (Z.to_nat t) ks' ++ [kt]); revgoals.
 rewrite Z2Nat.inj_add by lia.
 unfold kt.
 rewrite sublist.firstn_1_skipn by auto.
 rewrite <- firstn_app_2, firstn_skipn, firstn_length_le by lia.
 reflexivity.
rewrite rev_app_distr, map_app, fold_right_app.
set (fr := fold_right _ H _) in *.
replace (SHA256.nthi SHA256.K256 t) with (Int.repr kt) by (symmetry; apply map_nth).
clearbody ks'; clear k0 ks compression.
destruct IH as [IH0 IH1].
split.
 rewrite <- IH0.
 replace (SHA256.W (SHA256.nthi (repr_Block b)) t) with (hd Int.zero (repr_Block (snd (fr (h, b))))); revgoals.
  rewrite IH1.
  cbn.
  rewrite Z2Nat.id by lia.
  reflexivity.
 cbn -[round scribe32 kt].
 unfold scribe32; rewrite scribe_correct.
 match goal with
  |- _ (to_hash256 (round (_, ?p))) = _ =>
    destruct p as [[[[h0 h1][h2 h3]][[h4 h5][h6 h7]]] 
                   [[[[b0 b1][b2 b3]][[b4 b5][b6 b7]]]
                    [[[b8 b9][ba bb]][[bc bd][be bf]]]]]
 end.
 cbn -[rotate32 xor3Word32 majWord32 chWord32 add32 toZ fromZ kt].
 unfold SHA256.Sigma_0, SHA256.Sigma_1.
 assert (Hkt : Int.repr (toZ (fromZ kt : Word32)) = Int.repr kt).
  rewrite to_fromZ.
  symmetry.
  apply Int.eqm_samerepr.
  apply Zbits.eqmod_mod.
  reflexivity.
 repeat f_equal;
  rewrite !add32_correct, ?majWord32_Maj, chWord32_Ch,
          !xor3Word32_xor, !rotate32_correct, Hkt.
  rewrite Int.add_commut, Int.add_assoc; f_equal.
  rewrite Int.add_commut, <- Int.add_assoc; do 2 f_equal.
  rewrite Int.add_assoc; reflexivity.
 rewrite Int.add_commut; f_equal.
 rewrite Int.add_commut, <- Int.add_assoc; do 2 f_equal.
 rewrite Int.add_assoc; reflexivity.
unfold iden; simpl.
rewrite (Zplus_comm t 1), Z2Nat.inj_add by lia.
clear -IH1 Ht.
set (p := snd (fr (h, b))) in *.
match goal with
|- (Int.repr (toZ (O I H (fst (fst ?p0)))))::_ = _ => change p0 with p
end.
destruct p as [[[[b0 b1][b2 b3]][[b4 b5][b6 b7]]]
               [[[b8 b9][ba bb]][[bc bd][be bf]]]].
unfold drop, take, iden; simpl.
injection IH1; repeat (intros ->); intros _.
repeat f_equal.
rewrite !Pos2Z.inj_succ, Zpos_P_of_succ_nat, Z2Nat.id by auto with zarith.
replace (Z.succ _) with (16 + t)%Z by ring.
rewrite SHA256.W_equation.
destruct Coqlib.zlt;[lia|].
replace (16 + t - 2)%Z with (Z.of_nat 14 + t)%Z by ring.
replace (16 + t - 7)%Z with (Z.of_nat 9 + t)%Z by ring.
replace (16 + t - 15)%Z with (Z.of_nat 1 + t)%Z by ring.
replace (16 + t - 16)%Z with (Z.of_nat 0 + t)%Z by ring.
assert (HIH : forall i, i < 16 -> SHA256.W (SHA256.nthi (repr_Block b)) (Z.of_nat i + t) = 
  nth i (map (fun n : nat => SHA256.W (SHA256.nthi (repr_Block b)) (Z.of_nat n))
        (seq (Z.to_nat t) 16)) (SHA256.W (SHA256.nthi (repr_Block b)) (Z.of_nat 0))).
 intros i Hi.
 rewrite (map_nth (fun n => SHA256.W (SHA256.nthi (repr_Block b)) (Z.of_nat n))).
 rewrite seq_nth by auto.
 rewrite plus_comm, Nat2Z.inj_add, Z2Nat.id by lia.
 reflexivity.
rewrite <- IH1 in HIH.
rewrite !HIH by lia.
cbn -[shift32 rotate32 xor3Word32 add32 toZ].
rewrite !add32_correct, !xor3Word32_xor, !rotate32_correct, !shift32_correct by (cbn; lia).
rewrite Int.add_commut; f_equal; apply Int.add_commut.
Qed.

Lemma scribe32_Parametric z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) {A} :
  R A _ (scribe32 z) (scribe32 z).
Proof.
unfold scribe32.
auto with parametricity.
Qed.
Hint Immediate scribe32_Parametric : parametricity.

Lemma add32_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ add32 add32.
Proof.
unfold add32.
auto with parametricity.
Qed.
Hint Immediate add32_Parametric : parametricity.

Lemma xor3Word32_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ xor3Word32 xor3Word32.
Proof.
unfold xor3Word32.
auto with parametricity.
Qed.
Hint Immediate xor3Word32_Parametric : parametricity.

Lemma chWord32_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ chWord32 chWord32.
Proof.
unfold chWord32.
auto with parametricity.
Qed.
Hint Immediate chWord32_Parametric : parametricity.

Lemma majWord32_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ majWord32 majWord32.
Proof.
unfold majWord32.
auto with parametricity.
Qed.
Hint Immediate majWord32_Parametric : parametricity.

Lemma shift32_Parametric z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ (shift32 z) (shift32 z).
Proof.
unfold shift32.
auto with parametricity.
Qed.
Hint Immediate shift32_Parametric : parametricity.

Lemma rotate32_Parametric z {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ (rotate32 z) (rotate32 z).
Proof.
unfold rotate32.
auto with parametricity.
Qed.
Hint Immediate rotate32_Parametric : parametricity.

Lemma hashBlock_Parametric {term1 term2 : Core.Algebra} (R : Core.Parametric.Rel term1 term2) :
  R _ _ hashBlock hashBlock.
Proof.
unfold hashBlock.
change Word512 with (Word256*Word256).
change Word256 with ((Word64*Word64)*(Word64*Word64)).
set (f0 := fun k => _).
set (f1 := fun k => _).
assert (Hfold : forall l e0 e1, R _ _ e0 e1 ->
                (forall k rec0 rec1, R _ _ rec0 rec1 -> R _ _ (f0 k rec0) (f1 k rec1))
             -> R _ _ (fold_right f0 e0 l) (fold_right f1 e1 l));
 [induction l;simpl|unfold f0, f1 in *; clear f0 f1];
solve [auto 30 with parametricity].
Qed.

Hint Immediate hashBlock_Parametric : parametricity.

Require Import Simplicity.MerkleRoot.

Fact identityRoot_hashBlock : map Byte.unsigned (hash256_to_bytelist (identityRoot hashBlock)) =
  map Byte.unsigned (sha.functional_prog.hexstring_to_bytelist "da10f0e8530695d07564f0b32feebe77265a1d69cf802e22d77289daf6641b8d").
Proof.
vm_compute.
reflexivity.
Qed.

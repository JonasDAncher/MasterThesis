(** ElGamal encryption scheme.

  We show that DH security implies the security of ElGamal.

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  AsymScheme.

From Diffie Require Import El_Gamal.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Theory.
Import Order.POrderTheory.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import PackageNotation.

Module Type ElGamalParam.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter order_gt1 : (1 < #[g])%N.
  Parameter q_eq : BinInt.Z.of_nat #[g] = MachineIntegers.unsigned q_v.

End ElGamalParam.

Module ElGamal (EGP : ElGamalParam).

Import EGP.

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g. exact: g_gen.
Qed.

(* order of g *)
Definition q : nat := #[g].

Lemma g_gt_eq : 
  #|gT| = #[g].
Proof.
  pose proof generator_cycle.
  unfold generator in H.
  rewrite -cardsT.
  simpl.
  fold ζ.
  rewrite g_gen.
  by rewrite orderE.
Qed.

Lemma group_prodC :
  ∀ x y : gT, x * y = y * x.
Proof.
  move => x y.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  subst.
  repeat rewrite -expgD addnC. reflexivity.
Qed.

Module MyParam <: AsymmetricSchemeParams.

  Definition SecurityParameter : choiceType := nat_choiceType.
  Definition Plain  : finType := FinGroup.arg_finType gT.
  Definition Cipher : finType :=
    prod_finType (FinGroup.arg_finType gT) (FinGroup.arg_finType gT).
  Definition PubKey : finType := FinGroup.arg_finType gT.
  Definition SecKey : finType := [finType of 'Z_q].

  Definition plain0 := g.
  Definition cipher0 := (g, g).
  Definition pub0 := g.
  Definition sec0 : SecKey := 0.

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.

  #[export] Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  #[export] Instance positive_SecKey : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. exists sec0. auto.
  Qed.

  Definition Plain_pos : Positive #|Plain| := _.
  Definition PubKey_pos : Positive #|PubKey| := _.
  Definition SecKey_pos : Positive #|SecKey| := _.

  #[export] Instance Cipher_pos : Positive #|Cipher|.
  Proof.
    unfold Cipher. rewrite card_prod.
    exact _.
  Qed. 

  Definition chPlain  : choice_type := 'fin #|gT|.
  Definition chPubKey : choice_type := 'fin #|gT|.
  Definition chCipher : choice_type := 'fin #|Cipher|.
  Definition chSecKey : choice_type := 'fin #|SecKey|.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := (chPubKey ; 1%N).
  Definition sk_loc : Location := (chSecKey ; 2%N).
  Definition m_loc  : Location := (chPlain ; 3%N).
  Definition c_loc  : Location := (chCipher ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)
  Definition getpk_id : nat := 42. (* routine to get the public key *)

  Definition i_plain := #|Plain|.
  Definition i_cipher := #|Cipher|.
  Definition i_pk := #|PubKey|.
  Definition i_sk := #|SecKey|.
  Definition i_bool := 2.
 



  (** Key Generation algorithm *)
  Definition KeyGen {L : {fset Location}} :
    code L [interface] (chPubKey × chSecKey) :=
    {code
      x ← sample uniform i_sk ;;
      let x := otf x in
      ret (fto (g^+x), fto x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : chPubKey) (m : chPlain) :
    code L [interface] chCipher :=
    {code
      y ← sample uniform i_sk ;;
      let y := otf y in
      ret (fto (g^+y, (otf pk)^+y * (otf m)))
    }.

  (** Decryption algorithm *)
  Definition Dec_open {L : {fset Location}} (sk : chSecKey) (c : chCipher) :
    code L [interface] chPlain :=
    {code
      ret (fto ((fst (otf c))^-(otf sk) * ((snd (otf c)))))
    }.

  Notation " 'plain " :=
    chPlain
    (in custom pack_type at level 2).

  Notation " 'cipher " :=
    chCipher
    (in custom pack_type at level 2).

  Notation " 'pubkey " :=
    chPubKey
    (in custom pack_type at level 2).

End MyAlg.

Local Open Scope package_scope.

Module ElGamal_Scheme := AsymmetricScheme MyParam MyAlg.

Import MyParam MyAlg ElGamal_Scheme.

Lemma counter_loc_in :
  counter_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma pk_loc_in :
  pk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma sk_loc_in :
  sk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.



(*
  ordinal_finType_inhabited 
  
*)

Definition DH_loc := fset [:: pk_loc ; sk_loc].

Definition DH_real :
  package DH_loc [interface]
    [interface #val #[10] : 'unit → 'pubkey × 'cipher ] :=
    [package
      #def #[10] (_ : 'unit) : 'pubkey × 'cipher
      {
        a ← sample uniform i_sk ;;
        let a := otf a in
        b ← sample uniform i_sk ;;
        let b := otf b in
        #put pk_loc := fto (g^+a) ;;
        #put sk_loc := fto a ;;
        ret (fto (g^+a), fto (g^+b, g^+(a * b)))
      }
    ].

Definition DH_rnd :
  package DH_loc [interface]
    [interface #val #[10] : 'unit → 'pubkey × 'cipher ] :=
    [package
      #def #[10] (_ : 'unit) : 'pubkey × 'cipher
      {
        a ← sample uniform i_sk ;;
        let a := otf a in
        b ← sample uniform i_sk ;;
        let b := otf b in
        c ← sample uniform i_sk ;;
        let c := otf c  in
        #put pk_loc := fto (g^+a) ;;
        #put sk_loc := fto a ;;
        ret (fto (g^+a), fto (g^+b, g^+c))
      }
    ].

Definition Aux :
  package (fset [:: counter_loc ; pk_loc ])
    [interface #val #[10] : 'unit → 'pubkey × 'cipher]
    [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ]
  :=
  [package
    #def #[getpk_id] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;

    #def #[challenge_id'] (m : 'plain) : 'cipher
    {
      #import {sig #[10] : 'unit → 'pubkey × 'cipher } as query ;;
      count ← get counter_loc ;;
      #assert (count == 0)%N ;;
      #put counter_loc := (count + 1)%N ;;
      '(pk, c) ← query Datatypes.tt ;;
      @ret chCipher (fto ((otf c).1 , (otf m) * ((otf c).2)))
    }
  ].

Lemma ots_real_vs_rnd_equiv_true :
  Aux ∘ DH_real ≈₀ ots_real_vs_rnd true.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  (* We are now in the realm of program logic *)
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. intuition auto.
  - ssprove_sync_eq. intro count.
    ssprove_sync_eq. move => /eqP e. subst.
    ssprove_sync_eq.
    ssprove_sync_eq. intro a.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq.
    ssprove_sync_eq. intro b.
    rewrite !otf_fto. simpl.
    eapply r_ret. intuition eauto.
    f_equal. f_equal.
    rewrite group_prodC. f_equal.
    apply expgM.
Qed.

Lemma bijective_expgn :
  bijective (λ (a : 'Z_q), g ^+ a).
Proof.
  unshelve eexists (λ x, (proj1_sig (@cyclePmin gT g x _) %% q)%:R).
  - rewrite -g_gen. unfold ζ. apply in_setT.
  - simpl. intros a.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl.
    move: e => /eqP e. rewrite eq_expg_mod_order in e.
    move: e => /eqP e.
    rewrite -e.
    (* case_eq (q == 1)%N.
    1:{
      fold q in *. set (q' := q) in *. clearbody q'.
      move /eqP => ?. subst. rewrite modn1.
      clear h n e hn.
      destruct a as [a h]. unfold Zp_trunc in *. simpl in *.
      (* So in the case where q = 1, we have 'Z_1 = {0, 1} but a mod 1 = 0. *)
    } *)
    rewrite modn_small.
    2:{
      fold q. eapply leq_trans. 1: eapply ltn_ord.
      rewrite Zp_cast.
      2: apply order_gt1.
      auto.
    }
    apply natr_Zp.
  - simpl. intro x.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl. subst.
    rewrite modn_small. 2: auto.
    f_equal. rewrite val_Zp_nat. 2: apply order_gt1.
    apply modn_small. auto.
Qed.

#[local] Definition f m : 'Z_q * 'Z_q → gT * gT :=
  λ '(a,b), (g^+a, (otf m) * g^+b).

Lemma bijective_f : ∀ m, bijective (f m).
Proof.
  intro m.
  pose proof bijective_expgn as bij.
  destruct bij as [d hed hde].
  eexists (λ '(x,y), (d x, d ((otf m)^-1 * y))).
  - intros [? ?]. simpl. rewrite hed. f_equal.
    rewrite mulgA. rewrite mulVg. rewrite mul1g.
    apply hed.
  - intros [x y]. simpl. rewrite hde. f_equal.
    rewrite hde. rewrite mulgA. rewrite mulgV. rewrite mul1g.
    reflexivity.
Qed.

#[local] Definition f' (m : chPlain) :
  Arit (uniform (i_sk * i_sk)) → Arit (uniform i_cipher) :=
  λ x,
    let '(a, b) := ch2prod x in
    fto (f m (otf a, otf b)).

Lemma bijective_f' : ∀ m, bijective (f' m).
Proof.
  intro m.
  pose proof (bijective_f m) as bij. destruct bij as [g gf fg].
  unfold f'.
  exists (λ x, let '(a,b) := g (otf x) in prod2ch (fto a, fto b)).
  - cbn - [f]. intros x. rewrite -[RHS]prod2ch_ch2prod.
    set (y := ch2prod x). clearbody y. clear x.
    simpl in y. destruct y as [a b].
    rewrite otf_fto. rewrite gf.
    rewrite !fto_otf. reflexivity.
  - cbn - [f]. intro x.
    replace x with (fto (f m (g (otf x)))) at 2.
    2:{ rewrite fg. rewrite fto_otf. reflexivity. }
    set (y := g (otf x)). change (g (otf x)) with y. clearbody y. clear x.
    destruct y as [a b]. rewrite ch2prod_prod2ch. rewrite !otf_fto.
    reflexivity.
Qed.

Lemma ots_real_vs_rnd_equiv_false :
  ots_real_vs_rnd false ≈₀ Aux ∘ DH_rnd.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  (* We are now in the realm of program logic *)
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  - ssprove_sync_eq. intro count.
    ssprove_sync_eq.
    intros h.
    ssprove_sync_eq.
    ssprove_sync_eq. intros a.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq.
    eapply r_transR.
    1:{ eapply r_uniform_prod. intros x y. eapply rreflexivity_rule. }
    simpl.
    eapply rsymmetry.
    eapply @r_uniform_bij with (f := f' m). 1: apply bijective_f'.
    simpl. intros x.
    unfold f'. set (z := ch2prod x). clearbody z. clear x.
    destruct z as [x y]. simpl.
    rewrite !otf_fto.
    eapply r_ret.
    intros s ? e.
    subst. simpl. easy.
Qed.

Theorem ElGamal_OT :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ] A_export A →
    fdisjoint LA (ots_real_vs_rnd true).(locs) →
    fdisjoint LA (ots_real_vs_rnd false).(locs) →
    Advantage ots_real_vs_rnd A <= AdvantageE DH_rnd DH_real (A ∘ Aux).
Proof.
  intros LA A vA hd₀ hd₁.
  simpl in hd₀, hd₁. clear hd₁. rename hd₀ into hd.
  rewrite Advantage_E.
  ssprove triangle (ots_real_vs_rnd false) [::
    Aux ∘ DH_rnd ;
    Aux ∘ DH_real
  ] (ots_real_vs_rnd true) A
  as ineq.
  eapply le_trans. 1: exact ineq.
  clear ineq.
  rewrite ots_real_vs_rnd_equiv_true. 3: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite ots_real_vs_rnd_equiv_false. 2: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite GRing.addr0. rewrite GRing.add0r.
  rewrite -Advantage_link. auto.
Qed.


  (* nat to ordinal *)
  Definition NatToOrd {d} `{p:Positive d} : nat -> 'I_d := fun n => Ordinal (ltn_pmod n p).

  (* nat to MachineIntegers version of int128 *)
  Definition NatToInt : nat -> Hacspec_Lib.uint128 := fun x => MachineIntegers.repr (BinInt.Z.of_N (BinNat.N.of_nat x)). 
  
  (* 'fin to MachineIntegers version of int128 *)
  Definition FinToInt {n} `{Positive n} : 'fin n -> Hacspec_Lib.uint128 := fun x => NatToInt ((nat_of_ord x)). 
 
  (* Ordinal to nat *)
  Definition OrdToNat {d} `{p:Positive d} : 'I_d -> nat := fun n => (nat_of_ord n) .

  (* MachineIntergers version of int128 to nat *)
  Definition IntToNat : Hacspec_Lib.uint128 -> nat := fun x => (BinInt.Z.to_nat (MachineIntegers.unsigned x)).
 
  (* MachineIntergers version of int128 to 'fin *)
  Definition IntToFin {n} `{Positive n} : Hacspec_Lib.uint128 -> 'fin n := fun x => NatToOrd (IntToNat x) .
  
  (* ElGamal translated from rust to coq with Hacspec: Key generation algorithm *)
  Definition hacspec_gen {L : {fset Location}} :
    code L [interface] (chPubKey × chSecKey) :=
    {code
      let '(c1Int,c2Int) := El_Gamal.keygen in
      let c1Key := IntToFin c1Int in
      let c2Key := IntToFin c2Int in
      ret (c1Key,c2Key)
    }.
  
  (* ElGamal translated from rust to coq with Hacspec: Encryption algorithm *)
  Definition hacspec_enc {L : {fset Location}} (pkKey : chPubKey) (m : chPlain) :
    code L [interface] chCipher := 
    {code
      let pkInt     := FinToInt pkKey in
      let mInt      := FinToInt m in
      let cipherInt := El_Gamal.enc pkInt mInt in
      let cipher    := fto(
                        otf (IntToFin cipherInt.1),
                        otf (IntToFin cipherInt.2)) in
      ret cipher
    }.
  
  (* ElGamal translated from rust to coq with Hacspec: Decryption algorithm *)
  Definition hacspec_dec {L : {fset Location}} (skKey : chSecKey) (cipher : chCipher) :
    code L [interface] chPlain :=
    {code
      let skInt  := FinToInt skKey in
      let cipher := (
                      FinToInt (fto (fst (otf cipher))),
                      FinToInt (fto (snd (otf cipher)))) in
      let mInt   := El_Gamal.dec skInt cipher in
      ret (IntToFin(mInt))
    }.


Definition Enc_Dec_real :
  package fset0 [interface]
    [interface #val #[10] : 'plain → 'plain ] :=
    [package
      #def #[10] (m : 'plain) : 'plain
      {
        '(pk, sk) ← KeyGen ;;
        c ← Enc pk m ;;
        m ← Dec_open sk c ;;
        ret m
      }
    ].

Definition Hacspec_Enc_Dec_real :
  package fset0 [interface]
    [interface #val #[10] : 'plain → 'plain ] :=
    [package
      #def #[10] (m : 'plain) : 'plain
      {
        '(pk, sk) ← hacspec_gen ;;
        c ← hacspec_enc pk m ;;
        m ← hacspec_dec sk c ;;
        ret m
      }
    ].


Definition Enc_Dec_ideal :
  package fset0 [interface]
    [interface #val #[10] : 'plain → 'plain ] :=
    [package
      #def #[10] (m : 'plain) : 'plain
      {
        ret m
      }
    ].

Lemma Enc_Dec_Perfect :
  Enc_Dec_real ≈₀ Enc_Dec_ideal.
Proof.
(* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  2: intros sk.
  2: apply r_const_sample_L.
  1,2: apply LosslessOp_uniform.
  intros pk.
  apply r_ret.
  intros s0 s1 e1.
  split.
  2: apply e1.
  repeat rewrite otf_fto.
  simpl.
  rewrite -2!expgM.
  rewrite mulnC.
  rewrite mulgA.
  rewrite mulVg.
  rewrite mul1g.
  rewrite fto_otf.
  reflexivity.
Qed.

Lemma FinToInt_IntToFin_Eq {k:nat} `{Positive k} {H1: BinInt.Z.le (BinInt.Z.of_nat k) (@MachineIntegers.max_unsigned MachineIntegers.WORDSIZE128)}:
  ∀ {n: MachineIntegers.int128} , @FinToInt k _ (IntToFin n) = MachineIntegers.modu n (NatToInt k).  (* mod k *)
Proof.
  move => n.
  unfold FinToInt, IntToFin, NatToInt, NatToOrd, IntToNat, fto.
  simpl.
(*   above is prebwork, proof starts here *)
  unfold MachineIntegers.modu.
  repeat rewrite Znat.nat_N_Z.
  rewrite ssrZ.modnZE.
  2: apply lt0n_neq0.
  2: apply is_positive.
  repeat rewrite Znat.Z2Nat.id.
  2: apply MachineIntegers.unsigned_range_2.
  do 2 f_equal.
  rewrite MachineIntegers.unsigned_repr.
  1: reflexivity.
  split.
  2: apply H1.
  apply Znat.Nat2Z.is_nonneg.
Qed.




Lemma NatToInt_IntToNat_Eq:
  ∀ {n: Hacspec_Lib.uint128} , 
    NatToInt (IntToNat n) = n.
Proof.
  intros n.
  unfold NatToInt, IntToNat.
  repeat rewrite Znat.nat_N_Z.
  rewrite Znat.Z2Nat.id.
  2: apply MachineIntegers.unsigned_range_2.
  apply MachineIntegers.repr_unsigned.
Qed.



Axiom Remove_Classify  :
  ∀ {n: MachineIntegers.int128}, 
    Hacspec_Lib.uint128_classify(n) = n.

Axiom Remove_Declassify  :
  ∀ {n: MachineIntegers.int128}, 
    Hacspec_Lib.uint128_declassify(n) = n.

Axiom Remove_Secret :
  ∀ {n: MachineIntegers.int128},
    Hacspec_Lib.secret n = n.

Axiom unsigned_repr :
  ∀ {n: BinNums.Z},
    @MachineIntegers.unsigned MachineIntegers.WORDSIZE128 (MachineIntegers.repr n) = n.

Axiom Remove_mod_gT :
  ∀ {n: BinNums.Z},
    (BinInt.Z.modulo n (BinInt.Z.of_nat #|gT|)) = n.

Axiom mul_inv:
  ∀ {n z: BinNums.Z},
  BinInt.Z.mul (OrdersEx.Z_as_OT.pow n z) (BinInt.Z.pow n (BinInt.Z.opp z)) = (BinNums.Zpos 1%AC).


Lemma reprmod :
  ∀ {n: BinNums.Z} {q: nat} {h: Positive q} {H1: BinInt.Z.le BinNums.Z0 n} {H2: BinInt.Z.le n (@MachineIntegers.max_unsigned MachineIntegers.WORDSIZE128)},
  IntToFin (MachineIntegers.repr n) = IntToFin (MachineIntegers.repr (BinInt.Z.modulo n (BinInt.Z.of_nat q))).
Proof.
  intros.
  simpl.
  eapply ord_inj.
  simpl.
  unfold IntToNat.
  repeat rewrite MachineIntegers.unsigned_repr_eq.  
  rewrite -(Znat.Z2Nat.id n).
  2: done.
  rewrite -ssrZ.modnZE.
  2: apply lt0n_neq0.
  2: done.
  rewrite (Znat.Z2Nat.id n).
  2: done.
  assert ((BinInt.Z.modulo n (@MachineIntegers.modulus MachineIntegers.WORDSIZE128)) = n).
  1: rewrite -MachineIntegers.unsigned_repr_eq.
  1: rewrite MachineIntegers.unsigned_repr.
  1: reflexivity.
  1: split.
  1: apply H1.
  1: apply H2.
  rewrite H.
  rewrite -MachineIntegers.unsigned_repr_eq.
  rewrite unsigned_repr.
  rewrite Znat.Nat2Z.id.
  rewrite modn_mod.
  reflexivity.
(* 
  1: apply Znat.Nat2Z.is_nonneg.
  rewrite ssrZ.modnZE.
  2: eapply lt0n_neq0.
  2: done.
  rewrite -ssrZ.modnZE.
  2: eapply lt0n_neq0.
  2: done.
  rewrite modn_small.
  1: rewrite Znat.Z2Nat.id.
  1: apply H2.
  1: apply H1.
  admit. *)

Qed.

 
Lemma Hacspec_Enc_Dec_Perfect :
  Hacspec_Enc_Dec_real ≈₀ Enc_Dec_ideal.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_ret.
  intros s0 s1.
  intros e1.
  split.
  2: apply e1.
  repeat rewrite otf_fto.
  repeat rewrite fto_otf.
  repeat rewrite Remove_Declassify.
  repeat rewrite Remove_Classify.
  assert (BinInt.Z.of_nat #|gT| = MachineIntegers.unsigned secret_q_v).
  1: rewrite g_gt_eq.
  1: rewrite q_eq.
  1: unfold secret_q_v.
  1: rewrite Remove_Secret.
  1: done.  
  repeat rewrite FinToInt_IntToFin_Eq.
  3,4: rewrite H.
  3,4: unfold secret_q_v.
  3,4: rewrite Remove_Secret.
  3,4: apply MachineIntegers.unsigned_range_2.
  2: admit.
  unfold MachineIntegers.modu.

(*   unfold secret_q_v, secret_g_v. *)
  repeat rewrite Remove_Secret.

  unfold MachineIntegers.modu, MachineIntegers.mul, MachineIntegers.sub, 
    powmod.uint128_pow_mod, powmod.pow, powmod.uint128_modulo, MachineIntegers.modu.
  repeat rewrite unsigned_repr.
  repeat rewrite Znat.nat_N_Z.
  rewrite Remove_mod_gT.
  rewrite (Zdiv.Zmod_small (BinNums.Zpos (BinNums.xO (BinNums.xO 1%AC)))).
  2: split.
  2: done.
  2 : admit.

  repeat rewrite Zdiv.Zmod_mod.
  rewrite -BinInt.Z.mul_assoc.
  repeat rewrite OrdersEx.Z_as_OT.pow_pos_fold.
  Import BinInt.Z.
  rewrite reprmod.
  2: {
  repeat rewrite -Zpow_facts.Zpower_mod.
  

  rewrite H.
  repeat rewrite -Zpow_facts.Zpower_mod.
  2,3,4,5: unfold secret_q_v.
  2,3,4,5: repeat rewrite Remove_Secret.
  2,3,4,5: done.
  simpl.
  rewrite Zdiv.Zmod_0_l.
  repeat rewrite mul_0_r.
  done.
}
  2: {
  repeat rewrite -Zpow_facts.Zpower_mod.
  rewrite H.
  repeat rewrite -Zpow_facts.Zpower_mod.
  2,3,4,5: unfold secret_q_v.
  2,3,4,5: repeat rewrite Remove_Secret.
  2,3,4,5: done.
  simpl.
  rewrite Zdiv.Zmod_0_l.
  repeat rewrite mul_0_r.
  done.
}  
  rewrite Zdiv.Zmult_mod.
  rewrite H.
  repeat rewrite -Zpow_facts.Zpower_mod.
  2,3,4,5: unfold secret_q_v.
  2,3,4,5: rewrite Remove_Secret.
  2,3,4,5: done.  
  rewrite -(Zdiv.Zmult_mod ((MachineIntegers.unsigned secret_g_v ^ 4) ^ 4)).
  rewrite -Zdiv.Zmult_mod.
  rewrite -H.
  rewrite -reprmod.
  2: {rewrite mul_inv.
  rewrite mul_1_r.
  eapply Znat.Nat2Z.is_nonneg.
  }
  2:{
  unfold secret_g_v.
  rewrite Remove_Secret.
  rewrite mul_inv.
  rewrite OrdersEx.Z_as_OT.mul_1_r.
  admit. 
}  
  rewrite mul_inv.
  erewrite BinInt.Z.mul_1_r.
  unfold IntToFin, NatToOrd, IntToNat.
  eapply ord_inj.
  simpl.
  rewrite MachineIntegers.Z_mod_modulus_eq.
  rewrite -(Znat.Z2Nat.id MachineIntegers.modulus).
  2: done.  
  rewrite -ssrZ.modnZE.
  2: done.
  rewrite Znat.Nat2Z.id.
  rewrite (@modn_small m).
  2:{ eapply ltn_trans.
  1: eapply ltn_ord.
  simpl.
  rewrite -(Znat.Nat2Z.id (#|gT|)).
  rewrite H.
  unfold secret_q_v.
  rewrite Remove_Secret.
  done.
  }
  rewrite (@modn_small m).
  2: apply ltn_ord.
  reflexivity.
Admitted.


End ElGamal.

Module EGP_Z3 <: ElGamalParam.

  Definition gT : finGroupType := Zp_finGroupType 2.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := Zp1.

  Lemma g_gen : ζ = <[g]>.
  Proof.
    unfold ζ, g. apply Zp_cycle.
  Qed.

  Lemma order_gt1 : (1 < #[g])%N.
  Proof.
    unfold g.
    rewrite order_Zp1.
    reflexivity.
  Qed.
  
  Axiom q_eq : BinInt.Z.of_nat #[g] = MachineIntegers.unsigned q_v. 

End EGP_Z3.

Module ElGamal_Z3 := ElGamal EGP_Z3.



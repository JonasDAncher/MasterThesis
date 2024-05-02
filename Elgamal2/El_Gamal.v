(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.


From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.
From Diffie Require Import powmod.

Open Scope hacspec_scope.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition q_v : int128 :=
  @repr U128 29.

Definition g_v : int128 :=
  @repr U128 2.

Definition secret_q_v : uint128 :=
  secret (q_v).

Definition secret_g_v : uint128 :=
  secret (g_v).


Notation "'enc_aux_inp'" :=(
  uint128 '× int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'enc_aux_inp'" :=(
  uint128 '× int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'enc_aux_out'" :=((int128 '× int128
  ) : choice_type) (in custom pack_type at level 2).
Notation "'enc_aux_out'" :=((int128 '× int128) : ChoiceEquality) (at level 2).
Definition ENC_AUX : nat :=
  8.
Program Definition enc_aux (secret_source_sk_4 : uint128) (
    target_pk_0 : int128) (m_2 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb secret_target_pk_1 : uint128 :=
        uint128_classify (lift_to_both0 target_pk_0) in
      letb secret_m_3 : uint128 := uint128_classify (lift_to_both0 m_2) in
      letb secret_s_5 : uint128 :=
        uint128_pow_mod (lift_to_both0 secret_target_pk_1) (
          lift_to_both0 secret_source_sk_4) (lift_to_both0 secret_q_v) in
      letb secret_c1_6 : uint128 :=
        uint128_pow_mod (lift_to_both0 secret_g_v) (
          lift_to_both0 secret_source_sk_4) (lift_to_both0 secret_q_v) in
      letb secret_c2_7 : uint128 :=
        uint128_modulo ((lift_to_both0 secret_m_3) .* (
            lift_to_both0 secret_s_5)) (lift_to_both0 secret_q_v) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          uint128_declassify (lift_to_both0 secret_c1_6),
          uint128_declassify (lift_to_both0 secret_c2_7)
        ))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.


Notation "'keygen_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'keygen_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'keygen_out'" :=((int128 '× uint128
  ) : choice_type) (in custom pack_type at level 2).
Notation "'keygen_out'" :=((int128 '× uint128) : ChoiceEquality) (at level 2).
Definition KEYGEN : nat :=
  11.
Program Definition keygen 
  : both (fset.fset0) [interface] ((int128 '× uint128)) :=
  ((letb secret_sk_9 : uint128 :=
        uint128_classify (lift_to_both0 (@repr U128 4)) in
      letb pk_10 : int128 :=
        uint128_declassify (uint128_pow_mod (lift_to_both0 secret_g_v) (
            lift_to_both0 secret_sk_9) (lift_to_both0 secret_q_v)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 pk_10,
          lift_to_both0 secret_sk_9
        ))
      ) : both (fset.fset0) [interface] ((int128 '× uint128))).
Fail Next Obligation.


Notation "'enc_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'enc_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'enc_out'" :=((int128 '× int128
  ) : choice_type) (in custom pack_type at level 2).
Notation "'enc_out'" :=((int128 '× int128) : ChoiceEquality) (at level 2).
Definition ENC : nat :=
  16.
Program Definition enc (target_pk_14 : int128) (m_15 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb '(gy_12, y_13) : (int128 '× uint128) := keygen  in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (enc_aux (
          lift_to_both0 y_13) (lift_to_both0 target_pk_14) (lift_to_both0 m_15))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.


Notation "'dec_inp'" :=(uint128 '× (int128 '× int128
  ) : choice_type) (in custom pack_type at level 2).
Notation "'dec_inp'" :=(uint128 '× (int128 '× int128
  ) : ChoiceEquality) (at level 2).
Notation "'dec_out'" :=(int128 : choice_type) (in custom pack_type at level 2).
Notation "'dec_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition DEC : nat :=
  27.
Program Definition dec (secret_target_sk_22 : uint128) (c_17 : (
      int128 '×
      int128
    ))
  : both (fset.fset0) [interface] (int128) :=
  ((letb '(c1_18, c2_19) : (int128 '× int128) := lift_to_both0 c_17 in
      letb secret_c1_20 : uint128 := uint128_classify (lift_to_both0 c1_18) in
      letb secret_c2_21 : uint128 := uint128_classify (lift_to_both0 c2_19) in
      letb secret_s_23 : uint128 :=
        uint128_pow_mod (lift_to_both0 secret_c1_20) (
          lift_to_both0 secret_target_sk_22) (lift_to_both0 secret_q_v) in
      letb secret_s_inverse_24 : uint128 :=
        uint128_pow_mod (lift_to_both0 secret_s_23) ((
            lift_to_both0 secret_q_v) .- (lift_to_both0 secret_g_v)) (
          lift_to_both0 secret_q_v) in
      letb secret_m_25 : uint128 :=
        uint128_pow_mod ((lift_to_both0 secret_c2_21) .* (
            lift_to_both0 secret_s_inverse_24)) (uint128_classify (
            lift_to_both0 (@repr U128 1))) (lift_to_both0 secret_q_v) in
      letb m_26 : int128 := uint128_declassify (lift_to_both0 secret_m_25) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 m_26)
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


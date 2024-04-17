(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition q_v : int128 :=
  @repr WORDSIZE128 29.

Definition g_v : int128 :=
  @repr WORDSIZE128 2.

Definition secret_q_v : uint128 :=
  secret (q_v) : int128.

Definition secret_g_v : uint128 :=
  secret (g_v) : int128.

Definition enc_aux
  (secret_source_sk_0 : uint128)
  (target_pk_1 : int128)
  (m_2 : int128)
  
  : (int128 '× int128) :=
  let secret_target_pk_3 : uint128 :=
    uint128_classify (target_pk_1) in 
  let secret_m_4 : uint128 :=
    uint128_classify (m_2) in 
  let secret_s_5 : uint128 :=
    uint128_pow_mod (secret_target_pk_3) (secret_source_sk_0) (secret_q_v) in 
  let secret_c1_6 : uint128 :=
    uint128_pow_mod (secret_g_v) (secret_source_sk_0) (secret_q_v) in 
  let secret_c2_7 : uint128 :=
    uint128_modulo ((secret_m_4) .* (secret_s_5)) (secret_q_v) in 
  (uint128_declassify (secret_c1_6), uint128_declassify (secret_c2_7)).

Definition keygen   : (int128 '× uint128) :=
  let secret_sk_8 : uint128 :=
    uint128_classify (@repr WORDSIZE128 4) in 
  let pk_9 : int128 :=
    uint128_declassify (uint128_pow_mod (secret_g_v) (secret_sk_8) (
        secret_q_v)) in 
  (pk_9, secret_sk_8).

Definition enc (target_pk_10 : int128) (m_11 : int128)  : (int128 '× int128) :=
  let '(gy_12, y_13) :=
    keygen  in 
  enc_aux (y_13) (target_pk_10) (m_11).

Definition dec
  (secret_target_sk_14 : uint128)
  (c_15 : (int128 '× int128))
  
  : int128 :=
  let '(c1_16, c2_17) :=
    c_15 in 
  let secret_c1_18 : uint128 :=
    uint128_classify (c1_16) in 
  let secret_c2_19 : uint128 :=
    uint128_classify (c2_17) in 
  let secret_s_20 : uint128 :=
    uint128_pow_mod (secret_c1_18) (secret_target_sk_14) (secret_q_v) in 
  let secret_s_inverse_21 : uint128 :=
    uint128_pow_mod (secret_s_20) ((secret_q_v) .- (secret_g_v)) (
      secret_q_v) in 
  let secret_m_22 : uint128 :=
    uint128_pow_mod ((secret_c2_19) .* (secret_s_inverse_21)) (
      uint128_classify (@repr WORDSIZE128 1)) (secret_q_v) in 
  let m_23 : int128 :=
    uint128_declassify (secret_m_22) in 
  m_23.


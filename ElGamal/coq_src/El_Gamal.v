(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
From Diffie Require Import powmod.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition q_v : int128 :=
  @repr WORDSIZE128 29.

Definition g_v : int128 :=
  @repr WORDSIZE128 2.

Definition enc_aux
  (secret_source_sk_0 : uint128)
  (target_pk_1 : int128)
  (m_2 : int128)
  
  : (int128 '× int128) :=
  let secret_target_pk_3 : uint128 :=
    uint128_classify (target_pk_1) in 
  let secret_g_4 : uint128 :=
    uint128_classify (g_v) in 
  let secret_m_5 : uint128 :=
    uint128_classify (m_2) in 
  let secret_q_6 : uint128 :=
    uint128_classify (q_v) in 
  let secret_s_7 : uint128 :=
    uint128_pow_mod (secret_target_pk_3) (secret_source_sk_0) (secret_q_6) in 
  let secret_c1_8 : uint128 :=
    uint128_pow_mod (secret_g_4) (secret_source_sk_0) (secret_q_6) in 
  let secret_c2_9 : uint128 :=
    uint128_modulo ((secret_m_5) .* (secret_s_7)) (secret_q_6) in 
  (uint128_declassify (secret_c1_8), uint128_declassify (secret_c2_9)).

Definition keygen   : (int128 '× uint128) :=
  let secret_sk_10 : uint128 :=
    uint128_classify (@repr WORDSIZE128 4) in 
  let secret_g_11 : uint128 :=
    uint128_classify (g_v) in 
  let secret_q_12 : uint128 :=
    uint128_classify (q_v) in 
  let pk_13 : int128 :=
    uint128_declassify (uint128_pow_mod (secret_g_11) (secret_sk_10) (
        secret_q_12)) in 
  (pk_13, secret_sk_10).

Definition enc (target_pk_14 : int128) (m_15 : int128)  : (int128 '× int128) :=
  let '(gy_16, y_17) :=
    keygen  in 
  enc_aux (y_17) (target_pk_14) (m_15).

Definition dec
  (secret_target_sk_18 : uint128)
  (c_19 : (int128 '× int128))
  
  : int128 :=
  let secret_q_20 : uint128 :=
    uint128_classify (q_v) in 
  let secret_g_21 : uint128 :=
    uint128_classify (g_v) in 
  let '(c1_22, c2_23) :=
    c_19 in 
  let secret_c1_24 : uint128 :=
    uint128_classify (c1_22) in 
  let secret_c2_25 : uint128 :=
    uint128_classify (c2_23) in 
  let secret_s_26 : uint128 :=
    uint128_pow_mod (secret_c1_24) (secret_target_sk_18) (secret_q_20) in 
  let secret_s_inverse_27 : uint128 :=
    uint128_pow_mod (secret_s_26) ((secret_q_20) .- (secret_g_21)) (
      secret_q_20) in 
  let secret_m_28 : uint128 :=
    uint128_pow_mod ((secret_c2_25) .* (secret_s_inverse_27)) (
      uint128_classify (@repr WORDSIZE128 1)) (secret_q_20) in 
  let m_29 : int128 :=
    uint128_declassify (secret_m_28) in 
  m_29.


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

Definition el_int_t := nseq (uint8) (usize 2048).

Definition q_v : int128 :=
  @repr WORDSIZE128 29.

Definition g_v : int128 :=
  @repr WORDSIZE128 2.

Definition enc_aux
  (source_sk_0 : el_int_t)
  (target_pk_1 : int128)
  (m_2 : int128)
  
  : (int128 '× int128) :=
  let secret_target_pk_3 : uint128 :=
    uint128_classify (target_pk_1) in 
  let secret_source_sk_4 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (array_to_seq (source_sk_0))) in 
  let secret_g_5 : uint128 :=
    uint128_classify (g_v) in 
  let secret_m_6 : uint128 :=
    uint128_classify (m_2) in 
  let secret_q_7 : uint128 :=
    uint128_classify (q_v) in 
  let secret_s_8 : uint128 :=
    uint128_pow_mod (secret_target_pk_3) (secret_source_sk_4) (secret_q_7) in 
  let secret_c1_9 : uint128 :=
    uint128_pow_mod (secret_g_5) (secret_source_sk_4) (secret_q_7) in 
  let secret_c2_10 : uint128 :=
    uint128_modulo ((secret_m_6) .* (secret_s_8)) (secret_q_7) in 
  (uint128_declassify (secret_c1_9), uint128_declassify (secret_c2_10)).

Definition keygen   : (int128 '× el_int_t) :=
  let secret_sk_11 : uint128 :=
    uint128_classify (@repr WORDSIZE128 4) in 
  let secret_g_12 : uint128 :=
    uint128_classify (g_v) in 
  let secret_q_13 : uint128 :=
    uint128_classify (q_v) in 
  let pk_14 : int128 :=
    uint128_declassify (uint128_pow_mod (secret_g_12) (secret_sk_11) (
        secret_q_13)) in 
  let sk_15 : el_int_t :=
    array_from_seq (2048) (array_to_seq (uint128_to_be_bytes (
        secret_sk_11))) in 
  (pk_14, sk_15).

Definition enc (target_pk_16 : int128) (m_17 : int128)  : (int128 '× int128) :=
  let '(gy_18, y_19) :=
    keygen  in 
  enc_aux (y_19) (target_pk_16) (m_17).

Definition dec
  (target_sk_20 : el_int_t)
  (c_21 : (int128 '× int128))
  
  : int128 :=
  let secret_q_22 : uint128 :=
    uint128_classify (q_v) in 
  let secret_g_23 : uint128 :=
    uint128_classify (g_v) in 
  let '(c1_24, c2_25) :=
    c_21 in 
  let secret_target_sk_26 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (
        array_to_seq (target_sk_20))) in 
  let secret_c1_27 : uint128 :=
    uint128_classify (c1_24) in 
  let secret_c2_28 : uint128 :=
    uint128_classify (c2_25) in 
  let secret_s_29 : uint128 :=
    uint128_pow_mod (secret_c1_27) (secret_target_sk_26) (secret_q_22) in 
  let secret_s_inverse_30 : uint128 :=
    uint128_pow_mod (secret_s_29) ((secret_q_22) .- (secret_g_23)) (
      secret_q_22) in 
  let secret_m_31 : uint128 :=
    uint128_pow_mod ((secret_c2_28) .* (secret_s_inverse_30)) (
      uint128_classify (@repr WORDSIZE128 1)) (secret_q_22) in 
  let m_32 : int128 :=
    uint128_declassify (secret_m_31) in 
  m_32.


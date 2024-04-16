(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
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
  let secret_s_7 : uint128 :=
    (secret_target_pk_3) .^^ (secret_source_sk_4) in 
  let secret_c1_8 : uint128 :=
    (secret_g_5) .^^ (secret_source_sk_4) in 
  let secret_c2_9 : uint128 :=
    (secret_m_6) .* (secret_s_7) in 
  (uint128_declassify (secret_c1_8), uint128_declassify (secret_c2_9)).

Definition enc (target_pk_10 : int128) (m_11 : int128)  : (int128 '× int128) :=
  let '(gy_12, y_13) :=
    gen  in 
  enc_aux (y_13) (target_pk_10) (m_11).

Definition gen   : (int128 '× el_int_t) :=
  let secret_sk_14 : uint128 :=
    uint128_classify (@repr WORDSIZE128 4) in 
  let pk_15 : int128 :=
    uint128_declassify ((uint128_classify (g_v)) .^^ (secret_sk_14)) in 
  let sk_16 : el_int_t :=
    array_from_seq (2048) (array_to_seq (uint128_to_be_bytes (
        secret_sk_14))) in 
  (pk_15, sk_16).

Definition dec
  (target_sk_17 : el_int_t)
  (c_18 : (int128 '× int128))
  
  : int128 :=
  let secret_q_19 : uint128 :=
    uint128_classify (q_v) in 
  let '(c1_20, c2_21) :=
    c_18 in 
  let secret_target_sk_22 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (
        array_to_seq (target_sk_17))) in 
  let secret_c1_23 : uint128 :=
    uint128_classify (c1_20) in 
  let secret_c2_24 : uint128 :=
    uint128_classify (c2_21) in 
  let secret_s_inverse_25 : uint128 :=
    (secret_c1_23) .^^ ((secret_q_19) .- (secret_target_sk_22)) in 
  let secret_m_26 : uint128 :=
    (secret_c2_24) .* (secret_s_inverse_25) in 
  let m_27 : int128 :=
    uint128_declassify (secret_m_26) in 
  m_27.


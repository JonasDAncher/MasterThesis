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

Definition secret_q_v : uint128 :=
  secret (q_v) : int128.

Definition secret_g_v : uint128 :=
  secret (g_v) : int128.

Definition sk_v : int128 :=
  @repr WORDSIZE128 4.

Definition keygen   : (int128 '× uint128) :=
  let secret_sk_0 : uint128 :=
    uint128_classify (sk_v) in 
  let pk_1 : int128 :=
    uint128_declassify (uint128_pow_mod (secret_g_v) (secret_sk_0) (
        secret_q_v)) in 
  (pk_1, secret_sk_0).

Definition enc (target_pk_2 : int128) (m_3 : int128)  : (int128 '× int128) :=
  let '(gy_4, secret_source_sk_5) :=
    keygen  in 
  let secret_target_pk_6 : uint128 :=
    uint128_classify (target_pk_2) in 
  let secret_m_7 : uint128 :=
    uint128_classify (m_3) in 
  let secret_s_8 : uint128 :=
    uint128_pow_mod (secret_target_pk_6) (secret_source_sk_5) (secret_q_v) in 
  let secret_c1_9 : uint128 :=
    uint128_pow_mod (secret_g_v) (secret_source_sk_5) (secret_q_v) in 
  let secret_c2_10 : uint128 :=
    (secret_m_7) .* (secret_s_8) in 
  (uint128_declassify (secret_c1_9), uint128_declassify (secret_c2_10)).

Definition dec
  (secret_target_sk_11 : uint128)
  (c_12 : (int128 '× int128))
  
  : int128 :=
  let '(c1_13, c2_14) :=
    c_12 in 
  let secret_c1_15 : uint128 :=
    uint128_classify (c1_13) in 
  let secret_c2_16 : uint128 :=
    uint128_classify (c2_14) in 
  let secret_s_inverse_17 : uint128 :=
    uint128_pow_mod (secret_c1_15) (- (secret_target_sk_11)) (secret_q_v) in 
  let secret_m_18 : uint128 :=
    (secret_c2_16) .* (secret_s_inverse_17) in 
  let m_19 : int128 :=
    uint128_declassify (secret_m_18) in 
  m_19.


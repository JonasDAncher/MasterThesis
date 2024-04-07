(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition diff_int_t := nseq (uint8) (usize 2048).

Notation "'pk_t'" := ((int128 '× int128 '× int128)) : hacspec_scope.

Notation "'sk_t'" := (diff_int_t) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t '× sk_t)) : hacspec_scope.

Notation "'session_key_t'" := (diff_int_t) : hacspec_scope.

Definition calculate_pub_key
  (g_0 : int128)
  (q_1 : int128)
  (sk_2 : sk_t)
  
  : pk_t :=
  let ug_3 : uint128 :=
    secret (g_0) : int128 in 
  let uq_4 : uint128 :=
    secret (q_1) : int128 in 
  let usk_5 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (sk_2)) in 
  let ugz_6 : uint128 :=
    uint128_pow_mod (ug_3) (usk_5) (uq_4) in 
  let gz_7 : int128 :=
    uint128_declassify (ugz_6) in 
  (g_0, q_1, gz_7).

Definition calculates_shared_key (sk_8 : sk_t) (pk_9 : pk_t)  : session_key_t :=
  let '(g_10, q_11, pz_12) :=
    pk_9 in 
  let uq_13 : uint128 :=
    secret (q_11) : int128 in 
  let upz_14 : uint128 :=
    secret (pz_12) : int128 in 
  let usk_15 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (sk_8)) in 
  let hab_16 : uint128 :=
    uint128_pow_mod (upz_14) (usk_15) (uq_13) in 
  array_from_seq (2048) (array_to_seq (uint128_to_be_bytes (hab_16))).


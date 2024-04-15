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

Definition g_v : int128 :=
  @repr WORDSIZE128 6515131653.

Definition q_v : int128 :=
  @repr WORDSIZE128 507800679889911926255.

Definition enc_aux
  (y_0 : el_int_t)
  (pk_1 : int128)
  (m_2 : int128)
  
  : (int128 '× int128) :=
  let upk_3 : uint128 :=
    uint128_classify (pk_1) in 
  let ug_4 : uint128 :=
    uint128_classify (g_v) in 
  let uy_5 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (array_to_seq (y_0))) in 
  let um_6 : uint128 :=
    uint128_classify (m_2) in 
  let us_7 : uint128 :=
    (upk_3) .^^ (uy_5) in 
  let uc1_8 : uint128 :=
    (ug_4) .^^ (uy_5) in 
  let uc2_9 : uint128 :=
    (um_6) .* (us_7) in 
  (uint128_declassify (uc1_8), uint128_declassify (uc2_9)).

Definition enc (pk_10 : int128) (m_11 : int128)  : (int128 '× int128) :=
  let y_12 : el_int_t :=
    array_from_seq (2048) (array_to_seq (uint128_to_be_bytes (uint128_classify (
          @repr WORDSIZE128 9846516496)))) in 
  enc_aux (y_12) (pk_10) (m_11).

Definition gen   : (int128 '× el_int_t) :=
  let usk_13 : uint128 :=
    uint128_classify (@repr WORDSIZE128 407800679889911926255) in 
  let pk_14 : int128 :=
    uint128_declassify ((uint128_classify (g_v)) .^^ (usk_13)) in 
  let sk_15 : el_int_t :=
    array_from_seq (2048) (array_to_seq (uint128_to_be_bytes (usk_13))) in 
  (pk_14, sk_15).

Definition dec (x_16 : el_int_t) (c_17 : (int128 '× int128))  : int128 :=
  let uq_18 : uint128 :=
    uint128_classify (q_v) in 
  let '(c1_19, c2_20) :=
    c_17 in 
  let ux_21 : uint128 :=
    uint128_from_be_bytes (array_from_seq (16) (array_to_seq (x_16))) in 
  let uc1_22 : uint128 :=
    uint128_classify (c1_19) in 
  let uc2_23 : uint128 :=
    uint128_classify (c2_20) in 
  let us_inverse_24 : uint128 :=
    (uc1_22) .^^ ((uq_18) .- (ux_21)) in 
  let um_25 : uint128 :=
    (uc2_23) .* (us_inverse_24) in 
  let m_26 : int128 :=
    uint128_declassify (um_25) in 
  m_26.


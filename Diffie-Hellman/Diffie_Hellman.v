(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Num_Bigint.

Require Import Hacspec_Lib.

Definition diff_int_t := nat_mod pow2 2048.

Notation "'pk_t'" := ((diff_int_t '× diff_int_t '× diff_int_t
)) : hacspec_scope.

Notation "'sk_t'" := (diff_int_t) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t '× sk_t)) : hacspec_scope.

Notation "'session_key_t'" := (diff_int_t) : hacspec_scope.

Definition calculate_pub_key
  (g_0 : diff_int_t)
  (q_1 : diff_int_t)
  (sk_2 : sk_t)
  
  : pk_t :=
  (g_0, q_1, nat_mod_pow_mod (g_0) (sk_2) (q_1)).

Definition calculates_shared_key (sk_3 : sk_t) (pk_4 : pk_t)  : session_key_t :=
  let '(g_5, q_6, pz_7) :=
    pk_4 in 
  let hab_8 : session_key_t :=
    nat_mod_pow_mod (pz_7) (sk_3) (q_6) in 
  hab_8.


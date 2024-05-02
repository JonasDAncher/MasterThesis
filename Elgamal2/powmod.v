From Hacspec Require Import Hacspec_Lib Hacspec_Lib_Pre.
From Jasmin Require Import word.
From mathcomp.word Require Import ssrZ word.
From Coq Require Import ZArith.


From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

Definition uint128_pow_mod
  (g_0: uint128)
  (x_1: uint128)
  (n_2: uint128)

  : uint128 :=
    nat_to_int((g_0 ^ x_1) mod n_2).
  (**let asd_3 : int128 :=  **)
  (** Z.powm(g_0 x_1 n_2). **)
  
Definition pow
  (g_3: uint128)
  (x_4: uint128)
  
  : uint128 :=
    nat_to_int(g_3 ^ x_4).
    
Definition uint128_modulo
	(n_5: uint128)
	(n_6: uint128)
	
	: uint128 :=
		nat_to_int(n_5 mod n_6).
    
    
Notation "A .^^ B" := (pow A B) (at level 80). 

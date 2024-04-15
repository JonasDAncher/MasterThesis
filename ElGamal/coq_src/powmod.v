Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.

Definition uint128_pow_mod
  (g_0: int128)
  (x_1: int128)
  (n_2: int128)

  : int128 :=
    (g_0 ^ x_1) mod n_2.
  (**let asd_3 : int128 :=  **)
  (** Z.powm(g_0 x_1 n_2). **)
  
Definition pow
  (g_3: int128)
  (x_4: int128)
  
  : int128 :=
    g_3 ^ x_4.
    
    
Notation "A .^^ B" := (pow A B) (at level 80).

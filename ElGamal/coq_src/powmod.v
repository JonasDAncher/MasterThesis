Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.

Definition pow
  (g_3: int128)
  (x_4: int128)
  
  : int128 :=
	repr (unsigned g_3 ^ unsigned x_4).
    
    
Definition uint128_modulo
	(n_5: int128)
	(n_6: int128)
	
	: int128 :=
		MachineIntegers.modu n_5 n_6.

Definition uint128_pow_mod
  (g_0: int128)
  (x_1: int128)
  (n_2: int128)

  : int128 :=
    uint128_modulo (pow g_0 x_1) n_2.
  (**let asd_3 : int128 :=  **)
  (** Z.powm(g_0 x_1 n_2). **)
  
    
Notation "A .^^ B" := (pow A B) (at level 80). 

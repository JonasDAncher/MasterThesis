Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition pow_mod
  (g_0: int128)
  (x_1: int128)
  (n_2: int128)

  : int128 :=
    (g_0 ^ x_1) mod n_2.
  (**let asd_3 : int128 :=  **)
  (** Z.powm(g_0 x_1 n_2). **)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* For hoqide: Add LoadPath "coq/theories/" as Coq.*)
Require Export Coq.Classes.CRelationClasses.
(* Require Export Classes.SetoidTactics.*)

(* Export Morphisms.ProperNotations. *)
Definition Setoid_Theory := @Equivalence.
Definition Build_Setoid_Theory := @Build_Equivalence.

(* No paths yet.
Definition gen_st : forall A : Type, Setoid_Theory _ (@paths A).
Proof.
Admitted.
(* Bas: congruence is not defined yet.
  constructor; congruence.
Qed. *)*)

(* Bas: Should be added in Overture.
 Definition Type_st : Setoid_theory Type Equiv.*)

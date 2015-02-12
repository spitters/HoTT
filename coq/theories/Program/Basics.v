(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(** Standard functions and combinators.

   Proofs about them require functional extensionality and can be found
   in [Combinators].

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Logic Datatypes.

(* Set Universe Polymorphism. *)

(** The polymorphic identity function, here copied from [Datatypes]. *)
Definition ID := forall {A : Type}, A -> A.
Definition id : ID := fun A x => x.
(* Arguments id {A} x.*)

(** Function composition. *)

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity) : program_scope.

Local Open Scope program_scope.

(** The non-dependent function space between [A] and [B]. *)

Definition arrow (A B : Type) := A -> B.

(** The constant function [const a] always returns [a]. *)

Definition const {A B} (a : A) := fun _ : B => a.

(** The [flip] combinator reverses the first two arguments of a function. *)

Monomorphic Definition flip {A B C} (f : A -> B -> C) x y := f y x.

(** Application as a combinator. *)

Definition apply {A B} (f : A -> B) (x : A) := f x.

Arguments prod_curry   {A B C} f p.
(* sArguments prod_uncurry {A B C} f x y.*)
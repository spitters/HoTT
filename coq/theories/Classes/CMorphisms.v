(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Typeclass-based morphism definition and standard, minimal instances

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Export Coq.Classes.CRelationClasses.

Generalizable Variables A eqA B C D R RA RB RC m f x y.
Local Obligation Tactic := simpl_crelation.

Set Universe Polymorphism.

(** * Morphisms.

   We now turn to the definition of [Proper] and declare standard instances.
   These will be used by the [setoid_rewrite] tactic later. *)

(** A morphism for a relation [R] is a proper element of the relation.
   The relation [R] will be instantiated by [respectful] and [A] by an arrow
   type for usual morphisms. *)
Section Proper.
  Context {A B : Type}.

  Class Proper (R : crelation A) (m : A) :=
    proper_prf : R m m.

  (** Every element in the carrier of a reflexive relation is a morphism
   for this relation.  We use a proxy class for this case which is used
   internally to discharge reflexivity constraints.  The [Reflexive]
   instance will almost always be used, but it won't apply in general to
   any kind of [Proper (A -> B) _ _] goal, making proof-search much
   slower. A cleaner solution would be to be able to set different
   priorities in different hint bases and select a particular hint
   database for resolution of a type class constraint. *)

  Class ProperProxy (R : crelation A) (m : A) :=
    proper_proxy : R m m.
(* We don't have paths yet 
  Lemma path_proper_proxy (x : A) : ProperProxy (@paths A) x.
  Admitted. (* Proof. firstorder. Qed.*) *)
  
  Lemma reflexive_proper_proxy `(Reflexive A R) (x : A) : ProperProxy R x.
  Admitted. (* Proof. firstorder. Qed.*)

  Lemma proper_proper_proxy x `(Proper R x) : ProperProxy R x.
  Admitted. (* Proof. firstorder. Qed.*)

  (** Respectful morphisms. *)
  
  (** The fully dependent version, not used yet. *)
  
  Definition respectful_hetero
  (A B : Type)
  (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Type)
  (R' : forall (x : A) (y : B), C x -> D y -> Type) :
    (forall x : A, C x) -> (forall x : B, D x) -> Type :=
    fun f g => forall x y, R x y -> R' x y (f x) (g y).

  (** The non-dependent version is an instance where we forget dependencies. *)
  
  Definition respectful (R : crelation A) (R' : crelation B) : crelation (A -> B) :=
    Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').
End Proper.

(** We favor the use of Leibniz equality or a declared reflexive crelation 
  when resolving [ProperProxy], otherwise, if the crelation is given (not an evar),
  we fall back to [Proper]. *)
(* Hint Extern 1 (ProperProxy _ _) => 
  class_apply @eq_proper_proxy || class_apply @reflexive_proper_proxy : typeclass_instances.*)

(* Hint Extern 2 (ProperProxy ?R _) => 
  not_evar R; class_apply @proper_proper_proxy : typeclass_instances.*)

(** Notations reminiscent of the old syntax for declaring morphisms. *)
Delimit Scope signature_scope with signature.

Module ProperNotations.

  Notation " R ++> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R ==> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R --> R' " := (@respectful _ _ (flip (R%signature)) (R'%signature))
    (right associativity, at level 55) : signature_scope.

End ProperNotations.

Arguments Proper {A}%type R%signature m.
Arguments respectful {A B}%type (R R')%signature _ _.

Export ProperNotations.

Local Open Scope signature_scope.

(** [solve_proper] try to solve the goal [Proper (?==> ... ==>?) f]
    by repeated introductions and setoid rewrites. It should work
    fine when [f] is a combination of already known morphisms and
    quantifiers. *)

Ltac solve_respectful t :=
 match goal with
   | |- respectful _ _ _ _ =>
     let H := fresh "H" in
     intros ? ? H; solve_respectful ltac:(setoid_rewrite H; t)
   | _ => t; reflexivity
 end.

Ltac solve_proper := unfold Proper; solve_respectful ltac:(idtac).

(** [f_equiv] is a clone of [f_equal] that handles setoid equivalences.
    For example, if we know that [f] is a morphism for [E1==>E2==>E],
    then the goal [E (f x y) (f x' y')] will be transformed by [f_equiv]
    into the subgoals [E1 x x'] and [E2 y y']. *)
Ltac f_equiv :=
 match goal with
  | |- ?R (?f ?x) (?f' _) =>
    let T := type of x in
    let Rx := fresh "R" in
    evar (Rx : crelation T);
    let H := fresh in
    assert (H : (Rx==>R)%signature f f');
    unfold Rx in *; clear Rx; [ f_equiv | apply H; clear H; try reflexivity ]
  | |- ?R ?f ?f' =>
    solve [change (Proper R f); eauto with typeclass_instances | reflexivity ]
  | _ => idtac
 end.
 
Section Relations.
  Context {A B : Type}. 

  (** [forall_def] reifies the dependent product as a definition. *)
  
  Definition forall_def (P : A -> Type) : Type := forall x : A, P x.
  
  (** Dependent pointwise lifting of a crelation on the range. *)
  
  Definition forall_relation (P : A -> Type)
             (sig : forall a, crelation (P a)) : crelation (forall x, P x) :=
    fun f g => forall a, sig a (f a) (g a).

  (** Non-dependent pointwise lifting *)
  Definition pointwise_relation (R : crelation B) : crelation (A -> B) :=
    fun f g => forall a, R (f a) (g a).

  (* Lemma pointwise_pointwise (R : crelation B) :
    relation_equivalence (pointwise_relation R) (@paths A ==> R).
  Proof. intros. split. simpl_crelation. Rtauto. Qed. *)
  
  (** Subcrelations induce a morphism on the identity. *)
  
  (* Global Instance subrelation_id_proper `(subrelation A RA RA') : Proper (RA ==> RA') id.
  Proof. firstorder. Qed.*)

  (** The subrelation property goes through products as usual. *)
  
  Lemma subrelation_respectful `(subl : subrelation A RA' RA, subr : subrelation B RB RB') :
    subrelation (RA ==> RB) (RA' ==> RB').
  Proof. Admitted. (* simpl_crelation. Qed. *)

  (** And of course it is reflexive. *)
  
  Lemma subrelation_refl R : @subrelation A R R.
  Proof. Admitted. (* simpl_crelation. Qed. *)

  (** [Proper] is itself a covariant morphism for [subrelation].
   We use an unconvertible premise to avoid looping.
   *)
  
  Lemma subrelation_proper `(mor : Proper A R' m) 
        `(unc : Unconvertible (crelation A) R R')
        `(sub : subrelation A R' R) : Proper R m.
  Proof.
    intros. apply sub. apply mor.
  Qed.

(* We don't have paths yet 
  Global Instance proper_subrelation_proper_arrow :
    Proper (subrelation ++> paths ==> arrow) (@Proper A).
  Proof. Admitted. (* reduce. subst. firstorder. Qed.*)*)

  Global Instance pointwise_subrelation `(sub : subrelation B R R') :
    subrelation (pointwise_relation R) (pointwise_relation R') | 4.
  Proof. reduce. unfold pointwise_relation in *. apply sub. auto. Qed.
  
  (** For dependent function types. *)
  Lemma forall_subrelation (P : A -> Type) (R S : forall x : A, crelation (P x)) :
    (forall a, subrelation (R a) (S a)) -> 
    subrelation (forall_relation P R) (forall_relation P S).
  Proof. reduce. Admitted. (* firstorder. Qed.*)
End Relations.
Typeclasses Opaque respectful pointwise_relation forall_relation.
Arguments forall_relation {A P}%type sig%signature _ _.
Arguments pointwise_relation A%type {B}%type R%signature _ _.

Hint Unfold Reflexive : core.
Hint Unfold Symmetric : core.
Hint Unfold Transitive : core.

(** Resolution with subrelation: favor decomposing products over applying reflexivity
  for unconstrained goals. *)
Ltac subrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @subrelation_refl) ||
    class_apply @subrelation_respectful || class_apply @subrelation_refl.

Hint Extern 3 (@subrelation _ ?T ?U) => subrelation_tac T U : typeclass_instances.

CoInductive apply_subrelation : Prop := do_subrelation.

Ltac proper_subrelation :=
  match goal with
    [ H : apply_subrelation |- _ ] => clear H ; class_apply @subrelation_proper
  end.

Hint Extern 5 (@Proper _ ?H _) => proper_subrelation : typeclass_instances.

(** Essential subrelation instances for [pointwise_relation]. *)

(** Essential subrelation instances for [iffT] and [arrow]. *)

Instance iffT_arrow_subrelation : subrelation iffT arrow | 2.
Proof. Admitted. (* firstorder. Qed. *)

Instance iffT_flip_arrow_subrelation : subrelation iffT (flip arrow) | 2.
Proof. Admitted. (* firstorder. Qed. *)

(** We use an extern hint to help unification. *)

Hint Extern 4 (subrelation (@forall_relation ?A ?B ?R) (@forall_relation _ _ ?S)) =>
  apply (@forall_subrelation A B R S) ; intro : typeclass_instances.

(* Start with hoqide -R coq/theories/ Coq setoidtest.v *)
Require Import Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.CMorphisms.
Require Import HoTT.

(* This is still very experimental, but it seems to work for both Equiv and paths with some help. *)

Instance Proper_IsHProp: Proper (Equiv --> flip arrow) IsHProp.
intros X Y f H. unfold flip in f.
(* Why does ^-1 not refer to equiv_inverse *)
by apply (@trunc_equiv' _ _ f).
Qed.

Open Scope equiv_scope.
Goal forall {A B:Type}, IsHProp A -> (A <~>B) -> IsHProp B.
intros  ?? H e.
set (equiv_inverse e).
setoid_rewrite <- e.
assumption.
Abort.
Require Export Relation_Definitions.

(* This is deprecated syntax, but it works *)

Definition Setoid_Theory := @Equivalence.
Definition Build_Setoid_Theory := @Build_Equivalence.

Definition gen_st : forall A : Type, Setoid_Theory _ (@paths A).
Proof.
intro. split.
 - done.
 - unfold CRelationClasses.Symmetric. done.
 - unfold CRelationClasses.Transitive. intros. by transitivity y.
Defined.

Definition Type_st : Setoid_Theory Type Equiv.
Proof.
split.
 - unfold CRelationClasses.Reflexive. intro. apply equiv_idmap.
 - unfold CRelationClasses.Symmetric. done.
 - unfold CRelationClasses.Transitive. intros. by transitivity y.
Defined.

Instance Proper_paths_IsHProp: Proper (paths ==> flip arrow) IsHProp.
intros X Y f H. unfold CRelationClasses.flip in f.
by rewrite f.
Qed.

(* This also allows us to setoid_rewrite with paths*)
Goal forall {A B:Type}, IsHProp A -> (B = A) -> IsHProp B.
intros  ?? H e.
setoid_rewrite e.
assumption.
Abort.

(* Coq.Classes.RelationClasses.RewriteRelation 
Add Parametric Relation (A : Type): A (@paths A)
transitivity proved by admit
as rel_paths.*)
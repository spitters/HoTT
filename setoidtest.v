Require Import Basics.
Add LoadPath "coq/theories/" as Coq.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.CMorphisms.

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
Abort.

(* We might want to add this too *)
Definition Setoid_Theory := @Equivalence.
Definition Build_Setoid_Theory := @Build_Equivalence.

Definition gen_st : forall A : Type, Setoid_Theory _ (@paths A).
Admitted.

Definition Type_st : Setoid_Theory Type Equiv.

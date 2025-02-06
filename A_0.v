(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*      Copyright 2018-2019: Tianyu Sun, Yaoshun Fu and Wensheng Yu.       *)
(***************************************************************************)


Require Export Classical.

(* A.0 基本逻辑 *)

Module Property.

Proposition Lemma_x : forall A: Prop, A -> A /\ A.
Proof. intros; split; auto. Qed.

Proposition Lemma_y : forall (A B : Prop), A -> B -> A /\ B.
Proof. intros; split; auto. Qed.

Proposition Lemma_z : forall A B, (A<->B) -> (~ A) -> (~ B).
Proof. unfold not; intros; apply H in H1; apply H0 in H1; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Ltac add B H:= apply (Lemma_y _ B) in H; auto.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃ x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").



End Property.

Export Property.


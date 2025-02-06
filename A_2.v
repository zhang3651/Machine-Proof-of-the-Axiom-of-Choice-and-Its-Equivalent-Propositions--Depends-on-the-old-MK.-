(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*      Copyright 2018-2019: Tianyu Sun, Yaoshun Fu and Wensheng Yu.       *)
(***************************************************************************)


Require Export A_1.

(* A.2 分类公理图式续 *)

Module A2.

(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).


(* 分类公理II  *)

Axiom AxiomII : forall (b: Class) (P: Class -> Prop),
  b ∈ \{ P \} <-> Ensemble b /\ (P b).




End A2.

Export A2.
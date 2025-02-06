(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Zermelo_Postulate.


(** The proof of AC **)

Module Type Zermelo_Proof_AC.

Declare Module Ze : Zermelo_Postulate.

Definition En_p X : Class :=
  \{ λ z, exists A, A ∈ (pow(X)~[Φ]) /\ z = (A × [A]) \}.

Theorem Zermelo_AC : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros.
  assert (exists D, forall p, p ∈ (En_p X) -> exists x, p ∩ D = [x]).
  { assert (Ensemble (En_p X) /\ Φ ∉ (En_p X)).
    { assert ((En_p X) ⊂ pow(X × (pow(X)~[Φ]))).
      { unfold Included; intros; unfold En_p in H0; apply AxiomII in H0.
        destruct H0, H1 as [A H1], H1; rewrite H2 in *; clear H2.
        apply AxiomII; split; auto; unfold Included; intros.
        PP H2 a b; clear H2; apply AxiomII_P in H3; destruct H3, H3.
        unfold Setminus in H1; apply AxiomII in H1; destruct H1, H5; double H5.
        unfold PowerSet in H7; apply AxiomII in H7; destruct H7 as [_ H7].
        unfold Cartesian; apply AxiomII_P; repeat split; auto.
        unfold Singleton in H4; apply AxiomII in H4; destruct H4.
        rewrite H8 in *; try apply Theorem19; Ens; clear H8.
        unfold Setminus; apply Theorem4'; split; auto. }
      assert (Ensemble (pow( X × (pow( X) ~ [Φ])))).
      { apply Theorem38; auto; apply Theorem74; split; auto.
        unfold Setminus; apply Theorem38 in H; auto.
        apply Theorem33 with (x:= pow(X)); auto.
        unfold Included; intros; apply Theorem4' in H1; apply H1. }
      apply Theorem33 in H0; auto; clear H1; split; auto.
      intro; unfold En_p in H1; apply AxiomII in H1; destruct H1.
      destruct H2 as [A H2], H2; unfold Setminus in H2.
      apply Theorem4' in H2; destruct H2; unfold Complement in H4.
      apply AxiomII in H4; destruct H4.
      generalize (classic (A = Φ)); intros; destruct H6.
      - rewrite H6 in H5; destruct H5; apply AxiomII; Ens.
      - apply Property_NotEmpty in H6; destruct H6.
        assert ([x,A] ∈ Φ).
        { rewrite H3; unfold Cartesian; apply AxiomII_P.
          repeat split; try apply Theorem49; Ens; apply AxiomII; Ens. }
        generalize (Theorem16 ([x,A])); intros; contradiction. }
    destruct H0; apply Ze.Zermelo in H0; try destruct H0 as [D H0], H0; Ens.
    intros; unfold En_p in H2; destruct H2; apply AxiomII in H2.
    apply AxiomII in H4; destruct H2, H4, H5 as [A H5], H6 as [B H6], H5, H6.
    rewrite H7, H8 in *; clear H7 H8; apply AxiomI; split; intros.
    - apply Theorem4' in H7; destruct H7; PP H7 a b; clear H7.
      apply AxiomII_P in H8; apply AxiomII_P in H9; destruct H8, H9, H8, H10.
      unfold Singleton in H11, H12; apply AxiomII in H11; apply AxiomII in H12.
      destruct H11 as [_ H11], H12 as [_ H12]; AssE A; AssE B.
      apply Theorem19 in H13; apply Theorem19 in H14; apply H12 in H13.
      apply H11 in H14. rewrite H13 in H14; rewrite H14 in H3; destruct H3; Ens.
    - generalize (Theorem16 z); intros; contradiction. }
  destruct H0 as [D H0].
  set (fc := \{\ λ A B, A ∈ (pow(X) ~ [Φ]) /\ B = First( ∩((A×[A]) ∩ D)) \}\).
  assert (Function (fc)).
  { unfold Function; split; intros.
    - unfold Relation; intros; PP H1 a b; Ens.
    - destruct H1; apply AxiomII_P in H1; apply AxiomII_P in H2.
      destruct H1, H2, H3, H4; rewrite H5, H6; auto. }
  exists fc; unfold Choice_Function; repeat split; try apply H1; intros.
  - clear H1; unfold Included, Range; intros; apply AxiomII in H1.
    destruct H1, H2; apply AxiomII_P in H2; clear H1; destruct H2, H2.
    apply Theorem49 in H1; destruct H1.
    assert ((x × [x]) ∈ (En_p X)).
    { unfold En_p; apply AxiomII; split; Ens.
      apply Theorem74; split; try apply Theorem42; auto. }
    AssE (x × [x]); apply H0 in H5; destruct H5; rewrite H5 in H3.
    assert (Ensemble x0).
    { apply Theorem42'; rewrite <- H5.
      apply Theorem33 with (x:= x × [x]); auto; unfold Included; intros.
      apply Theorem4' in H7; apply H7. }
    clear H6; double H7; apply Theorem44 in H7; destruct H7 as [H7 _].
    rewrite H7 in H3; clear H7.
    assert (x0 ∈ (x × [x] ∩ D)).
    { rewrite H5; unfold Singleton; apply AxiomII; Ens. }
    apply Theorem4' in H7; destruct H7 as [H7 _]; PP H7 a b; clear H6 H7.
    apply AxiomII_P in H8; destruct H8, H7; apply Theorem49 in H6.
    apply Theorem54 in H6; destruct H6 as [H6 _]; rewrite H6 in H3.
    rewrite H3 in *; unfold Setminus, PowerSet in H2; apply Theorem4' in H2.
    destruct H2 as [H2 _]; apply AxiomII in H2; apply H2 in H7; auto.
  - clear H1; apply AxiomI; split; intros.
    + unfold Domain in H1; apply AxiomII in H1; destruct H1, H2.
      apply AxiomII_P in H2; apply H2.
    + unfold Domain; apply AxiomII; split; Ens.
      assert ((z × [z]) ∈ (En_p X)).
      { unfold En_p; apply AxiomII; split.
        - apply Theorem74; split; try apply Theorem42; Ens.
        - exists z; split; auto. }
      AssE (z × [z]); apply H0 in H2; destruct H2.
      assert (Ensemble x).
      { apply Theorem42'; rewrite <- H2.
        apply Theorem33 with (x:= z × [z]); auto; unfold Included; intros.
        apply Theorem4' in H4; apply H4. }
      assert (x ∈ (z × [z] ∩ D)); clear H3.
      { rewrite H2; unfold Singleton; apply AxiomII; Ens. }
      apply Theorem4' in H5; destruct H5 as [H3 _]; PP H3 a b.
      clear H3; apply Theorem49 in H4; elim H4; intros; clear H6.
      apply Theorem54 in H4; destruct H4 as [H4 _]; apply AxiomII_P in H5.
      destruct H5, H6; exists a; apply AxiomII_P; repeat split; auto.
      * apply Theorem49; split; Ens.
      * rewrite H2; apply Theorem44 in H5; destruct H5 as [H5 _].
        rewrite H5, H4; auto.
  - apply Property_Value in H2; auto; apply AxiomII_P in H2; destruct H2, H3.
    assert ((A × [A]) ∈ (En_p X)).
    { unfold En_p; apply AxiomII; split.
      - apply Theorem74; split; try apply Theorem42; Ens.
      - exists A; split; auto. }
    AssE (A × [A]); apply H0 in H5; destruct H5.
    assert (Ensemble x).
    { apply Theorem42'; rewrite <- H5.
      apply Theorem33 with (x:= A × [A]); auto; unfold Included; intros.
      apply Theorem4' in H7; apply H7. }
    assert (x ∈ (A × [A] ∩ D)); clear H6.
    { rewrite H5; unfold Singleton; apply AxiomII; Ens. }
    apply Theorem4' in H8; destruct H8 as [H6 _]; PP H6 a b.
    clear H6; apply Theorem49 in H7; apply Theorem54 in H7.
    destruct H7 as [H7 _]; apply AxiomII_P in H8; destruct H8, H8.
    rewrite H5 in H4; apply Theorem44 in H6; destruct H6 as [H6 _].
    rewrite H6, H7 in H4; rewrite H4; auto.
Qed.


End Zermelo_Proof_AC.


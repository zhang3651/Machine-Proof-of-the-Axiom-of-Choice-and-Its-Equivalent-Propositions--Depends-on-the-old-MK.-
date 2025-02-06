(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Tukey_Lemma.

(* The Proof of Axiom of Choice *)

Module Type Tukey_Proof_AC.

Declare Module Tu : Tukey_Lemma.

(* Special form of Choice Function *)

Definition Choice_Function' ε u : Prop :=
  Ensemble u /\ Function ε /\ dom(ε) = u /\ ran(ε) ⊂ ∪u
  /\ (forall x, x ∈ dom(ε) -> ε[x] ∈ x).

(* Hypotheses *)

Definition En_f X :=
  \{ λ g, exists A, A ⊂ (pow(X)~[Φ]) /\ Choice_Function' g A \}.

(* Properties *)

Lemma Property_CF x : Ensemble x -> Choice_Function' Φ Φ.
Proof.
  intros.
  unfold Choice_Function'; repeat split; intros.
  - generalize (Theorem26 x); intros.
    apply Theorem33 in H0; auto.
  - unfold Relation; intros.
    generalize (Theorem16 z); contradiction.
  - destruct H0; generalize (Theorem16 ([x0,y])).
    intros; contradiction.
  - apply AxiomI; split; intros.
    + unfold Domain in H0; apply AxiomII in H0; destruct H0, H1.
      generalize (Theorem16 ([z,x0])); contradiction.
    + generalize (Theorem16 z); contradiction.
  - unfold Included; intros; unfold Range in H0.
    apply AxiomII in H0; destruct H0, H1.
    generalize (Theorem16 ([x0,z])); contradiction.
  - unfold Domain in H0; apply AxiomII in H0; destruct H0, H1.
    generalize (Theorem16 ([x0,x1])); contradiction.
Qed.

Lemma Included_Function : forall (g f: Class),
  Function g /\ Function f /\ g ⊂ f -> (dom(g) ⊂ dom(f))
  /\ (forall x, x ∈ dom(g) -> g[x] = f[x]).
Proof.
  intros.
  destruct H, H0.
  unfold Included in H1; split.
  - unfold Included; intros.
    unfold Domain in H2; apply AxiomII in H2; destruct H2, H3.
    unfold Domain; apply AxiomII; split; auto.
    exists x; apply H1 in H3; auto.
  - intros; apply Property_Value in H2; auto.
    apply H1 in H2; apply Theorem70 in H0; auto.
    rewrite H0 in H2; apply AxiomII_P in H2; apply H2.
Qed.

(* Lemma *)

Lemma Lemma_Fin_not_Em : forall X,
  Ensemble X -> FiniteSet (En_f X) /\ (En_f X) ≠ Φ.
Proof.
  intros.
  assert ((En_f X) ≠ Φ).
  { apply Property_NotEmpty; auto.
    exists Φ; unfold En_f; apply AxiomII; split.
    - assert (Φ ⊂ X); try apply Theorem26.
      apply Theorem33 in H0; auto.
    - exists Φ; split; try apply Theorem26.
      apply (Property_CF X); auto. }
  split; auto; unfold FiniteSet; repeat split; intros.
  - assert (En_f X ⊂ pow(pow(X) × (∪pow(X)))).
    { unfold Included; intros.
      unfold En_f in H1; apply AxiomII in H1; destruct H1.
      destruct H2 as [A H2]; destruct H2.
      assert (pow(X) ~ [Φ] ⊂ pow(X)).
      { unfold Setminus, Included; intros.
        apply Theorem4' in H4; apply H4. }
      add (pow(X)~[Φ] ⊂ pow( X)) H2; apply Theorem28 in H2.
      unfold Choice_Function' in H3; destruct H3, H5, H6, H7.
      unfold PowerSet at 1; apply AxiomII; split.
      - rewrite <- H6 in H3; apply Theorem75; auto.
      - unfold Included; intros; unfold Cartesian; double H9.
        apply H5 in H10; destruct H10 as [a [b H10]]; rewrite H10 in *.
        clear H10; apply AxiomII_P; repeat split; Ens.
        + apply Property_dom in H9; rewrite H6 in H9.
          unfold Included in H2; apply H2; auto.
        + apply Property_ran in H9.
          unfold Included in H7; apply H7 in H9.
          apply Theorem31 in H2; destruct H2.
          unfold Included in H2; apply H2; auto. }
    apply Theorem38 in H; auto; double H.
    apply AxiomVI in H2; add (Ensemble (∪ pow( X))) H.
    apply Theorem74 in H; apply Theorem38 in H; auto.
    apply Theorem33 in H1; auto.
  - destruct H2; unfold En_f in H1; unfold En_f.
    apply AxiomII in H1; apply AxiomII; destruct H1.
    destruct H4 as [D H4], H4; unfold Choice_Function' in H5.
    destruct H5, H6, H7, H8; split.
    + apply Theorem33 in H2; auto.
    + generalize (classic (z=Φ)); intros; destruct H10.
      * exists Φ; split; try apply Theorem26.
        rewrite H10; apply (Property_CF X); auto.
      * assert (Function z).
        { unfold Function in H6; destruct H6.
          unfold Function; split; intros.
          - unfold Relation in H6; unfold Relation; intros.
            unfold Included in H2; apply H2 in H12.
            apply H6 in H12; destruct H12, H12; exists x, x0; auto.
          - destruct H12; unfold Included in H2.
            apply H2 in H12; apply H2 in H13.
            add ([x,z0] ∈ F) H12; apply H11 in H12; auto. }
        double H11; add (Function F /\ z⊂F) H11.
        apply Included_Function in H11; destruct H11.
        exists (dom(z)); split.
        -- rewrite H7 in H11; add (D ⊂ pow(X)~[Φ]) H11.
           apply Theorem28 in H11; auto.
        -- { unfold Choice_Function'; repeat split; try apply H12; auto.
             - rewrite H7 in H11; apply Theorem33 in H11; auto.
             - unfold Included; intros.
               unfold Element_U; apply AxiomII.
               unfold Range in H14; apply AxiomII in H14.
               destruct H14, H15; double H15; split; auto.
               apply Theorem70 in H12; auto.
               rewrite H12 in H15; apply AxiomII_P in H15.
               apply Property_dom in H16; destruct H15.
               exists x; split; auto; rewrite H17; double H16.
               unfold Included in H11; apply H11 in H16.
               apply H9 in H16; apply H13 in H18; rewrite H18; auto.
             - intros; double H14.
               unfold Included in H11; apply H11 in H14.
               apply H9 in H14; apply H13 in H15; rewrite H15; auto. }
  - intros; destruct H1.
    unfold En_f; apply AxiomII; split; auto.
    assert (F ⊂ ∪(En_f X) /\ ∪(En_f X) ⊂ ((pow( X) ~ [Φ]) × X)).
    { split.
      - unfold Included; intros; AssE z.
        unfold Element_U; apply AxiomII; split; auto.
        exists [z]; split.
        + unfold Singleton; apply AxiomII; split; auto.
        + apply H2; split; try apply Finite_Single; auto.
          unfold Included; intros; unfold Singleton in H5; apply AxiomII in H5.
          destruct H5; apply Theorem19 in H4; apply H6 in H4; rewrite H4; auto.
      - unfold Included; intros.
        unfold Element_U in H3; apply AxiomII in H3.
        destruct H3, H4 as [f1 H4], H4.
        assert (exists a b, z = [a,b]).
        { unfold En_f in H5; apply AxiomII in H5; destruct H5, H6, H6.
          unfold Choice_Function' in H7; apply H7 in H4; apply H4. }
        destruct H6 as [a [b H6]]; unfold Cartesian.
        rewrite H6; rewrite H6 in H3; rewrite H6 in H4.
        apply AxiomII_P; split; auto.
        unfold En_f in H5; apply AxiomII in H5.
        destruct H5, H7 as [A H7], H7.
        unfold Choice_Function' in H8.
        destruct H8, H9, H10, H11; split.
        + apply Property_dom in H4; rewrite H10 in H4.
          unfold Included in H7; apply H7 in H4; auto.
        + apply Property_ran in H4.
          unfold Included in H11; apply H11 in H4.
          unfold Element_U in H4; apply AxiomII in H4.
          destruct H4, H13, H13.
          unfold Included in H7; apply H7 in H14.
          unfold Setminus in H14; apply Theorem4' in H14; destruct H14.
          unfold PowerSet in H14; apply AxiomII in H14; destruct H14.
          unfold Included in H16; apply H16 in H13; auto. }
    elim H3; intros; apply Theorem28 in H3.
    generalize (classic (F = Φ)); intros; destruct H6.
    + exists Φ; split; try apply Theorem26.
      rewrite H6; apply (Property_CF X); auto.
    + assert (Function F).
      { unfold Function, Relation; split; intros.
        - unfold Included in H3; apply H3 in H7; PP H7 a b; Ens.
        - destruct H7.
          assert ([[x,y]|[x,z]] ⊂ F /\ Finite ([[x,y]|[x,z]])).
          { unfold Included, Unordered; split; intros.
            - apply AxiomII in H9; destruct H9, H10.
              + unfold Singleton in H10; apply AxiomII in H10.
                destruct H10; rewrite H11; auto; apply Theorem19; Ens.
              + unfold Singleton in H10; apply AxiomII in H10.
                destruct H10; rewrite H11; auto; apply Theorem19; Ens.
            - apply Theorem168; split; apply Finite_Single; Ens. }
          apply H2 in H9; unfold En_f in H9; apply AxiomII in H9.
          destruct H9, H10, H10; unfold Choice_Function' in H11.
          destruct H11, H12, H13; unfold Function in H12.
          apply H12 with (x0:=x); split; unfold Unordered; apply AxiomII.
          + split; try left; Ens; unfold Singleton; apply AxiomII; Ens.
          + split; try right; Ens; unfold Singleton; apply AxiomII; Ens. }
      exists dom(F); split.
      * unfold Included; intros; apply Property_Value in H8; auto.
        unfold Included in H3; apply H3 in H8.
        unfold Cartesian in H8; apply AxiomII_P in H8; apply H8.
      * { unfold Choice_Function'; repeat split; try apply H7; auto; intros.
          - assert (dom(F) ⊂ pow(X)).
            { unfold Included; intros.
              unfold Domain in H8; apply AxiomII in H8; destruct H8, H9.
              unfold Included in H3; apply H3 in H9.
              unfold Cartesian in H9; apply AxiomII_P in H9; destruct H9, H10.
              unfold Setminus in H10; apply Theorem4' in H10; apply H10. }
            apply Theorem33 in H8; apply Theorem38 in H; auto.
          - unfold Included; intros; apply AxiomII; split; Ens.
            unfold Range in H8; apply AxiomII in H8; destruct H8, H9.
            double H9; exists x; apply Property_dom in H9; split; auto.
            unfold Element_U in H4; apply H4 in H10.
            apply AxiomII in H10; destruct H10, H11 as [f H11], H11.
            unfold En_f in H12; apply AxiomII in H12; destruct H12, H13, H13.
            unfold Choice_Function' in H14; destruct H14, H15, H16, H17.
            double H11; apply Property_dom in H19; double H19.
            apply Property_Value in H20; auto; apply H18 in H19.
            add ([x,z] ∈ f) H20; unfold Function in H15.
            apply H15 in H20; rewrite H20 in H19; auto.
          - apply Property_Value in H8; auto; apply H4 in H8.
            unfold Element_U in H8; apply AxiomII in H8.
            destruct H8, H9 as [f H9], H9; unfold En_f in H10.
            apply AxiomII in H10; destruct H10, H11, H11.
            unfold Choice_Function' in H12; destruct H12, H13, H14, H15.
            double H9; apply Property_dom in H17; double H17.
            apply H16 in H17; apply Property_Value in H18; auto.
            add ([x,F[x]] ∈ f) H18; unfold Function in H13.
            apply H13 in H18; rewrite H18 in H17; auto. }
Qed.

Theorem Tukey_AC : forall X,
  Ensemble X -> exists ε, Choice_Function ε X.
Proof.
  intros.
  double H; apply Lemma_Fin_not_Em in H0.
  apply Tu.Tukey in H0; destruct H0 as [F H0]; exists F.
  assert ((En_f X) ≠ Φ).
  { apply Property_NotEmpty; exists Φ; unfold En_f; apply AxiomII; split.
    - assert (Φ ⊂ X); try apply Theorem26; apply Theorem33 in H1; auto.
    - exists Φ; split; try apply Theorem26; apply (Property_CF X); auto. }
  unfold MaxMember in H0; apply H0 in H1; clear H0.
  assert (Ensemble (En_f X)).
  { assert (En_f X ⊂ pow(pow(X) × (∪pow(X)))).
    { clear H1; unfold Included; intros; unfold En_f in H0.
      apply AxiomII in H0; destruct H0, H1 as [A H1]; destruct H1.
      assert (pow(X) ~ [Φ] ⊂ pow(X)).
      { unfold Setminus, Included; intros; apply Theorem4' in H3; apply H3. }
      add (pow(X)~[Φ] ⊂ pow( X)) H1; apply Theorem28 in H1.
      unfold Choice_Function' in H2; destruct H2, H4, H5, H6.
      unfold PowerSet at 1; apply AxiomII; split.
      - rewrite <- H5 in H2; apply Theorem75; auto.
      - unfold Included; intros; unfold Cartesian; double H8.
        apply H4 in H9; destruct H9 as [a [b H9]]; rewrite H9 in *.
        clear H9; apply AxiomII_P; repeat split; Ens.
        + apply Property_dom in H8; rewrite H5 in H8; apply H1; auto.
        + apply Property_ran in H8; unfold Included in H6; apply H6 in H8.
          apply Theorem31 in H1; destruct H1; apply H1; auto. }
    apply Theorem38 in H; auto; double H; apply AxiomVI in H2.
    add (Ensemble (∪ pow( X))) H; apply Theorem74 in H.
    apply Theorem38 in H; auto; apply Theorem33 in H0; auto. }
  destruct H1; double H1; unfold En_f in H3; apply AxiomII in H3.
  destruct H3, H4 as [D H4], H4; apply Property_ProperIncluded in H4; destruct H4.
  - double H4; apply Property_ProperIncluded' in H6; destruct H6 as [E H6], H6.
    double H6; unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
    clear H8; unfold Complement in H9; apply AxiomII in H9; destruct H9.
    unfold NotIn in H9; assert (E ∈ [Φ] <-> Ensemble E /\ (E=Φ)).
    { split; intros.
      - unfold Singleton in H10; apply AxiomII in H10; destruct H10.
        split; auto; apply H11; apply Theorem19.
        generalize (Theorem26 E); intros; apply Theorem33 in H12; auto.
      - destruct H10; unfold Singleton; apply AxiomII; split; auto. }
    apply Lemma_z in H10; auto; clear H9.
    apply not_and_or in H10; destruct H10; try contradiction.
    apply Property_NotEmpty in H9; destruct H9 as [e H9].
    cut ((F ∪ [[E,e]])∈ (En_f X) /\ F ⊊ (F ∪ [[E,e]])); intros.
    { destruct H10; apply H2 in H10; contradiction. }
    assert (Ensemble ([E,e])). { apply Theorem49; split; Ens. }
    unfold Choice_Function' in H5; destruct H5, H11, H12, H13.
    assert (F ⊊ (F ∪ [[E,e]])).
    { unfold ProperIncluded; split.
      - unfold Included; intros; apply Theorem4; left; auto.
      - intro; rewrite <- H12 in H7; assert ([E,e]∈F).
        { rewrite H15; apply Theorem4; right.
          unfold Singleton; apply AxiomII; split; auto. }
        apply Property_dom in H16; contradiction. }
    split; auto; unfold En_f; apply AxiomII; split.
    + apply AxiomIV; split; auto; apply Theorem42; auto.
    + { exists (D ∪ [E]); split.
        - unfold Included; intros; apply Theorem4 in H16; destruct H16.
          + unfold ProperIncluded in H4; destruct H4.
            unfold Included in H4; apply H4 in H16; auto.
          + unfold Singleton in H16; apply AxiomII in H16.
            destruct H8; destruct H16; rewrite H17; auto.
            apply Theorem19; Ens.
        - assert (Function (F ∪ [[E,e]])).
          { unfold Function; split.
            - unfold Function in H11; destruct H11.
              unfold Relation in H11; unfold Relation; intros.
              apply Theorem4 in H17; destruct H17.
              + apply H11 in H17; auto.
              + unfold Singleton in H17; apply AxiomII in H17.
                exists E, e; apply H17; apply Theorem19; auto.
            - intros; destruct H16; apply Theorem4 in H16.
              apply Theorem4 in H17; destruct H16, H17.
              + unfold Function in H11; apply H11 with (x:=x); auto.
              + apply Property_dom in H16; rewrite H12 in H16.
                double H10; unfold Singleton in H17; apply AxiomII in H17.
                destruct H17; apply Theorem19 in H18; apply H19 in H18.
                apply Theorem49 in H10; apply (Theorem55 _ _ x z) in H10.
                symmetry in H18; apply H10 in H18; destruct H18.
                rewrite H18 in H7; contradiction.
              + apply Property_dom in H17; rewrite H12 in H17.
                double H10; unfold Singleton in H16; apply AxiomII in H16.
                destruct H16; apply Theorem19 in H18; apply H19 in H18.
                apply Theorem49 in H10; apply (Theorem55 _ _ x y) in H10.
                symmetry in H18; apply H10 in H18; destruct H18.
                rewrite H18 in H7; contradiction.
              + unfold Singleton in H16, H17.
                apply AxiomII in H16; apply AxiomII in H17.
                destruct H16, H17; double H10; apply Theorem19 in H20.
                double H20; apply H18 in H20; apply H19 in H21; double H10.
                apply Theorem49 in H10; apply (Theorem55 _ _ x y) in H10.
                apply Theorem49 in H22; apply (Theorem55 _ _ x z) in H22.
                symmetry in H20, H21; apply H10 in H20; apply H22 in H21.
                destruct H20, H21; rewrite <- H23, <- H24; auto. }
          assert (dom((F ∪ [[E,e]])) = D ∪ [E]).
          { apply AxiomI; split; intros.
            - unfold Domain in H17; apply AxiomII in H17.
              destruct H17, H18; apply Theorem4 in H18; destruct H18.
              + apply Property_dom in H18; rewrite H12 in H18.
                apply Theorem4; tauto.
              + unfold Singleton in H18; apply AxiomII in H18; double H10.
                destruct H18; apply Theorem19 in H10; apply H20 in H10.
                apply Theorem49 in H19; apply (Theorem55 _ _ z x) in H19.
                symmetry in H10; apply H19 in H10; destruct H10.
                apply Theorem4; right; unfold Singleton.
                apply AxiomII; split; auto.
            - unfold Domain; apply AxiomII; split; Ens.
              apply Theorem4 in H17; destruct H17.
              + exists F[z]; apply Theorem4; left.
                rewrite <- H12 in H17; apply Property_Value in H17; auto.
              + exists e; apply Theorem4; right; unfold Singleton in H17.
                apply AxiomII in H17; destruct H17.
                rewrite H18; try (apply Theorem19; Ens).
                unfold Singleton; apply AxiomII; split; auto. }
          unfold Choice_Function'; repeat split; try apply H16; auto.
          + apply AxiomIV; split; try apply Theorem42; Ens.
          + unfold Included; intros.
            unfold Range in H18; apply AxiomII in H18; destruct H18, H19.
            apply Theorem4 in H19; destruct H19.
            * unfold Element_U; apply AxiomII; split; auto.
              apply Property_ran in H19.
              unfold Included in H13; apply H13 in H19.
              unfold Element_U in H19; apply AxiomII in H19.
              destruct H19, H20, H20; exists x0; split; auto.
              apply Theorem4; tauto.
            * unfold Singleton in H10; apply AxiomII in H19.
              double H10; apply Theorem19 in H20; destruct H19.
              apply H21 in H20; apply Theorem49 in H10.
              apply (Theorem55 _ _ x z) in H10; symmetry in H20.
              apply H10 in H20; destruct H20; unfold Element_U.
              apply AxiomII; split; auto; exists E; rewrite <- H22.
              split; auto; apply Theorem4; right.
              unfold Singleton; apply AxiomII; split; Ens.
          + intros; unfold ProperIncluded in H15; destruct H15.
            add (Function (F ∪ [[E, e]]) /\ F ⊂ (F ∪ [[E, e]])) H11.
            apply Included_Function in H11; destruct H11.
            rewrite H17 in H18; apply Theorem4 in H18; destruct H18.
            * rewrite <- H12 in H18; double H18; apply H14 in H18.
              apply H20 in H21; rewrite <- H21; auto.
            * unfold Singleton in H18; apply AxiomII in H18; destruct H18.
              assert (Ensemble E); Ens.
              apply Theorem19 in H22; apply H21 in H22.
              assert (E ∈ dom(F ∪ [[E, e]])).
              { rewrite H17; apply Theorem4; right.
                unfold Singleton; apply AxiomII; auto. }
              apply Property_Value in H23; auto.
              assert ([E,e] ∈ (F ∪ [[E, e]])).
              { apply Theorem4; right.
                unfold Singleton; apply AxiomII; auto. }
              pattern E at 3 in H23; rewrite <- H22 in H23.
              add ([E, e] ∈ (F ∪ [[E, e]])) H23; unfold Function in H16.
              apply H16 in H23; rewrite H23; rewrite H22; auto. }
  - rewrite H4 in H5.
    unfold Choice_Function' in H5; unfold Choice_Function.
    destruct H5, H6, H7, H8; repeat split; try apply H6; auto.
    unfold Included; intros; unfold Included in H8.
    apply H8 in H10; unfold Element_U in H10.
    apply AxiomII in H10; destruct H10, H11, H11.
    unfold Setminus in H12; apply Theorem4' in H12.
    destruct H12; unfold PowerSet in H12.
    apply AxiomII in H12; destruct H12.
    unfold Included in H14; apply H14 in H11; auto.
Qed.


End Tukey_Proof_AC.
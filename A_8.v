(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*      Copyright 2018-2019: Tianyu Sun, Yaoshun Fu and Wensheng Yu.       *)
(***************************************************************************)


Require Export A_7.

(* A.8 序数 *)

Module A8.

(* 正则公理 VII *)

Axiom AxiomVII : forall x, x ≠ Φ -> exists y, y ∈ x /\ x ∩ y = Φ.



(* 定理 101 *)

Theorem Theorem101 : forall x, x ∉ x.
Proof.
  intros; intro.
  assert ([x] ≠ Φ).
  { apply Property_NotEmpty; exists x; apply AxiomII; split; Ens. }
  apply AxiomVII in H0; destruct H0, H0.
  assert (x0 = x).
  { apply AxiomII in H0; destruct H0; apply H2; apply Theorem19; Ens. }
  subst x0; assert (x ∈ ([x] ∩ x)). { apply AxiomII; repeat split; Ens. }
  rewrite H1 in H2; generalize (Theorem16 x); intro; contradiction.
Qed.


(* 定理102 *)

Theorem Theorem102 : forall x y, ~ (x ∈ y /\ y ∈ x).
Proof.
  intros; intro; destruct H.
  assert (\{ λ z, z = x \/ z =y \} ≠ Φ).
  { apply Property_NotEmpty; exists x; apply AxiomII; split; Ens. }
  apply AxiomVII in H1; destruct H1, H1; apply AxiomII in H1.
  destruct H1, H3; subst x0.
  + assert (y ∈ (\{ λ z, z = x \/ z = y \} ∩ x)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 y); intro; contradiction.
  + assert (x ∈ (\{ λ z, z = x \/ z = y \} ∩ y)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 x); intro; contradiction.
Qed.


(* 定义103 *)

Definition E : Class := \{\ λ x y, x ∈ y \}\.


(* 定理104 *)

Lemma Lemma104 : forall a b c, a ∈ b -> b ∈ c -> c ∈ a -> False.
Proof.
  intros.
  assert (\{ λ x, x = a \/ x =b \/ x = c \} ≠ Φ).
  { apply Property_NotEmpty; exists a; apply AxiomII; split; Ens. }
  apply AxiomVII in H2; destruct H2, H2; apply AxiomII in H2; destruct H2.
  destruct H4 as [H4 | [H4 | H4]]; subst x.
  + assert (c ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ a)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
    rewrite H3 in H4; generalize (Theorem16 c); intro; contradiction.
  + assert (a ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ b)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
    rewrite H3 in H4; generalize (Theorem16 a); intro; contradiction.
  + assert (b ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ c)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
    rewrite H3 in H4; generalize (Theorem16 b); intro; contradiction.
Qed.

Theorem Theorem104 : ~ Ensemble E.
Proof.
  intro; generalize (Theorem42 _ H); intro.
  assert (E ∈ [E]). { apply AxiomII; split; auto. }
  assert ([E, [E]] ∈ E).
  { apply AxiomII_P; split; auto; apply Theorem49; tauto. }
  assert ([E] ∈ [E, [E]]).
  { apply AxiomII; split; Ens; left; apply AxiomII; split; auto. }
  eapply Lemma104; eauto.
Qed.


(* 定义105 *)

Definition full x : Prop := forall m, m∈x -> m⊂x.

Corollary Property_Full : forall x, 
  full x <-> (forall u v : Class, v ∈ x /\ u ∈ v -> u ∈ x).
Proof.
  intros; split; intros.
  - unfold full in H; destruct H0; apply H in H0; auto.
  - unfold full; intros; unfold Included; intros; apply H with m; tauto.
Qed.


(* 定义106 *)

Definition Ordinal x : Prop := Connect E x /\ full x.


(* 定理107 *)


Theorem Theorem107 : forall x, 
  Ordinal x -> WellOrdered E x.
Proof.
  intros.
  unfold Ordinal in H; destruct H; unfold WellOrdered.
  intros; split; auto; intros; destruct H1.
  apply AxiomVII in H2; destruct H2, H2.
  exists x0; unfold FirstMember; intros.
  split; auto; intros; intro.
  unfold Rrelation in H5; apply AxiomII_P in H5; destruct H5.
  assert (y0 ∈ (y ∩ x0)). { apply AxiomII; split; Ens. }
  rewrite H3 in H7; generalize (Theorem16 y0); intro; contradiction.
Qed.


(* 定理108 *)

Theorem Theorem108 : forall x y, 
  Ordinal x -> y ⊂ x -> y≠x -> full y -> y ∈ x.
Proof.
  intros.
  assert (Section y E x).
  { apply Theorem107 in H; unfold Section; intros.
    split; auto; split; auto; intros; destruct H3, H4.
    unfold Rrelation in H5; apply AxiomII_P in H5; destruct H5.
    unfold full in H2; apply H2 in H4; auto. }
  generalize (Lemma_y _ _ H3 H1); intro.
  apply Theorem91 in H4; destruct H4, H4.
  assert (x0 = \{ λ u : Class,u ∈ x /\ Rrelation u E x0 \}).
  { apply AxiomI; split; intros; AssE z.
    - apply AxiomII; split; auto.
      unfold Ordinal in H; destruct H.
      double H4; unfold full in H8; apply H8 in H4.
      split; auto; apply AxiomII_P; split; auto.
      apply Theorem49; split; Ens.
    - apply AxiomII in H6; destruct H6, H8.
      unfold Rrelation in H9; apply AxiomII_P in H9; tauto. }
  rewrite <- H6 in H5; subst x0; auto.
Qed.


(* 定理109 *)

Lemma Lemma109 : forall x y,
  Ordinal x /\ Ordinal y -> full (x ∩ y).
Proof.
  intros; destruct H; unfold Ordinal in H, H0; destruct H, H0.
  unfold full in *; intros; apply AxiomII in H3; destruct H3, H4.
  apply H1 in H4; apply H2 in H5.
  unfold Included; intros; apply AxiomII; repeat split; Ens.
Qed.

Lemma Lemma109' : forall x y,
  Ordinal x /\ Ordinal y -> ((x ∩ y) = x) \/ ((x ∩ y) ∈ x).
Proof.
  intros.
  generalize (classic ((x ∩ y) = x)); intro; destruct H0; try tauto.
  assert ((x ∩ y) ⊂ x).
  { unfold Included; intros; apply Theorem4' in H1; tauto. }
  elim H; intros; apply Lemma109 in H.
  eapply Theorem108 in H2; eauto.
Qed.

Theorem Theorem109 : forall x y,
  Ordinal x /\ Ordinal y -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; elim H; intros; generalize (Lemma_y _ _ H1 H0); intro.
  apply Lemma109' in H; apply Lemma109' in H2; destruct H.
  - apply Theorem30 in H; tauto.
  - destruct H2.
    + apply Theorem30 in H2; tauto.
    + assert ((x ∩ y) ∈ (x ∩ y)).
      { rewrite Theorem6' in H2; apply AxiomII; repeat split; Ens. }
      apply Theorem101 in H3; elim H3.
Qed.


(* 定理110 *)

Theorem Theorem110 : forall x y,
  Ordinal x /\ Ordinal y -> x ∈ y \/ y ∈ x \/ x = y.
Proof.
  intros; generalize (classic (x = y)); intro; destruct H0; try tauto.
  elim H; intros; apply Theorem109 in H; destruct H.
  - left; unfold Ordinal in H1; destruct H1; eapply Theorem108; eauto.
  - right; left; unfold Ordinal in H2; destruct H2.
    eapply Theorem108; eauto; intro; auto.
Qed.


(* 定理111 *)

Theorem Theorem111 : forall x y, Ordinal x /\ y ∈ x -> Ordinal y.
Proof.
  intros; destruct H; double H; unfold Ordinal in H; destruct H.
  assert (Connect E y).
  { unfold Connect; intros; unfold Ordinal in H1; apply H1 in H0.
    unfold Connect in H; destruct H3; apply H; auto. }
  unfold Ordinal; split; auto.
  unfold full; intros; unfold Included; intros.
  apply Theorem107 in H1; unfold Ordinal in H1.
  assert (y ⊂ x); auto; assert (m ∈ x); auto.
  assert (m ⊂ x); auto; assert (z ∈ x); auto.
  apply Theorem88 in H1; destruct H1.
  unfold Transitive in H1; specialize H1 with z m y.
  assert (Rrelation z E y).
  { apply H1; repeat split; Ens.
    - unfold Rrelation; apply AxiomII_P; split; auto.
      apply Theorem49; split; Ens.
    - unfold Rrelation; apply AxiomII_P; split; auto.
      apply Theorem49; split; Ens. }
  unfold Rrelation in H11; apply AxiomII_P in H11; tauto.
Qed.


(* 定义112 *)

Definition R : Class := \{ λ x, Ordinal x \}.


(* 定理113 *)

Lemma Lemma113 :forall u v,
  Ensemble u -> Ensemble v -> Ordinal u /\ Ordinal v ->
  (Rrelation u E v \/ Rrelation v E u \/ u = v) .
Proof.
  intros; apply Theorem110 in H1; repeat split.
  destruct H1 as [H1 | [H1 | H1]].
  - left; unfold Rrelation; apply AxiomII_P; split; Ens.
    apply Theorem49; auto.
  - right; left; apply AxiomII_P; split; Ens.
    apply Theorem49; auto.
  - right; right; auto.
Qed.

Theorem Theorem113 : Ordinal R /\ ~ Ensemble R.
Proof.
  intros.
  assert (Ordinal R).
  { unfold Ordinal; intros; split.
    - unfold Connect; intros; destruct H.
      apply AxiomII in H; destruct H; apply AxiomII in H0; destruct H0.
      generalize (Lemma_y _ _ H1 H2); intro; apply Lemma113; auto.
    - unfold full; intros; apply AxiomII in H; destruct H.
      unfold Included; intros; apply AxiomII; split; Ens.
      eapply Theorem111; eauto. }
  split; auto; intro.
  assert (R ∈ R). { apply AxiomII; split; auto. }
  apply Theorem101 in H1; auto.
Qed.


(* 定理114 *)

Theorem Theorem114 : forall x, Section x E R -> Ordinal x.
Proof.
  intros.
  generalize (classic (x = R)); intro; destruct H0.
  - rewrite H0; apply Theorem113.
  - generalize (Lemma_y _ _ H H0); intro.
    apply Theorem91 in H1; destruct H1, H1.
    assert (x0 = \{ λ u, u ∈ R /\ Rrelation u E x0 \}).
    { apply AxiomI; split; intros.
      - apply AxiomII; repeat split; Ens.
        + apply AxiomII in H1; destruct H1.
          apply AxiomII; split; Ens; eapply Theorem111; eauto.
        + unfold Rrelation; apply AxiomII_P; split; auto.
          apply Theorem49; Ens.
      - apply AxiomII in H3; destruct H3, H4.
        unfold Rrelation in H5; apply AxiomII_P in H5; tauto. }
    subst x; rewrite H3 in H1; apply AxiomII in H1; tauto.
Qed.

Corollary Property114 : forall x, Ordinal x -> Section x E R.
Proof.
  intros; unfold Section; split.
  - unfold Included; intros; apply AxiomII; split; try Ens.
    eapply Theorem111; eauto.
  - split; intros; try apply Theorem107; try apply Theorem113.
    destruct H0, H1; unfold Ordinal in H2; apply AxiomII_P in H2.
    destruct H2; unfold Ordinal in H; destruct H; apply H4 in H1; auto.
Qed.



(* 定义115 *)

Definition Ordinal_Number x : Prop := x ∈ R.


(* 定义116 *)

Definition Less x y : Prop := x ∈ y.

Notation "x ≺ y" := (Less x y)(at level 67, left associativity).


(* 定义117 *)

Definition LessEqual x y := x ∈ y \/ x=y.

Notation "x ≼ y" := (LessEqual x y)(at level 67, left associativity).


(* 定理118 *)

Theorem Theorem118 : forall x y,
  Ordinal x /\ Ordinal y -> (x ⊂ y <-> x ≼ y).
Proof.
  intros; destruct H; split; intros.
  - unfold LessEqual.
    generalize (classic (x = y)); intro; destruct H2; try tauto.
    unfold Ordinal in H; destruct H.
    left; apply Theorem108; auto.
  - unfold LessEqual in H1; destruct H1.
    + unfold Ordinal in H0; destruct H0; auto.
    + rewrite H1; auto; unfold Included; intros; auto.
Qed.


(* 定理119 *)

Theorem Theorem119 : forall x,
  Ordinal x -> x = \{ λ y, (y ∈ R /\ Less y x) \}.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII; repeat split; Ens.
    apply AxiomII; split; Ens; eapply Theorem111; eauto.
  - apply AxiomII in H0; destruct H0, H1; auto.
Qed.


(* 定理120 *)

Theorem Theorem120 : forall x, 
  x ⊂ R -> Ordinal (∪ x).
Proof.
  intros; red; split.
  - unfold Connect; intros; destruct H0; apply AxiomII in H0.
    apply AxiomII in H1; destruct H0, H2, H2, H1, H4, H4.
    apply H in H3; apply H in H5; apply AxiomII in H3.
    destruct H3; apply AxiomII in H5; destruct H5.
    assert (Ordinal u). { eapply Theorem111; eauto. }
    assert (Ordinal v). { eapply Theorem111; eauto. }
    generalize (Lemma_y _ _ H8 H9); intro; apply Lemma113; auto.
  - apply Property_Full; intros; destruct H0.
    apply AxiomII in H0; destruct H0, H2, H2.
    apply AxiomII; split; Ens; exists x0; split; auto.
    apply H in H3; apply AxiomII in H3; destruct H3 as [_ H3].
    unfold Ordinal in H3; destruct H3; apply H4 in H2; auto.
Qed.


(* 定理121 *)

Lemma Lemma121 : forall x, x ⊂ R /\ x ≠ Φ -> FirstMember (∩ x) E x.
Proof.
  intros; destruct H.
  generalize (Theorem113); intro; destruct H1.
  apply Theorem107 in H1; unfold WellOrdered in H1; destruct H1.
  generalize (Lemma_y _ _ H H0); intro; apply H3 in H4; destruct H4.
  double H4; unfold FirstMember in H4; destruct H4.
  assert ((∩ x) = x0).
  { apply AxiomI; split; intros.
    - apply AxiomII in H7; destruct H7; apply H8; auto.
    - apply AxiomII; split; Ens; intros.
      assert (~ Rrelation y E x0); auto.
      assert (Ordinal x0). { apply H in H4; apply AxiomII in H4; tauto. }
      assert (Ordinal y). { apply H in H8; apply AxiomII in H8; tauto. }
      generalize (Lemma_y _ _ H10 H11); intro; apply Theorem110 in H12.
      destruct H12 as [H12 | [H12 | H12]].
      + apply H in H8; apply AxiomII in H8; destruct H8 as [_ H8].
        unfold Ordinal in H8; destruct H8; generalize (Property_Full y); intro.
        destruct H14; eapply H14; eauto.
      + elim H9; unfold Rrelation; apply AxiomII_P; split; auto.
        apply Theorem49; Ens.
      + subst x0; auto. }
  rewrite H7 ; auto.
Qed.

Theorem Theorem121 : forall x, x ⊂ R /\ x ≠ Φ -> (∩ x) ∈ x.
Proof.
  intros; apply Lemma121 in H.
  unfold FirstMember in H; tauto.
Qed.


(* 定义122 *)

Definition PlusOne x := x ∪ [x].


(* 定理123 *)

Lemma Lemma123 : forall x, x ∈ R -> (PlusOne x) ∈ R.
Proof.
  intros; apply AxiomII; split.
  - apply AxiomIV; split; Ens; apply Theorem42; Ens.
  - unfold Connect; split.
    + unfold Connect; intros; destruct H0.
      apply AxiomII in H0; apply AxiomII in H1; destruct H0, H1, H2, H3.
      * apply AxiomII in H; destruct H as [_ H].
        assert (Ordinal u). { eapply Theorem111; eauto. }
        assert (Ordinal v). { eapply Theorem111; eauto. }
        generalize (Lemma_y _ _ H4 H5); intro; apply Lemma113; auto.
      * apply AxiomII in H3; destruct H3.
        AssE x; apply Theorem19 in H5; apply H4 in H5; subst v.
        left; unfold Rrelation; apply AxiomII_P; split; auto.
        apply Theorem49; tauto.
      * apply AxiomII in H2; destruct H2.
        AssE x; apply Theorem19 in H5; apply H4 in H5; subst u.
        right; left; unfold Included; apply AxiomII_P; split; auto.
        apply Theorem49; tauto.
      * AssE x; apply Theorem19 in H4; double H4.
        apply AxiomII in H2; destruct H2; apply H6 in H4.
        apply AxiomII in H3; destruct H3; apply H7 in H5.
        subst u; subst v; tauto.
    + unfold full; intros; unfold Included; intros.
      apply AxiomII in H; apply AxiomII in H0; destruct H, H0.
      apply AxiomII; split; Ens; destruct H3.
      * unfold Ordinal in H2; destruct H2.
        unfold full in H4; left; eapply H4; eauto.
      * apply AxiomII in H3; destruct H3.
        apply Theorem19 in H; apply H4 in H; subst m; tauto.
Qed.

Theorem Theorem123 : forall x,
  x ∈ R -> FirstMember (PlusOne x) E (\{ λ y, (y ∈ R /\ Less x y) \}).
Proof.
  intros; unfold FirstMember; split; intros.
  - apply AxiomII; repeat split.
    + unfold Ensemble; exists R; apply Lemma123; auto.
    + apply Lemma123; auto.
    + unfold Less; intros; apply AxiomII; split; Ens.
      right; apply AxiomII; split; Ens.
  - intro; apply AxiomII in H0; destruct H0, H2.
    unfold Rrelation in H1; apply AxiomII_P in H1; destruct H1.
    apply AxiomII in H4; destruct H4; unfold Less in H3; destruct H5.
    + eapply Theorem102; eauto.
    + AssE x; apply Theorem19 in H6; apply AxiomII in H5; destruct H5.
      apply H7 in H6; subst y; eapply Theorem101; eauto.
Qed.


(* 定理124 *)

Theorem Theorem124 : forall x, 
  x ∈ R -> ∪ PlusOne x = x.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H0; destruct H0, H1, H1.
    apply AxiomII in H2; destruct H2, H3.
    + apply AxiomII in H; destruct H, H4.
      generalize (Property_Full x); intro; destruct H6.
      apply H6 with (u:=z) (v:=x0) in H5; tauto.
    + apply AxiomII in H3; destruct H3.
      rewrite <- H4; auto; try (apply Theorem19; Ens).
  - apply AxiomII; split; Ens; exists x; split; auto.
    apply AxiomII; split; Ens; right; apply AxiomII; Ens.
Qed.


(* 定义125 *)

Definition Restriction f x : Class := f ∩ (x × μ).

Notation "f | ( x )" := (Restriction f x)(at level 30).


(* 定理126 *)

Theorem Theorem126 : forall f x,
  Function f -> Function (f|(x)) /\ dom(f|(x)) = x ∩ dom( f) /\
  (forall y, y ∈ dom(f|(x)) -> (f|(x)) [y] = f [y]).
Proof.
  intros; repeat split; intros.
  - unfold Relation; intros; apply AxiomII in H0; destruct H0, H1.
    PP H2 a b; eauto.
  - destruct H0; apply AxiomII in H0; destruct H0 as [_ [H0 _]].
    apply AxiomII in H1; destruct H1 as [_ [H1 _]].
    unfold Function in H; eapply H; eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H0; destruct H0, H1.
      apply AxiomII in H1; destruct H1, H2.
      apply Property_dom in H2; apply AxiomII_P in H3.
      apply AxiomII; split; tauto.
    + apply AxiomII in H0; destruct H0, H1; apply AxiomII; split; auto.
      apply Property_Value in H2; auto.
      exists f[z]; apply AxiomII; repeat split; Ens.
      apply AxiomII_P; repeat split; Ens; apply Theorem19.
      apply Property_ran in H2; Ens.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1.
      apply AxiomII in H0; destruct H0, H3.
      apply AxiomII in H3; destruct H3, H4.
      apply Property_dom in H4; apply H2.
      assert (Ensemble f[y]). { apply Theorem19; apply Theorem69; auto. }
      apply AxiomII; split; Ens; apply AxiomII; repeat split.
      * apply Theorem49; auto.
      * apply Property_Value in H4; auto.
      * apply AxiomII_P in H5; apply Theorem19 in H6.
        apply AxiomII_P; repeat split; try tauto; try apply Theorem49; Ens.
    + apply AxiomII in H1; destruct H1; apply AxiomII; split; auto; intros.
      apply AxiomII in H3; destruct H3; apply AxiomII in H4.
      apply H2; apply AxiomII; split; tauto.
Qed.


(* 定理127 *)

Theorem Lemma127 : forall f h,
  dom( f) ⊂ dom( h) -> Function f -> Function h ->
  \{ λ a,a ∈ (dom( f) ∩ dom( h)) /\ f [a] ≠ h [a] \} = Φ -> f ⊂ h.
Proof.
  intros.
  unfold Included; intros; rewrite Theorem70 in H3; auto; PP H3 a b.
  double H4; rewrite <- Theorem70 in H4; auto; apply Property_dom in H4.
  apply AxiomII_P in H5; destruct H5.
  rewrite Theorem70; auto; apply AxiomII_P; split; auto; rewrite H6.
  generalize (classic (f[a] = h[a])); intro; destruct H7; auto.
  assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
  { apply Theorem30 in H; rewrite H; apply AxiomII; split; Ens. }
  rewrite H2 in H8; generalize (Theorem16 a); contradiction.
Qed.

Theorem Theorem127 : forall f h g,
  Function f -> Ordinal dom(f) ->
  (forall u0, u0 ∈ dom(f) -> f[u0] = g[f|(u0)]) ->
  Function h -> Ordinal dom(h) ->
  (forall u1, u1 ∈ dom(h) -> h[u1] = g [h|(u1)]) -> h ⊂ f \/ f ⊂ h.
Proof.
  intros.
  generalize (Lemma_y _ _ H0 H3); intro; apply Theorem109 in H5.
  generalize (classic (\{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \} = Φ));
  intro; destruct H6.
  - destruct H5.
    + right; apply Lemma127; auto.
    + left; rewrite Lemma97'' in H6; apply Lemma127; auto.
  - assert (exists u, FirstMember u E \{λ a, a∈(dom(f)∩dom(h))/\f[a]≠h[a]\}).
    { apply Theorem107 in H0; unfold WellOrdered in H0; apply H0; split; auto.
      unfold Included; intros; apply AxiomII in H7; destruct H7, H8.
      apply AxiomII in H8; tauto. }
    destruct H7 as [u H7]; unfold FirstMember in H7; destruct H7.
    apply AxiomII in H7; destruct H7, H9.
    apply AxiomII in H9; destruct H9 as [_[H9 H11]].
    generalize (H1 _ H9); generalize (H4 _ H11); intros.
    assert ((h | (u)) = (f | (u))).
    { apply AxiomI; intros; split; intros.
      - apply AxiomII in H14; destruct H14, H15.
        apply AxiomII; repeat split; auto; PP H16 a b.
        apply AxiomII_P in H17; destruct H17 ,H18.
        generalize H15 as H22; intro; apply Property_dom in H22.
        rewrite Theorem70 in H15; auto; rewrite Theorem70; auto.
        apply AxiomII_P in H15; destruct H15; apply AxiomII_P; split; auto.
        rewrite H20; symmetry.
        generalize (classic (f [a] = h [a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply AxiomII; repeat split; Ens; apply AxiomII; repeat split; Ens.
          unfold Ordinal in H0; destruct H0; apply H23 in H9; auto. }
        apply H8 in H23; elim H23; unfold Rrelation, E.
        apply AxiomII_P; split; auto; apply Theorem49; split; Ens.
      - apply AxiomII in H14; destruct H14, H15.
        apply AxiomII; repeat split; auto; PP H16 a b.
        apply AxiomII_P in H17; destruct H17 ,H18.
        generalize H15 as H22; intro; apply Property_dom in H22.
        rewrite Theorem70 in H15; auto; rewrite Theorem70; auto.
        apply AxiomII_P in H15; destruct H15; apply AxiomII_P; split; auto.
        rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply AxiomII; repeat split; Ens; apply AxiomII; repeat split; Ens.
          unfold Ordinal in H3; destruct H3; apply H23 in H11; auto. }
        apply H8 in H23; elim H23; unfold Rrelation, E.
        apply AxiomII_P; split; auto; apply Theorem49; split; Ens. }
  rewrite <- H14 in H13; rewrite <- H12 in H13; contradiction.
Qed.


(* 定理128 *)

Definition En_f' g := \{\ λ u v, u ∈ R /\ (exists h, Function h /\
  Ordinal dom(h) /\ (forall z, z ∈ dom(h) -> h[z] = g [h | (z)] ) /\
  [u,v] ∈ h ) \}\.

Lemma Lemma128 : forall u v w,
  Ordinal u -> v ∈ u -> w ∈ v -> w ∈ u.
Proof.
  intros; unfold Ordinal in H; destruct H.
  unfold full in H2; eapply H2; eauto.
Qed.

Lemma Lemma128' : forall f x,
  Function f -> Ordinal dom(f) -> Ordinal_Number x ->
  ~ x ∈ dom(f) -> f | (x) = f .
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H3; tauto.
  - apply AxiomII; split; Ens; split; auto.
    unfold Function, Relation in H; destruct H as [H _].
    double H3; apply H in H4; destruct H4 as [a [b H4]]; rewrite H4 in *.
    clear H H4; apply AxiomII_P; split; Ens; split.
    + unfold Ordinal in H1; apply AxiomII in H1; destruct H1.
      assert (Ordinal dom(f) /\ Ordinal x); auto.
      apply Theorem110 in H4; apply Property_dom in H3; auto.
      destruct H4 as [H4 | [H4 | H4]]; try contradiction.
      * eapply Lemma128; eauto.
      * rewrite H4 in H3; auto.
    + apply Property_ran in H3; apply Theorem19; Ens.
Qed.

Theorem Theorem128 :  forall g,
  exists f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]).
Proof.
  intros; exists (En_f' g).
  assert (Function (En_f' g)).
  { unfold Function; intros; split; intros.
    - unfold Relation; intros; PP H a b; eauto.
    - destruct H; apply AxiomII_P in H; apply AxiomII_P in H0.
      destruct H, H1, H2, H2, H3, H4, H0, H6, H7, H7, H8, H9.
      generalize (Theorem127 _ _ _ H2 H3 H4 H7 H8 H9); intro; destruct H11.
      + apply H11 in H10; eapply H2; eauto.
      + apply H11 in H5; eapply H7; eauto. }
  split; auto.
  - assert (Ordinal dom(En_f' g)).
    { apply Theorem114; unfold Section; intros; split.
      - unfold Included; intros; apply AxiomII in H0.
        destruct H0, H1; apply AxiomII_P in H1; tauto.
      - split; intros.
        + apply Theorem107; apply Theorem113.
        + destruct H0, H1; apply AxiomII in H1; destruct H1, H3.
          apply AxiomII_P in H3; destruct H3, H4, H5, H5, H6, H7.
          apply AxiomII_P in H2; destruct H2.
          apply Theorem49 in H2; destruct H2.
          apply AxiomII; split; auto; apply Property_dom in H8.
          assert (u ∈ dom( x0)). { eapply Lemma128; eauto. }
          exists (x0[u]); apply AxiomII_P.
          split; try apply Theorem49; split; auto.
          * apply Theorem19; apply Theorem69; auto.
          * exists x0; split; auto; split; auto; split; auto.
            apply Property_Value; auto. }
    split; intros; auto.
    generalize (classic (x ∈ dom(En_f' g))); intro; destruct H2.
    + apply AxiomII in H2; destruct H2, H3; apply AxiomII_P in H3.
      destruct H2, H3, H4, H5 as [h [H5 [H6 [H7 H8]]]].
      assert (h ⊂ En_f' g).
      { double H5; unfold Included; intros; unfold Function, Relation in H9.
        destruct H9 as [H9 _]; double H10; apply H9 in H11.
        destruct H11 as [a [b H11]]; rewrite H11 in *; clear H9 H11 z.
        apply AxiomII_P; split; try Ens; double H10; apply Property_dom in H9.
        split; try apply AxiomII; Ens; split; Ens.
        eapply Theorem111; eauto. }
      double H8; apply H9 in H10; double H8.
      apply Property_dom in H11; apply H7 in H11.
      double H8; apply Property_dom in H12; apply Property_dom in H8.
      apply Property_Value in H8; auto; apply Property_dom in H10.
      apply Property_Value in H10; auto; apply H9 in H8.
      assert (h [x] = (En_f' g) [x]). { eapply H; eauto. }
      rewrite <- H13; clear H13.
      assert (h | (x) = En_f' g | (x)).
      { apply AxiomI; split; intros; apply AxiomII in H13; destruct H13, H14.
       - apply AxiomII; repeat split; auto.
       - apply AxiomII; repeat split; auto; rewrite Theorem70; auto.
         PP H15 a b; apply AxiomII_P in H16; apply AxiomII_P; split; auto.
         destruct H16, H17; assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
         apply Property_Value in H19; auto; apply H9 in H19; eapply H; eauto. }
      rewrite <- H13; auto.
    + generalize H2; intro; apply Theorem69 in H2; auto.
      rewrite (Lemma128' _ _ H H0 H1 H3).
      generalize (classic (En_f' g ∈ dom(g))); intro; destruct H4.
      * generalize Theorem113; intro; destruct H5 as [H5 _].
        apply Theorem107 in H5; unfold WellOrdered in H5; destruct H5.
        assert ((R ~ dom(En_f' g)) ⊂ R /\ (R ~ dom(En_f' g)) ≠ Φ).
        { split; try (red; intros; apply AxiomII in H7; tauto).
          intro; generalize (Property114 _ H0); intro.
          unfold Section in H8; destruct H8.
          apply Property_Φ in H8; apply H8 in H7.
          rewrite <- H7 in H3; contradiction. }
        apply H6 in H7; destruct H7 as [y H7].
        assert (((En_f' g) ∪ [[y,g[En_f' g]]]) ⊂ (En_f' g)).
        { unfold Included; intros; apply AxiomII in H8; destruct H8, H9; auto.
          assert (Ensemble ([y, g [En_f' g]])).
          { destruct H7; AssE y; apply Theorem69 in H4.
            apply Theorem19 in H4; apply Theorem49; tauto. }
          apply AxiomII in H9; destruct H9.
          rewrite H11; try apply Theorem19; auto.
          apply AxiomII_P; split; auto; split.
          - unfold FirstMember in H7; destruct H7; apply AxiomII in H7; tauto.
          - exists ((En_f' g) ∪ [[y,g[En_f' g]]]).
            assert (Function (En_f' g ∪ [[y, g [En_f' g]]])).
            { unfold Function; split; intros.
              - unfold Relation; intros; apply AxiomII in H12.
                destruct H12, H13; try PP H13 a b; eauto.
                apply AxiomII in H13; destruct H13; apply Theorem19 in H10.
                apply H14 in H10; eauto.
              - destruct H12; apply AxiomII in H12; destruct H12 as [_ H12].
                apply AxiomII in H13; destruct H13 as [_ H13].
                unfold FirstMember in H7; destruct H7.
                apply AxiomII in H7; destruct H7 as [_ [_ H7]].
                apply AxiomII in H7; destruct H7, H12, H13.
                + eapply H; eauto.
                + apply AxiomII in H13; destruct H13; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10;
                  destruct H10; try apply Theorem49; auto; rewrite H10 in H12.
                  apply Property_dom in H12; contradiction.
                + apply AxiomII in H12; destruct H12; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; rewrite H10 in H13.
                  apply Property_dom in H13; contradiction.
                + double H12; apply AxiomII in H12; apply AxiomII in H13.
                  destruct H12, H13; double H10.
                  apply Theorem19 in H10; apply H17 in H10.
                  apply Theorem19 in H19; apply H18 in H19.
                  apply Theorem55 in H10; destruct H10;
                  apply Theorem49 in H12; auto.
                  apply Theorem55 in H19; destruct H19;
                  apply Theorem49 in H13; auto.
                  rewrite H20, H21; auto. }
            split; auto; split.
            + apply Theorem114; unfold Section; intros; split.
              * unfold Included; intros.
                apply AxiomII in H13; destruct H13, H14.
                apply AxiomII in H14; destruct H14, H15.
                -- apply Property_dom in H15; apply AxiomII.
                   split; Ens; eapply Theorem111; eauto.
                -- apply AxiomII in H15; destruct H15; apply Theorem19 in H10.
                   apply H16 in H10; apply Theorem55 in H10; destruct H10;
                   try apply Theorem49; auto; destruct H7.
                   apply AxiomII in H7; rewrite H10; tauto.
              * split; try (apply Theorem107; apply Theorem113); intros.
                destruct H13, H14; apply AxiomII in H14; destruct H14, H16.
                apply AxiomII in H16; destruct H16, H17.
                -- apply AxiomII; split; Ens.
                   assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                   { apply Property_Value; auto; apply Property_dom in H17.
                     unfold Rrelation in H15; apply AxiomII_P in H15.
                     destruct H15; eapply Lemma128; eauto. }
                   exists ((En_f' g) [u]); apply AxiomII; split; Ens.
                -- assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                   { apply Property_Value; auto.
                     apply AxiomII in H17; destruct H17.
                     apply Theorem19 in H10; apply H18 in H10.
                     apply Theorem55 in H10;
                     destruct H10; try apply Theorem49; auto.
                     subst v; unfold FirstMember in H7; destruct H7.
                     generalize (classic (u ∈ dom( En_f' g))); intro.
                     destruct H20; auto.
                     absurd (Rrelation u E y); auto; try apply H10.
                     apply AxiomII; repeat split; Ens.
                     apply AxiomII; split; Ens. }
                   apply AxiomII; split; Ens; exists ((En_f' g) [u]).
                   apply AxiomII; split; Ens.
            + split; intros.
              * apply Property_Value in H13; auto.
                apply AxiomII in H13; destruct H13, H14.
                -- apply AxiomII_P in H14; destruct H14, H15.
                   destruct H16 as [h [H16 [H17 [H18 H19]]]].
                   double H19; apply Property_dom in H20.
                   rewrite Theorem70 in H19; auto.
                   apply AxiomII_P in H19; destruct H19.
                   assert (h ⊂ En_f' g).
                   { unfold Included; intros; double H16.
                     unfold Function, Relation in H23; destruct H23 as [H23 _].
                     double H22; apply H23 in H24; destruct H24 as [a [b H24]].
                     rewrite H24 in *; clear H23 H24; apply AxiomII_P.
                     split; try Ens; double H22; apply Property_dom in H23.
                     split; try apply AxiomII; Ens.
                     split; try Ens; eapply Theorem111; eauto. }
                   assert ((En_f' g ∪ [[y, g[En_f' g]]])|(z0) = En_f' g|(z0)).
                   { unfold Restriction; rewrite Theorem6'; rewrite Theorem8.
                     assert ((z0) × μ ∩ [[y, g [En_f' g]]] = Φ).
                     { apply AxiomI; split; intros.
                       - apply AxiomII in H23; destruct H23, H24; auto.
                         PP H24 a b; apply AxiomII_P in H26; destruct H26, H27.
                         apply AxiomII in H25; destruct H25.
                         apply Theorem19 in H10; apply H29 in H10.
                         apply Theorem55 in H10; apply Theorem49 in H25; auto.
                         destruct H10; rewrite H10 in H27.
                         assert (y ∈ dom( h)).   { eapply Lemma128; eauto. }
                         apply Property_Value in H31; auto.
                         apply H22 in H31; apply Property_dom in H31.
                         unfold FirstMember in H7; destruct H7.
                         apply AxiomII in H7; destruct H7, H33.
                         apply AxiomII in H34; destruct H34; contradiction.
                       - generalize (Theorem16 z1); contradiction. }
                     rewrite H23, Theorem6, Theorem17; apply Theorem6'. }
                   rewrite H21, H23.
                   assert (h | (z0) = En_f' g | (z0)).
                   { apply AxiomI; split; intros.
                     - apply AxiomII in H24; destruct H24, H25.
                       apply AxiomII; repeat split; auto.
                     - apply AxiomII in H24; destruct H24, H25; apply AxiomII.
                       repeat split; auto; rewrite Theorem70; auto.
                       PP H26 a b; apply AxiomII_P in H27; apply AxiomII_P.
                       split; auto; destruct H27 as [_ [H27 _]].
                       assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
                       apply Property_Value in H28; auto; apply H22 in H28.
                       eapply H; eauto. }
                   rewrite <- H24; auto.
                -- apply AxiomII in H14; destruct H14.
                   double H10; apply Theorem19 in H10; apply H15 in H10.
                   apply Theorem55 in H10; apply Theorem49 in H13; auto.
                   destruct H10; subst z0; rewrite H17.
                   assert ((En_f' g ∪ [[y, g [En_f' g]]])|(y) = En_f' g|(y)).
                   { apply AxiomI; split; intros.
                     - apply AxiomII in H10; destruct H10, H18.
                       apply AxiomII in H18; destruct H18, H20.
                       + apply AxiomII; tauto.
                       + PP H19 a b; apply AxiomII_P in H21; destruct H21, H22.
                         apply AxiomII in H20; destruct H20.
                         apply Theorem19 in H16; apply H24 in H16.
                         apply Theorem55 in H16; apply Theorem49 in H21; auto.
                         destruct H16; rewrite H16 in H22.
                         generalize (Theorem101 y); intro; contradiction.
                     - unfold Restriction; rewrite Theorem6', Theorem8.
                      apply AxiomII; split; Ens; left; rewrite Theorem6'; Ens. }
                   rewrite H10; unfold FirstMember in H7; destruct H7.
                   apply AxiomII in H7; destruct H7, H19.
                   apply AxiomII in H20; destruct H20; rewrite Lemma128'; auto.
              * apply AxiomII; split; Ens; right; apply AxiomII; split; Ens. }
        unfold FirstMember in H7; destruct H7.
        assert (y ∈ dom(En_f' g ∪ [[y, g [En_f' g]]])).
        { apply AxiomII; split; Ens; exists g [En_f' g].
          assert (Ensemble ([y, g [En_f' g]])).
          { apply Theorem49; split; Ens.
            apply Theorem69 in H4; apply Theorem19; auto. }
          apply AxiomII; split; Ens; right; apply AxiomII; auto. }
        apply AxiomII in H7; destruct H7, H11; apply AxiomII in H12.
        destruct H12; elim H13; apply AxiomII in H10; destruct H10, H14.
        apply H8 in H14; apply Property_dom in H14; auto.
      * apply Theorem69 in H4; rewrite H2, H4; auto.
Qed.

Lemma Lemma128'' : forall f h,
  Function f -> Function h -> h ⊂ f -> f | (dom(h)) = h.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H2; destruct H2, H3.
    PP H4 a b; apply AxiomII_P in H5; destruct H5, H6; double H3.
    rewrite Theorem70; rewrite Theorem70 in H3; auto.
    apply AxiomII_P in H3; destruct H3.
    apply AxiomII_P; split; Ens; rewrite H9 in *.
    apply Property_Value in H6; auto.
    apply H1 in H6; eapply H; eauto.
  - apply AxiomII; repeat split; Ens.
    rewrite Theorem70 in H2; auto.
    PP H2 a b; rewrite <- Theorem70 in H3; auto.
    apply AxiomII_P; repeat split; Ens.
    + apply Property_dom in H3; auto.
    + AssE [a,b]; apply Theorem49 in H4.
      apply Theorem19; tauto.
Qed.

Lemma Lemma128''' : forall h, Function h -> h | (dom(h)) = h.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H0; tauto.
  - apply AxiomII; repeat split; Ens.
    rewrite Theorem70 in H0; auto.
    PP H0 a b; rewrite <- Theorem70 in H1; auto.
    apply AxiomII_P; repeat split; Ens.
    + apply Property_dom in H1; auto.
    + AssE [a,b]; apply Theorem49 in H2.
      apply Theorem19; tauto.
Qed.

Lemma Lemma128'''' : forall f g h,
  Function f -> Function h -> Ordinal dom(f) ->
  Ordinal dom( h)-> (forall x, Ordinal_Number x -> f [x] = g [f | (x)]) ->
  (forall x, Ordinal_Number x -> h [x] = g [h | (x)]) -> h ⊂ f -> h = f.
Proof.
  intros.
  generalize (Theorem110 _ _ (Lemma_y _ _ H1 H2)); intro.
  destruct H6 as [H8 | [H6 | H6]].
  - apply Property_Value in H8; auto.
    apply H5 in H8; apply Property_dom in H8.
    apply Theorem101 in H8; elim H8.
  - assert (Ordinal_Number dom(h)).
    { unfold Ordinal_Number; apply AxiomII; split; Ens. }
    double H7; apply H3 in H7; apply H4 in H8.
    rewrite Lemma128'' in H7; rewrite Lemma128''' in H8; auto.
    apply Theorem69 in H6; rewrite H7 in H6.
    generalize (Theorem101 dom(h)); intro.
    apply Theorem69 in H9; rewrite H8 in H9.
    rewrite H9 in H6; apply Theorem101 in H6; elim H6.
  - apply Theorem27; split; auto.
    unfold Included; intros.
    rewrite Theorem70; rewrite Theorem70 in H7; auto.
    PP H7 a b; double H8; rewrite <- Theorem70 in H8; auto.
    apply AxiomII_P in H9; destruct H9.
    apply AxiomII_P; split; auto; rewrite H10 in *.
    assert ([a,h[a]] ∈ h).
    { apply Property_Value; auto.
      apply Property_dom in H8; rewrite <- H6; auto. }
    apply H5 in H11; eapply H; eauto.
Qed.

Theorem Theorem128' :  forall g,
  forall f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]) ->
  forall h, Function h /\ Ordinal dom(h) /\
  (forall x, Ordinal_Number x -> h [x] = g [h | (x)]) -> f = h.
Proof.
  intros; destruct H, H0, H1, H2.
  assert (forall u, u ∈ dom(f) -> f [u] = g [f | (u)]); intros.
  { apply H3; unfold Ordinal_Number; apply AxiomII; split; Ens.
    apply Theorem111 with (x:= dom(f)); auto. }
  assert (forall u, u ∈ dom(h) -> h [u] = g [h | (u)]); intros.
  { apply H4; unfold Ordinal_Number; apply AxiomII; split; Ens.
    apply Theorem111 with (x:= dom(h)); auto. }
  generalize (Theorem127 f h g H H1 H5 H0 H2 H6); intro; destruct H7.
  - symmetry; eapply Lemma128''''; eauto.
  - eapply Lemma128''''; eauto.
Qed.



End A8.

Export A8.


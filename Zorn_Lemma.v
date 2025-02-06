(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Maximal_Principle.


(** Zorn Lemma **)

Module Type Zorn_Lemma.

Declare Module Max : Maximal_Principle.

Definition F_x X le x:= \{λ u,u∈X /\ Rrelation u le x\}.

Definition FA_a A X le := \{λ u,exists a, a∈A /\ u= F_x X le a \}.

Definition En_A X A le := \{ λ u, u∈X /\ (F_x X le u) ∈ A \}.

Lemma Zorn': forall X le A, A⊂X ->A≠Φ -> PartialOrder le X 
   ->PartialOrder (le ∩ (A × A)) A. 
Proof.
  intros. unfold PartialOrder. split. apply Theorem33 in H; auto. apply H1. 
  repeat split.
  - unfold Relation. intros. apply AxiomII in H2 as [_[_H3]]. apply AxiomII
    in H2. destruct H2, H3, H3, H3. exists x. exists x0. auto.
  - unfold Included; intros. apply AxiomII in H2. apply H2. 
  - unfold Reflexivity; intros. unfold Rrelation. apply AxiomII. split. 
    apply Theorem49; split; Ens. unfold PartialOrder in H1.
    destruct H1 as [_[_[HR[HA HT]]]]. unfold Reflexivity in HR. 
    specialize (HR a). unfold Included in H. specialize (H a). double H2. 
    apply H in H2. apply HR in H2.
    unfold Rrelation in H2. split. apply H2. apply AxiomII. 
    split. Ens. exists a. exists a. auto.
  - unfold Antisymmetry; intros. destruct H3. unfold Rrelation in H3, H4.
    apply AxiomII in H3 as [_[H5 _]]. apply AxiomII in H4 as [_[H6 _]].
     destruct H1 as [_[_[HR[HA HT]]]]. unfold Antisymmetry in HA. 
    specialize (HA x y). double H. unfold Included in H. specialize (H x). 
    destruct H2. 
    apply H in H2. unfold Included in H1. specialize (H1 y).  
    apply H1 in H3. apply HA. split; auto. split; auto.
  - unfold Transitivity; intros. double H. unfold Rrelation. apply AxiomII.
    split. apply Theorem49; destruct H2 as [[H8 [H4 H5]][H6 H7]]; split; Ens.
    destruct H2 as [[H8 [H4 H5]][H6 H7]]. unfold Rrelation in H6, H7. 
    apply AxiomII in H6. destruct H6 as [H11[H9 H10]]. 
    apply AxiomII in H7. destruct H7 as [H12[H13 H14]]. 
    destruct H1 as [_[_[HR[HA HT]]]]. unfold Transitivity in HT. 
    specialize (HT u v w). double H3.  unfold Included in H. specialize (H u).
    double H8. apply H in H3. unfold Included in H1. specialize (H1 v).
    double H4. apply H1 in H4. unfold Included in H2. specialize (H2 w).
    double H5. apply H2 in H5. split. apply HT; split ; auto. 
    apply AxiomII. split. apply Theorem49. split; Ens. exists u. exists w.
    auto.
Qed.
    
Lemma Zorn'' : forall X le  y, PartialOrder le X -> y∈X -> y ∈ (F_x X le y).  
Proof.
  intros. apply AxiomII. split. Ens. split. auto. unfold PartialOrder in H.
  destruct H. destruct H1, H2. 
      unfold Reflexivity in H2. apply H2. auto.
Qed. 

Lemma Zornl : forall X le A, PartialOrder le X -> A⊂X ->A≠Φ ->
(Chain A X le <->
(FA_a A X le)⊂(FA_a X X le)/\Nest (FA_a A X le)).
Proof.
  intros;split;intros. double H1.
  - split; unfold Chain in H2; unfold F_x,FA_a, Included; intros.
    + double H. apply H2 in H as [[ _]HT]. unfold TotalOrder in HT.
      apply AxiomII in H4 as [H6[a0[H7 H8]]]. apply AxiomII; split; auto.
      exists a0. split. apply H0;auto. auto.
    + double H. unfold Nest; intros. destruct H5. 
      apply AxiomII in H5 as [H7[a[H8 H9]]].
      apply AxiomII in H6 as [H12[c[H10 H11]]]. apply H2 in H as [[_ _]H5].
      unfold TotalOrder in H5. destruct H5. destruct (classic (a=c)).
      rewrite H6 in H9. rewrite H9. rewrite H11. left. auto. unfold Included.
      intros. auto. apply H5 in H6. destruct H6.
      * unfold Rrelation in H6. apply AxiomII in H6.
      rewrite H9. rewrite H11.
      unfold Included. left. intros. apply AxiomII. split. Ens. 
      apply AxiomII in H13. destruct H13 as [H16[H14 H15]]. split. auto.
      destruct H4. destruct H13. destruct H17 as [_[_HTR]].
      unfold Transitivity in H17. apply (H17 z a c). split. auto. split. auto.
      apply H6.
      * unfold Rrelation in H6. apply AxiomII in H6. rewrite H9. rewrite H11.
      unfold Included. right. intros. apply AxiomII. split. Ens. 
      apply AxiomII in H13. destruct H13 as [H16[H14 H15]]. split. auto.
      destruct H4. destruct H13. destruct H17 as [_[_HTR]].
      unfold Transitivity in H17. apply (H17 z c a). split. auto. split. auto.
      apply H6.
     * split; auto.
  - unfold Chain. intros. split. split; auto. unfold TotalOrder. split.
    + apply (Zorn' X le A H0 H1 H3).
    + intros. destruct H4. destruct H2. rename H7 into H8. rename H2 into H7.
       double H1.
       unfold Nest in H8.
      destruct (H8 (F_x X le x)(F_x X le y)). split.
      * apply AxiomII. destruct H. split. 
        apply Theorem33 with X. auto. unfold Included. 
        intros. apply AxiomII in H10. destruct H10 as [_[H11_]]. auto. exists x.
        split; auto.
      * apply AxiomII. destruct H. split. 
        apply Theorem33 with X. auto. unfold Included. 
        intros. apply AxiomII in H10. destruct H10 as [_[H11_]]. auto. exists y.
        split; auto.
      * left. unfold Included in H9. specialize (H9 x). 
        assert (x ∈ (F_x X le x)).
        { apply AxiomII. split. Ens. split. auto. destruct H. destruct H10.
          destruct H11. auto. }
        apply H9 in H10. apply AxiomII in H10. destruct H10 as [_[_HR]].
        unfold Rrelation. apply AxiomII. split. apply Theorem49. split; Ens.
        split. apply H10. apply AxiomII. split. apply Theorem49. split; Ens.
         exists x. exists y. auto.
      *  right. unfold Included in H9. specialize (H9 y). 
        assert (y ∈ (F_x X le y)).
        { apply AxiomII. split. Ens. split. auto. destruct H. destruct H10.
          destruct H11. auto. }
        apply H9 in H10. apply AxiomII in H10. destruct H10 as [_[_HR]].
        unfold Rrelation. apply AxiomII. split. apply Theorem49. split; Ens.
        split. apply H10. apply AxiomII. split. apply Theorem49. split; Ens.
         exists y. exists x. auto.
Qed.

Lemma Zorn2 : forall X le A y, PartialOrder le X -> Chain A X le -> y∈X ->
   (BoundU y A X le <-> forall z, z ∈ (FA_a A X le) -> z ⊂ (F_x X le y)).
Proof.
  intros. split; intros.
  - unfold Included; intros. apply AxiomII in H3 as [H5[a[H6 H7]]]. 
    rewrite H7 in H4. apply AxiomII in H4 as [H8[H9 H10]]. apply AxiomII.
    split. Ens. split. auto.  assert (Rrelation a le y).
    { unfold BoundU in H2. destruct H2. split. auto. intro. rewrite H2 in H9.
      apply Theorem16 with z0. auto. destruct H3. specialize (H4 a). auto. }
    double H. destruct H. destruct H11. destruct H12, H13.
      unfold Transitivity in H14. apply H14 with (v:= a).
    repeat split; auto. unfold Chain in H0. destruct H0. auto. destruct H0.
    apply H0. auto. 
   - unfold BoundU. intros. split; auto. split. unfold Chain in H0.
     destruct H0. auto. destruct H0. auto. intros. specialize (H2 (F_x X le a)).
     assert ((F_x X le a) ∈ (FA_a A X le)).
    { apply AxiomII. split.  apply Theorem33 with X. unfold PartialOrder in H.
      destruct H. auto. unfold Included. intros. apply AxiomII in H5 as [_[hh]].
      auto. exists a. split; auto. }
      apply H2 in H5. unfold Included in H5. specialize (H5 a). 
      assert (a ∈ (F_x X le a)). { apply AxiomII. split. Ens. split. 
      unfold Chain in H0. destruct H0. auto. destruct H0. apply H0; auto. 
      unfold PartialOrder in H. destruct H. destruct H6, H7. 
      unfold Reflexivity in H7. apply H7. unfold Chain in H0. destruct H0.
      destruct H3. auto. destruct H0. apply H0; auto. }
     apply H5 in H6. apply AxiomII in H6 as [_[_ HG]]. auto.
Qed.

Lemma Zorn3 : forall X le  y, PartialOrder le X  -> y∈X ->
  (MaxElement y X le <-> 
   ( MaxMember (F_x X le y) (FA_a X X le))).
Proof.
  intros. split; intros. double H.
  -  unfold MaxMember. intros. split.
    + apply AxiomII. split. apply Theorem33 with X. unfold PartialOrder in H.
      destruct H. auto. unfold Included. intros. apply AxiomII in H4.
      destruct H4, H5. auto. exists y. split; auto.
    + intros Fx H5. intro. unfold ProperIncluded in H4. destruct H4.
      unfold Included in H4. apply AxiomII in H5. destruct H5, H7, H7.
      unfold MaxElement in H1. destruct H1. intro. rewrite H1 in H7.
      apply Theorem16 with x in H7. auto. specialize (H4 y).
       assert (y ∈ (F_x X le y)). { apply Zorn''; auto. } apply H4 in H10.      
      rewrite H8 in H10. specialize (H9 x). apply H9 in H7. apply H7.
      split. apply AxiomII in H10. destruct H10 as [_[_HH]]. auto. intro.
       rewrite <- H11 in H8. rewrite H8 in H6. apply H6; auto.
  - unfold MaxMember in H1. unfold MaxElement. intros. split; auto.
    intros. destruct H1. intro. apply (Theorem16 (F_x X le y)).
    rewrite <- H1. apply AxiomII. split. apply Theorem33 with X. 
    unfold PartialOrder in H. destruct H. auto. unfold Included. 
    intros. apply AxiomII in H4. destruct H4, H5. auto. exists y. split; auto.
    specialize (H4 (F_x X le y0)). 
    intro. apply H4. apply AxiomII. split. apply Theorem33 with X. 
    unfold PartialOrder in H.
      destruct H. auto. unfold Included. intros. apply AxiomII in H6.
      destruct H6, H7. auto. exists y0. split; auto. destruct H5.
    unfold ProperIncluded. split. unfold Included. intros. apply AxiomII. split.
     Ens. apply AxiomII in H7. destruct H7. split. apply H8. destruct H8.
     double H. destruct H. destruct H11. destruct H12, H13.
      unfold Transitivity in H14. apply H14 with (v:= y).
    repeat split; auto. intro. rewrite AxiomI in H7. specialize (H7 y0).
    assert (y0 ∈ (F_x X le y0)). { apply Zorn''; auto. } apply H7 in H8.
      apply AxiomII  in H8. destruct H8 as [_[_H9]]. destruct H.
      destruct H9, H10, H11. unfold Antisymmetry in H11. destruct (H11 y y0);
     try split; auto.
Qed. 
    
Theorem Zorn : forall X le, PartialOrder le X ->
  (forall A, Chain A X le -> exists y, BoundU y A X le) ->
  (exists z, MaxElement z X le).
Proof.
  intros. destruct (classic(X=Φ)).
  - exists Φ. unfold MaxElement. intros. contradiction.
  - assert  (exists Fmax, MaxMember Fmax (FA_a X X le)).
    { apply Max.MaxPrinciple. 
       unfold PartialOrderSet, PartialOrder in H; destruct H.
       clear H2; assert ((FA_a X X le ) ⊂ pow(X)).
       { unfold Included; intros; unfold FA_a in H2.
        apply AxiomII in H2; destruct H2, H3, H3.
        unfold PowerSet; apply AxiomII; split; auto.
        rewrite H4; unfold Included; intros.
        unfold F_x in H5; apply AxiomII in H5; apply H5. }
        apply Theorem38 in H; auto; apply Theorem33 in H2; auto. 
      intros. 
      destruct H2. destruct (classic (n=Φ)).
      - apply Property_NotEmpty in H1. destruct H1. exists (F_x X le x). split.
        apply AxiomII. split. apply Theorem33 with X. apply H. unfold Included.
        intros. apply AxiomII in H5 as [_[HH_]]. auto. exists x; auto. intros.
        rewrite H4 in H5. apply Theorem16 in H5. destruct H5.
      -  assert ((FA_a (En_A X n le) X le) ⊂ (FA_a X X le)).
        { intros; unfold Included; intros.
          apply AxiomII in H5. destruct H5, H6 as [a H6], H6.
          apply AxiomII in H6; destruct H6; apply AxiomII; split; auto. 
          destruct H8.
          unfold Included in H2; apply H2 in H9; unfold FA_a in H6.
          double H9; apply AxiomII in H10; destruct H10, H11 as [a1 H11].
          destruct H11. double H12. double H12. rewrite AxiomI in H12. 
          specialize (H12 a).
          destruct H12. assert (a ∈ (F_x X le a)). apply Zorn''; auto. 
          apply H12 in H16.
          apply AxiomII in H16 as [_[_ HA]]. rewrite AxiomI in H13. 
          specialize (H13 a1).
          destruct H13. assert (a1 ∈ (F_x X le a1)). apply Zorn''; auto. 
          apply H16 in H17.
          apply AxiomII in H17 as [_[_ HB]]. assert (a=a1). 
          apply H; split; auto.
          exists a. split. auto. auto. }
          assert ( Nest (FA_a (En_A X n le) X le)).
          { unfold Included in H5. unfold Nest; intros. destruct H6. 
           apply AxiomII in H6. apply AxiomII in H7.
          destruct H6, H7, H8 as [a H8], H9 as [b H9], H8, H9.
          apply AxiomII in H8; apply AxiomII in H9. destruct H8, H9. 
          destruct H12, H13.
           rewrite H10, H11. unfold Nest in H3. apply H3. auto. }
           assert ((En_A X n le)⊂X/\(En_A X n le)≠Φ).
          { split. unfold Included; intros. apply AxiomII in H7 as [_[HH_]]. 
            auto. apply Property_NotEmpty in H4; destruct H4; double H4.
          apply H2 in H7; apply AxiomII in H7; destruct H7, H8, H8.
          rewrite H9 in H4; apply Property_NotEmpty; exists x0.
          apply AxiomII; split; Ens. } 
          assert (Chain (En_A X n le) X le).
          { apply Zornl; auto; apply H7. } double H8. apply H0 in H8. 
          destruct H8 as [y Ho]; unfold Chain in H9; double H.
          unfold PartialOrderSet in H8; apply H9 in H8; clear H9.
          destruct H8; exists (F_x X le y); split; intros.
          + unfold BoundU in Ho; double H; add (X≠Φ) H10; apply Ho in H10.
            clear Ho. destruct H10.  destruct H11.  clear H11.
            unfold FA_a; apply AxiomII; split.
            assert (F_x X le y ⊂ X).
           { unfold Included; intros; apply AxiomII in H11; apply H11. }
           destruct H; apply Theorem33 in H11; auto.  
           exists y; split; auto.
          + assert (PartialOrder le X /\X <> Φ) as HH. split;auto.
            double H10; unfold Included in H2; apply H2 in H11.
            apply AxiomII in H11; destruct H11, H12, H12.
            apply Zorn2 with (A:=(En_A X n le))(y:=y)(z:=u) in H; auto. 
            apply Zornl; auto; apply H7. unfold BoundU in Ho. apply Ho in HH. 
            destruct HH. auto. 
            apply AxiomII; split; auto; exists x; split; auto.
            apply AxiomII; split; Ens; rewrite <- H13; auto. } 
      destruct H2 as [M H2]; double H2; unfold MaxMember in H3.
      assert (FA_a X X le ≠ Φ).
      { apply Property_NotEmpty in H1; destruct H1.
        apply Property_NotEmpty; exists (F_x X le x).
        unfold F_x; apply AxiomII; split.
        - destruct H; apply Theorem33 with (x:= X); auto.
          unfold Included; intros; apply AxiomII in H5; apply H5.
        - exists x; split; auto. }
      apply H3 in H4; clear H3; destruct H4.
      unfold F_x in H3; apply AxiomII in H3; destruct H3. 
      destruct H5. destruct H5. rewrite H6 in H2.
      exists x; apply Zorn3 with (y:=x) in H; auto; apply H; auto.
Qed.

End Zorn_Lemma.
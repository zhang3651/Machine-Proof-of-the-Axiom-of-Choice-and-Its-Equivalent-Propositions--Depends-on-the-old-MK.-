(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*      Copyright 2018-2019: Tianyu Sun, Yaoshun Fu and Wensheng Yu.       *)
(***************************************************************************)


Require Export A_4.

(* A.5 序偶：关系 *)

Module A5.

(* 定义48  [x,y] = [[x]|[x|y]] *)

Definition Ordered x y : Class := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).


(* 定理49  [x,y]是一个集当且仅当x是一个集,并且y是一个集;如果[x,y]不是一个集，则[x,y]=μ *)

Theorem Theorem49 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intro.
  - unfold Ordered in H; unfold Unordered in H.
    apply AxiomIV' in H; destruct H; apply Theorem42' in H.
    apply Theorem42' in H; apply Theorem42' in H0; split; auto.
    unfold Unordered in H0; apply AxiomIV' in H0.
    destruct H0; apply Theorem42' in H1; auto.
  - destruct H; unfold Ordered, Unordered; apply AxiomIV; split.
    + apply Theorem42; auto; apply Theorem42; auto.
    + apply Theorem42; auto; apply Theorem46; auto.
Qed.

Theorem Theorem49' : forall (x y: Class),
  ~ Ensemble [x,y] -> [x,y] = μ.
Proof.
  intros; generalize (Theorem49 x y); intros.
  apply Lemma_z with (B:= Ensemble x /\ Ensemble y) in H; try tauto.
  apply not_and_or in H; apply Theorem46' in H; auto.
  generalize Theorem39; intros; rewrite <-H in H1.
  unfold Ordered; apply Theorem46'; auto.
Qed.


(* 定理50  如果x与y均为集,则∪[x,y]=[x|y],∩[x,y]=[x],∪∩[x,y]=x,∩∩[x,y]=x,∪∪[x,y]=x∪y,∩∪[x,y]=x∩y如果x或者y不是一个集,则∪∩[x,y]=Φ,∩∩[x,y]=Φ,∪∪[x,y]=Φ,∩∪[x,y]=Φ *)

Lemma Lemma50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x | y].
Proof.
  intros; apply Theorem49 in H; auto.
  unfold Ordered in H; unfold Unordered in H.
  apply AxiomIV' in H; destruct H.
  apply Theorem42' in H; auto.
  apply Theorem42' in H0; auto.
Qed.

Theorem Theorem50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  intros; elim H; intros.
  repeat unfold Ordered; apply Lemma50 in H.
  apply Theorem47 in H; auto; elim H; intros; repeat split.
  - rewrite H3; apply AxiomI; split; intros; try (apply Theorem4; tauto).
    apply Theorem4 in H4; destruct H4; auto; apply Theorem4; tauto.
  - rewrite H2; apply AxiomI; split; intros.
    + apply Theorem4' in H4; apply H4.
    + apply Theorem4'; split; auto; apply Theorem4; tauto.
  - rewrite H2; apply AxiomI; split; intros.
    + apply AxiomII in H4; destruct H4, H5, H5. 
      apply Theorem4' in H6; destruct H6; apply AxiomII in H6.
      destruct H6; rewrite <- H8; auto.
      apply Theorem19; auto.
    + apply AxiomII; split; Ens; exists x. 
      split; auto; apply Theorem4'; split.
      * apply AxiomII; split; auto.
      * apply Theorem4; left; apply AxiomII.
        split; try apply H0; trivial.
  - rewrite H2; apply AxiomI; split; intros.
    + apply AxiomII in H4; destruct H4.
      apply H5; apply Theorem4'; split.
      * apply AxiomII; split; auto.
      * apply Theorem4; left; apply AxiomII; split; auto.
    + apply AxiomII; split; Ens.
      intros; apply Theorem4' in H5. destruct H5. 
      apply AxiomII in H5. destruct H5. rewrite H7; auto. 
      apply Theorem19; auto.
  - rewrite H3; apply AxiomI; split; intros.
    + apply Theorem4; apply AxiomII in H4; destruct H4, H5, H5. 
      apply Theorem4 in H6; destruct H6.
      * apply AxiomII in H6; destruct H6; left; rewrite <- H7; auto. 
        apply Theorem19; auto.
      * apply Theorem4 in H6; destruct H6. 
        -- apply AxiomII in H6; destruct H6.
           left; rewrite <- H7; auto; apply Theorem19; auto.
        -- apply AxiomII in H6; destruct H6.
           right; rewrite <- H7; auto; apply Theorem19; auto.
    + apply AxiomII; apply Theorem4 in H4; split.
      * unfold Ensemble; destruct H4; Ens.
      * destruct H4.
        -- exists x; split; auto; apply Theorem4; left.
           apply AxiomII; split; auto.
        -- exists y; split; auto; apply Theorem4; right.
           apply Theorem4; right; apply AxiomII; split; auto.
  - rewrite H3; apply AxiomI; split; intros.
    + apply Lemma_x in H4; elim H4; intros.
      apply AxiomII in H5; apply AxiomII in H6.
      destruct H4; apply Theorem4'; split; auto.
      * apply H5; apply Theorem4; left.
        apply AxiomII; split; auto.
      * apply H6; apply Theorem4; right.
        apply Theorem4; right.
        apply AxiomII; split; auto.
    + apply Theorem4' in H4; destruct H4. 
      apply AxiomII; split; Ens.
      intros; apply Theorem4 in H6; destruct H6.
      * apply AxiomII in H6; destruct H6; rewrite H7; auto.
        apply Theorem19; auto.
      * apply AxiomII in H6; destruct H6, H7.
        -- apply AxiomII in H7; destruct H7. 
           rewrite H8; auto; apply Theorem19; auto.
        -- apply AxiomII in H7; destruct H7.
           rewrite H8; auto; apply Theorem19; auto.
Qed.

Lemma Lemma50' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> ~Ensemble [x] \/ ~Ensemble [x | y].
Proof.
  intros; elim H; intros. 
  - left; apply Theorem43 in H0; auto.
    rewrite H0; apply Theorem39; auto.
  - right; apply Theorem46' in H; auto.
    rewrite H; apply Theorem39; auto.
Qed.

Theorem Theorem50' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ)
  /\ (∪(∪[x,y]) = μ) /\ (∩(∪[x,y]) = Φ).
Proof.
  intros; apply Lemma50' in H; auto.
  apply Theorem47' in H; destruct H.
  repeat unfold Ordered; repeat split.
  - rewrite H; apply Theorem24'; auto.
  - rewrite H; apply Theorem24; auto.
  - rewrite H0; rewrite <- Theorem34'; auto.
  - rewrite H0; rewrite <- Theorem34; auto.
Qed.


(* 定义51  z的1st坐标=∩∩z *)

Definition First z := ∩∩z.


(* 定义52  z的2nd坐标=(∩∪z)∪(∪∪z)~(∪∩z) *)

Definition Second z := (∩∪z)∪(∪∪z)~(∪∩z).


(* 定理53  μ的2nd坐标=μ *)

Lemma Lemma53 : μ ~ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4' in H; destruct H; auto.
  - apply Theorem4'; split; auto.
    apply AxiomII; split.
    * apply Theorem19 in H; auto.
    * apply Theorem16; auto.
Qed.

Theorem Theorem53 : Second μ = μ.
Proof.
  intros; unfold Second.
  repeat rewrite <-Theorem34'; auto.
  repeat rewrite <-Theorem34 ; auto.
  rewrite Theorem24'; auto.
  rewrite Lemma53; auto.
  apply Theorem20; auto.
Qed.

Hint Rewrite Theorem53 : set.


(* 定理54  如果x与y均为集,[x,y]的1st坐标=x同时[x,y]的2nd坐标=y
          如果x或者y不是一个集，则[x,y]的1st坐标=μ,同时[x,y]的2nd坐标=μ *)

Lemma Lemma54 : forall (x y: Class),
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros.
  apply AxiomI; split; intros.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; apply Theorem4 in H; split; auto.
    destruct H; auto; apply AxiomII in H0.
    destruct H0; elim H1; auto.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; split; auto.
    apply Theorem4; tauto.
Qed.

Theorem Theorem54 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> First [x,y] = x /\ Second [x,y] = y.
Proof.
  intros; apply Theorem50 in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1, H2, H3; unfold Second.
    rewrite H4; rewrite H3; rewrite H1.
    rewrite Lemma54; auto; unfold Setminus.
    rewrite Theorem6'; auto; rewrite <- Theorem8; auto.
    rewrite Property_μ; auto; rewrite Theorem20'; auto.
Qed.


Theorem Theorem54' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> First [x,y] = μ /\ Second [x,y] = μ.
Proof.
  intros; apply Theorem50' in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1; unfold Second.
    rewrite H2; rewrite H1; rewrite H.
    rewrite Lemma53; auto.
    apply Theorem20; auto.
Qed.


(* 定理55  如果x与y均为集,同时[x,y]=[u,v],则z=x同时y=v *)

Theorem Theorem55 : forall (x y u v: Class),
  Ensemble x /\ Ensemble y -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  intros; split; intros.
  - double H; apply Theorem49 in H; apply Theorem54 in H1; destruct H1.
    rewrite H0 in H, H1, H2; apply Theorem49 in H; apply Theorem54 in H.
    destruct H; rewrite H1 in H; rewrite H2 in H3; split; auto.
  - destruct H0; rewrite H0, H1; auto.
Qed.



(* 定义56  r是一个关系当且仅当对于r的每个元z存在x与y使得z=[x,y]; 一个关系是一个类，它的元为序偶 *)

Definition Relation r : Prop :=
  forall z, z∈r -> exists x y, z = [x,y].



(* { (x,y) : ... } *)

Notation "\{\ P \}\" := 
  \{ λ z, exists x y, z = [x,y] /\ P x y \}(at level 0).

Fact Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.
Proof.
  intros. apply AxiomII in H as [? [x [y []]]]. subst. split; eauto.
  apply AxiomII; split; eauto.
Qed.

Fact AxiomII_P : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).
Proof.
  split; intros.
  - split; Ens. apply AxiomII in H as [? [x [y []]]].
    apply Theorem55 in H0 as []; [subst|apply Theorem49]; auto.
  - destruct H. apply AxiomII; split; Ens.
Qed.

Ltac PP H a b := apply Property_P in H; destruct H as [[a [b H]]]; rewrite H in *.



(* 定义57 r∘s={u:对于某个x，某个y及某个z,u=[x,z],[x,y]∈s同时[y,z]∈r},类r∘s是r与s的合成 *)

Definition Composition r s : Class :=
 \{\ λ x z, exists y, [x,y]∈s /\ [y,z]∈r \}\.

Notation "r ∘ s" := (Composition r s) (at level 50, no associativity).

Definition Composition' r s : Class :=
  \{ λ u, exists x y z, u = [x,z] /\ [x,y] ∈ s /\ [y,z] ∈ r \}.



(* 定理58  (r∘s)∘t=r∘(s∘t) *)

Theorem Theorem58 : forall (r s t: Class),
  (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; apply AxiomI; split; intros.
  - PP H a b. apply AxiomII_P in H0; destruct H0, H1 as [y H1], H1.
    apply AxiomII_P in H2; destruct H2, H3, H3; apply AxiomII_P; split; auto.
    exists x; split; try tauto; apply AxiomII_P; split; Ens.
    AssE [a,y]; AssE [y,x]; apply Theorem49 in H5; apply Theorem49 in H6.
    destruct H5, H6; apply Theorem49; auto.
  - PP H a b; apply AxiomII_P in H0; destruct H0, H1 as [y H1], H1.
    apply AxiomII_P in H1; destruct H1, H3, H3; apply AxiomII_P; split; auto.
    exists x; split; auto; apply AxiomII_P; split; Ens.
    AssE [a,x]; AssE [y,b]; apply Theorem49 in H5; apply Theorem49 in H6.
    destruct H5, H6; apply Theorem49; Ens.
Qed.

Hint Rewrite Theorem58 : set.


(* 定理59  r∘(s∪t)=r∘s∪r∘t,同时r∘(s∩t)⊂r∩s∘r∩t *)

Theorem Theorem59 : forall (r s t: Class),
  Relation r /\ Relation s -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) /\ 
  r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  intros; split.
  - apply AxiomI; split; intros.
    + PP H0 a b; apply AxiomII_P in H1; destruct H1.
      apply Theorem4.
      destruct H2 as [y H2]; destruct H2.
      apply Theorem4 in H2; destruct H2.
      * left; apply AxiomII_P; split; auto.
        exists y; split; auto.
      * right; apply AxiomII_P; split; auto.
        exists y; split; auto.
    + apply Theorem4 in H0; destruct H0; PP H0 a b; apply AxiomII_P.
      * apply AxiomII_P in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply Theorem4; try tauto.
      * apply AxiomII_P in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply Theorem4; try tauto.
  - unfold Included; intros; PP H0 a b.
    apply AxiomII_P in H1; destruct H1.
    destruct H2 as [y H2]; destruct H2.
    apply Theorem4' in H2; apply Theorem4'; split.
    + apply AxiomII_P; split; auto.
      exists y; split; try apply H2; auto.
    + apply AxiomII_P; split; auto.
      exists y; split; try apply H2; auto.
Qed.



(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).



(* 定理61  (r ⁻¹)⁻¹=r *)

Lemma Lemma61 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble [y,x].
Proof.
  intros; split; intros.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
Qed.

Theorem Theorem61 : forall (r: Class),
  Relation r -> (r ⁻¹)⁻¹ = r.
Proof.
  intros; apply AxiomI; split; intros.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1.
    apply AxiomII_P in H2; apply H2.
  - unfold Relation in H; double H0; apply H in H1.
    destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply AxiomII_P; split; Ens; apply AxiomII_P; split; auto.
    apply Lemma61; auto; Ens.
Qed.

Hint Rewrite Theorem61 : set.


(* 定理62  (r∘s)⁻¹=(s⁻¹)∘(r⁻¹) *)

Theorem Theorem62 : forall (r s: Class),
  (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; apply AxiomI; split; intros.
  - PP H a b; apply AxiomII_P in H0; destruct H0 as [H0 H1].
    apply AxiomII_P; split; auto.
    apply AxiomII_P in H1; destruct H1, H2, H2.
    exists x; split.
    + apply AxiomII_P; split; auto. 
      apply Lemma61; Ens; exists r; auto.
    + apply AxiomII_P; split; auto.
      apply Lemma61; Ens.
  - PP H a b; apply AxiomII_P in H0; destruct H0, H1, H1.
    apply AxiomII_P; split; auto.
    apply AxiomII_P in H1; apply AxiomII_P in H2.
    apply AxiomII_P; split.
    + apply Lemma61; auto.
    + exists x; split; try apply H0; try apply H2.
      destruct H1; auto.
Qed.

Hint Rewrite Theorem62 : set.


End A5.

Export A5.


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.

Require Import lc.Sets.
Import SetNotations.
Local Open Scope set_scope.

Require Import lc.List.

Require Import lc.model_definitions.
Require Import lc.denot.
Require Import lc.valid_theory.


(* 
   The default induction principle for values is not
   strong enough for lists in the v_map and v_list case. So we prove a stronger
   version below.

   Value_ind
     : forall P : Value -> Prop,
       (forall n : nat, P (v_nat n)) ->
       (forall (l : list Value) (v : Value), P v -> P (v_map l v)) ->
       P v_fun -> 
       (forall l : list Value, P (v_list l)) -> 
       P v_wrong -> 
       forall v : Value, P v 
*)

Fixpoint Value_ind' (P : Value -> Prop)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : list Value) (v : Value), Forall P l -> P v -> P (v_map l v)) 
       (f : P v_fun)
       (l : (forall l : list Value, Forall P l -> P (v_list l)))
       (w : P v_wrong) 
       (v : Value) : P v := 
  let rec := Value_ind' P n m f l w 
  in
  let fix rec_list (vs : list Value) : Forall P vs :=
    match vs with 
    | nil => Forall_nil _
    | cons w ws => @Forall_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  match v with 
  | v_nat k => n k
  | v_map X v => 
      m X v (rec_list X) (rec v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  | v_wrong => w 
  end.

(* We do the same thing for Value_rect *)

Fixpoint Value_rec' (P : Value -> Type)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : list Value) (v : Value),
           List.ForallT P l -> P v -> P (v_map l v)) 
       (f : P v_fun)
       (l : (forall l : list Value, List.ForallT P l -> P (v_list l)))
       (w : P v_wrong) (v : Value) : P v := 
  let rec := Value_rec' P n m f l w 
  in
  let fix rec_list (vs : list Value) : ForallT P vs :=
    match vs with 
    | nil => ForallT_nil _
    | cons w ws => @ForallT_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  match v with 
  | v_nat k => n k
  | v_map X v => 
      m X v (rec_list X) (rec v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  | v_wrong => w 
  end.


(* ----------------------------------------------- *)


Definition ConsistentPointwiseList XS YS := 
  List.Forall2 Consistent XS YS.
Definition InconsistentPointwiseList XS YS := 
  length XS <> length YS \/ List.Exists2 Inconsistent XS YS.
Definition ConsistentAnyList XS YS := 
  forall x y, List.In x XS -> List.In y YS -> Consistent x y.
Definition InconsistentAnyList XS YS := 
  (exists x y, List.In x XS /\ List.In y YS /\ Inconsistent x y).



(* Two values cannot be both consistent and inconsistent. *)

Lemma Consistent_Inconsistent_disjoint : 
  forall x y, Consistent x y -> Inconsistent x y -> False.
Proof.
  intros x.
  eapply Value_ind' with (P := fun x => 
  forall y : Value, Consistent x y -> Inconsistent x y -> False).
  all: intros.
  all: try solve [inversion H; inversion H0; subst; done].
  + inversion H2; inversion H1; subst.
    all: try simpl in H3; try done.
    - inversion H9; subst. clear H9.
      eapply H0; eauto.
    - inversion H9; subst. clear H9.
    destruct H11 as [x1 [x2 [I1 [I2 ii]]]].
    specialize (H5 _ _ I1 I2).
    rewrite Forall_forall in H.
    eapply H; eauto.
  + inversion H0; inversion H1; subst. simpl in H5; try done.
    - inversion H7; subst. eauto using Forall2_length.
    - inversion H7; subst; clear H7.
      clear H1 H0. move: YS H3 H6.
      induction H; intros YS h1 h2;
        inversion h1; inversion h2; subst.  
      inversion H7; subst. eauto.
      inversion H7; subst. eauto.
Qed.

(* Determining whether two values are consistent or inconsistent 
   is decidable *)

Definition ConsistentDecidable := fun v1 => forall v2 : Value, 
                     {Consistent v1 v2} + {Inconsistent v1 v2}.



Lemma dec_any : forall XS, ForallT ConsistentDecidable XS -> forall YS, { ConsistentAnyList XS YS } + {InconsistentAnyList XS YS}.
induction XS.
- intros h. intros ys. left. intros x y h1 h2. inversion h1.
- intros h. inversion h. subst. clear h.
  intros YS. unfold ConsistentDecidable in H1.
  destruct (IHXS H2 YS).
  + induction YS. left. intros x y h1 h2. inversion h2.
    have CE: (ConsistentAnyList XS YS).
    intros x y h1 h2. 
    eapply c; eauto. simpl. eauto.
    specialize (IHYS CE). destruct IHYS.
    ++ destruct (H1 a0).       
       left. 
       { intros x y h1 h2.
         destruct h1 as [EQ|INXS]; destruct h2 as [EQ2|INYS]; subst.
         -- auto.
         -- apply c0; eauto. simpl; auto.
         -- apply c; eauto. simpl; auto.
         -- apply CE; eauto.
       } 
       right. exists a . exists a0. simpl. split; auto.
    ++ right. destruct i as [x [y [h1 [h2 h3]]]].
       exists x. exists y. simpl. eauto.

  + right. destruct i as [x1 [x2 [h1 [h2]]]].
    exists x1. exists x2. simpl. split; eauto. 
Qed.

Lemma dec_point : forall XS,  ForallT ConsistentDecidable XS -> forall YS, { ConsistentPointwiseList XS YS } + {InconsistentPointwiseList XS YS}.
Proof.  
induction XS; intros IH [|y YS].
+ left. unfold ConsistentPointwiseList. eauto.
+ right. unfold InconsistentPointwiseList. simpl; left; auto.
+ right. left; simpl; auto.
+ inversion IH; subst. 
  destruct (H1 y); destruct (IHXS H2 YS); unfold ConsistentPointwiseList in *; 
    unfold InconsistentPointwiseList in *.
  all: try solve [simpl; left; eauto].
  all: try solve [right; destruct i; simpl; right; eauto].
  right; destruct i; simpl.
  left; eauto. 
  right; eauto.
Qed.  
  
Lemma dec_con : forall v1 v2, {Consistent v1 v2 } + {Inconsistent v1 v2 }.
intros v1. 
eapply Value_rec' with 
(P := fun v1 =>  forall v2 : Value, {Consistent v1 v2} + {Inconsistent v1 v2}).
all: intros.
all: destruct v2.
all: try solve [right; eapply i_head; simpl; done].
all: try solve [left; eauto].
+ destruct (Nat.eq_dec n n0). subst.
  left. eauto. right. eapply i_head; simpl. intro h.
  inversion h. subst.  done.
+ destruct (H0 v2).
  left. eapply c_map2; eauto.
  destruct (dec_any l H l0).
  right. eapply i_map; eauto.
  left. eauto.
+ destruct (dec_point l H l0).
  left; eauto.
  right. destruct i; eauto.
Qed.

Lemma DecSetList : forall XS, ForallT ConsistentDecidable XS.
intros XS. induction XS. econstructor; eauto.
econstructor; eauto. unfold ConsistentDecidable. eapply dec_con; eauto.
Qed.


(* Consistency is also reflexive *)

Definition ConsistentReflexive (x : Value) := Consistent x x.

Lemma ConsistentPointwiseList_refl : forall XS, ForallT ConsistentReflexive XS -> ConsistentPointwiseList XS XS. 
Proof.
  induction 1; unfold ConsistentPointwiseList; eauto.
Qed.

#[export] Instance Consistent_refl : Reflexive Consistent.
intro x.
eapply Value_ind' with (P := ConsistentReflexive).
all: unfold ConsistentReflexive; intros; eauto using ConsistentPointwiseList_refl.
econstructor. rewrite <- Forall_Forall2. auto.
Qed.


(* ------------------------------------------------- *)
(* Consistent sets *)

Lemma ConsistentSets_sub {X1 X2 Y1 Y2} : 
  ConsistentSets Y1 Y2 -> X1 ⊆ Y1 -> X2 ⊆ Y2 -> ConsistentSets X1 X2.
Proof.
  unfold ConsistentSets in *.
  unfold Included in *. eauto.
Qed.

Lemma ConsistentSet_sub {X Y} : ConsistentSet Y -> X ⊆ Y -> ConsistentSet X.
Proof.
  unfold ConsistentSet, ConsistentSets in *.
  unfold Included in *. eauto.
Qed.

(* Not transitive. The middle set may be empty! *)
(* Instance ConsistentSets_Transitive : Transitive ConsistentSets. *)


(* ------------------------------------------------- *)

Definition APPLY_ConsistentSets : forall w1 w2 w1' w2', 
    ConsistentSets w1 w1' -> 
    ConsistentSets w2 w2' -> 
    ConsistentSets (APPLY w1 w2) (APPLY w1' w2'). 
Proof.
  intros w1 w2 w1' w2' C1 C2.
  unfold ConsistentSets in *.
  intros x y h1 h2.

  inversion h1; inversion h2; subst; eauto; clear h1 h2.

  all: try (move: (C1 _ _ H H3) => h; inversion h; subst; auto).
  all: try (move: (C1 _ _ H H5) => h; inversion h; subst; auto).
  all: try (move: (C2 _ _ H H4) => h; inversion h; subst; auto).
  all: try (move: (C2 _ _ H0 H5) => h; inversion h; subst; auto).

  all: try solve [  match goal with [ H : ~ applicable ?X |- _ ] => exfalso; apply H; auto end ].

  (* Application of a function to "wrong". This case is impossible because
     the map's domain is valid and all elements of w2 are consistent with wrong. *) 
  move: H5 => [NE NW]. 
  exfalso.
  have L: forall y, y ∈ w2' -> Consistent v_wrong y.
  { intros. eauto. }
  destruct V; try done.
  specialize (L v ltac:(eauto)). inversion L. subst; simpl in NW. inversion NW; simpl in *; done.

  move: H1 => [NE NW]. 
  exfalso.
  have L: forall y, y ∈ w2 -> Consistent y v_wrong.
  { intros. eauto. }
  destruct V; try done.
  specialize (L v ltac:(eauto)). inversion L. subst; simpl in NW. inversion NW; simpl in *; done.

  (* two successful betas *)
  move: H3 => [x1 [x2 [I1 [I2 ii]]]].
  have h3 : x1 ∈ w2. eapply H0; eauto.
  have h4 : x2 ∈ w2'. eapply H6; eauto.
  move: (C2 x1 x2 h3 h4) => h5.
  assert False. eapply Consistent_Inconsistent_disjoint; eauto. done.

  (* two successful projections *)
  move: (C2 _ _ H0 H6)=> c1. inversion c1; subst; clear c1; eauto. 
  clear h H H0 H5 H6.
  move: k0 H1 H7.
  induction H4; intros k0; destruct k0; simpl;  try done.
  intros h1 h2; inversion h1; inversion h2; subst. auto.
  intros h1 h2. eauto.

  move: (C2 _ _ H0 H6) => c. inversion c; subst; clear c.
  specialize (H8 k). done.

  move: (C1 _ _ H H6) => c. inversion c; subst; clear c.

  move: (C2 _ _ H0 H7) => c. inversion c; subst; clear c.
  specialize (H2 k). done.
Qed.

Definition APPLY_ConsistentSet : forall w1 w2, 
    ConsistentSet w1 -> 
    ConsistentSet w2 -> 
    ConsistentSet (APPLY w1 w2). 
Proof.
  intros.  unfold ConsistentSet in *.
  eapply APPLY_ConsistentSets; eauto.
Qed.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).


Lemma Consistent_denot :
  forall t ρ1 ρ2, Env.ForallT2 ConsistentSets ρ1 ρ2 -> valid_env ρ1 -> valid_env ρ2 ->
             ConsistentSets (denot t ρ1) (denot t ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ1 ρ2 CR VR1 VR2.
  all: autorewrite with denot.
  all: intros x1 x2 I1 I2.
  all: try solve [inversion I1; inversion I2; eauto].

  - (* var *) 
    induction CR; simpl in I1, I2.
    ++ inversion I1. inversion I2. subst. auto.
    ++ destruct (x == x0) eqn:E; rewrite E in I1, I2. eapply f; eauto.
       inversion VR1. inversion VR2. eauto.

  - (* app *)
    move: (IH1 ρ1 ρ2 ltac:(eauto) ltac:(eauto) ltac:(eauto)) => C1.
    move: (IH2 ρ1 ρ2 ltac:(eauto) ltac:(eauto) ltac:(eauto)) => C2.

    move: (APPLY_ConsistentSets _ _ _ _ C1 C2) => CA.

    eapply (CA x1 x2 I1 I2).

  - (* abs *)
    pick fresh y.
    rewrite (denot_abs y) in I1; eauto.
    rewrite (denot_abs y) in I2; eauto.
    destruct x1; unfold In, Λ in I1; try done;
    destruct x2; unfold In, Λ in I2; try done.
    move: I1 => [I1 [Vl Cl]].
    move: I2 => [I2 [Vl0 Cl0]].
    destruct (dec_any l (DecSetList l) l0).
    destruct (dec_con x1 x2). eapply c_map2; eauto.
    ++ (* Domains are consistent, ranges are not. Should be a contradiction. *)
      have CS: ConsistentSets (mem l) (mem l0). admit.
      have V1:  valid_env (y ~ mem l ++ ρ1). econstructor; eauto. admit.
      have V2:  valid_env (y ~ mem l0 ++ ρ2). admit.
      move: (IH y ltac:(auto)) => h. 
      specialize (h (y ~ mem l ++ ρ1) (y ~ mem l0 ++ ρ2)). 
      have k9: Env.ForallT2 ConsistentSets (y ~ mem l ++ ρ1) (y ~ mem l0 ++ ρ2).
      econstructor; eauto.
      specialize (h ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      move: (h x1 x2 I1 I2) => C12.
      exfalso. eapply Consistent_Inconsistent_disjoint; eauto.
    ++ unfold InconsistentAnyList in i. 
       eapply c_map1; eauto.
  - (* nat *)
    unfold NAT in *. 
    destruct x1; try done.
    destruct x2; try done.
    inversion I1; inversion I2; subst; eauto.
  - (* ADD: need a lemma that ADD is consistent *) 
    destruct x1; try done.
    destruct x2; try done.
    destruct x1; try done.
    destruct x2; try done. 
    + move: I1 => [i1 [j1 [h1 m1]]].
      move: I2 => [i2 [j2 [h2 m2]]].
      destruct (eq_dec n n0).
      ++ subst. rewrite e. eauto.
      ++ admit.
    + move: I1 => [i1 [j1 [h1 m1]]].
      cbn in I2. 
      (* decide whether l0 and l are consistent. *)
      admit.
    + admit.
  - (* CONS: need a lemma about CONS *)
    admit.
Admitted.

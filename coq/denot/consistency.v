(* Consistency: when do two values approximate the result?

   Consistent: Value -> Value -> Prop
   Inconsistent: Value -> Value -> Prop
   
   dec_con : { Consistent x y } + { Inconsistent x y }

  ConsistentSets : P Value -> P Value -> Prop
     - all pairs of values in two sets are consistent

  ConsistentSet : P Value -> Prop
     - all pairs of values in the same set are consistent
     - diagonal of the above

  Main result here: Consistency is preserved by the operators.

  APPLY_ConsistentSets : forall w1 w2 w1' w2', 
    ConsistentSets w1 w1' -> 
    ConsistentSets w2 w2' -> 
    ConsistentSets (APPLY w1 w2) (APPLY w1' w2'). 

  denot_ConsistentSets :
     forall t ρ1 ρ2, Env.Forall2 ConsistentSets ρ1 ρ2 -> 
                     ConsistentSets (denot t ρ1) (denot t ρ2).

  Furthermore, the denotation function produces a consistent set

  denot_ConsistentSet :
     forall t ρ1 ρ2, Env.Forall ConsistentSet ρ1 -> 
                     ConsistentSet (denot t ρ1).

   

 *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.

Require Import denot.definitions.
Require Import denot.denot.
Require Import denot.valid_theory.


Import SetNotations.
Local Open Scope set_scope.


Definition consistent_env : Rho -> Type := Env.ForallT ConsistentSet. 

(* ------------------------------------------------- *)

Class ConsistencyTheory (A : Type) `{Consistency A} := 
  {  exclusive : forall x y, Consistent x y -> Inconsistent x y -> False ;
     decidable : forall x y, {Consistent x y} + {Inconsistent x y}
  }.

Definition Exclusive {A} (f g : A -> A -> Prop) :=  forall x y, f x y -> g x y -> False .
Definition Decidable {A} (f g : A -> A -> Prop) :=  forall x y, {f x y} + {g x y}.


Section List.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Lemma exclusive_list :
  Exclusive f g -> 
  Exclusive (@Consistent_list A f) (@Inconsistent_list A g).
Proof.
  intros efg. intros x y FF. 
  induction FF; intros EG; inversion EG; eauto.
  - inversion H.
  - move: (Forall2_length _ _ FF) => eq. 
    simpl in H0. rewrite eq in H0. done.
  - inversion H0; subst. eauto.
    eapply IHFF. right. eauto.
Qed.

Lemma exclusive_list2: forall l, 
  List.Forall (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, (@Consistent_list A f) l YS -> (@Inconsistent_list A g) l YS -> False.
Proof.
  induction l; intros h YS h1 h2.
  - inversion h1. subst. inversion h2. done.
    inversion H.
  - inversion h1. subst. inversion h. subst.
    specialize (IHl H4 l' H3).
    destruct h2. unfold Consistent_list in h1. 
    apply Forall2_length in h1. done.
    inversion H; subst; eauto.
    eapply IHl. right. auto.
Qed.    

Lemma decidable_list : 
  Decidable f g ->
  Decidable (@Consistent_list A f) (@Inconsistent_list A g).
Proof.
  intros dfg. intros x.
  induction x; intros y; destruct y.
  - left; eauto. econstructor.
  - right; eauto. left. done.
  - right; eauto. left. done.
  - destruct (IHx y). destruct (dfg a a0).
    left. econstructor; eauto.
    right. right. econstructor; eauto.
    right. destruct i. left. eauto. right. eauto.
Qed.

End List.

#[export] Instance Consistency_list_theory { A : Type } `{ ConsistencyTheory A } : ConsistencyTheory (list A) := 
  { exclusive := exclusive_list (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_list (f := Consistent)(g := Inconsistent) decidable ;
  }.

Section FSet.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.


Lemma exclusive_fset :
  Exclusive f g ->
  Exclusive (@Consistent_fset A f) (@Inconsistent_fset A g).
Proof.
  intros efg. intros x. destruct x as [x].
  induction x; intros y FF EG; destruct y as [y]; destruct y; 
    unfold Consistent_fset, List.Forall2_any in FF;
    unfold Inconsistent_fset, List.Exists2_any in EG.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h1.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h1.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h2.
  - destruct EG as [x0 [y0 [h1 [h2 gg]]]]. 
    specialize (FF x0 y0 h1 h2).
    eapply efg; eauto.
Qed.

Lemma decidable_fset :
  Decidable f g ->
  Decidable (@Consistent_fset A f) (@Inconsistent_fset A g).
Proof.
  intros dfg. intros x. destruct x as [x].
  induction x; intros y; destruct y as [y].
     unfold Consistent_fset, List.Forall2_any;
     unfold Inconsistent_fset, List.Exists2_any.
  - left. done.
  - destruct (IHx (FSet y)). 
    + simpl in c. simpl.
      induction y. unfold List.Forall2_any in c.
      left. intros x0 y0 h1 h2. inversion h2. 
      have CE: (List.Forall2_any f x y). { intros x0 y0 h1 h2. eapply c; eauto. simpl. eauto. }
      specialize (IHy CE). destruct IHy.
      ++ destruct (dfg a a0).
         left.
         { intros x0 y0 i1 i2.
           destruct i1; destruct i2; subst. 
           -- auto.
           -- apply f0; eauto. simpl; auto.
           -- apply c; eauto. simpl; auto.
           -- apply CE; eauto.
         }
         right.
         exists a. exists a0. simpl. split; auto.
      ++ right. destruct e as [x0 [y0 [h1 [h2 h3]]]].
         exists x0. exists y0. simpl. eauto.
    + right. destruct i as [x0 [y0 [i1 [i2 h]]]]. 
      exists x0. exists y0. 
      repeat split; try right; auto. 
Qed.

Lemma exclusive_fset2: forall l, 
  Forall_fset (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, (@Consistent_fset A f) l YS -> (@Inconsistent_fset A g) l YS -> False.
Proof.
  intro l. destruct l. 
  move=> h YS. destruct YS as [l']. simpl in *.
  move: h l'.
  induction l; intros h l' h1 h2;  unfold List.Forall2_any in h1; destruct h2 as [x0 [y0 [I0 [I1 IC]]]]. 
  - inversion I0.
  - inversion h. subst. 
    specialize (IHl H2).
    rewrite Forall_forall in H2.
    destruct I0; subst.
    -- specialize (h1 x0 y0 ltac:(left; auto) I1).
       eauto.
    -- eapply (IHl l').
       intros x1 y1 I3 I4. eapply  h1. right; eauto. eauto.
       exists x0. exists y0. repeat split; eauto.
Qed. 

(* Consistency is reflexive ?? *)

End FSet.

#[export] Instance ConsistencyTheory_fset { A : Type}  `{ ConsistencyTheory A } : ConsistencyTheory (fset A) := 
  { exclusive := exclusive_fset (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_fset (f := Consistent)(g := Inconsistent) decidable ;
  }.

Section Computations.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Lemma exclusive_Comp : 
  Exclusive f g ->
  Exclusive (@ConsistentComp A f) (@InconsistentComp A g).
Proof.
  intros efg x y CC IC.
  induction CC; inversion IC.
  eapply exclusive_list; eauto.
Qed.


Lemma exclusive_Comp2: forall l, 
  Comp.Forall (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, (@ConsistentComp A f) l YS -> (@InconsistentComp A g) l YS -> False.
Proof.
  destruct l. intros.
Admitted.

Lemma decidable_Comp : 
  Decidable f g ->
  Decidable (@ConsistentComp A f) (@InconsistentComp A g).
Proof.
  intros dfg x y.
  destruct x eqn:EX; destruct y eqn:EY.
  - left; econstructor.
  - right; econstructor.
  - right; econstructor.
  - destruct (decidable_list dfg l l0).
    left; econstructor; eauto.
    right; econstructor; eauto.
Qed.


End Computations.

#[export] Instance ConsistencyTheory_Comp { A : Type}  `{ ConsistencyTheory A } : ConsistencyTheory (Comp A) := 
  { exclusive := exclusive_Comp (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_Comp (f := Consistent)(g := Inconsistent) decidable ;
  }.


 
Fixpoint Value_ind' (P : Value -> Prop)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : fset Value) (c : Comp (fset Value)), 
           Forall_fset P l -> Comp.Forall (Forall_fset P) c -> P (v_map l c)) 
       (f : P v_fun)
       (l : (forall l : list Value, List.Forall P l -> P (v_list l)))
       (v : Value) : P v := 
  let rec := Value_ind' P n m f l  
  in
  let fix rec_list (vs : list Value) : List.Forall P vs :=
    match vs with 
    | nil => List.Forall_nil _
    | cons w ws => @List.Forall_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  let fix rec_fset (fs : fset Value) : Forall_fset P fs :=
    match fs with 
      | FSet xs => rec_list xs
    end in
  let fix rec_list_fset (vs : list (fset Value)) : List.Forall (Forall_fset P) vs :=
    match vs with 
    | nil => List.Forall_nil _
    | cons w ws => @List.Forall_cons (fset Value) (Forall_fset P) w ws (rec_fset w) (rec_list_fset ws)
    end
  in 

  let rec_comp (c : Comp (fset Value)) : Comp.Forall (Forall_fset P) c :=
    match c as c1 return Comp.Forall (Forall_fset P) c1 with 
    | c_wrong => I
    | c_multi vs => rec_list_fset _
    end
  in
  match v with 
  | v_nat k => n k
  | v_map X v => m X v (rec_fset X) (rec_comp v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  end.

Lemma Consistent_not_Inconsistent : Exclusive ConsistentValue InconsistentValue.
Proof.
  intros x.
  eapply Value_ind' with (P := fun x => forall y : Value, ConsistentValue x y -> InconsistentValue x y -> False).
  all: intros.
  all: try solve [inversion H; inversion H0; subst; done].
  + inversion H2; inversion H1; subst; clear H2 H1.
    all: try simpl in H3; try done.
    - clear H0 H7.
      inversion H9. subst. clear H9.
      inversion H5. subst. clear H5.
      inversion H11. subst. clear H11.
      simpl in *.
      rewrite Forall_forall in H.
      have IH: (Forall_fset (fun x0 : Value => forall y : Value, ConsistentValue x0 y -> InconsistentValue x0 y -> False) (FSet X1)).
      { unfold Forall_fset. rewrite Forall_forall. eapply H. }
      eapply (exclusive_fset2 (FSet X1) IH (FSet X0)); simpl; auto.
    - inversion H11. subst. clear H11.
      move: (@exclusive_Comp2 (fset Value)) => h.
      specialize h with (l := c) (YS:= r2).
      eapply h; try eassumption.
      destruct c; simpl in *; auto.
      eapply Forall_impl; eauto.
      intros.
      inversion H2. inversion H3. subst. inversion H11. inversion H13. subst.
      eapply exclusive_fset2; eauto.
  + inversion H0; subst. clear H0.
    inversion H1; subst. done.
    eapply exclusive_list2; eauto.
Qed.


(* We do the same thing for Value_rect *)



Fixpoint Value_rec' (P : Value -> Type)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : fset Value) (c : Comp (fset Value)), 
           ForallT_fset P l -> Comp.ForallT (ForallT_fset P) c -> P (v_map l c)) 
       (f : P v_fun)
       (l : (forall l : list Value, List.ForallT P l -> P (v_list l)))
       (v : Value) : P v := 
  let rec := Value_rec' P n m f l  
  in
  let fix rec_list (vs : list Value) : List.ForallT P vs :=
    match vs with 
    | nil => List.ForallT_nil _
    | cons w ws => @List.ForallT_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  let fix rec_fset (fs : fset Value) : ForallT_fset P fs :=
    match fs with 
      | FSet xs => rec_list xs
    end in
  let fix rec_list_fset (vs : list (fset Value)) : List.ForallT (ForallT_fset P) vs :=
    match vs with 
    | nil => List.ForallT_nil _
    | cons w ws => @List.ForallT_cons (fset Value) (ForallT_fset P) w ws (rec_fset w) (rec_list_fset ws)
    end
  in 

  let rec_comp (c : Comp (fset Value)) : Comp.ForallT (ForallT_fset P) c :=
    match c as c1 return Comp.ForallT (ForallT_fset P) c1 with 
    | c_wrong => I
    | c_multi vs => rec_list_fset _
    end
  in
  match v with 
  | v_nat k => n k
  | v_map X v => m X v (rec_fset X) (rec_comp v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  end.



(* ------------------------------------------------- *)
(* Consistent is a reflexive relation *)

Lemma Consistent_list_refl {A} `{Consistency A} {l : list A} :
  Forall (fun x : A => Consistent x x) l ->
  Consistent_list (f:= Consistent) l l.
Proof. 
  induction 1; econstructor; eauto.
Qed.

(* This is not necessarily true, if the fsets are not self consistent *)
Lemma Consistent_fset_refl {A} `{Consistency A} {l : fset A} :
 Forall_fset (fun x => Consistent x x) l ->
 Consistent_fset (f:=Consistent) l l.
Proof.
  destruct l.
  unfold Forall_fset.
  unfold Consistent_fset.
  intro h.
  rewrite Forall_forall in h.
Abort.

(* This is not necessarily true, if the fsets are not self consistent *)
#[export] Instance Consistent_Value_refl : Reflexive (@Consistent Value _).
Proof.
  intro x. cbn.
  eapply Value_ind' with (P := fun x => ConsistentValue x x).
  all: intros; eauto.
  - eapply c_map1.
    destruct l.
    eapply c_fset.
    admit.
    admit.
  - eapply c_list. eapply (@Consistent_list_refl _ Consistency_Value); eauto.
Abort.





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

(* 
Lemma ConsistentSets_Singleton_refl {x} : ConsistentSets ⌈ x ⌉ ⌈ x ⌉.
Proof. intros x1 x2 I1 I2. inversion I1. inversion I2. subst. reflexivity. Qed.
*)

Lemma ConsistentSets_mem : forall l1 l2, List.Forall2_any Consistent l1 l2 -> 
                                    ConsistentSets (mem (FSet l1)) (mem (FSet l2)).
Proof. intros l1 l2 h. unfold List.Forall2_any in h. intros x y I1 I2.
       eapply h; eauto using mem_In.
Qed.

(* ------------------------------------------------- *)
(* All of the Operations respect Consistency         *)
(* ------------------------------------------------- *)


(*
Lemma Λ_ConsistentSets : forall F1 F2,
  (forall D1 D2 : P Value,
       valid D1 -> valid D2 -> ConsistentSets D1 D2 -> ConsistentSets (F1 D1) (F2 D2)) ->
  ConsistentSets (Λ F1) (Λ F2).
Proof.
  intros F1 F2 IH x1 x2 I1 I2.
  destruct x1; unfold In, Λ in I1; try done;
  destruct x2; unfold In, Λ in I2; try done.
  move: I1 => [I1 VM].
  move: I2 => [I2 VM0].
  destruct (dec_any l (DecSetList l) l0).
  destruct (dec_con x1 x2). eapply c_map2; eauto.
  ++ (* Domains are consistent, ranges are not. Should be a contradiction. *)
    have CS: ConsistentSets (mem l) (mem l0). eauto using ConsistentSets_mem. 
    have C : ConsistentSets (F1 (mem l)) (F2 (mem l0)). 
    eapply IH; eauto using valid_mem_valid.
    specialize (C _ _ I1 I2).
    exfalso. eapply Consistent_not_Inconsistent; eauto.
  ++ unfold Exists2_any in *. 
     eapply c_map1; eauto.
Qed.


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
  assert False. eapply Consistent_not_Inconsistent; eauto. done.

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

Lemma CONS_ConsistentSets : forall w1 w2 w1' w2', 
    ConsistentSets w1 w1' -> 
    ConsistentSets w2 w2' -> 
    ConsistentSets (CONS w1 w2) (CONS w1' w2'). 
Proof.
  intros w1 w2 w1' w2' C1 C2.
  unfold ConsistentSets in *.
  intros x y h1 h2.
  destruct x; destruct y; try done.
  destruct l; destruct l0; try done.
  move: h1 => [h1 h3].
  move: h2 => [h2 h4].
  move: (C2 _ _ h3 h4) => h5. inversion h5. subst.
  eapply c_list.
  eapply Forall2_cons; eauto.
Qed.


Lemma NAT_ConsistentSets {i} : ConsistentSets (NAT i) (NAT i). 
Proof.
  unfold ConsistentSets.
  intros x1 x2 I1 I2.
  unfold NAT in *. 
  destruct x1; try done.
  destruct x2; try done.
  inversion I1; inversion I2; subst; eauto.
Qed.

Lemma ADD_ConsistentSets : ConsistentSets ADD ADD. 
Proof.
  unfold ConsistentSets.
  intros x1 x2 I1 I2.
  destruct x1; try done.
  destruct x2; try done.
  destruct x1; try done.
  destruct x2; try done. 
  3: destruct x2; try done.
  + (* results both nats *)
    move: I1 => [i1 [j1 [h1 m1]]].
    move: I2 => [i2 [j2 [h2 m2]]].
    destruct (eq_dec n n0).
    ++ subst. rewrite e. eauto.
    ++ have NE: not (i1 = i2 /\ j1 = j2).
       intros [e1 e2]. subst. done.
       eapply c_map1. unfold Exists2_any.
       exists (v_list (v_nat i1 :: v_nat j1 :: nil)).
       exists (v_list (v_nat i2 :: v_nat j2 :: nil)).
       split. eapply mem_In; auto.
       split. eapply mem_In; auto.
       eapply i_list_e.
       have: i1 <> i2 \/ j1 <> j2. lia.
       move=> [e1|e2]. 
       eapply List.Exists2_cons1. eapply i_head. simpl. intro h. inversion h. done.
       eapply List.Exists2_cons2.
       eapply List.Exists2_cons1. eapply i_head. simpl. intro h. inversion h. done.
  + (* results are nat / wrong *)
    move: I1 => [i1 [j1 [h1 m1]]].
    cbn in I2. 
    move: I2 => [I2 [NE vm2]].
    (* decide whether l0 and l are consistent. *)
    destruct (dec_any l (DecSetList l) l0).
    ++ (* contradiction *)
      unfold Forall2_any in f.
      destruct l0; try done.
      exfalso. eapply I2. 
      apply mem_In in h1.
      specialize (f (v_list (v_nat i1 :: v_nat j1 :: nil)) v h1 ltac:(econstructor;eauto)).
      inversion f. subst. inversion H0. subst. inversion H4. subst. inversion H6. subst.
      clear H0 H4 H6.
      inversion H2. inversion H3. clear H2 H3. subst.
      exists i1. exists j1. cbv. left. auto.
    ++ eapply c_map1. unfold Exists2_any in *. auto.
  + (* results are wrong / nat *)
    move: I2 => [i1 [j1 [h1 m1]]].
    cbn in I1. 
    move: I1 => [I1 [NE vm1]].
    (* decide whether l0 and l are consistent. *)
    destruct (dec_any l (DecSetList l) l0).
    ++ (* contradiction *)
      unfold Forall2_any in f.
      destruct l; try done.
      exfalso. eapply I1. 
      apply mem_In in h1.
      specialize (f v (v_list (v_nat i1 :: v_nat j1 :: nil)) ltac:(econstructor;eauto) h1).
      inversion f. subst. inversion H1. inversion H4. inversion H8. inversion H9. inversion H3. subst.
      clear H1 H3 H4 H8 H9.
      exists i1. exists j1. cbv. left. auto.
    ++ eapply c_map1. unfold Exists2_any in *. auto.
  + (* results both wrong *) 
    eapply c_map2. auto.
Qed.




Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).

Import LCNotations.
Import EnvNotations.

Lemma access_ConsistentSets : forall ρ1 ρ2 x,
    Env.Forall2 ConsistentSets ρ1 ρ2 ->
    ConsistentSets (ρ1 ⋅ x) (ρ2 ⋅ x).
Proof.
  intros.
  induction H.
  simpl. 
  ++ eapply ConsistentSets_Singleton_refl.
  ++ simpl. destruct (x == x0) eqn:E; auto. 
Qed.

Lemma denot_ConsistentSets :
  forall t ρ1 ρ2, Env.Forall2 ConsistentSets ρ1 ρ2 -> 
             ConsistentSets (denot t ρ1) (denot t ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ1 ρ2 CR. (* VR1 VR2. *)
  all: autorewrite with denot.
  all: intros x1 x2 I1 I2.
  all: try solve [inversion I1; inversion I2; eauto].

  - (* var *) 
    eapply access_ConsistentSets; eauto.

  - (* app *)
    specialize (IH1 ρ1 ρ2 ltac:(eauto)). 
    specialize (IH2 ρ1 ρ2 ltac:(eauto)). 
    eapply (APPLY_ConsistentSets _ _ _ _ IH1 IH2); eauto.

  - (* abs *)
    pick fresh y.
    rewrite (denot_abs y) in I1; eauto.
    rewrite (denot_abs y) in I2; eauto.

    have: forall D1 D2, 
        valid D1 ->
        valid D2 -> 
        ConsistentSets D1 D2 ->
        ConsistentSets (denot (t' ^ y) (y ~ D1 ++ ρ1)) (denot (t' ^ y) (y ~ D2 ++ ρ2)).
    { 
      intros.
      eapply IH; eauto.
    } clear IH. move=> IH.
    
    eapply Λ_ConsistentSets. apply IH. eapply I1. eapply I2. 

  - (* nat *)
    eapply NAT_ConsistentSets; eauto.

  - (* ADD *) 
    apply ADD_ConsistentSets; eauto.

  - (* CONS *)
    specialize (IH2 _ _ CR). 
    specialize (IH1 _ _ CR). 
    eapply (CONS_ConsistentSets _ _ _ _ IH1 IH2); eauto.
Qed.

Lemma denot_ConsistentSet :
     forall t ρ, Env.Forall ConsistentSet ρ  -> ConsistentSet (denot t ρ).
Proof.
  intros.
  rewrite Env.Forall_Forall2 in H.
  eapply denot_ConsistentSets. auto.
Qed.

*)

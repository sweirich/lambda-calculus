
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Labels                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Set Implicit Arguments.

Declare Scope label_scope.
Delimit Scope label_scope with label.
Open Scope label_scope.

Inductive label (A : Type) : Type := 
   | Bot : label                   (* unfinished *)
   | Top : label                   (* Returned value *)
   | Br  : label -> label -> label   (* sequenced choices *)
   | L   : label -> label           (* inside a left choice *)
   | R   : label -> label           (* inside a right choice *)
.

Module Label.

  Fixpoint compare (l m : label) : comparison := 
    match l , m with 
    | Bot  , Bot  => Eq
    | Bot  , _    => Lt
    | _    , Bot  => Gt

    | L l0 , L m0 => compare l0 m0
    | R l0 , R m0 => compare l0 m0 
    | L _  , R _  => Lt
    | R _ , L _   => Gt

    | Top , Top => Eq

    | Br l1 l2 , Br l3 l4 => 
        match compare l1 l3 with
        | Eq => compare l2 l4
        | o  => o
        end

    (* these don't matter, we only compare comparable things *)
    | L _ , _  => Lt
    | _   , L _  => Gt
    | Top , _ => Lt
    | _   , Top => Gt
    | Br _ _ , _ => Lt
    | _   , Br _ _ => Gt
   
    end.

  Fixpoint comparable (l1 l2 : label) : bool :=
    match l1 , l2 with 
    | Bot  , _    => true
    | _    , Bot  => true
    | L l0 , L m0 => comparable l0 m0
    | R l0 , R m0 => comparable l0 m0 
    | L _  , R _  => true
    | R _ , L _   => true
    | Top , Top => true
    | Br l1 l2 , Br l3 l4 => comparable l1 l3 && comparable l2 l4
    | _ , _ => false
    end.

  Definition eqb l m : bool := 
    match compare l m with 
    | Eq => true
    | _ => false
    end.

  Definition ltb l m : bool := 
    match compare l m with 
    | Lt => true
    | _ => false
    end.

  Definition leb l m : bool := 
    match compare l m with 
    | Lt => true
    | Eq => true
    | _ => false
    end.


  (* During computation, a partial result have label "Bot". However, 
     if we give the evaluator more fuel, the expression may make 
     choices, so the label will grow more structure.

          Bot ⊑ L Bot
              ⊑ L (R Bot) 
              ⊑ L (R (Bot ⋈ Bot))
              ⊑ L (R (L Bot ⋈ Bot))
              ⊑ L (R (L Bot ⋈ R Bot))
   *)
  
  Fixpoint approxb (l1 l2 : label) : bool := 
    match l1 , l2 with 
    | Bot , _  => true
    | Top , Top => true 
    | L l0 , L l1 => approxb l0 l1 
    | R l0 , R l1 => approxb l0 l1 
    | Br l1 l2 , Br l3 l4 => approxb l1 l3 && approxb l2 l4
    | _ , _ => false
    end.

  Lemma approxb_refl : forall l, approxb l l = true.
  Proof. induction l; eauto. simpl. rewrite IHl1. rewrite IHl2. auto. Qed.

  Lemma approxb_trans : forall l2 l1 l3, 
      approxb l1 l2 = true -> approxb l2 l3 = true -> approxb l1 l3 = true.
  Proof. induction l2. all: intros l1 l3. 
         all: destruct l1; destruct l3.
         all: simpl; intros h1 h2; try done. 

         all: try (apply andb_prop in h1; move: h1 => [h1 h1']).
         all: try (apply andb_prop in h2; move: h2 => [h2 h2']).

         all: try (apply andb_true_intro; split; eauto 3).
         eauto.
         eauto.
  Qed.



  (* comparison relations *)
  Definition lt (l m : label) : Prop := ltb l m = true.
  Definition le (l m : label) : Prop := leb l m = true.
  Definition eq (l m : label) : Prop := eqb l m = true.
  Definition approx (l m : label) : Prop := approxb l m = true.

Lemma approx_refl : forall x, approx x x.
Proof. intros x. unfold approx. eapply approxb_refl. Qed.
 
Lemma approx_trans l1 l2 l3 : Label.approx l1 l2 -> Label.approx l2 l3 -> Label.approx l1 l3.
Proof. unfold Label.approx.  intros. eapply Label.approxb_trans; eauto. Qed.


Lemma compare_refl: forall x, compare x x = Eq.
Proof. induction x; simpl; eauto.
       rewrite IHx1. rewrite IHx2. done.
Qed.


Lemma compare_eq : forall x y, compare x y = Eq <-> x = y.
Proof. 
intros x y.
split.
- move: y. 
  induction x; intros y; destruct y.
  all: simpl.
  all: try done.
  all: try (destruct (compare x1 y1) eqn:c1).
  all: intro c2.
  all: try done.
  all: try rewrite (IHx1 y1); auto. 
  all: try rewrite (IHx2 y2); auto. 
  all: try rewrite (IHx y); auto. 
- move: y. induction x; intros y; destruct y.
  all: simpl.
  all: try done.
  all: try (destruct (compare x1 y1) eqn:c1).
  all: intro c2.
  all: try (inversion c2; subst; clear c2).
  all: try rewrite (IHx1 y1); auto. 
  all: rewrite IHx1 in c1; auto.
Qed.


  Lemma eq_eq : forall x y, eq x y <-> x = y.
    intros x y. unfold eq. unfold eqb.
    destruct (compare x y) eqn:h.
    all: try rewrite compare_eq in h; subst.
    all: intuition.
    all: try done.
    subst. rewrite compare_refl in h. done.
    subst. rewrite compare_refl in h. done.
  Qed.
      

Lemma compare_transitive: forall y x z o, 
    compare x y = o -> compare y z = o -> compare x z = o.
Proof. 
  move=> y. induction y; intros x z o h1 h2.
  all: destruct x; destruct z; simpl in *; subst; auto.
  all: try solve [inversion h2; auto].
  destruct (compare y1 z1) eqn: c1;
  destruct (compare x1 y1) eqn: c2.
  all: try (rewrite compare_eq in c1; subst).
  all: try (rewrite compare_eq in c2; subst).
  all: try (rewrite compare_refl).
  all: try rewrite c2; auto.
  all: try rewrite c1; auto.
  all: try solve [inversion h2].
  + erewrite IHy1 with (o := Lt); auto.
  + erewrite IHy1 with (o := Gt); auto.
Qed.

Lemma compare_antisymmetry : 
  forall x, (forall y, compare x y = Lt <-> compare y x = Gt).
Proof. intros x. induction x.
       all: intros y. 
       all: split.
       all: intros h.
       all: destruct y eqn:Ey; try (simpl in h; done).
       - simpl.
         simpl in h. 
         destruct (compare l1 x1) eqn:h1.
         rewrite compare_eq in h1. subst.
         rewrite compare_refl in h. eauto.
         eapply IHx2; eauto.
         destruct (compare x1 l1) eqn:h2.
         rewrite compare_eq in h2. subst. 
         rewrite compare_refl in h1. done. 
         eapply IHx1 in h2. rewrite h2 in h1. done.
         move: (IHx1 l1) => [IH1 IH1']. done. 
         move: (IHx1 l1) => [IH1 IH1'].  apply IH1' in h1.
         rewrite h1 in h. done.
       - simpl in *.
         destruct (compare x1 l1) eqn: h1; try done.
         + rewrite compare_eq in h1. subst.
           rewrite compare_refl in h. rewrite IHx2. done.
         + destruct (compare l1 x1) eqn:h2.
           rewrite compare_eq in h2. subst.
           rewrite compare_refl in h1. done.
           done. 
           rewrite <- IHx1 in h2. rewrite h2 in h1. done.

       - simpl. simpl in h. rewrite IHx in h. done.
       - simpl. simpl in h. rewrite IHx. done.
       - simpl in *. rewrite IHx in h. done.
       - simpl in *. rewrite IHx. done.
Qed.


Lemma ltb_irreflexive: forall x, not (ltb x x = true).
intros x. unfold ltb. rewrite compare_refl. done.
Qed.

Lemma ltb_transitive : forall x y z, ltb x y = true -> ltb y z = true -> ltb x z = true.
intros x y z. unfold ltb. 
destruct (compare x y) eqn:h1; intro h; try discriminate; clear h.
destruct (compare y z) eqn:h2; intro h; try discriminate; clear h.
move: (compare_transitive _ _ _ h1 h2) => h3. rewrite h3. done.
Qed.


  Lemma lt_irreflexive: forall x, not (lt x x).
    intros x. unfold lt, ltb. rewrite compare_refl. done.
  Qed.

  Lemma lt_transitive: forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z. unfold lt, ltb.
    destruct (compare x y) eqn:h1;
    destruct (compare y z) eqn:h2;
    destruct (compare x z) eqn:h3.
    all: try solve [intuition].
    +  move: (compare_transitive _ _ _ h1 h2) => h4.
       rewrite h3 in h4. done.
    +  move: (compare_transitive _ _ _ h1 h2) => h4.
       rewrite h3 in h4. done.
  Qed.


Lemma leb_L l1 l1'  :
  leb (L l1) (L l1') = true <->
    leb l1 l1' = true.
Proof.
  split; unfold leb; simpl.
  all: destruct (compare l1 l1') eqn:E1.
  all: try done.
Qed.
  
Lemma leb_R l1 l1'  :
  leb (R l1) (R l1') = true <->
    leb l1 l1' = true.
Proof.
  split; unfold leb; simpl.
  all: destruct (compare l1 l1') eqn:E1.
  all: try done.
Qed.

Lemma leb_Br l1 l1' l2 l2'  :
  leb (Br l1 l2) (Br l1' l2') = true <->
    ((ltb l1 l1' = true) \/ (l1 = l1' /\ leb l2 l2' = true)).
Proof.
  split.
  -  unfold leb, ltb; simpl.
     all: destruct (compare l1 l1') eqn:E1.
     all: destruct (compare l2 l2') eqn:E2.
     all: try solve [intuition].
     all: intro h1; right; rewrite compare_eq in E1; split; auto.
  - intros [h1|h1]; unfold leb, ltb; simpl.
    all: destruct (compare l1 l1') eqn:E1.
    all: destruct (compare l2 l2') eqn:E2.
    all: try solve [intuition].
    all: try rewrite compare_eq in E1; subst. 
    all: try rewrite compare_eq in E2; subst. 
    all: try move: (ltb_irreflexive l1') => h; try done.
    all: unfold ltb in h1. 
    all: try solve [destruct (compare l1 l1'); try done].
    all: try move: h1 => [E h1]; subst.
    all: unfold leb in h1. 
    all: try solve [destruct (compare l2 l2'); try done].
    rewrite compare_refl in E1. done.
    rewrite compare_refl in E1. done.
Qed.

  Lemma le_transitive :  forall y x z, 
      le x y -> le y z -> le x z.
  Proof. 
    intros y; induction y; intros x z h1 h2.
    all: destruct x; destruct z; simpl.
    all: try done.
    - unfold le in *. rewrite leb_Br.
      repeat rewrite leb_Br in h1, h2.
      destruct h1 as [h1 | [-> h1]];
        destruct h2 as [h2 | [-> h2]].
      left. unfold ltb in *.
      destruct (compare x1 y1) eqn:E1; destruct (compare y1 z1) eqn:E2; 
        destruct (compare x1 z1) eqn:E3.
      all: try intuition.
      rewrite compare_eq in E3. subst.
      move: (compare_transitive _ _ _ E1 E2) => h. rewrite compare_refl in h. done.
      move: (compare_transitive _ _ _ E1 E2) => h. rewrite h in E3. done.
    - unfold le in *. repeat rewrite leb_L in h1, h2. rewrite leb_L. eauto.
    - unfold le in *. repeat rewrite leb_R in h1, h2. rewrite leb_R. eauto.       
  Qed.


Lemma approxb_leb : forall l1 l2, 
    Label.approxb l1 l2 = true -> Label.leb l1 l2 = true.
Proof. 
  induction l1; intros l2; destruct l2; simpl.
    all: try done.
    - rewrite -> Bool.andb_true_iff.
      intros [h1 h2].
      apply IHl1_1 in h1.
      apply IHl1_2 in h2.
      unfold Label.leb in h1, h2.
      destruct (Label.compare l1_1 l2_1) eqn:E1.
      destruct (Label.compare l1_2 l2_2) eqn:E2.
      all: try done.
      all: try rewrite Label.compare_eq in E1.
      all: try rewrite Label.compare_eq in E2.
      all: subst.
      ++ unfold Label.leb. rewrite Label.compare_refl. auto.
      ++ unfold Label.leb. simpl. rewrite Label.compare_refl. rewrite E2. auto.
      ++ unfold Label.leb. simpl. rewrite E1.
         destruct (Label.compare l1_2 l2_2) eqn:E2; try done.
    - intro h. apply IHl1 in h.
      unfold Label.leb in *. simpl. auto.
    - intro h. apply IHl1 in h.
      unfold Label.leb in *. simpl. auto.
  Qed.


  Lemma approxb_le : forall l1 l2, 
      approxb l1 l2 = true -> Label.le l1 l2.
  Proof. intros. unfold Label.le. eapply Label.approxb_leb. auto. Qed.

Lemma leb_antisymmetry k1 k2 : 
  Label.leb k1 k2 = true -> Label.leb k2 k1 = true -> k1 = k2.
Proof. 
  unfold leb.
Admitted.

End Label.

Module LabelNotation.
Infix "⋈" := Br (at level 70, right associativity) : label_scope.
Infix "=?" := Label.eqb (at level 70) : label_scope.
Infix "<=?" := Label.leb (at level 70) : label_scope.
Infix "<?" := Label.ltb (at level 70) : label_scope.
Infix "<=" := Label.le (at level 70) : label_scope.
Infix "<" := Label.lt (at level 70) : label_scope.
Infix "⊑" := Label.approx (at level 70) : label_scope.
End LabelNotation.
  
Instance LtStrict : StrictOrder (fun x y : label => (Label.ltb x y) = true).
constructor.
- intros l h. eapply Label.ltb_irreflexive; eauto.
- intros x y z. eapply Label.ltb_transitive; eauto.
Qed.



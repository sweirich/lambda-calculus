Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Require structures.Option.
Require Import structures.Sets.
Require Import structures.Monad.
Require structures.Vector.

(* autosubst2 "generated" syntax *)
Require Import fintype.
Require Import verse.syntax.
Require verse.notations.

Open Scope bool_scope.

Set Implicit Arguments.

(* This file defines a "denotational" semantics for Verse.

   W* == (label * option W) -> Prop

   The label records which branch of an "Or" we are in
   The option records whether that branch diverges or not
   If a branch fails, that label will not be in the set

   NOTE: In Coq, the type A -> Prop represents a set of "A"s. In 
   this semantics, we have an invariant that for any l, there is at most *one*
   x in the set. So really instead of a set of values, we have 
   a partial mapping of labels to values.

   W* == Set of (label * option W) 

   Can we capture this invariant in the type some how? I'm not sure

     o  W* == label -> option A   
 
        is not the same because it requires a deciable function, not a relation

     o  W* == label -> option W -> Prop 

        doesn't enforce the invariant, because it is just currying the above

     o  W* == { S : P (label * option W) | partial_function S }

        enforces invariant but is annoying to work with

*)

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Labels                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Module Label.

Declare Scope label_scope.
Delimit Scope label_scope with label.
Open Scope label_scope.

Create HintDb label.

Inductive label : Type := 
   | Bot : label                   (* computation in progress *)
   | Br  : label -> label -> label   (* sequenced choices *)
   | L   : label -> label           (* inside a left choice *)
   | R   : label -> label           (* inside a right choice *)
.

Fixpoint hasBot (l : label) :=
  match l with 
  | Bot => true
  | Br l1 l2 => hasBot l1 || hasBot l2
  | L l => hasBot l 
  | R l => hasBot l
  end.

Module Label.

  (* --------------- lexicographic comparison ----------------- *)

  (* Compare two labels lexicographically *)
  Fixpoint compare (l m : label) : comparison := 
    match l , m with 
    | L l0 , L m0 => compare l0 m0
    | R l0 , R m0 => compare l0 m0 
    | L _  , R _  => Lt
    | R _ , L _   => Gt

    | Top, Top => Eq
    | Bot , Bot => Eq

    | Br l1 l2 , Br l3 l4 => 
        match compare l1 l3 with
        | Eq => compare l2 l4
        | o => o
        end

    (* these don't matter, we will only compare comparable things *)
    | Bot , _ => Lt
    | _   , Bot => Gt
    | L _ , _  => Lt
    | _   , L _  => Gt
    | Br _ _ , _ => Lt
    | _   , Br _ _ => Gt
   
    end.

  (* All labels in an set will be 'comparable' *)
  Fixpoint comparable (l1 l2 : label) : bool :=
    match l1 , l2 with 
    | L l0 , L m0 => comparable l0 m0
    | R l0 , R m0 => comparable l0 m0 
    | L _  , R _  => true
    | R _ , L _   => true
    | Bot , Bot => true
    | Top , Top => true
    | Br l1 l2 , Br l3 l4 => comparable l1 l3 && comparable l2 l4
    | _ , _ => false
    end.

  (* alternative definition we would like to have. *)
  (*
  Inductive glabel : label -> Type := 
    | GL : forall {l r}, ((r = L l) \/ (r = Bot)) -> glabel l -> glabel r
    | GR : forall {l r}, ((r = L l) \/ (r = Bot)) -> glabel l -> glabel r
    | GT : glabel Bot
    | GBr : forall {l1 l2}, glabel l1 -> glabel l2 -> glabel (Br l1 l2)
  .

  Fixpoint gcompare {l} (g1 g2 : glabel l) : comparison := 
    match g1 , g2 with 
    | GL _ l0 , GL _ m0 => gcompare l0 m0
    | GR _ l0 , GR _ m0 => gcompare l0 m0 
    | GL _ _  , GR _ _  => Lt
    | GR _ _ , GL _ _   => Gt
    | GT , GT => Eq
    | GBr l1 l2 , GBr l3 l4 => 
        match gcompare l1 l3 with
        | Eq => gcompare l2 l4
        | o => o
        end
    end.
    *)

  (* boolean valued comparison functions *)
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

  (* comparison relations *)
  Definition lt (l m : label) : Prop := ltb l m = true.
  Definition le (l m : label) : Prop := leb l m = true.
  Definition eq (l m : label) : Prop := eqb l m = true.

  (* properties *)

  Lemma compare_refl: forall x, compare x x = Eq.
  Proof. induction x.
         cbv. done. 
         simpl. rewrite IHx1. rewrite IHx2. done.
         simpl; auto.
         simpl; auto.
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
      all: destruct (compare x2 y2); try done.
    - move: y. induction x; intros y; destruct y.
      all: simpl.
      all: try done.
      all: try (destruct (compare x1 y1) eqn:c1).
      all: intro c2.
      all: try (inversion c2; subst; clear c2).
      all: try rewrite (IHx1 y1); auto. 
      all: rewrite IHx1 in c1; auto.
      all: try done.
  Qed.
  
  Lemma eq_eq : forall x y, eq x y <-> x = y.
    intros x y. unfold eq. unfold eqb.
    destruct (compare x y) eqn:h.
    all: try rewrite compare_eq in h; subst.
    all: intuition.
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

  (* < is a strict order *)
 
  Lemma ltb_irreflexive: forall x, not (ltb x x = true).
    intros x. unfold ltb. rewrite compare_refl. done.
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

  (* <= is a partial order  *)

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
   
  (* --------- approx : information ordering of labels ---------- *)

  (* During computation, a partial result will have label "Bot". However, 
     if we give the evaluator more fuel, the expression may make 
     choices, so the label will grow more structure.

          Bot ⊑ L Bot
              ⊑ L (R Bot) 
              ⊑ L (R (Bot ⋈ Bot))
              ⊑ L (R (L Bot ⋈ Bot))
              ⊑ L (R (L Bot ⋈ R Bot))
   *)
  Fixpoint approx (l1 l2 : label) : bool := 
    match l1 , l2 with 
    | Bot , _ => true 
    | L l0 , L l1 => approx l0 l1 
    | R l0 , R l1 => approx l0 l1 
    | Br l1 l2 , Br l3 l4 => approx l1 l3 && approx l2 l4            
    | _ , _ => false
    end.


  Lemma approx_refl : forall l, approx l l = true.
  Proof. induction l; eauto. simpl. rewrite IHl1. rewrite IHl2. auto. Qed.

  Lemma approx_trans : forall l2 l1 l3, 
      approx l1 l2 = true -> approx l2 l3 = true -> approx l1 l3 = true.
  Proof. induction l2. all: intros l1 l3. 
         all: destruct l1; destruct l3.
         all: simpl; intros h1 h2; try done. 
         all: try (apply andb_prop in h1; move: h1 => [h1 h1']).
         all: try (apply andb_prop in h2; move: h2 => [h2 h2']).
         all: try (apply andb_true_intro; split; eauto 3).
         eauto.
         eauto.
  Qed.

  Hint Resolve approx_refl approx_trans : label.
  Hint Rewrite approx_refl : label.




  Lemma approx_leb : forall l1 l2, 
      approx l1 l2 = true -> leb l1 l2 = true.
  Proof. 
    induction l1; intros l2; destruct l2; simpl.
    all: try done.
    - rewrite -> Bool.andb_true_iff.
      intros [h1 h2].
      apply IHl1_1 in h1.
      apply IHl1_2 in h2.
      unfold leb in h1, h2.
      destruct (compare l1_1 l2_1) eqn:E1.
      destruct (compare l1_2 l2_2) eqn:E2.
      all: try done.
      all: try rewrite compare_eq in E1.
      all: try rewrite compare_eq in E2.
      all: subst.
      ++ unfold leb. rewrite compare_refl. auto.
      ++ unfold leb. simpl. rewrite compare_refl. rewrite E2. auto.
      ++ unfold leb. simpl. rewrite E1.
         destruct (compare l1_2 l2_2) eqn:E2; try done.
    - intro h. apply IHl1 in h.
      unfold leb in *. simpl. auto.
    - intro h. apply IHl1 in h.
      unfold leb in *. simpl. auto.
  Qed.

  Lemma approx_le : forall l1 l2, 
      approx l1 l2 = true -> le l1 l2.
  Proof. intros. unfold le. eapply approx_leb. auto. Qed.
 

  Lemma comparable_approx :
    forall a b, comparable a b = true -> approx a b = true -> a = b.
  Proof.
    induction a; intros b; destruct b; simpl.
    all: try done.
    + repeat rewrite Bool.andb_true_iff.
      move => [h1 h2] [h3 h4].
      erewrite IHa1; eauto.
      erewrite IHa2; eauto.
    + intros h1 h2. erewrite IHa; eauto.
    + intros h1 h2. erewrite IHa; eauto.
  Qed.

  
  Lemma comparable_preapprox :
    forall b a1 a2, comparable a1 a2 = true -> 
               approx a1 b = true ->
               approx a2 b = true -> 
               a1 = a2.
  Proof.
    induction b.
    all: intros a1 a2; destruct a1; destruct a2; simpl.
    all: try done.
    + repeat rewrite Bool.andb_true_iff.
      move => [h1 h2] [h3 h4] [h5 h6].
      move: (IHb1 _ _ h1 h3 h5) => h7.
      move: (IHb2 _ _ h2 h4 h6) => h8.
      f_equal; auto.
    + intros h1 h2 h3. 
      f_equal. eapply IHb; eauto.
    + intros h1 h2 h3.
      f_equal. eapply IHb; eauto.
  Qed.


  Lemma approx_Br l1 l1' l2 l2' :
    approx (Br l1 l2) (Br l1' l2') = true <->
      approx l1 l1' = true /\ approx l2 l2' = true.
  Admitted.
  
  Lemma approx_L l1 l1'  :
    approx (L l1) (L l1') = true <->
      approx l1 l1' = true.
  Admitted.

  Lemma approx_R l1 l1'  :
    approx (R l1) (R l1') = true <->
      approx l1 l1' = true.
  Admitted.

  Hint Resolve Label.approx_Br Label.approx_L Label.approx_R : label.

End Label.


(* eq is an equivalence relation *)
Instance eq_refl : Reflexive Label.eq.
intros x. rewrite Label.eq_eq. done.
Defined.

Instance eq_trans : Transitive Label.eq.
intros x y z. 
repeat rewrite Label.eq_eq. intuition; subst; auto.
Qed.

Instance lt_strict : StrictOrder Label.lt.
split. 
- intros x. unfold complement. eapply Label.lt_irreflexive; eauto.
- exact Label.lt_transitive. 
Defined.

Lemma lt_asymmetry : forall x y, Label.lt x y -> Label.lt y x -> False. 
  intros x y. eapply asymmetry.
Qed.

Instance PO_le : PreOrder Label.le.
split. 
- intros x. unfold Label.le, Label.leb. rewrite Label.compare_refl. auto.
- intros x y z. eapply Label.le_transitive; eauto.
Defined. 

Lemma le_antisymmetry : forall x y, Label.le x y -> Label.le y x -> x = y.
Proof.
  intros x y. unfold Label.le, Label.leb.
  destruct (Label.compare x y) eqn:E1;
    destruct (Label.compare y x) eqn:E2.
  all: try rewrite Label.compare_eq in E1.
  all: try rewrite Label.compare_eq in E2.
  all: subst.
  all: try done.
  assert False. eapply (@Label.lt_asymmetry x y); unfold Label.lt, Label.ltb; 
    try rewrite E1; try rewrite E2; eauto.
  done.
Qed.



Module LabelNotation.
Infix "⋈" := Br (at level 70, right associativity) : label_scope.
Infix "=?" := Label.eqb (at level 70) : label_scope.
Infix "<=?" := Label.leb (at level 70) : label_scope.
Infix "<?" := Label.ltb (at level 70) : label_scope.
Infix "<=" := Label.le (at level 70) : label_scope.
Infix "<" := Label.lt (at level 70) : label_scope.
Infix "⊑" := Label.approx (at level 70) : label_scope.
End LabelNotation.

Import LabelNotation.

(* If two comparable labels approx the same label, then 
   they are equal *)
Lemma eq_preserving : forall l2 l1 l1',
  Label.comparable l1 l1' = true ->
  l1 ⊑ l2 = true -> l1' ⊑ l2 = true -> l1 = l1'.
Proof. 
  intros l2. induction l2; intros l1 l1' hc h2 h3.
  + destruct l1; try done.
    destruct l1'; cbv in h3; try done.
  + (* l2 is l2_1 ⋈ l2_2 *)
    destruct l1; try done.
    destruct l1'; cbn in hc; try done. 
    (* l1 is l1_1 ⋈ l1_2 *)
    simpl in h2.
    eapply Bool.andb_true_iff in h2. move: h2 => [h21 h22].
    destruct l1'; cbn in h3; try done.  
    eapply Bool.andb_true_iff in h3. move: h3 => [h31 h32].
    simpl in hc.
    eapply Bool.andb_true_iff in hc. move: hc => [hc1 hc2].
    specialize (IHl2_1 l1_1 l1'1). rewrite IHl2_1; eauto.
    specialize (IHl2_2 l1_2 l1'2). rewrite IHl2_2; eauto.
  + (* l2 is L l2 *)
    destruct l1; try done.
    destruct l1'; cbn in hc; try done. 
    (* l1 is L l1 ⋈ l1_2 *)
    simpl in h2.
    destruct l1'; cbn in h3; try done.  
    simpl in hc.
    f_equal. eauto.
  + (* l2 is R l2 *)
    destruct l1; try done.
    destruct l1'; cbn in hc; try done. 
    (* l1 is R l1 ⋈ l1_2 *)
    simpl in h2.
    destruct l1'; cbn in h3; try done.  
    simpl in hc.
    f_equal. eauto.
Qed.

(* strictly ordered labels are approximated by 
   strictly ordered labels *)
Lemma order_preserving : forall l2 l2' l1 l1',
  Label.comparable l1 l1' = true ->
  Label.comparable l2 l2' = true ->
  l2 < l2' -> l1 ⊑ l2 = true -> l1' ⊑ l2' = true -> l1 < l1'.
Proof. 
  intros l2. induction l2; intros l2' l1 l1' hc1 hc2 h1 h2 h3.
  + destruct l1; try done.
    destruct l1'; eauto.
    destruct l2'; eauto.
  + (* l2 is l2_1 ⋈ l2_2 *)
    destruct l1; try done.
    ++ (* l1 is Bot *)
      destruct l1'; cbn in hc1; try done. 
       (* l1' is Bot *)
Abort.
(* Lemma is not true when l1 and l1' are Bot. By backing 
   up the approximation, we can lose the distinction between 
   l2 and l2'. *)
    

(* If ordered labels are approximated by ordered labels *)
Lemma order_preserving : forall l2 l2' l1 l1',
  Label.comparable l1 l1' = true ->
  l2 <= l2' -> l1 ⊑ l2 = true -> l1' ⊑ l2' = true -> l1 <= l1'.
Proof. 
  intros l2. induction l2; intros l2' l1 l1' hc h1 h2 h3.
  + destruct l1; try done.
    destruct l1'; eauto.
  + (* l2 is l2_1 ⋈ l2_2 *)
    destruct l1; try done.
    destruct l1'; eauto.
    (* l1 is l1_1 ⋈ l1_2 *)
    simpl in h2.
    eapply Bool.andb_true_iff in h2. move: h2 => [h21 h22].
    destruct l2'; try done.
    ++ (* l2' is l2'1 ⋈ l2'2 *)
      unfold Label.le in h1.
      rewrite Label.leb_Br in h1.
      destruct l1'; try done. 
      (* l1' is l1'1 ⋈ l1'2 *)
      cbn in h3.
      eapply Bool.andb_true_iff in h3. move: h3 => [h31 h32].
      (* how are l2 and l2' related? *)
      destruct h1.
      ++++  (*  l2_1 < l2_2 *)    
            (* eg: L Bot ⋈ R Bot < R Bot ⋈ L Bot *)
        (* then l1 could be     Bot ⋈ R Bot 
           and  l1' could be    Bot ⋈ L Bot 
           so the two labels could swap orderings as we 
           gain more information during the computation.

           This is unfortunate because it wouldn't happen 
           in practice due to the strictness of ;
           we will completely evaluate the first side 
           before we start evaluating the second side.

           would it help to have a "bot" label for 
           computation that isn't finished yet? then 
           we can equate Bot ⋈ R Bot and Bot ⋈ L Bot
           instead of ordering them.

           or is there a better behaved Br label?

           or could we drop the Br labels?
           
         *)
Abort.


End Label.

Import Label.


Section PartialFunctions.

Import SetNotations.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*      partial functions as sets of pairs                   *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(* A set of pairs is a partial function if there is at most one 
   mapping for any key in the set. NOTE: this definition uses 
   syntactic equality for values. That means that for values 
   with multiple representations (i.e. functions) this definition 
   is too rigid. 
*)
Definition partial_function {K}{V}  (S : P (K * V)) := 
  forall k v1 v2, (k , v1) ∈ S -> (k , v2) ∈ S -> v1 = v2.

(* This predicate defines when a key is in the domain of 
   the partial function *)
Definition in_dom {K}{V} (s : P (K * V)) (k : K) : Prop := 
  exists v, (k,v) ∈ s.

(* Access the canonical list of elements in a finite mapping *)
Definition elements {K}{V} (R : K -> K -> Prop) (s : P (K * V)) (l : list (K * V)) : Prop := 
  let LT := fun '(l1,_) '(l2, _)=> R l1 l2 in
  (mem l = s) /\                        (* memberships are equal *)
  @Sorted.LocallySorted _ LT l.        (* the list is sorted by the labels *)


Lemma smaller_notpresent {K}{V}{R : K -> K -> Prop}`{StrictOrder _ R} 
  (a : K * V) (w : list (K * V)) :
  List.Forall (let '(l1, _) := a in fun '(l2, _) => R l1 l2) w ->
  ~(List.In a w).
Proof. destruct a. 
       induction w.
       intros h1 h2. inversion h2.
       intros h1 h2. simpl in h2. 
       inversion h1. subst.
       destruct h2.
       + rewrite H0 in H2. destruct H. 
         unfold Irreflexive, complement, Reflexive in *. 
         eauto.
       + apply IHw; eauto.
Qed.

Lemma elements_functional {K}{V}{R : K -> K -> Prop}
  `{StrictOrder _ R}{e: P (K * V) }{w1 w2} : 
  partial_function e -> 
  elements R e w1 -> elements R e w2 -> w1 = w2.
Proof.
  move=> pfe.
  have TR: Transitive (fun '(l1, _) '(l2, _) => R l1 l2).
  { intros t. unfold Transitive.
    intros [l1 _][l2 _][l3 _]. eapply H. }
  unfold elements in *.
  repeat rewrite <- Sorted.Sorted_LocallySorted_iff.
  move=> [m1 S1].
  move=> [m2 S2]. rewrite <- m1 in m2. 
  apply Sorted.Sorted_StronglySorted in S1; try apply TR.
  apply Sorted.Sorted_StronglySorted in S2; try apply TR.
  remember ((fun '(l1, _) '(l2, _) => R l1 l2) : (K * V) -> (K * V) -> Prop) as Rl.
  move: S1 w2 m2 S2.
  induction w1.
  - intros S1 w2 m2 s2. destruct w2. done.
Admitted.
(*    
    unfold mem in m2. 
    
    move: m2 => [m21 _].
    specialize (m21 p ltac:(left; eauto)).
    inversion m21.
  - intros S1 w2 m2 S2. destruct w2. 
    -- move: m2 => [_ m22].
       specialize (m22 a ltac:(left; eauto)).
       inversion m22.
    -- inversion S1. subst.
       inversion S2. subst.
       move: (@smaller_notpresent K V R H a w1 H3) => ni1.
       move: (@smaller_notpresent K V R H p w2 H5) => ni2.
       have: (a = p). admit. move => h. subst a.
       apply Sets.mem_cons_inv in m2.
       f_equal. eapply IHw1; eauto.
Admitted. *)

End PartialFunctions.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Result                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Module R.

Inductive Result (A : Type) : Type := 
  | Bottom : Result A
  | Wrong  : Result A 
  | Fail   : Result A
  | Value  : A -> Result A
.

Arguments Bottom {_}.
Arguments Wrong {_}.
Arguments Fail {_}.
Arguments Value  {_}.

Definition strict {A} (w1 w2 : Result A) : Prop := 
  match w1 , w2 with
  | Bottom , Bottom => True 
  | Wrong , Wrong => True
  | Fail , _ => True
  | Value _ , _ => True       
  | _ , _ => False
  end.

Definition approx {A} (r1 r2 : Result A) : Prop := 
  match r1 , r2 with 
  | Bottom , _ => True
  | Wrong , Wrong => True
  | Fail , Fail => True
  | Value w1 , Value w2 => w1 = w2
  | _ , _ => False
end.


End R.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Domain of values                      *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(* This is our domain of values (W): numbers, primitives, tuples of values 
   and closures *)

Inductive W : Type := 
  | IntV    : nat -> W
  | PrimV   : Op -> W
  | TupleV  : list W -> W
  | LamV    : forall {n}, Vector.vec W n -> Exp (S n) -> W   (* a closure *)
.

#[export] Hint Constructors W.

Module W.

(* syntactic equality for values *)
Fixpoint eqb (x : W) (y : W) : bool := 
  let fix eqbs (xs : list W) (ys : list W) : bool :=
    match xs , ys with 
    | (x :: xs)%list , (y :: ys)%list => (eqb x y && eqbs xs ys)%bool
    | nil , nil => true
    | _ , _ => false
    end 
  in match x , y with 
     | IntV x , IntV y => Nat.eqb x y
     | PrimV x , PrimV y => Op.eqb x y
     | TupleV xs , TupleV ys => eqbs xs ys
     | LamV v1 e1 , LamV v2 e2 => false (* todo *)
     | _ , _ => false
     end.

End W.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                Semantic operators                         *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Section Semantics.

Import LabelNotation.
Import SetNotations.
Import MonadNotation.
Import AlternativeNotation.

Local Open Scope monad_scope.

Definition left {A} : (label * option A) -> (label * option A) := 
  fun '(l,w) => (L l, w).
Definition right {A} : (label * option A) -> (label * option A) := 
  fun '(l,w) => (R l, w).


Definition M (A : Type) := (label * option A) -> Prop.  

Definition BOTTOM {A} : P (label * option A) := ⌈ (Bot, None) ⌉.

Definition WRONG {A} : P (label * option A) := ∅.

Definition FAIL {A} : P (label * option A) := ∅.

Definition UNIT {A} (x : A) : P (label * option A) := 
  ⌈ (Top, Some x) ⌉.

(* { (L𝑙,𝑤) | (𝑙,𝑤) ∈ 𝑠1 } ∪ {(R𝑙,𝑤) | (𝑙,𝑤) ∈ 𝑠2 } *)
Definition UNION {A} (s1 s2 : P (label * option A)) := 
  fmap left s1 ∪ fmap right s2.


(* enforce strictness *)
Definition strictly {A} (r1 : option A) (r2 : option A) : option A := 
  match r1 with 
  | None => None
  | Some _ => r2 
  end.


(* sequence diverges when either the first or second argument diverges. *)
  (* {(𝑙1 ⋈ 𝑙2,𝑤2) | (𝑙1,𝑤1) ∈ 𝑠1, (𝑙2,𝑤2) ∈ 𝑠2} *)
Definition SEQ {A} s1 s2 :  P (label * option A)%type :=
  '(l1, r1) <- s1 ;;
  '(l2, r2) <- s2 ;;
  ⌈ (l1 ⋈ l2, strictly r1 r2) ⌉.

(* Find the result associated with the *smallest* label in the set. *)
(* If the smallest result diverges then ONE also diverges. *)

Definition minimalIn {A} (k : label) (s : P (label * option A)) := 
  forall k' w', (k', w') ∈ s -> (k <= k').

Definition ONE {A} (s : P (label * option A)) : (label * option A) -> Prop := 
  fun '(l,w) => 
    match l with 
    | Top => exists k, ((k,w) ∈ s) /\ minimalIn k s
    | _ => False
    end.

(* Merge togther the result of the function f applied to every w in W.
   - Ensure that we only have one result per label. If a label has a 
     different mapping (for any picked value), then do not include it in 
     the set. (TODO: make entire result wrong instead?)
*)
                                          
Definition EXISTS {A} (f : A -> M A) : M A := 
  fun '(l,r) => (exists w, (l,r) ∈ f w) 
           /\ (forall w' r', (l, r') ∈ f w' -> r = r') (* make ∃x.x fail *)
           /\ (forall w' l' r', (l', r') ∈ f w' -> Label.comparable l l' = true)  
.


(* Could value w1 be represented by the entry? *)
Definition keep (w1 : W) (entry : label * option W) : bool := 
  match entry with
  | (l, Some w2) => W.eqb w1 w2
  | (l, None) => true
  end.
(*  Intersection fails if its argument fails
    and diverges if its argument diverges *)
  (* { (l2, 𝑤2) | (𝑙2,𝑤2) ∈ 𝑠2, 𝑤1 = 𝑤2} *)
Definition INTER (w : W) : M W -> M W := Sets.filter (keep w).


(* The 'elements' proposition asserts that a set s is finite and contains the ordered 
   list of entries (i.e. labeled results). *)
Definition ALL : M W -> M W := 
  fun s => fun '(l,r) => 
    match l , r with 
    | Top , Some (TupleV ws) => 
        exists entries , elements (fun x y => x < y) s entries 
               /\ (List.map snd entries = List.map Some ws) 
                                          (* all of the results must succeed *)
    | Top , None => exists l, (l , None) ∈ s    (* if any of the results diverge, ALL diverges *)
    | _   , _ => False                         (* if there are no results, ALL fails *)
    end.



End Semantics.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                Evaluator                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Section Eval.

Open Scope vec_scope.
Import Vector.VectorNotation.


Definition Env (n : nat) := Vector.vec W n.
Definition lookupEnv {n} (e : Env n) (x : fin n) : W := Vector.nth e x. 

(* semantics of values *)
Fixpoint evalVal {n} (env : Env n) (V : Val n) : W :=
  let evalVals (vs : list (Val n)) : list W := List.map (evalVal env) vs in
  match V with 
  | var_Val v => lookupEnv env v
  | Lam e => LamV env e
  | Tuple vs => TupleV (evalVals vs)
  | Int k => IntV k
  | Prim o => PrimV o
  end.

Definition evalVals {n} (env : Env n) := (List.map (evalVal env)).

Definition evalPrim (o : Op) (w : W) : M W := 
  match o , w with 
  (* addition *)
  | opAdd , TupleV (cons (IntV j) (cons (IntV k) nil)) => UNIT (IntV (j+k))
  | opAdd , _ => WRONG
  (* Gt *)
  | opGt  , TupleV (cons (IntV j) (cons (IntV k) nil)) =>
      if Nat.leb k j then UNIT ( IntV j ) else FAIL
  | opGt , _ => WRONG
  (* type test: identity function on Int, fails when given a non int value *)
  | opInt , IntV k => UNIT ( IntV k )
  | opInt , _ => FAIL
  end.

(* semantics of expressions *)

Fixpoint evalExp (m:nat) {n : nat} (e: Exp n) : Env n -> M W :=  
  match m with 
  | 0 => fun env => BOTTOM
  | S m' => match e with 
           | Ret v => fun env => UNIT (evalVal env v)

           | Fail => fun env => FAIL

           | Or e1 e2 => fun env => UNION (evalExp m' e1 env) (evalExp m' e2 env)

           | Unify v1 e2 => fun env => INTER (evalVal env v1) (evalExp m' e2 env)

           | Seq e1 e2 => fun env => SEQ (evalExp m' e1 env) (evalExp m' e2 env)

           | App e v => fun env =>
               let w := evalVal env v in
               match evalVal env e with                      
                 | LamV env1 e1 => evalExp m' e1 (w :: env1)
                 | PrimV p => evalPrim p w
                 | _ => WRONG   (* non-function application *)
               end

           | Exists e => fun env => EXISTS (fun w => evalExp m' e (w :: env))

           | One e => fun env => ONE (evalExp m' e env)

           | All e => fun env => ALL (evalExp m' e env)
           end
  end.

Lemma eval_Ret {m' n} {v} : evalExp (S m') (Ret v) = fun (env : Env n) => UNIT (evalVal env v).
Proof. reflexivity. Qed.
Lemma eval_Or  {m' n} {e1 e2} : 
   evalExp (S m') (Or e1 e2) = fun (env : Env n) => UNION (evalExp m' e1 env) (evalExp m' e2 env).
Proof. reflexivity. Qed.
Lemma eval_App  {m' n} {e v} : 
   evalExp (S m') (App e v) = fun (env : Env n) => let w := evalVal env v in
               match evalVal env e with                      
                 | LamV env1 e1 => evalExp m' e1 (w :: env1) 
                 | PrimV p => evalPrim p w
                 | _ => WRONG   (* non-function application *)
               end.
Proof. reflexivity. Qed.
Lemma eval_Seq {m' n} {e1 e2} : 
  evalExp (S m') (Seq e1 e2) = fun (env : Env n) => SEQ (evalExp m' e1 env) (evalExp m' e2 env).
Proof. reflexivity. Qed.
Lemma eval_Unify {m' n} {v1 e2} : 
  evalExp (S m') (Unify v1 e2) = fun (env : Env n) => INTER (evalVal env v1) (evalExp m' e2 env).
Proof. reflexivity. Qed.
Lemma eval_Exists {m' n} {e} : 
  evalExp (S m') (Exists e) = fun (env : Env n) => EXISTS (fun w => evalExp m' e (Vector.cons w env)).
Proof. reflexivity. Qed.
Lemma eval_One {m' n} {e} : 
  evalExp (S m') (One e) = fun (env : Env n) => ONE (evalExp m' e env).
Proof. reflexivity. Qed.
Lemma eval_All {m' n} {e} : 
  evalExp (S m') (All e) = fun (env : Env n) => ALL (evalExp m' e env).
Proof. reflexivity. Qed.

End Eval.

Create HintDb evalExp.
Hint Rewrite @eval_Ret @eval_Or @eval_App @eval_Seq @eval_Unify @eval_Exists @eval_One @eval_All : evalExp.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Validity                                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


Section Validity.

Import SetNotations.

(* We want to ensure that all interpretations are "valid". In other words, 
   the sets are all partial functions. *)

Definition Valid {A} : M A -> Prop := partial_function.

Lemma partial_function_BOTTOM {A} : partial_function (@BOTTOM A).
  intros k v1 v2 in1 in2. inversion in1. inversion in2. done.
Qed.

Lemma partial_function_UNIT {A} (x:A) : partial_function (UNIT x).
  intros k v1 v2 in1 in2. inversion in1. inversion in2. done.
Qed.

Lemma partial_function_FAIL {A} : partial_function (@FAIL A).
  intros k v1 v2 in1 in2. inversion in1. 
Qed.

Lemma partial_function_WRONG {A} : partial_function (@WRONG A).
  intros k v1 v2 in1 in2. inversion in1. 
Qed.

Lemma partial_function_UNION {A} (s1 s2 : M A) : partial_function s1 -> partial_function s2 -> partial_function (UNION s1 s2).
intros pf1 pf2 k v1 v2 in1 in2.
unfold UNION in *. unfold partial_function in *.
inversion in1 as [? h1|? h1]; inversion in2 as [? h2|? h2]; subst; clear in1 in2.
cbv in h1,h2.
all: move: h1 => [[l1 r1] [h1 h1']]; inversion h1'; subst; clear h1'.
all: move: h2 => [[l2 r2] [h2 h2']]; inversion h2'; subst; clear h2'.
eauto.
eauto.
Qed.

Lemma partial_function_INTER  
  (v : W)(s2 : M W) : partial_function s2 -> partial_function (INTER v s2).
Proof.
  intros pf k v1 v2 in1 in2.
  unfold INTER in *. unfold partial_function in *.
  unfold filter in *.
  move: in1 => [k1 in1].
  move: in2 => [k2 in2].
  eauto.
Qed.

Lemma partial_function_SEQ {A} (s1 s2 : M A) : partial_function s1 -> partial_function s2 -> partial_function (SEQ s1 s2).
Proof.
  move=> pf1 pf2 k v1 v2 in1 in2.
  unfold partial_function in *.
  cbn in in1.
  move: in1 => [[l1 r1] [h1 [[l1' r1'] [h1' h]]]]. inversion h. subst. clear h.
  move: in2 => [[l2 r2] [h2 [[l2' r2'] [h2' h]]]]. inversion h. subst. clear h.
  move: (pf1 _ _ _ h1 h2) => E1.
  move: (pf2 _ _ _ h1' h2') => E2.
  subst.
  auto.
Qed.

(* The IH doesn't help here because it only talks about individual 
   sets f w. But we need to reason about all f w. *)
Lemma partial_function_EXISTS {A} (f : A -> M A) : 
  (forall w, partial_function (f w)) -> partial_function (EXISTS f).
Proof.
intros ih k v1 v2 in1 in2.
move: in1 => [[w1 in1] p1].
move: in2 => [[w2 in2] p2].
eapply p1; eauto.    
Qed.


Lemma partial_function_ONE (e : M W) : partial_function e -> partial_function (ONE e).
Proof.
  intros pf k v1 v2 in1 in2.
  unfold ONE, partial_function in *.
  destruct k; try done.
  move: in1 => [k1 [h1 h1']].
  move: in2 => [k2 [h2 h2']].
  have LE1: (Label.le k1 k2); eauto.
  have LE2: (Label.le k2 k1); eauto.
  move: (Label.le_antisymmetry LE1 LE2) => eq. subst.
  eauto.
Qed.

Lemma map_Some_inv {A} {l l0 : list A} : list_map Some l = list_map Some l0 -> l = l0.
Proof. move: l0. 
       induction l; intros [|l0] h; inversion h; subst; f_equal.
       eapply IHl; eauto.
Qed.

Lemma partial_function_ALL (e : M W) : partial_function e -> partial_function (ALL e).
Proof.
  intros pfe k v1 v2 in1 in2.
  destruct k; try done.
  destruct v1; try done.
  destruct v2; try done.
  destruct w; try done.
  destruct w0; try done.
  move: in1 => [w1 [in1 p1]].
  move: in2 => [w2 [in2 p2]].
  - f_equal. f_equal.
    have EQ : (w1 = w2). eapply elements_functional; eauto. subst.
    rewrite p1 in p2.
    apply map_Some_inv in p2. auto.
  - destruct w; try done. 
    destruct in1 as [xs [h1 h2]].
    destruct in2 as [l' h3].
    move: h1 => [h1 SS]. subst.
    apply mem_In in h3.
    apply List.in_map with (f := snd) in h3. rewrite h2 in h3. simpl in h3.
    rewrite List.in_map_iff in h3.
    move: h3 => [? [h3 _]]. done.
  - destruct v2. destruct w; try done.
    destruct in1 as [l' h3].
    destruct in2 as [xs [h1 h2]].
    move: h1 => [h1 SS]. subst.
    apply mem_In in h3.
    apply List.in_map with (f := snd) in h3. rewrite h2 in h3. simpl in h3.
    rewrite List.in_map_iff in h3.
    move: h3 => [? [h3 _]]. done.
    auto.
Unshelve.
Qed.

Lemma partial_function_evalPrim {o w} :
   partial_function (evalPrim o w).
Proof.
  destruct o; destruct w; simpl.
  all: try eapply partial_function_WRONG.
  all: try eapply partial_function_UNIT.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try eapply partial_function_WRONG.
  all: try eapply partial_function_UNIT.
  destruct (Nat.leb n0 n).
  all: try eapply partial_function_UNIT.
  all: try eapply partial_function_FAIL.
Qed.

Lemma partial_function_evalExp : forall k n (env : Env n) e , partial_function (evalExp k e env).
intros k. induction k.
- intros. cbn. eapply partial_function_BOTTOM.
- intros.
  destruct e.
  + simpl. eapply partial_function_UNIT.
  + repeat rewrite eval_App.    
    remember (evalVal env v0) as w. cbv zeta.
    destruct (evalVal env v).
    all: try eapply partial_function_WRONG.
    eapply partial_function_evalPrim.
    eapply IHk.
  + repeat rewrite eval_Seq. eapply partial_function_SEQ; eauto.
  + repeat rewrite eval_Unify. eapply partial_function_INTER; eauto.
  + repeat rewrite eval_Exists.
    eapply partial_function_EXISTS. intro w; eauto.
  + repeat rewrite eval_Or.
    eapply partial_function_UNION; eauto.
  + simpl.
    eapply partial_function_FAIL; eauto.
  + rewrite eval_One.
    eapply partial_function_ONE; eauto.
  + rewrite eval_All.
    eapply partial_function_ALL; eauto.
Qed.

End Validity.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Comparable                                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


Section Comparable.

Import SetNotations.

(* We want to ensure that all interpretations are "comparable". In other words, 
   the labels in the sets are comparable. *)

Definition Comparable {A} : M A -> Prop := 
  fun s => forall l1 r1 l2 r2, (l1, r1) ∈ s -> (l2, r2) ∈ s -> Label.comparable l1 l2 = true.

Lemma Comparable_BOTTOM {A} : Comparable (@BOTTOM A).
  intros k1 v1 k2 v2 in1 in2. inversion in1. inversion in2. subst. done.
Qed.

Lemma Comparable_UNIT {A} (x:A) : Comparable (UNIT x).
  intros k1 v1 k2 v2 in1 in2. inversion in1. inversion in2. done.
Qed.

Lemma Comparable_FAIL {A} : Comparable (@FAIL A).
  intros k1 v1 k2 v2 in1 in2. inversion in1. 
Qed.

Lemma Comparable_WRONG {A} : Comparable (@WRONG A).
  intros k1 v1 k2 v2 in1 in2. inversion in1. 
Qed.

Lemma Comparable_UNION {A} (s1 s2 : M A) : Comparable s1 -> Comparable s2 -> Comparable (UNION s1 s2).
intros pf1 pf2 k1 v1 k2 v2 in1 in2.
unfold UNION in *. unfold Comparable in *.
inversion in1 as [? h1|? h1]; inversion in2 as [? h2|? h2]; subst; clear in1 in2.
cbv in h1,h2.
all: move: h1 => [[l1 r1] [h1 h1']]; inversion h1'; subst; clear h1'.
all: move: h2 => [[l2 r2] [h2 h2']]; inversion h2'; subst; clear h2'.
simpl. eauto.
simpl. eauto.
simpl. eauto.
simpl. eauto.
Qed.

Lemma Comparable_INTER  
  (v : W)(s2 : M W) : Comparable s2 -> Comparable (INTER v s2).
Proof.
  intros pf k1 v1 k2 v2 in1 in2.
  unfold INTER in *. unfold Comparable in *.
  unfold filter in *.
  move: in1 => [l1 in1].
  move: in2 => [l2 in2].
  eauto.
Qed.

Lemma Comparable_SEQ {A} (s1 s2 : M A) : Comparable s1 -> Comparable s2 -> Comparable (SEQ s1 s2).
Proof.
  move=> pf1 pf2 k1 v1 k2 v2 in1 in2.
  unfold Comparable in *.
  cbn in in1.
  move: in1 => [[l1 r1] [h1 [[l1' r1'] [h1' h]]]]. inversion h. subst. clear h.
  move: in2 => [[l2 r2] [h2 [[l2' r2'] [h2' h]]]]. inversion h. subst. clear h.
  move: (pf1 _ _ _ _ h1 h2) => E1.
  move: (pf2 _ _ _ _ h1' h2') => E2.
  simpl.
  rewrite E1. rewrite E2. done.
Qed.

(* The IH doesn't help here because it only talks about individual 
   sets f w. But we need to reason about all f w. *)

(* 
 (forall w l r w' l' r', (l,r) ∈ f w -> (l', r') ∈ f w' -> Label.comparable l l' = true)  
*)

Lemma Comparable_EXISTS {A} (f : A -> M A) : 
  (forall w, Comparable (f w)) -> Comparable (EXISTS f).
Proof.
intros ih k1 v1 k2 v2 in1 in2.
move: in1 => [[w1 in1] [p1 p1']].
move: in2 => [[w2 in2] [p2 p2']].
move: (p1' _ _ _ in2) => e1.
eauto.
Qed.

Lemma Comparable_ONE (e : M W) : Comparable e -> Comparable (ONE e).
Proof.
  intros pf k1 v1 k2 v2 in1 in2.
  unfold ONE, Comparable in *.
  destruct k1; try done.
  destruct k2; try done.
Qed. 


Lemma Comparable_ALL (e : M W) : Comparable e -> Comparable (ALL e).
Proof.
  intros pfe k1 v1 k2 v2 in1 in2.
  destruct k1; try done.
  destruct k2; try done.
Qed.

Lemma Comparable_evalPrim {o w} :
   Comparable (evalPrim o w).
Proof.
  destruct o; destruct w; simpl.
  all: try eapply Comparable_WRONG.
  all: try eapply Comparable_UNIT.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try eapply Comparable_WRONG.
  all: try eapply Comparable_UNIT.
  destruct (Nat.leb n0 n).
  all: try eapply Comparable_UNIT.
  all: try eapply Comparable_FAIL.
Qed.

Lemma Comparable_evalExp : forall k n (env : Env n) e , Comparable (evalExp k e env).
intros k. induction k.
- intros. cbn. eapply Comparable_BOTTOM.
- intros.
  destruct e.
  + simpl. eapply Comparable_UNIT.
  + repeat rewrite eval_App.    
    remember (evalVal env v0) as w. cbv zeta.
    destruct (evalVal env v).
    all: try eapply Comparable_WRONG.
    eapply Comparable_evalPrim.
    eapply IHk.
  + repeat rewrite eval_Seq. eapply Comparable_SEQ; eauto.
  + repeat rewrite eval_Unify. eapply Comparable_INTER; eauto.
  + repeat rewrite eval_Exists.
    eapply Comparable_EXISTS. intro w; eauto.
  + repeat rewrite eval_Or.
    eapply Comparable_UNION; eauto.
  + simpl.
    eapply Comparable_FAIL; eauto.
  + rewrite eval_One.
    eapply Comparable_ONE; eauto.
  + rewrite eval_All.
    eapply Comparable_ALL; eauto.
Qed.

End Comparable.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Monotonicity                                              *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


Section Monotonicity.

Import SetNotations.
Import MonadNotation.
Import LabelNotation.

(* one interpretation (s1) approximates another (s2) when

   for each (l1,r1) entry in s1: 
      1. if it has succeeded, 
         it continues to succeed in s2 with the same label

      2. if it has bottomed, 
          a. l1 could be extended to multiple labels in s2
                with either sucess, bottom, or failing results

      3. if it fails (i.e. is not in the first set)
          - it should continue to fail and all extensions shouldn't be in s2

We need (1) to know that successful values do not change with more fuel.
We need (3) to show the monotonicity for ONE
   i.e. no new "smaller" elements will show up when we add more fuel. 

*)

(* 

We express this by saying:

   (1)  forall l r, (l,Some r) ∈ s1  -> (l,Some r) ∈ s2

   (2)  Every label in s2 is an extension of some label in s1

        forall l' r', (l', r') ∈ s2 -> exists l r, l ⊑ l' /\ (l,r) ∈ s1

   (3)  (I think this is equivalent to the above???)

        forall l r, (l,r) ∉ s1 -> forall l' r', l ⊑ l' -> (l',r') ∉ s2)
*)

Definition entry_approx {A} : label * option A -> label * option A ->  Prop := 
  fun '(l1, r1) '(l2, r2) => 
    match r1 , r2 with 
    | Some v1 , Some v2 => l1 = l2 /\ v1 = v2
    | None , _ => l1 ⊑ l2  = true
    | _ , _ => False
    end.

Definition approx {A} (s1 s2 : M A) : Prop := 
  (forall l r, ((l, Some r) ∈ s1) -> ((l, Some r) ∈ s2)) /\
  (forall l' r', ((l',r') ∈ s2) -> exists l r, ((l,r) ∈ s1) /\ entry_approx (l,r) (l',r')).



Lemma approx_minimal_Some {A} (s s' : M A) l1 l1' a r1' : 
  Valid s -> 
  Valid s' -> 
  approx s s' -> 
  (l1,Some a) ∈ s -> minimalIn l1 s -> 
  (l1',r1') ∈ s' -> minimalIn l1' s' -> 
  entry_approx (l1,Some a) (l1',r1').
Proof. intros V1 V2 [ap1 ap2] in1 min in1' min'.
       (* both l1 and l1' are minimal in their sets. *)
       (* there is some l2 ⊑ l1' in s and l1 <= l2 *)
       move: (ap2 _ _ in1') => [l2 [r2 [in2 eap]]].
       move: (ap1 _ _ in1) => in2'.
       all: destruct r1'; simpl.
       - (* r1 = Some a, r1' = Some a0 *)
         move: (min _ _ in2) => le2.
         move: (min' _ _ in2') => le1'.
         have LE12: (l1' <= l2). transitivity l1; auto.
         destruct r2. 
         -- move: eap => [e1 e2]. subst.
         have EQ: (l1 = l1'). {  apply le_antisymmetry; eauto. }
         split; auto. subst.
         move: (V1 _ _ _ in1 in2) => h. inversion h. done.
         -- simpl in eap.
         have EQ1: (l2 = l1'). 
           eapply le_antisymmetry; eauto. eapply Label.approx_le. auto.
         subst.
         have EQ2: (l1 = l1'). 
           eapply le_antisymmetry; eauto. 
         subst.
         split; auto. 
         move: (V2 _ _ _ in1' in2') => h. inversion h. done.
       - (* r1 = Some a, r1' = None *) 
         simpl in eap. destruct r2; try done.
         move: (min _ _ in2) => le2.
         move: (min' _ _ in2') => le1'.
         apply Label.approx_le in eap.
         (* need to prove l1 = l1' *)
         have EQ: (l1 = l1'). 
           eapply le_antisymmetry; eauto. transitivity l2; eauto.
         subst.
         move: (V2 _ _ _ in1' in2') => h. done.
Qed.


Lemma approx_minimal_None {A} (s s' : M A) l1 l1' r1' : 
  Valid s -> 
  Valid s' -> 
  approx s s' -> 
  (l1,None) ∈ s -> minimalIn l1 s -> 
  (l1',r1') ∈ s' -> minimalIn l1' s' -> 
  exists l2, exists r2, entry_approx (l2,r2) (l1',r1').
Admitted.

Lemma ONE_monotone {s s' : M W} : 
  Valid s -> Valid s' ->
  approx s s' -> approx (ONE s) (ONE s').
Proof.
  intros V1 V2 [A1 A2].
  split.
  + intros l1 r1 in1.
    destruct l1; try done.
    cbn in in1.
    move: in1 => [k [kin kmin]].
    have kin': (k, Some r1) ∈ s'; eauto.
    exists k. split; eauto.
    (* prove that k is *still* the smallest *)
    intros l2' r2' in2'.
    move: (A2 _ _ in2') => [l2 [r2 [in2 A3]]].
    destruct r2, r2'; try done; simpl in A3.
    ++ destruct A3; subst. eapply kmin; eauto.
    ++ apply Label.approx_le in A3.
      move: (kmin _ _ in2) => h. transitivity l2; eauto.
    ++ apply Label.approx_le in A3.
      move: (kmin _ _ in2) => h. transitivity l2; eauto.
 + intros l' r' in'.
   unfold ONE in in'. cbn in in'.
   destruct l'; try done.
   move: in' => [k' [kin' kmin']].
   move: (A2 _ _ kin') => [l [r [lin eap]]].
   destruct r.
   ++
Admitted.        

Lemma elements_in {A} (s : M A) entries : 
  elements (fun x y : label => x < y) s entries -> 
  forall x, x ∈ s -> List.In x entries.
Admitted.

Lemma ALL_monotone {s s' : M W} : 
  Valid s -> Valid s' ->
  approx s s' -> approx (ALL s) (ALL s').
Proof.
  intros V1 V2 [A1 A2].
  split.
  + intros l1 r1 in1.
    destruct l1; try done.
    destruct r1; try done.
    cbn in in1.
    move: in1 => [entries [hsort hsome]].
    move: (elements_in hsort) => ine.
    exists entries. split; eauto.
    move: hsort => [h1 h2].
    unfold elements. split. 

Lemma SEQ_monotone {A} {s1 s2 s1' s2' : M A} : 
  approx s1 s1' -> approx s2 s2' -> approx (SEQ s1 s2) (SEQ s1' s2').
Proof.
  intros [A1 A1'] [A2 A2'].
  repeat split.
  + intros l r in1.
    move: in1 => [[l1 r1] [h1 in2]].
    move: in2 => [[l2 r2] [h2 in3]].
    inversion in3. subst. clear in3.
    destruct r1; destruct r2; simpl. simpl in H1. inversion H1. subst. clear H1.
    ++ move: (A1 _ _ h1) => in1'.
       exists (l1, Some a). repeat split; eauto.
       move: (A2 _ _ h2) => in2'.
       exists (l2, Some r). repeat split; eauto.
    ++ simpl in H1. done.
    ++ simpl in H1. done.
    ++ simpl in H1. done.
  + intros l' r' in1'.
    move: in1' => [[l1' r1'] [h1' in2']].
    move: in2' => [[l2' r2'] [h2' in3']].
    inversion in3'. subst. clear in3'.
    move:(A1' _ _ h1') => [l1 [r1 [h1 ea1]]].
    move:(A2' _ _ h2') => [l2 [r2 [h2 ea2]]].
    destruct r1; destruct r2; simpl. 
    ++ 
      destruct r1'; simpl in ea1; try done.
      destruct r2'; simpl in ea2; try done.
      move: ea1 => [e1 e2]. move: ea2 => [e3 e4]. subst.
      exists (l1' ⋈ l2'). exists (Some a2).
       split. exists (l1', Some a1). split; auto.
              exists (l2', Some a2). split; auto.
       simpl. split; auto.
    ++ destruct r1'; simpl in ea1; try done.
       simpl in ea2.
       move: ea1 => [e1 e2]. subst.
       exists (l1' ⋈ l2).  exists None.
       split; simpl; eauto.
       eexists; split; eauto. cbn.
       eexists; split; eauto. cbn.
       eapply in_singleton.
       rewrite Bool.andb_true_iff. split; auto. 
       eapply Label.approx_refl.
    ++ destruct r2'; simpl in ea2; try done.
       simpl in ea1.
       move: ea2 => [e1 e2]. subst.
       exists (l1 ⋈ l2').  exists None.
       split; simpl; eauto.
       eexists; split; eauto. cbn.
       eexists; split; eauto. cbn.
       eapply in_singleton.
       rewrite Bool.andb_true_iff. split; auto. 
       eapply Label.approx_refl.
    ++ simpl in ea1; simpl in ea2.
       exists (l1 ⋈ l2). exists None.
       split; simpl; eauto.
       eexists; split; eauto. cbn.
       eexists; split; eauto. cbn.
       eapply in_singleton.
       rewrite Bool.andb_true_iff. split; auto. 
Qed.

      
Lemma INTER_monotone {w}{s2 s2' : M W} : 
  approx s2 s2' -> approx (INTER w s2) (INTER w s2').
Proof.
  intros [A1 A2].
  unfold INTER , approx, filter, In in *. 
  split.
  - intros l1 v1 h.
    move: h => [h1 h2].
    split. eauto. eauto.
  - intros l2 v2 [h2 h3].
    move: (A2 _ _ h3) => [l1 [v1 [h1 A3]]].
    exists l1. exists v1. split; eauto.
    split; auto.
    destruct v2; simpl in A3, h2.
    destruct v1; simpl in A3.
    destruct A3 as [e1 e2]. subst. simpl. auto.
    simpl. auto.
    destruct v1; try done.
Qed.

Lemma EXISTS_monotone {A} {f f' : A -> M A} :
  (forall w, approx (f w) (f' w)) ->
  approx (EXISTS f) (EXISTS f').
Proof.
  intros hA.
  unfold EXISTS, approx in *.
  split.
  - intros l v h0.
    move: h0 => [[w h0] h1].
    move: (hA w) => [hA1 hA2].
    split.
    exists w. eauto.
    split.
    intros w' r' wIn'.
Admitted.

Lemma approx_BOTTOM {A} : forall (s : M A), approx ⌈ (Bot, None) ⌉ s.
intros s. split.
+ intros l r lin. inversion lin.
+ intros l' r' lin'. exists Bot. exists None. split.
  eapply in_singleton. simpl. auto.
Qed.

Lemma approx_refl {A} : forall (s : M A), approx s s.
intros s. split.
+ eauto.
+ intros. exists l'. exists r'. split; auto. destruct r'. simpl. split; auto.
  simpl. eapply Label.approx_refl.
Qed.

Lemma evalExp_monotone : forall k n (env : Env n) e , approx (evalExp k e env) (evalExp (S k) e env).
intros k. induction k.
- intros. simpl. unfold BOTTOM. eapply approx_BOTTOM.
- intros.
  destruct e.
  + simpl. eapply approx_refl.
  + repeat rewrite eval_App.    
    remember (evalVal env v0) as w. cbv zeta.
    destruct (evalVal env v).
    all: try eapply approx_refl.
    eapply IHk.
  + repeat rewrite eval_Seq. eapply SEQ_monotone; eauto.
  + repeat rewrite eval_Unify. eapply INTER_monotone; eauto.
  + repeat rewrite eval_Exists.
    eapply EXISTS_monotone. intro w; eauto.
  + repeat rewrite eval_Or.
Admitted.

End Monotonicity.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Finite semantics                                          *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Require Import Logic.PropExtensionality.

Section FiniteSemantics.

Import SetNotations.
Import List.ListNotations.
Import MonadNotation.
Import LabelNotation.

Open Scope list_scope.
Open Scope monad_scope.

Lemma singleton_mem {A}{x:A} : ⌈ x ⌉ = mem ([ x ]%list).
Proof. 
  eapply Extensionality_Ensembles.
  rewrite mem_singleton_eq.
  reflexivity.
Qed.

Lemma fmap_mem {A B}{f : A -> B}{s} :
  mem (List.map f s) = fmap f (mem s).
Proof. 
Admitted.

Lemma filter_mem {A}{f : A -> bool}{s} :
  mem (List.filter f s) = filter f (mem s).
Proof. 
Admitted.

Lemma bind_cong {A B}{m1 m2 : P A}{k1 k2 : A -> P B} : 
  (m1 = m2) -> (forall x, k1 x = k2 x) -> bind m1 k1 = bind m2 k2.
Proof. 
  intros -> R.
  cbv.
  eapply Extensionality_Ensembles.
  split; intros x [a [h1 h2]].
    rewrite -> R in h2; exists a; eauto.
    rewrite <- R in h2; exists a; eauto.
Qed.

Lemma bind_mem {A B} (m : list A) (k : A -> list B) : 
  mem (bind m k) = bind (mem m) (fun y => mem (k y)).
Proof. 
  induction m.
  - eapply Extensionality_Ensembles.
    cbv. split.
    intros x xIn. done.
    intros x [y [z w]]. done.
  - cbn.
    rewrite union_mem.
    rewrite IHm.
    eapply Extensionality_Ensembles.
    split.
    + intros x xIn. inversion xIn; subst; clear xIn.
    ++ exists a. split. left; auto. auto.
    ++ move: H => [a' [aIn xIn]].
       exists a'. split. right. auto. auto.
    + intros x [a' [[h1|h1] h2]]. 
      ++ subst. econstructor; eauto.
      ++ right. exists a'. split; eauto.
Qed.

Lemma UNIT_mem {A} : forall (x : A), 
    UNIT x = mem ([(Top, Some x)]).
Proof.
  intro x. unfold UNIT. eapply singleton_mem.
Qed.

Lemma UNION_mem {A}{l1 l2: list (label * option A)} : 
  UNION (mem l1) (mem l2) = mem (List.map left l1 ++ List.map right l2).
Proof.
  unfold UNION.
  rewrite union_mem.
  repeat rewrite fmap_mem.
  reflexivity.
Qed.


Lemma INTER_mem {x:W}{xs:list (label * option W)} : 
  INTER x (mem xs) = mem (List.filter (keep x) xs).
Proof. 
  unfold INTER.
  rewrite filter_mem.
  reflexivity.
Qed.


Lemma SEQ_mem {A}{l1 l2: list (label * option A)} :
  SEQ (mem l1) (mem l2) = 
    mem ( '(l1, r1) <- l1 ;;
          '(l2, r2) <- l2 ;;
          [ (l1 ⋈ l2, strictly r1 r2) ] ).
Proof.
  unfold SEQ.
  rewrite -> bind_mem.
  apply bind_cong.
  reflexivity.
  intros [l0 r0].
  rewrite -> bind_mem.
  apply bind_cong.
  reflexivity.
  intros [k0 r1].
  rewrite singleton_mem.
  reflexivity.
Qed.


Definition union_map {A B} (m : list A) (k : A -> P B) : P B :=
  List.fold_left Union (List.map k m) Empty_set.

Lemma SEQ_mem' {A}{l1: list (label * option A)}{s2} :
  SEQ (mem l1) s2 = 
    union_map l1 (fun '(l1 , r1) => 
          '(l2, r2) <- s2 ;;
          ⌈ (l1 ⋈ l2, strictly r1 r2) ⌉).
Proof.
  unfold SEQ.
  induction l1.
  - cbv.
    eapply Extensionality_Ensembles.
    split. intros x [y [h xIn]]. done. intros x xIn. done.
  - 
Admitted.

End FiniteSemantics.

Create HintDb mem.
Hint Rewrite @UNIT_mem @UNION_mem @INTER_mem @SEQ_mem : mem.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Examples                                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Section Examples.

Import SetNotations.
Import VerseNotations.
Import Vector.VectorNotation.
Import LabelNotation.

Ltac process := 
  repeat match goal with 
  | [H : True |- _ ] => clear H
  | [H : ?a ∈ ⌈ ?a ⌉ |- _ ] => clear H
  | [H : ?a ∈ ⌈ ?b ⌉ |- _ ] => inversion H; clear H; subst
  | [H : ?A /\ ?B |- _ ] => inversion H; clear H; subst
  | [H : ?x ∈ UNIT ?a |- _ ] => inversion H; clear H; subst
  | [H : UNIT ?a ?x |- _ ] => inversion H; clear H; subst
  | [H : Some ?a = Some ?b |- _ ] => inversion H; clear H; subst
  | [H : ⌈ ?a ⌉ ?b |- _ ] => inversion H; clear H; subst
  | [ |- forall x , _ ] => intros ? 
  | [H : (exists h, _ ) |- _ ] => move: H => [? H]
  | [ H : match ?x with _ => _ end |- _ ] => 
      (destruct x; try done; auto; let n:=numgoals in guard n <= 1) + idtac "too many goals"
  end.

Ltac go := process;auto.

Hint Unfold UNIT ONE EXISTS.
Hint Constructors Ensembles.Singleton.

(*
Lemma f_equal_mem {A}{l1 l2 : list A}: l1 = l2 -> mem l1 ≃ mem l2.
Admitted. *)
Lemma P_In {A}{f : P A}{x} : (f x) -> x ∈ f. cbv. auto. Qed.


(* 3 = 3 || 4 = 4 || 5 = 5 *)
Definition exb : Exp 0 := Or (Int 3 ≡ Int 3) (Or (Int 4 ≡ Int 4) (Int 5 ≡ Int 5)).

Example exb_example : evalExp 10 exb Vector.nil = 
  mem ((L Top, Some (IntV 3)) :: (R (L Top), Some (IntV 4)) :: (R (R Top),Some (IntV 5)) :: nil).
unfold exb. autorewrite with evalExp.
unfold evalVal.
autorewrite with mem.
f_equal.
Qed.

Lemma In_extensionality {A} {s1 s2 : P A} : 
  (forall x, (x ∈ s1) <-> x ∈ s2) -> s1 = s2.
Proof.
  intros h.
  eapply Extensionality_Ensembles.
  split. intros x xIn; eapply h; eauto.
  intros x xIn; eapply h; eauto.
Qed.

Lemma In_mem : forall (A : Type) (x : A) (l : list A), x ∈ mem l <-> List.In x l.
Admitted.

(* ∃ x. x = (1 || 2) ;; x *)
Definition ex_two : Exp 0 := bind1 (Or (Int 1) (Int 2)) x0.

Lemma W_eqb_eq (w1 w2: W) : W.eqb w1 w2 = true <-> w1 = w2.
Admitted.

Lemma ev_ex_two1 : evalExp 10 ex_two Vector.nil =
                     mem ((L Top ⋈ Top, Some (IntV 1)) :: (R Top ⋈ Top, Some (IntV 2)) :: nil).
Proof.
unfold ex_two,bind1. asimpl.
autorewrite with evalExp.
unfold evalVal, lookupEnv, Vector.nth, var_zero.
eapply In_extensionality.
intros [l r].
rewrite In_mem.
repeat rewrite UNIT_mem.
rewrite UNION_mem.
Opaque INTER SEQ mem. cbn.
Transparent INTER SEQ mem.
split.
+ move=>[[w wIn] _].
  cbn in wIn.
  move: wIn => [[l0 r0][ h1 [[l1 r1] [h2 h3]]]].
  inversion h3; subst; clear h3.
  unfold UNIT in h2. inversion h2; subst; clear h2.
  have C: ((w = IntV 1 /\ l0 = L Top) \/ (w = IntV 2 /\ l0 = R Top)).
  { unfold INTER in h1.
    rewrite <- filter_mem in h1.
    rewrite In_mem in h1.
    cbn in h1.
    destruct (W.eqb w (IntV 1)) eqn:E1.
    rewrite W_eqb_eq in E1. subst. cbn in h1. inversion h1; try done. inversion H. subst.
    left. split; auto.
    destruct (W.eqb w (IntV 2)) eqn:E2.
    rewrite W_eqb_eq in E2. subst. inversion h1; try done. inversion H. subst.
    right. auto.
    destruct h1.
  }
  rewrite INTER_mem in h1.
  rewrite In_mem in h1.
  destruct C as [[-> ->]|[-> ->]].
  ++ cbn in h1. inversion h1; try done. inversion H. subst.
     simpl. left; eauto.
  ++ cbn in h1. inversion h1; try done. clear h1. inversion H. subst.
     simpl. right; left; eauto.
+ move=> [h1|[h1|]]; try done; inversion h1; clear h1; subst.
  split.
  ++ exists (IntV 1). exists (L Top, Some (IntV 1)). cbv. split; eauto. econstructor.
Admitted.
(*
     exists (Top, Some (IntV 1)). split; try econstructor; eauto.
  ++ intros w' r' h.
     have C : (r' = Some (IntV 1)).
     { cbn in h.
       move: h => [[l0 r0] [h1 h2]].
       move: h2 => [[l1 r1] [h2 h3]].
       inversion h3; subst; clear h3.
       inversion h2; subst; clear h2.
       rewrite INTER_mem in h1.
       rewrite In_mem in h1.
       cbn in h1.
       destruct (W.eqb w' (IntV 1)) eqn:E1. 
       rewrite W_eqb_eq in E1. subst. 
       destruct h1. inversion H. done.
       simpl in H. done.
       destruct (W.eqb w' (IntV 2)) eqn:E2.
       rewrite W_eqb_eq in E2. subst. 
       destruct h1; inversion H. inversion h1.
     } subst.  auto.
  ++ admit.
Admitted. *)

Lemma INTER_two : forall w l1 v1 l2 v2 s, 
  INTER w (mem ((L l1, Some v1) :: (R l2, Some v2) :: nil)) = s -> 
  ((w = v1 /\ s = mem ((L l1, Some v1) :: nil)) \/
   (w = v2 /\ s = mem ((R l2, Some v2) :: nil))).
Proof.
Admitted.

       (* prove that there is only one y 
       rewrite INTER_mem in h.
       rewrite UNIT_mem in h.
       simpl in h.
       destruct (W.eqb w' (IntV 3)) eqn:E1.
       rewrite W_eqb_eq in E1. subst. simpl in h.
       rewrite SEQ_mem in h. simpl in h. inversion h. inversion H. auto.
       inversion H.
       destruct (W.eqb w' (IntV 4)) eqn:E2. 
       rewrite W_eqb_eq in E2. subst.
       rewrite SEQ_mem in h. simpl in h. inversion h. inversion H. auto.
       rewrite SEQ_mem in h. simpl in h. inversion h.  *)


(* ∃ x. x = (1 || 2) ;; exists y. y = (3 || 4) ;; < x , y > *)
Definition ex_four : Exp 0 := 
  bind2 (Or (Int 1) (Int 2)) (Or (Int 3) (Int 4)) (Tuple (cons x1 (cons x0 nil))).

Lemma ev_ex_four1 : (L Top ⋈ (L Top ⋈ Top), 
                      Some (TupleV (cons (IntV 1) (cons (IntV 3) nil))))
                      ∈ evalExp 30 ex_four Vector.nil.
Proof.
  unfold ex_four, bind2.
  autorewrite with evalExp. 
  asimpl.
  autorewrite with evalExp.
  simpl.
  unfold lookupEnv, Vector.nth, var_zero, var_one.
  autorewrite with mem. simpl.
  split.
  - exists (IntV 1). 
    autorewrite with mem. simpl.
    exists (L Top, Some (IntV 1)). split; eauto.
    simpl.
    exists (L Top ⋈ Top, Some (TupleV (IntV 1 :: IntV 3 :: nil))). 
    split. 2: econstructor; eauto.
    split.
    -- cbn.
       exists (IntV 3). 
       exists (L Top, Some (IntV 3)). 
       rewrite INTER_mem. rewrite In_mem.
       simpl. split; eauto.
       exists (Top,  Some (TupleV (IntV 1 :: IntV 3 :: nil))). 
       split. econstructor; eauto.
       econstructor; eauto.
    -- intros w' r' h.
       move: (@INTER_two w' Top (IntV 3) Top (IntV 4) _ ltac:(reflexivity)) => [[h0 h1]| [h0 h1]].
       subst. rewrite h1 in h. clear h1.
       rewrite UNIT_mem in h. rewrite SEQ_mem in h. rewrite In_mem in h. simpl in h.
       inversion h; try done. inversion H. done.
       subst. rewrite h1 in h. clear h1.
       autorewrite with mem in h. simpl in h.
       inversion h; try done. 

  - intros w' r' h.
    move: (@INTER_two w' Top (IntV 1) Top (IntV 2) _ ltac:(reflexivity)) => [[h0 h1]| [h0 h1]];
    rewrite h1 in h; clear h1; subst w'.
    unfold SEQ in h. simpl in h.
Admitted.





Eval cbv in evalExp 10 Vector.nil ex_four.

Lemma label_comparable_SEQ {A}{s1 s2 : M A}{ l1 l2 } :
  label_comparable s1 l1 -> label_comparable s2 l2 ->
  label_comparable (SEQ s1 s2) (l1 ⋈ l2).
Proof.
  unfold label_comparable.
  move=> h1 h2.
  move=> k [v h3]. unfold SEQ in h3.
  destruct k; try done.
  simpl.
  rewrite (h1 k1).
  2: 
  rewrite (h2 k2).
  3: 
    destruct v; reflexivity.
  destruct v; cbn in h3.
  go. econstructor; eauto.
  destruct h3. go. econstructor; eauto.
  go. econstructor; eauto.
  destruct v; cbn in h3.
  go. econstructor; eauto.
  destruct h3. go. econstructor; eauto.
  go. econstructor; eauto.
Qed.


  
End Example1.



Module Monotonicity.




Definition contains (w : W) (m : M W ) : Prop := 
  exists l , (l, Some w) ∈ m.



(* Examples *)



(* exists x. x = 3 ; x *)
Definition ex0 : Exp 0 := 
  Exists (Seq (Unify (Ret (var_Val var_zero)) (Ret (Int 3))) (Ret (var_Val var_zero))).

Lemma evex0 : exists n, UNIT (IntV 3) ≃ ONE (evalExp n Vector.nil ex0).
exists 4. 
cbn. unfold ONE, EXISTS, UNIT.
split.
- intros x xIn. go.  
  exists ((Top ⋈ Top) ⋈ Top)%label.
  repeat split.
  -- exists (IntV 3). eexists; repeat econstructor; eauto.
  -- cbn. go.
  -- (* label_comparable *)
    unfold label_comparable, in_dom. go. 
    cbn in H. go.
  -- go. cbn in H. go.
- intros x xIn.
  cbn in xIn.
  destruct x; try done.
  destruct l; try done.
  cbn in xIn.
  go.
Qed.

(* exists x. x = 3 | x = 4 *)

Lemma mem_nil_contra {A}(s : P A): (mem nil ≃ s) -> forall x, (x ∈ s) -> False.
Proof. intros. unfold mem in H. move: H => [h1 h2].
specialize (h2 x H0). inversion h2.
Qed.

Definition ex1 : Exp 0 := 
 Exists (Or (Unify (Ret (var_Val var_zero)) (Ret (Int 3)))
            (Unify (Ret (var_Val var_zero)) (Ret (Int 4)))).

Lemma evex1 : exists n, ALL (evalExp n Vector.nil ex1) ≃ UNIT (TupleV (cons (IntV 3) (cons (IntV 4) nil))).
exists 10.
unfold ALL, EXISTS.
split.
- intros x xIn.
  destruct x as [l sw].
  destruct l; try done. 
  destruct sw as [x|]; cbn in xIn.
  -- destruct x; try done.
     move: xIn => [xs ?]. go.
     have EQ: (l = (IntV 3 :: IntV 4 :: nil)%list).
     { unfold elements in H. 
       go.
       have h1: (List.In (L (Top ⋈ Top), Some (IntV 3)) xs). admit.
       have h2: (List.In (R (Top ⋈ Top), Some (IntV 4)) xs). admit.
       admit.
(*       destruct xs as [|x1 xs].
       + move: (mem_nil_contra H1 (L (Top ⋈ Top), Some (IntV 3))) => h1. 
         exfalso. apply h1.
         cbn.
         repeat split. eexists. repeat split.
         go. inversion H4. done.
         intros. unfold label_comparable. intros k.
         go. unfold in_dom in H. go. cbn in H. destruct k; try done.
         destruct k; try done. go. inversion H3. inversion H4. subst. done.
       + destruct xs as [|x2 xs].
         *)
     } subst l.
     unfold UNIT. econstructor; eauto.
  -- move: xIn => [l h].
     go. 
     destruct l; try done; go. 

- intros x xIn.
  go.
  cbn.
  exists ( (L (Top ⋈ Top), Some (IntV 3)) :: (R (Top ⋈ Top), Some (IntV 4)) :: nil )%list.
  repeat split.
  ++ intros x xIn. cbn in xIn. destruct xIn; try done; subst.
     +++ cbn. repeat split.
         eexists. repeat split. intros. go. 
         intros. unfold label_comparable. intros.
         unfold in_dom in H. go. cbn in H. destruct k; try done.
         destruct k; try done. go. 
     +++ destruct H; try done; subst.
         cbn. repeat split.
         eexists. repeat split. intros. go. 
         intros. unfold label_comparable. intros.
         unfold in_dom in H. go. cbn in H. destruct k; try done.
         destruct k; try done. go. 
  ++ intros x xIn. unfold EXISTS in xIn. destruct x. cbn in xIn. go.
     destruct l; try done. destruct l; try done. go.
     destruct l; try done. go.
  ++ repeat econstructor; eauto.
Admitted.

(* 
    exists x. x 1 = 2 ; x 1 
*)

Definition ex2 : Exp 0 := 
  Exists (Seq (Unify (App (var_Val var_zero) (Int 1)) (Ret (Int 2)))
              (App (var_Val var_zero) (Int 1))).

(* We can show that "2" is in the meaning of this expression *)
Lemma evex2 : exists n, exists l, (l, Some (IntV 2)) ∈ evalExp n Vector.nil ex2.
Proof.
  exists 20.
  eexists. unfold ex2. 
  rewrite -> eval_Exists.
  unfold EXISTS.
  remember (LamV Vector.nil (Ret (Int 2))) as w'.
  remember ((App (var_Val var_zero) (Int 1) ≡ Int 2); App (var_Val var_zero) (Int 1)) as ebody.
  have VE: forall w', Valid (evalExp 19 (Vector.cons w' Vector.nil) ebody). admit.
  have EE: (((Top ⋈ Top) ⋈ Top), Some (IntV 2)) ∈ (evalExp 19 (Vector.cons w' Vector.nil) ebody).
  { subst ebody. subst w'. cbn. eexists. repeat split. }
  repeat split.
  - eexists. eauto.
  - (* need to prove that there is only one possible result *)
    intros w'' v'.
    rewrite eval_Seq. unfold SEQ.
    intro h.
    destruct h as [w1 [h1 [h2 h3]]].
    rewrite eval_Unify in h1.
    unfold INTER in h1.
    destruct h1 as [h4 h5].
    cbn in h5. inversion h5. subst.
    (* here we should know that 
       - evalExp 17 env e ⊆ evalExp 18 env e 
       - evalExp 18 env e is Valid, so a partial function
       - thus v' = Some (IntV 2)
     *)
    admit.
  - (* need to prove that all result labels are compareable with the one that we have. *)
    
    intros w'.
    unfold label_comparable.
    intro k.
    intros x.
    -- unfold WRONG in H. done.
    -- destruct o; cbn in H1; unfold WRONG in H1; try  done.
       go.
    -- unfold WRONG in H. done.
    -- 

  split; eauto. exists (IntV 2). constructor; eauto. constructor; eauto.
Qed.

(* 
What is the meaning of this term?
if (x=1) then (2 || 3) else 4; x=(1 || 2); if (x=1) then 5 else (6 || 7) 

exists x. if (x=1) then (2 || 3) else 4    ==   [2;3] ∪ [4]

exists x. if (x=1) then (2 || 3) else 4 ; if (x = 1) then 5 else (6 || 7)  

            == [5;5] ∪ [6;7]

               

*) 



(* 

(* 
∃x. (if x = 1 then 11 || 22 else 33); x = (1 || 2); (if x = 1 then 44 else (55 || 66))

           < x is 1 >               < x is 2 >
    == ([11 || 22] ; <> ; [44])  ∪ ( 33 ; <> ; [55 || 66] ) 

    == (L Top ⋈ Top ⋈ Top, 44)  ∪   (Top ⋈ Top ⋈ L Top , 55)
       (R Top ⋈ Top ⋈ Top, 44)      (Top ⋈ Top ⋈ R Top , 66)

    == (44 , 44 , 55 , 66)  or  (55, 66 , 44 , 44)

*)





Section ProperInstances.

Import SetNotations.
Import MonadNotation.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Proper instances for semantic operators                   *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


#[export] Instance UNION_Included_Proper {A} :
  Morphisms.Proper (Included ==> Included ==> Included) (@UNION A).
intros s1 t1 R1 s2 t2 R2.
unfold UNION. 
eapply union_left. 
+ eapply (@fmap_Included _ _ left) in R1.
rewrite -> R1.
eapply sub_union_left.
+ eapply (@fmap_Included _ _ right) in R2.
rewrite -> R2.
eapply sub_union_right.
Qed.

#[export] Instance UNION_Same_set_Proper {A} : Morphisms.Proper (Same_set ==> Same_set ==> Same_set) (@UNION A).
intros s1 t1 [R1 S1] s2 t2 [R2 S2].
split; eapply UNION_Included_Proper; eauto.
Qed.


#[export] Instance INTER_Included_Proper : Morphisms.Proper (Logic.eq ==> Included ==> Included) INTER.
intros s1 t1 -> s2 t2 R2.
unfold INTER. 
intros [l w] xIn.
destruct w; cbn in xIn; try done.
Admitted.

#[export] Instance INTER_Same_set_Proper : Morphisms.Proper (Logic.eq ==> Same_set ==> Same_set) INTER.
intros s1 t1 eq s2 t2 [R2 S2]. subst.
split; eapply INTER_Included_Proper; eauto.
Qed.

#[export] Instance SEQ_Included_Proper {A} : Morphisms.Proper (Included ==> Included ==> Included) (@SEQ A).
intros s1 t1 R1 s2 t2 R2.
unfold SEQ. 
apply bind_Included_Proper; auto.
intros [l1 r1].
apply bind_Included_Proper; auto.
intros [l2 r2].
reflexivity.
Qed.

#[export] Instance SEQ_Same_set_Proper {A} : Morphisms.Proper (Same_set ==> Same_set ==> Same_set) (@SEQ A).
intros s1 t1 [R1 S1] s2 t2 [R2 S2].
split; eapply SEQ_Included_Proper; eauto.
Qed.

(* NOTE: ONE is not monotonic. A larger set gives a different answer. *)
#[export] Instance ONE_Included_Proper {A} : Morphisms.Proper (Same_set ==> Included) (@ONE A).
intros s1 t1 [R1 S1].
unfold ONE. 
intros [l w] xIn.
destruct l; cbn in xIn; try done.
move: xIn => [l [h1 h2]].
cbn. exists l. split. eapply R1. auto.
intros k' w' h. apply S1 in h. eauto.
Qed.

#[export] Instance ONE_Same_set_Proper {A} : Morphisms.Proper (Same_set ==> Same_set) (@ONE A).
intros s1 t1 R1.
split; eapply ONE_Included_Proper; eauto. symmetry. auto.
Qed.

#[export] Instance EXISTS_Included_Proper {A} : Morphisms.Proper ((fun f1 f2 => (forall x, Same_set (f1 x) (f2 x))) ==> Included) (@EXISTS A).
intros s1 t1 R.
unfold EXISTS.
intros [l r] xIn.
cbn in xIn. cbn.
move: xIn => [[w h] k].
move: (R w) => [R1 R2].
split.
apply R1 in h. eauto.
intros w' r' h1.
move: (R w') => [R1' R2'].
apply R2' in h1. eauto.
Qed.

#[export] Instance EXISTS_Same_set_Proper {A} : Morphisms.Proper ((fun f1 f2 => (forall x, Same_set (f1 x) (f2 x))) ==> Same_set) (@EXISTS A).
intros s1 t1 R1.
split; eapply EXISTS_Included_Proper; eauto. symmetry. auto.
Qed.

#[export] Instance ALL_Included_Proper : Morphisms.Proper (Same_set ==> Included) ALL.
intros s1 t1 R.
unfold ALL.
intros [l r] xIn.
cbn in xIn. destruct l; try done. cbn.
destruct r. destruct w; try done.
Admitted.

#[export] Instance ALL_Same_set_Proper : Morphisms.Proper (Same_set ==> Same_set) ALL.
intros s1 t1 R.  Admitted.



(*
Definition InUpTo {A}(eqv : A -> A -> Prop) (s : A -> Prop) (w:A)  : Prop := 
  exists w', eqv w w' /\ s w'.
Definition IncludedUpTo {A}(eqv : A -> A -> Prop) (s1 s2 : A -> Prop) : Prop := 
  (forall x, InUpTo eqv s1 x -> InUpTo eqv s2 x).
Definition EqUpTo {A} (eqv : A -> A -> Prop) (s1 s2 : A -> Prop) : Prop := 
  IncludedUpTo eqv s1 s2 /\ IncludedUpTo eqv s2 s1.
*)
  
(*
Definition EqOption {A} (eqv : A -> A -> Prop) : option A -> option A -> Prop := 
  fun o1 o2 =>
    match o1 , o2 with 
    | None , None => True
    | Some a1 , Some a2 => eqv a1 a2 
    | _ , _ => False
    end.
Definition EqPair {A}{B} (eqa : A -> A -> Prop) (eqb : B -> B -> Prop) : A * B -> A * B -> Prop := 
  fun '(a1,y1) '(a2,y2) => eqa a1 a2 /\ eqb y1 y2.
*)

(*
Inductive EqV : W -> W -> Prop := 
  | EqV_IntV : forall k, EqV (IntV k) (IntV k)
  | EqV_LamV : forall m1 (env1 : Env m1) e1 m2 (env2 : Env m2) e2,
      (forall w, exists n, 
          EqUpTo (EqPair (fun l1 l2 => Label.eqb l1 l2 = true) (EqOption EqV)) 
            (evalExp n (Vector.cons w env1) e1) (evalExp n (Vector.cons w env2) e2)) ->
      EqV (LamV env1 e1) (LamV env2 e2).
*)

End ProperInstances.

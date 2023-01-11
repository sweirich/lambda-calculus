Require Export lc.tactics.

Import LCNotations.
Local Open Scope lc_scope.

(* Formalization of Barendregt's Chapter 3 (REDUCTION). *)

(** Section 3.1 Notions of reduction *)

(* We start by defining *properties* of binary term relations.
  
   In our Ott generated definitions, a `relation` is something of type
   `tm -> tm -> Prop`.
 *)

(* First, Barendregt defines three substitution properties for binary term 
   relations. Ours are similar.
*)

(* 3.1.14 *)
Definition subst1 (R : relation) := 
  forall t t' x u, lc_tm u ->
    R t t' -> R (t [ x ~> u ]) (t' [ x ~> u ]) .
Definition subst2 (R : relation) :=
  forall x t u u', lc_tm t -> 
    R u u' -> R (t [ x ~> u ]) (t [ x ~> u' ]).
Definition subst3 (R : relation) :=
  forall x t t' u u', 
    R t t' -> R u u' -> R (t [ x ~> u ]) ( t' [ x ~> u' ]).

(* In general, we expect the first property to always hold for 
   any binary term relation. 

   However, the second and third may or may not be true. 
   (For example, the second is not true for the relation "beta".)

   We'll make a class for relations that satisfy the first 
   substitution property. *)
Class substitutive (R : relation) := {
    subst : subst1 R
}.


(* An equivalence relation is one that is reflexive, symmetric and transitive.
   These definitions are similar to the Coq standard library
   (https://coq.inria.fr/library/Coq.Classes.RelationClasses.html)
   but reflexivity is only required for locally closed terms.
 *)
Class reflexive (R: relation) := {
  reflexivity : forall a : tm, lc_tm a -> R a a
}.
Class transitive (R: relation) := {
  transitivity : forall a b c : tm, R a b -> R b c -> R a c
}.
Class symmetric (R: relation) := {
  symmetry : forall a b : tm, R a b -> R b a
}.

Class equivalence (R : relation) : Prop := {
    equivalence_reflexive  :> reflexive R ;
    equivalence_symmetric  :> symmetric R ;
    equivalence_transitive :> transitive R 
}.


(* Definition 3.1.1 (i)

   A compatible relation is one that is preserved by the constructors of the
   language definition.

   Compatibility with the `abs` constructor is an important property for
   inductive relations defined by cofinite quantification and corresponds to
   an "exists-fresh" lemma.

 *)

Class compatible (R: relation) := {

    compatible_abs :  forall x t u,
      x `notin` fv_tm t \u fv_tm u ->
      R (t ^ x)(u ^ x) -> R (abs t) (abs u) ;

    compatible_app1 : forall t t' u, 
      R t t' -> lc_tm u -> R (app t u) (app t' u) ;

    compatible_app2 : forall t u u', 
      lc_tm t -> R u u' -> R (app t u) (app t u')
  }.

(* In the case when the relation is reflexive and transitive, we can 
   use the two separate properties for application at once. *)

Definition compatible_app {R} `{lc R} `{reflexive R} `{transitive R} `{compatible R} :
  forall t u t' u',
  R t t' -> R u u' -> R (app t u) (app t' u').
Proof.
  (* WORKINCLASS *)
  intros. 
  eapply transitivity with (b := (app t' u)).
  eapply compatible_app1; eauto with lngen.  
  eapply compatible_app2; eauto with lngen.
Qed. (* /WORKINCLASS *)

(* Definition 3.1.1 (ii) a congruence relation (also called an equality) is 
   a compatible equivalence relation. *)
Class congruence R := {
  congruence_equivalence :> equivalence R ;
  congruence_compatible  :> compatible R 
}.

(* Definition 3.1.1 (iii) a reduction relation is reflexive, transitive and 
  compatible. *)
Class reduction R := {
  reduction_reflexive  :> reflexive R ;
  reduction_transitive :> transitive R ;
  reduction_compatible :> compatible R
}.

(* ----------------------------------------------------------------------- *)

(* We diverge slightly from Barendregt and define a general definition for
reflexive-transitive closure and symmetric-transitive closure instead of
layering them on top of the compatible closure of the relation. *) 

Definition R_reduction (R : relation) := refl_trans_closure (compatible_closure R).
Definition R_convertibility (R : relation) := sym_trans_closure (R_reduction R).

(* We will then specialize these two to the beta relation *)

Definition β_reduction := R_reduction beta.
Definition β_convertibility := R_convertibility beta.

(* ----------------------------------------------------------------------- *)

(** ----- Properties of the compatible closure operation ------ **)

#[local]
Instance lc_compatible_closure {R} `{lc R} : lc (compatible_closure R).
Proof.
  split.
  - intros a b CC. induction CC; eauto using lc1.
  - intros a b CC. induction CC; eauto using lc2.
Qed. 

(** *** Exercise [subst1_compatible closure] *)

(* This is a standard substitution lemma *)
#[local]
Instance subst1_compatible_closure R { SR : substitutive R } : substitutive (compatible_closure R).
Proof. 
(* ADMITTED *)
  constructor. intros t t' x u LCu CC. 
  induction CC.
  - eapply cc_rel; eauto. apply subst; eauto.
  - pick fresh y and apply cc_abs. fold subst_tm. 
    spec y.
    autorewrite with lngen in H0; auto.
  - eapply cc_app1; eauto with lngen.
  - eapply cc_app2; eauto with lngen.
Qed. (* /ADMITTED *)

(** Due to the use of co-finite quantification in our definition of
    compatible_closure, we need the underlying relation to be substitutive.
    Showing this result is similiar to proving an "exists-fresh" lemma *)

#[local]
Instance compatible_compatible_closure {R} `{substitutive R} : compatible (compatible_closure R).
Proof.
    (* WORKINCLASS *)
  split;  intros; eauto.
  have SS: substitutive (compatible_closure R) by typeclasses eauto.
  pick fresh y and apply cc_abs.
  rewrite (subst_tm_intro x t); auto.
  rewrite (subst_tm_intro x u); auto.
  eapply subst; eauto.
Qed. (* /WORKINCLASS *)

(** ----------- Properties of refl_trans_closure operation ----------- **)

(** *** Exercise [lc_refl_trans_closure ] *)

#[local]
Instance lc_refl_trans_closure {R} `{lc R} : lc (refl_trans_closure R).
Proof. (* ADMITTED *)
  split.
  - induction 1; eauto using lc1.
  - induction 1; eauto using lc2.
Qed. (* /ADMITTED *)

#[local]
Instance subst1_refl_trans_closure {R} `{substitutive R} : substitutive (refl_trans_closure R).
Proof.
  constructor. unfold subst1.
  intros t t' x u LC RTC.
  induction RTC; eauto using subst with lngen.
Qed.

#[local]
Instance compatible_refl_trans_closure {R} `{compatible R} : 
  compatible (refl_trans_closure R).
Proof.
  (* WORKINCLASS *)
  split;  intros x t u H1 H0; eauto.
  + dependent induction H0. 
    - (* rt_rel *)
      eapply rt_rel. 
      eapply (compatible_abs x); eauto.
    - (* rt_refl *)
      autorewrite with lngen in x. subst. 
      eapply rt_refl; eauto with lngen.
    - (* rt_trans *) 
      eapply rt_trans with (t2 := abs (close x t2)).
      eapply IHrefl_trans_closure1 with (x := x); auto;
      autorewrite with lngen; auto.
      eapply IHrefl_trans_closure2 with (x:= x); auto;
      autorewrite with lngen; auto.
  + dependent induction H1; eauto using compatible_app1.
  + dependent induction H0; eauto using compatible_app2.
  (* /WORKINCLASS *)
Qed.


(* Properties of sym_trans_closure *)

#[local]
Instance lc_sym_trans_closure {R} `{lc R} : lc (sym_trans_closure R).
Proof. 
  have LC:forall a b, sym_trans_closure R a b -> lc_tm a /\ lc_tm b.
  { intros a b STC. induction STC; split.
    all: try destruct IHSTC. 
    all: try destruct IHSTC1.
    all: try destruct IHSTC2.    
    all: eauto with lngen.
  } 
  split.
  intros; edestruct LC; eauto.
  intros; edestruct LC; eauto.
Qed.

#[local]
Instance subst1_sym_trans_closure {R} {SR : substitutive R} : substitutive (sym_trans_closure R).
Proof.
  constructor. unfold subst1. intros t t' x u LCu STC.
  induction STC.
  - eapply st_rel; eauto using subst. 
  - eapply st_sym; eauto.
  - eapply st_trans with (t2 := t2 [x ~> u]); eauto.
Qed.

(** *** Exercise [compatible_sym_trans_closure] *)

#[local]
Instance compatible_sym_trans_closure {R} {CR: compatible R} : compatible (sym_trans_closure R).
Proof.
  (* ADMITTED *)
  constructor.
  + intros.
    dependent induction H0.
    - eapply st_rel; eauto.
      eapply compatible_abs; eauto.
    - eapply st_sym; eauto.
    - eapply st_trans with (t2 := (abs (close x t2))).
      eapply IHsym_trans_closure1; eauto.
      autorewrite with lngen; auto.
      autorewrite with lngen; auto.
      eapply IHsym_trans_closure2; eauto.
      autorewrite with lngen; auto.
      autorewrite with lngen; auto.
 + intros.
   dependent induction H.
   - eapply st_rel; eauto. 
     eapply compatible_app1; eauto.
   - eapply st_sym; eauto.
   - eapply st_trans with (t2 := app t2 u); eauto.
 + intros. dependent induction H0.
   - eapply st_rel; eauto. 
     eapply compatible_app2; eauto.      
   - eapply st_sym; eauto.
   - eapply st_trans with (t2 := app t t2); eauto.
Qed. (* /ADMITTED *)

(* --------------------------------------------------------------- *)

(* Now let's put everything together and show properties of R-reduction and R-convertibility. *)

(* Lemma 3.1.6  
   Our definition of the R_reduction operation produces a reduction relation
   and R_convertibility produces a congruence relation. *)

#[local]
Instance reduction_R_reduction R `{substitutive R} : reduction (R_reduction R).
Proof.
  split.
  constructor. eapply rt_refl.
  constructor. intros. eapply rt_trans; eauto.
  typeclasses eauto.
Qed.

#[local]
Instance congruence_R_convertibility {R} `{substitutive R}: congruence (R_convertibility R).
Proof.
  unfold R_convertibility.
  split.
  - split.  
    + constructor. intros. eapply st_rel. eapply rt_refl; eauto.
    + constructor. intros. eapply st_trans; eauto.
    + constructor. intros. eapply st_sym; eauto.
  - typeclasses eauto. 
Qed.


(* Remark 3.1.7 *)

Lemma subst2_R_reduction R `{lc R}`{substitutive R}: subst2 (R_reduction R).
Proof.
  (* WORKINCLASS *)
  unfold subst2. 
  intros x t u u' LCt Red.
  have LC: lc (refl_trans_closure (compatible_closure R)). { typeclasses eauto. }
  have CC: compatible (refl_trans_closure (compatible_closure R)). { typeclasses eauto. }
  (* induction on the "syntax" of the term *)
  induction LCt; simpl; eauto.
  + (* var *)
    destruct_var_eq.
    auto.
    eapply rt_refl. auto.
  + (* abs *) 
    pick fresh y. repeat spec y.
    eapply compatible_abs with (x:=y).
    autorewrite with lngen. auto.
    rewrite_subst_open_hyp; eauto with lngen.    
  + (* app *)
    eapply compatible_app; eauto.
Qed. (* /WORKINCLASS *)

(* --------------------------------------------------------------- *)

(** The next part defines what it means for a term to be a normal
    form (nf) according to some reduction relation R. 
  *)

(* Definition 3.1.8 *)

(* (i) A term t is a R-redex if there exists u, such that R t u *)
Print redex.

(* (ii) A term t is R-normal-form if no subterm contains an R-redex *)
Print nf.

(* (iii) A term u is a R-nf of t if u is an R-nf and t =R u. *)
Definition R_nf_of R u t := nf R u /\ R_convertibility R t u.

(* Lemma 3.1.10  (i) *)

(* Normal forms do not single-step *)

Lemma nf_normal R : forall t,
  nf R t -> not (redex (compatible_closure R) t).
Proof.
  intros t nft.
  induction nft.
  all: intros h; inversion h; subst.
  all: match goal with [H0 : compatible_closure ?R ?x ?u |- _ ] => inversion H0; subst end; eauto. 
  pick fresh x. spec x. eauto.
Qed.

(* Lemma 3.1.10  (ii) *)

(* Normal forms only reduce to themselves *)

Lemma nf_noreduction {R} : forall t,  nf R t -> forall u, R_reduction R t u -> t = u /\ nf R u.
Proof.
  intros.
  unfold R_reduction in H0. 
  dependent induction H0.
  - apply nf_normal in H.
    apply False_ind. apply H.
    exists u. auto.
  - auto.
  - destruct (IHrefl_trans_closure1 R); auto. subst.
    destruct (IHrefl_trans_closure2 R); auto.
Qed.

(* Definition 3.1.11 *) 

Definition diamond_property (R : relation) := 
  forall t t1 t2, R t t1 -> R t t2 -> exists t3, R t1 t3 /\ R t2 t3.

Definition church_rosser (R : relation) := diamond_property (R_reduction R).  

(* R-compatible terms R-reduce to a common term *)

(* Theorem 3.1.12 *)
Theorem convertibility_reduction_diamond {R} `{lc R} (CR: church_rosser R) :
  forall t u, R_convertibility R t u -> exists z, R_reduction R t z /\ R_reduction R u z.
Proof. 
  intros t u Rconv.
  have lcRR: lc (R_reduction R). { typeclasses eauto. }
  unfold R_convertibility in *.
  dependent induction Rconv.
  - exists u. split; unfold R_reduction. auto. eapply rt_refl. eapply lc2; eauto.
  - edestruct (IHRconv R) as [z [Ruz Rtz]]; eauto.
  - edestruct (IHRconv1 R) as [z1 [Rt1z1 Rt2z1]]; eauto.
    edestruct (IHRconv2 R) as [z2 [Rt2z2 Rt3z2]]; eauto.
    unfold church_rosser, diamond_property in CR.
    destruct (CR _ _ _ Rt2z1 Rt2z2) as [z3 [Rz1z3 Rz2z3]]; eauto.
    (*      t1     t2    t3
               z1     z2
                   z3           *)
    exists z3. split. 
    eapply rt_trans with (t2:= z1); eauto.
    eapply rt_trans with (t2:= z2); eauto.
Qed.


(* Corollary 3.1.13 *)
Lemma nf_reduce R `{lc R} (CR: church_rosser R) : forall u t, R_nf_of R u t -> R_reduction R t u.
Proof.
  intros u t.
  unfold R_nf_of.
  intros [NF RC].
  destruct (convertibility_reduction_diamond CR _ _ RC) as [z[Rtz Rzu]].
  edestruct (nf_noreduction _ NF _ Rzu). subst.
  auto.
Qed.
  
(* 3.1.15 *)

#[local]
Instance subst1_R_reduction {R} `{substitutive R} : substitutive (R_reduction R).
Proof.
  typeclasses eauto.
Qed.

#[local]
Lemma subst1_R_convertibility {R} `{substitutive R} : substitutive (R_convertibility R).
Proof.
  typeclasses eauto.
Qed.

(* ------------------------------- *)


(* 3.1.16 *)

#[local]
Instance subst1_beta : substitutive beta.
Proof. 
  constructor. intros t t' x u LCu Beta.
  inversion Beta. subst.
  simpl.
  autorewrite with lngen; auto.
  eapply beta_reduct; eauto with lngen.
  pick fresh y. eapply (lc_abs_exists y). 
  inversion H. spec y.
  apply subst_tm_lc_tm with (t2 := u) (x1 := x) in H2; auto.
  autorewrite with lngen in H2; auto.
Qed.

#[local]
Instance lc_beta : lc beta.
Proof. 
  econstructor.
  - intros. inversion H; auto.
  - intros. inversion H; subst; auto.
    eauto with lngen.
Qed.

(* Section 3.2 Beta reduction *)

(* If a relation has the diamond property, then so does its transitive closure. *)
(* Lemma 3.2.2 *)

Lemma diamond_property_trans_closure {R} : diamond_property R -> diamond_property (trans_closure R). 
Proof.
  intros DR.
  unfold diamond_property in *.
  intros t t1 t2 TC1.
  move: t2.
  (* A simple diagram chase suggested by figure 3.4 *)
  induction TC1; intros t2' TC2.
  - have lemma: forall u,  R t u -> exists t3, trans_closure R u t3 /\ R t2' t3.
    { clear u H.
    induction TC2; intros u0 H1.
    + edestruct (DR t u u0) as [u1 [R1 R2]]; eauto.
    + destruct (IHTC2_1 DR _ H1) as [u2 [R1 R2]].
      edestruct (IHTC2_2 DR) as [e3 [R3 R4]]. eauto. eauto.
    } 
    edestruct lemma; eauto.
    exists x. split_hyp. split; eauto.
  - destruct (IHTC1_1 DR ltac:(eauto)) as [u2 [R1 R2]]; eauto.
    edestruct (IHTC1_2 DR) as [u3 [R3 R4]]. eauto.
    exists u3. split. eauto. eapply t_trans with (t2 := u2); eauto.
Qed.

(* Definition 3.2.3 is called parallel reduction. Here are its properties. *)

#[local]
Instance lc_parallel : lc parallel.
Proof.
  have: forall a b, parallel a b -> lc_tm a /\ lc_tm b.
  { intros a b P. induction P; split; split_hyp; eauto.
  eapply lc_abs_open; eauto.
  pick fresh x. repeat spec x. split_hyp. eapply lc_abs_exists; eauto.
  pick fresh x. repeat spec x. split_hyp. eapply lc_abs_exists; eauto. }
  intros.
  split.
  intros. edestruct x; eauto.
  intros. edestruct x; eauto.  
Qed.

#[local]
Instance parallel_reflexive : reflexive parallel.
Proof.
  constructor. intros t LC.
  induction LC; eauto.
   Unshelve. exact empty.
Qed.

#[local]
Instance subst1_parallel : substitutive parallel.
Proof.
  constructor. unfold subst1.
  intros t t' x u LCu Ptt'. 
  induction Ptt'; simpl.
  - (* beta *)
    autorewrite with lngen; auto.
  - (* var *)
    destruct_var_eq;
    eauto using reflexivity.
  - (* abs *)
    pick fresh y and apply p_abs.
    spec y.
    rewrite_subst_open_hyp.
  - (* app *)
    eauto.
Qed.

#[local]
Instance compatible_parallel : compatible parallel.
Proof.
  split. 
  + intros x t u Fr P.
    pick fresh y and apply p_abs.
    rewrite (subst_tm_intro x t); auto.
    rewrite (subst_tm_intro x u); auto.
    eapply subst; eauto.
  + intros. eauto using reflexivity.
  + intros. eauto using reflexivity.
Qed.

(* Lemma 3.2.4 *)

(* This is done inline. But we have already identified this property for 
   relations, so we'll prove it separately first. *)
Lemma subst2_parallel : subst2 parallel.
Proof.
  unfold subst2.
  intros x t u u' LC P.
  induction LC; simpl.
  - (* var *)
    destruct_var_eq; auto. 
  - (* abs *)
    pick fresh y and apply p_abs.
    spec y.
    rewrite_subst_open_hyp.
    eapply lc1; eauto.
    eapply lc2; eauto. 
  - (* app *)
    eauto.
Qed.

(* Parallel reduction is *not* transitive. So we need to prove this by induction. *)
Lemma subst3_parallel : subst3 parallel.
Proof.
  unfold subst3.
  intros x t t' u u' Ptt' Puu'.
  have LCu : lc_tm u. { eapply lc1; eauto. }
  have LCu' : lc_tm u'. { eapply lc2; eauto. }
  induction Ptt'; simpl.
  - (* beta *)
    autorewrite with lngen; auto.
  - (* var *)
    destruct_var_eq; auto.
  - (* abs *)
    pick fresh y and apply p_abs.
    spec y.
    rewrite_subst_open_hyp.
  - (* app *)
    eauto.
Qed.

(* Lemma 3.2.5 *)

(* Inversion lemmas that we will inline below *)

(* Lemma 3.2.6 *)
Lemma diamond_property_parallel : diamond_property parallel.
Proof.
  unfold diamond_property.
  intros t t1 t2 H1 H2.
  move: t2 H2. (* make IH stronger *)
  induction H1; 
    intros t2 H2; inversion H2; subst.
  - (* beta / beta *)
    destruct (IHparallel1 _ H1) as [t3' [P31 P32]].
    inversion P31. subst.
    inversion P32. subst.
    destruct (IHparallel2 _ H4) as [t4' [P41 P42]].
    have LCu : lc_tm u'. eapply lc2; eauto.
    have LCu'0 : lc_tm u'0. eapply lc2; eauto.
    have LCt4' : lc_tm t4'. eapply lc2; eauto.
    pick fresh x. spec x.
    exists (open t'1 t4'). 
    apply (subst3_parallel x _ _ _ _ H0) in P41.
    repeat rewrite subst_tm_open_tm_wrt_tm in P41; auto. 
    repeat rewrite subst_eq_var in P41.
    repeat rewrite subst_tm_fresh_eq in P41; auto.
    apply (subst3_parallel x _ _ _ _ H5) in P42.
    repeat rewrite subst_tm_open_tm_wrt_tm in P42; auto. 
    repeat rewrite subst_eq_var in P42.
    repeat rewrite subst_tm_fresh_eq in P42; auto.
  - (* beta / app *)
    destruct (IHparallel1 _ H1) as [t2 [P1 P2]].
    inversion P1. subst.
    destruct (IHparallel2 _ H4) as [t3 [P3 P4]].
    have LCu : lc_tm u'. eapply lc2; eauto.
    have LCt3 : lc_tm t3. eapply lc2; eauto.
    pick fresh x. spec x.
    apply (subst3_parallel x _ _ _ _ H0) in P3.
    repeat rewrite subst_tm_open_tm_wrt_tm in P3; auto. 
    repeat rewrite subst_eq_var in P3.
    repeat rewrite subst_tm_fresh_eq in P3; auto.
    exists (open t'1 t3).
    split; auto.
  - (* var / var *)
    exists (var_f x). split; auto.
  - (* abs / abs *)
    pick fresh x. repeat spec x.
    destruct (H0 _ H3) as [t3 [P1 P2]].
    exists (abs (close x t3)).
    split.
    eapply (compatible_abs x). 
    autorewrite with lngen; auto.
    autorewrite with lngen; auto.
    eapply (compatible_abs x). 
    autorewrite with lngen; auto.
    autorewrite with lngen; auto.
  - (* app / beta *)
    destruct (IHparallel1 _ H1) as [t2 [P1 P2]].
    inversion P2. subst.
    destruct (IHparallel2 _ H4) as [t3 [P3 P4]].
    have LCu : lc_tm u. eapply lc1; eauto.
    have LCu'0 : lc_tm u'0. eapply lc2; eauto.
    have LCt3 : lc_tm t3. eapply lc2; eauto.
    pick fresh x. spec x.
    apply (subst3_parallel x _ _ _ _ H0) in P4.
    repeat rewrite subst_tm_open_tm_wrt_tm in P4; auto. 
    repeat rewrite subst_eq_var in P4.
    repeat rewrite subst_tm_fresh_eq in P4; auto.
    exists (open t'1 t3).
    split; auto.
  - (* app / app *)
    destruct (IHparallel1 _ H1) as [t2 [P1 P2]].
    destruct (IHparallel2 _ H4) as [t3 [P3 P4]].
    exists (app t2 t3).
    split; auto.
Unshelve.
   all: exact compatible_parallel.
Qed.

(* ---------------------------------------------------------------------- *)
(* Lemma 3.2.7 *)

(* This next part talks about relations between relations. *)

Module RelationNotation.
  Notation "R1 [<=] R2" := (forall t u, R1 t u -> R2 t u).
  Notation "R1 [=] R2" := (forall t u, R1 t u <-> R2 t u).
End RelationNotation.
Import RelationNotation.

(* Lemma 3.2.7 states that 

               β_reduction = trans_closure parallel

   To prove this lemma, Barendregt notes that 

           refl_closure (compatible_closure beta) [<=] parallel [<=] β_reduction

   He then says: 

      Since β_reduction is the transitive closure of the first, then it is also 
      the transitive closure of parallel reduction.

  This proof is captured in then next four lemmas.

*)

Lemma refl_compatible_sub_parallel : refl_closure (compatible_closure beta) [<=] parallel.
Proof.
  intros t u H. dependent induction H.
  - dependent induction H.
    + inversion H. eapply p_beta; eauto using reflexivity.
    + pick fresh x. spec x. eapply (compatible_abs x); eauto.
    + eapply compatible_app1; eauto using reflexivity.
    + eapply compatible_app2; eauto using reflexivity.      
  - eapply reflexivity; auto.
Qed.

Lemma parallel_sub_β_reduction : parallel [<=] β_reduction.
Proof. 
  intros.
  induction H; unfold β_reduction in *; unfold R_reduction in *.
  - apply rt_trans with (t2:= app (abs t') u').
    eapply compatible_app; eauto.
    eapply rt_rel.
    eapply cc_rel.
    eapply beta_reduct; eauto using lc1, lc2.
  - eauto.
  - pick fresh x. spec x.
    eapply (compatible_abs x); eauto.
  - eapply compatible_app; eauto.
Qed.   

Lemma β_reduction_trans_refl_cc : β_reduction [=] trans_closure (refl_closure (compatible_closure beta)).
Proof.
  unfold β_reduction, R_reduction in *. 
  split; intros h; dependent induction h; eauto.
  inversion H. eauto. eapply reflexivity. auto.
Qed.

Lemma implication : 
    β_reduction [=] trans_closure parallel.
Proof. 
  intros.
  split.
  - rewrite β_reduction_trans_refl_cc.
    intros h.
    dependent induction h.
    eapply t_rel. eapply  refl_compatible_sub_parallel. auto.
    eapply t_trans; eauto.
  - intros h.
    dependent induction h.
    eapply parallel_sub_β_reduction; auto. 
    eapply transitivity; eauto.
Qed.

(* Finally, we'll cheat a bit and to convert the [=] into a =. 
   Alternatively, we can show that the diamond property respects
   logical equivalence. *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality. 

Lemma beta_reduction_is_trans_closure_parallel : 
  β_reduction = trans_closure parallel.
Proof.
  extensionality t.
  extensionality u.
  apply propositional_extensionality.
  apply implication.
Qed.

(* Lemma 3.2.8 (Church-Rosser Theorem) *)

Lemma church_rosser_beta : church_rosser beta.
Proof.
  unfold church_rosser.
  fold β_reduction.
  rewrite beta_reduction_is_trans_closure_parallel.
  apply diamond_property_trans_closure.
  apply diamond_property_parallel.
Qed.

Lemma joinability t u (H : β_convertibility t u) :
  exists v, β_reduction t v /\ β_reduction u v.
Proof.
  apply convertibility_reduction_diamond.
  apply church_rosser_beta.
  auto.
Qed.

(* Corollary 3.2.9 (i) *)

Lemma nf_reduce_beta : forall u t, R_nf_of beta u t -> β_reduction t u.
Proof.
  intros. eapply nf_reduce; eauto.
  typeclasses eauto.
  eapply church_rosser_beta.
Qed.

(* Corollary 3.2.9 (ii) *)

Lemma nf_unique_beta : forall u1 u2 t, R_nf_of beta u1 t -> R_nf_of beta u2 t -> u1 = u2.
Proof.
  intros u1 u2 t h1 h2. 
  move: (nf_reduce_beta _ _ h1) => r1.
  move: (nf_reduce_beta _ _ h2) => r2.
  destruct h1 as [h1 h1'].
  destruct h2 as [h2 h2'].
  move: (church_rosser_beta _ _ _ r1 r2) => [v [r1' r2']].
  apply nf_noreduction in r1'; auto. destruct r1' as [eq nfv1]. subst.
  apply nf_noreduction in r2'; auto. destruct r2' as [eq nfv2]. subst.
  auto.
Qed.

(* Main result: different normal forms are not beta convertible. *)

Lemma consistency : forall t u, nf beta t -> nf beta u -> t <> u -> not (β_convertibility t u).
Proof.
  intros.
  intros h.
  move: (joinability _ _ h) => [v [rtv ruv]].
  move: (nf_noreduction _ H _ rtv) => [EQ nfv].
  move: (nf_noreduction _ H0 _ ruv) => [EQ' nfv'].
  rewrite <- EQ' in EQ.
  contradiction.
Qed.

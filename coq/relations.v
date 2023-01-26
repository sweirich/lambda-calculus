Require Export lc.tactics.
Import LCNotations.
Local Open Scope lc_scope.


(*** Formalization of Barendregt's Chapter 3 (REDUCTION). *)


(* ################################################################# *)
(** * Section 3.1 Notions of reduction *)

(** We start by defining *properties* of binary term relations.
  
    In our Ott generated definitions, a [relation] is defined as the type
    [tm -> tm -> Prop]. 

    Below, we'll use the metavariable [R] for relations, and if terms [t] and 
    [u] are related by [R], then we will write that as [R t u].

    Because we are working with a locally nameless representation, if we have 
    [R t u], we'll want to know that both [t] and [u] are locally closed. In 
    other words, we have satisfied the [lc R] constraint.

 *)

(** ** Equivalence relation (and type classes) *)

(** This is a standard mathematical definitions. An *equivalence* relation is
    one that is reflexive, symmetric and transitive.  These definitions are
    similar to those in the the Coq standard library
    (https://coq.inria.fr/library/Coq.Classes.RelationClasses.html) but note
    that reflexivity is only required for *locally closed* terms.

    A type class is a form of record type that is determined by its parameter
    [R]. We expect that there will only be one meaningful way that a relation
    can be reflexive. Later on, we will create values of this record type for
    specific relations by supplying appropriate proofs. By declaring these
    records asw type classes, Coq can find these proofs automatically, just by
    knowing what relation we are working with.  *)

Class reflexive (R: relation) := {
  reflexivity : forall t : tm, lc_tm t -> R t t
}.
Class transitive (R: relation) := {
  transitivity : forall t1 t2 t3 : tm, R t1 t2 -> R t2 t3 -> R t1 t3
}.
Class symmetric (R: relation) := {
  symmetry : forall t1 t2 : tm, R t1 t2 -> R t2 t1
}.

Class equivalence (R : relation) : Prop := {
    equivalence_reflexive  :> reflexive R ;
    equivalence_symmetric  :> symmetric R ;
    equivalence_transitive :> transitive R 
}.

(* ================================================================= *)

(** ** Compatible relation *)

(** Definition 3.1.1 (i)

   A *compatible* relation is one that is preserved by the constructors of the
   language definition. We might write this informally, using the three
   conditions.

       - (abs) R t u implies R \x.t \x.u

       - (app1) R t t' implies R (t u) (t' u)

       - (app2) R u u' implies R (t u) (t u')

   Because of our use of the locally nameless representation, we'll need to 
   add lc_tm preconditions to `compatible_app1` and `compatible_app2`.

   Also, compatibility for the `abs` constructor is stated in the "exists-fresh"
   form. We need to be able to show that the relation holds for a single 
   variable that is sufficiently fresh.

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

(** In the case when the relation is reflexive and transitive, we can use the
    two separate properties for application at once. The notation `{_} marks 
    type class arguments to this lemma. When we apply the lemma, Coq will 
    search for the values automatically. *)

Lemma compatible_app {R} `{lc R} `{reflexive R} `{transitive R} `{compatible R} :
  forall t u t' u',
  R t t' -> R u u' -> R (app t u) (app t' u').
Proof.
  (* WORKINCLASS *)
  intros. 
  eapply transitivity with (t2 := (app t' u)).
  eapply compatible_app1; eauto with lngen.  
  eapply compatible_app2; eauto with lngen.
Qed. (* /WORKINCLASS *)

(* ================================================================= *)

(** Definition 3.1.1 (ii) a *congruence* relation (also called an equality) is 
   a compatible equivalence relation. *)
Class congruence R := {
  congruence_equivalence :> equivalence R ;
  congruence_compatible  :> compatible R 
}.

(** Definition 3.1.1 (iii) a *reduction* relation is reflexive, transitive and 
  compatible. *)
Class reduction R := {
  reduction_reflexive  :> reflexive R ;
  reduction_transitive :> transitive R ;
  reduction_compatible :> compatible R
}.


(** We'll jump ahead a bit in the chapter and also define the following three
    substitution properties for binary term relations.

    In general, we expect the first property to always hold for any binary
    term relation. If two terms are related, then they should still be 
    related after substitution.

    However, the second and third may or may not be true.  (For example, the
    second is not true for primitive "beta" reduction.)  *)

(** Definition 3.1.14 *)
Definition subst1 (R : relation) := 
  forall t t' x u, lc_tm u ->
    R t t' -> R (t [ x ~> u ]) (t' [ x ~> u ]) .
Definition subst2 (R : relation) :=
  forall x t u u', lc_tm t -> 
    R u u' -> R (t [ x ~> u ]) (t [ x ~> u' ]).
Definition subst3 (R : relation) :=
  forall x t t' u u', 
    R t t' -> R u u' -> R (t [ x ~> u ]) ( t' [ x ~> u' ]).

(** We'll also make a class for relations that satisfy the first substitution
    property. *)
Class substitutive (R : relation) := {
    subst : subst1 R
}.

(** Finally, we'll say that a relation S is a closure of relation R if it 
    includes everything that is related by R (and possibly more things.
 *)
Class closure (R S : relation) := { 
    embed : forall t u, R t u -> S t u
  }.


(* ================================================================= *)

(** ** Definition 3.1.4 and 3.1.5
    
   Next, We will diverge slightly from Barendregt and use a general definition
   for reflexive-transitive closure and symmetric-transitive closure instead
   of layering them on top of compatible closure.

   Take a moment to look at the following inductive definitions that appear in
   the Ott file. These definitions are a way of taking a relation and forcing
   it to be compatible, reflexive, and transitive.  *)

Print compatible_closure.
Print refl_trans_closure.
Print sym_trans_closure.
 
(** Below are some names for specific closures of R. Below, we will call an
    arbitrary [R] a "reduction" and imagine it as a step or transition
    rule. i.e. if we have [R t u] then we say "[t] reduces to [u] via [R]".  *)

(** Allow exactly one R-reduction, anywhere inside the term. *)
Definition one_step_R_reduction (R : relation) := compatible_closure R.

(** Allow a sequence of arbitrarily many one step R-reductions *)
Definition R_reduction (R : relation) := refl_trans_closure (compatible_closure R).

(** Generate congruence relation from R-reduction, by forcing it 
    to also be symmetric. *)
Definition R_convertibility (R : relation) := sym_trans_closure (R_reduction R).

(** We will also specialize the latter definitions to the [beta] relation *)

Definition beta_reduction := R_reduction beta.
Definition beta_convertibility := R_convertibility beta.

(** Note: beta_convertibility is almost the same as beta_equivalence. However,
    beta_equivalence is defined directly as the reflexive, symmtric,
    transitive, compatible closure of beta_reduction, which is not quite the
    same as the above proof. Both definitions do relate the same terms, but
    beta_equivalence derivations are less structured than beta_conversion.

    If each of the \ and / below are beta_reductions, then a
    beta_convertibility proof looks like:

            t t1 t2 ...  t3 u \ / \ / \ / \ / t' t1' ...  u' *)


(* ================================================================= *)

(** We'll want to show that beta_reduction and beta_convertibility have the
    properties listed above. We can do so by proving those properties about
    the closure operations and asking Coq to glue these results together 
    via type class resolution. 

 *)

(** ** Properties of the compatible closure operation *)

#[local]
Instance lc_compatible_closure {R} `{lc R} : lc (compatible_closure R).
Proof.
  split.
  - intros a b CC. induction CC; eauto using lc1.
  - intros a b CC. induction CC; eauto using lc2.
Qed. 

#[local]
Instance closure_compatible_closure {R} : closure R (compatible_closure R).
Proof. constructor. intros; eauto using cc_rel. Qed.

(** *** Exercise [subst1_compatible closure] *)

(** This is a standard substitution lemma *)
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
    compatible_closure (in the Ott file), we need the underlying relation to
    be substitutive.  Showing this result is similiar to proving an
    "exists-fresh" lemma *)

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

(** ** Properties of refl_trans_closure operation **)

(** *** Exercise [lc_refl_trans_closure] *)

#[local]
Instance lc_refl_trans_closure {R} `{lc R} : lc (refl_trans_closure R).
Proof. (* ADMITTED *)
  split.
  - induction 1; eauto using lc1.
  - induction 1; eauto using lc2.
Qed. (* /ADMITTED *)

#[local]
Instance closure_refl_trans_closure {R} : closure R (refl_trans_closure R).
Proof. constructor. intros; eauto using rt_rel. Qed.

#[local]
Instance reflexive_refl_trans_closure {R}: reflexive (refl_trans_closure R).
Proof. constructor. intros. eauto using rt_refl with lngen. Qed.

#[local]
Instance transitive_refl_trans_closure {R} : transitive (refl_trans_closure R).
Proof. constructor. intros. eauto using rt_trans with lngen. Qed.

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
      eapply reflexivity; eauto with lngen.
    - (* rt_trans *) 
      eapply transitivity with (t2 := abs (close x t2)).
      eapply IHrefl_trans_closure1 with (x := x); auto;
      autorewrite with lngen; auto.
      eapply IHrefl_trans_closure2 with (x:= x); auto;
      autorewrite with lngen; auto.
  + dependent induction H1; eauto using compatible_app1.
  + dependent induction H0; eauto using compatible_app2.
Qed. (* /WORKINCLASS *)


(** ** Properties of sym_trans_closure: it preserves local closure,
substitutivity and compatibility *)

(** *** Exercise [lc_sym_trans_closure] *)
#[local]
Instance lc_sym_trans_closure {R} `{lc R} : lc (sym_trans_closure R).
Proof.  (* ADMITTED *)
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
Qed. (* /ADMITTED *)

#[local]
Instance closure_sym_trans_closure {R} : closure R (sym_trans_closure R).
Proof. constructor. intros; eauto using st_rel. Qed.

#[local]
Instance symmetric_sym_trans_closure {R} : symmetric (sym_trans_closure R).
Proof. constructor. intros. eauto using st_sym with lngen. Qed.

#[local]
Instance transitive_sym_trans_closure {R} : transitive (sym_trans_closure R).
Proof. constructor. intros. eauto using st_trans with lngen. Qed.

#[local]
Instance reflexive_sym_trans_closure {R} `{reflexive R} : 
  reflexive (sym_trans_closure R).
Proof. constructor. intros. apply embed. apply reflexivity. auto. Qed.

#[local]
Instance subst1_sym_trans_closure {R} {SR : substitutive R} : substitutive (sym_trans_closure R).
Proof.
  constructor. unfold subst1. intros t t' x u LCu STC.
  induction STC.
  - eapply embed; eauto using subst. 
  - eapply symmetry; eauto.
  - eapply transitivity with (t2 := t2 [x ~> u]); eauto.
Qed.

(** *** Exercise [compatible_sym_trans_closure] *)

#[local]
Instance compatible_sym_trans_closure {R} {CR: compatible R} : compatible (sym_trans_closure R).
Proof.
  (* ADMITTED *)
  constructor.
  + intros.
    dependent induction H0.
    - eapply embed; eauto.
      eapply compatible_abs; eauto.
    - eapply symmetry; eauto.
    - eapply transitivity with (t2 := (abs (close x t2))).
      eapply IHsym_trans_closure1; eauto.
      autorewrite with lngen; auto.
      autorewrite with lngen; auto.
      eapply IHsym_trans_closure2; eauto.
      autorewrite with lngen; auto.
      autorewrite with lngen; auto.
 + intros.
   dependent induction H.
   - eapply embed; eauto. 
     eapply compatible_app1; eauto.
   - eapply symmetry; eauto.
   - eapply transitivity with (t2 := app t2 u); eauto.
 + intros. dependent induction H0.
   - eapply embed; eauto. 
     eapply compatible_app2; eauto.      
   - eapply symmetry; eauto.
   - eapply transitivity with (t2 := app t t2); eauto.
Qed. (* /ADMITTED *)

(* ================================================================= *)

(** Now let's put everything together and show properties of R-reduction and R-convertibility. *)

(** ** Lemma 3.1.6  

   Our definition of the R_reduction operation produces a reduction relation
   and R_convertibility produces a congruence relation. 
   
*)

#[local]
Instance reduction_R_reduction R `{substitutive R} : reduction (R_reduction R).
Proof.
  split; typeclasses eauto.
Qed.

#[local]
Instance congruence_R_convertibility {R} `{substitutive R}: congruence (R_convertibility R).
Proof.
  split.
  - split; typeclasses eauto.
  - typeclasses eauto. 
Qed.


(** ** Remark 3.1.7 *)

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
    eapply reflexivity; auto.
  + (* abs *) 
    pick fresh y. spec y.
    eapply compatible_abs with (x:=y).
    autorewrite with lngen. auto.
    rewrite_subst_open_hyp; eauto with lngen.    
  + (* app *)
    eapply compatible_app; eauto.
Qed. (* /WORKINCLASS *)

(* ================================================================= *)

(** The next part defines what it means for a term to be a normal
    form [nf] according to some reduction relation R. 
  *)

(** ** Definition 3.1.8 *)

(** (i) A term t is a R-redex if there exists u, such that R t u *)
Print redex.

(** (ii) A term t is R-normal-form if no subterm contains an R-redex *)
Print nf.

(** (iii) A term u is a R-nf-of t if u is an R-nf and t is R-convertible to u. *)
Definition R_nf_of R u t := nf R u /\ R_convertibility R t u.

(** ** Lemma 3.1.10  (i) *)

(** Normal forms do not single-step *)

Lemma nf_normal R : forall t,
  nf R t -> not (redex (compatible_closure R) t).
Proof.
  intros t nft.
  induction nft.
  all: intros h; inversion h; subst.
  all: match goal with [H0 : compatible_closure ?R ?x ?u |- _ ] => inversion H0; subst end; eauto. 
  pick fresh x. spec x. eauto.
Qed.

(** ** Lemma 3.1.10  (ii) *)

(** Normal forms only reduce to themselves *)

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

(* ================================================================= *)

(** ** Definition 3.1.11 *) 

Definition diamond_property (R : relation) := 
  forall t t1 t2, R t t1 -> R t t2 -> exists t3, R t1 t3 /\ R t2 t3.

Definition church_rosser (R : relation) := diamond_property (R_reduction R).  

(** ** Theorem 3.1.12 *)

(** R-compatible terms R-reduce to a common term *)

Theorem convertibility_reduction_diamond {R} `{lc R} (CR: church_rosser R) :
  forall t u, R_convertibility R t u -> exists z, R_reduction R t z /\ R_reduction R u z.
Proof. 
  intros t u Rconv.
  have lcRR: lc (R_reduction R). { typeclasses eauto. }
  unfold R_convertibility in *.
  dependent induction Rconv.
  - exists u. split; unfold R_reduction. auto. eapply reflexivity. eapply lc2; eauto.
  - edestruct (IHRconv R) as [z [Ruz Rtz]]; eauto.
  - edestruct (IHRconv1 R) as [z1 [Rt1z1 Rt2z1]]; eauto.
    edestruct (IHRconv2 R) as [z2 [Rt2z2 Rt3z2]]; eauto.
    unfold church_rosser, diamond_property in CR.
    destruct (CR _ _ _ Rt2z1 Rt2z2) as [z3 [Rz1z3 Rz2z3]]; eauto.
    (*      t1     t2    t3
               z1     z2
                   z3           *)
    exists z3. split. 
    eapply transitivity with (t2:= z1); eauto.
    eapply transitivity with (t2:= z2); eauto.
Qed.


(** ** Corollary 3.1.13 *)
Lemma nf_reduce R `{lc R} (CR: church_rosser R) : forall u t, R_nf_of R u t -> R_reduction R t u.
Proof.
  intros u t.
  unfold R_nf_of.
  intros [NF RC].
  destruct (convertibility_reduction_diamond CR _ _ RC) as [z[Rtz Rzu]].
  edestruct (nf_noreduction _ NF _ Rzu). subst.
  auto.
Qed.
  
(** ** Proposition 3.1.15 *)

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

(** ** Proposition 3.1.16 *)

(** *** Exercise [subst1_beta] *)

#[local]
Instance subst1_beta : substitutive beta.
Proof. (* ADMITTED *)
  constructor. intros t t' x u LCu Beta.
  inversion Beta. subst.
  simpl.
  autorewrite with lngen; auto.
  eapply beta_reduct; eauto with lngen.
  pick fresh y. eapply (lc_abs_exists y). 
  inversion H. spec y.
  apply subst_tm_lc_tm with (t2 := u) (x1 := x) in H2; auto.
  autorewrite with lngen in H2; auto.
Qed. (* /ADMITTED *)

#[local]
Instance lc_beta : lc beta.
Proof. 
  econstructor.
  - intros. inversion H; auto.
  - intros. inversion H; subst; auto.
    eauto with lngen.
Qed.

(* ################################################################# *)
(** * Section 3.2 Beta reduction *)

(** This section studies the relation [beta_reduction] more closely and shows 
    that it is Church-Rosser using a proof that Barendregt attributes to 
    Tait and Martin-Lof. 

   We won't show that beta_reduction satisfies the diamond property directly. Instead 
   we will define another relation, called "parallel reduction", and derive this 
   property from the lemma below and the following two facts:

      - parallel reduction satisfies the diamond property

      - beta_reduction is the transitive closure of parallel reduction
      
   *)

(** ** Lemma 3.2.2 *)
(** If a relation has the diamond property, then so does its transitive closure. 

Barendregt's proof is "A simple diagram chase suggested by figure 3.4". See 
if you can figure out how to translate that figure to a (nested) induction.
*)

(** *** Exercise [diamond_property_trans_closure] *)

Lemma diamond_property_trans_closure {R} : diamond_property R -> diamond_property (trans_closure R). 
Proof. 
  intros DR.
  unfold diamond_property in *.
  intros t t1 t2 TC1.
  move: t2.
  (* ADMITTED *)
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
Qed. (* /ADMITTED *)

(* ================================================================= *)

(** ** Definition 3.2.3 is often called parallel reduction. *)

Print parallel.

(** Properties of parallel reduction *)

#[local]
Instance lc_parallel : lc parallel.
Proof.
  have: forall a b, parallel a b -> lc_tm a /\ lc_tm b.
  { intros a b P. induction P; split; split_hyp; eauto.
  eapply lc_abs_open; eauto.
  pick fresh x. repeat spec x. split_hyp. eapply lc_abs_exists; eauto.
  pick fresh x. repeat spec x. split_hyp. eapply lc_abs_exists; eauto. }
  intros h.
  split;  intros a b h1; edestruct h; eauto.
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

(** ** Lemma 3.2.4  

   Parallel reduction satisfies the second and third substitution properties.
   This is a key part of the Church-Rosser proof.
 *)

(** This is done inline. But we have already identified this property for 
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

(** Parallel reduction is *not* transitive. So we need to prove this by induction. *)
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

(** A corollary of the above lets us reason about parallel reduction for opened terms. *)
Corollary parallel_open : forall x t t' u u',
  x `notin` fv_tm t 
  -> x `notin` fv_tm t'
  -> parallel (t ^ x) (t' ^ x) 
  -> parallel u u' 
  -> parallel (open t u) (open t' u').
Proof.  
  intros x t t' u u' F1 F2 H0 P41.
  move: (subst3_parallel x _ _ _ _ H0 P41) => h.
  repeat rewrite subst_tm_open_tm_wrt_tm in h; eauto.
  eapply lc1; eauto with lngen.
  eapply lc2; eauto with lngen.
  repeat rewrite subst_eq_var in h.
  repeat rewrite subst_tm_fresh_eq in h; auto.
Qed.



(* ================================================================= *)

(** ** Lemma 3.2.6 *)

(** The first of our two key lemmas: parallel reduction satisfies 
the diamond property. *)

Lemma diamond_property_parallel : diamond_property parallel.
Proof.
  (* WORKINCLASS *)
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
    pick fresh x. spec x.
    exists (open t'1 t4'). 
    split; eauto using parallel_open. 
  - (* beta / app *)
    destruct (IHparallel1 _ H1) as [t2 [P1 P2]].
    inversion P1. subst.
    destruct (IHparallel2 _ H4) as [t3 [P3 P4]].
    pick fresh x. spec x.
    exists (open t'1 t3).
    split; eauto using parallel_open.
  - (* var / var *)
    exists (var_f x). split; auto.
  - (* abs / abs *)
    pick fresh x. repeat spec x.
    destruct (H0 _ H3) as [t3 [P1 P2]].
    exists (abs (close x t3)).
    split.
    eapply (compatible_abs x);
    autorewrite with lngen; auto.
    eapply (compatible_abs x);
    autorewrite with lngen; auto.
  - (* app / beta *)
    destruct (IHparallel1 _ H1) as [t2 [P1 P2]].
    inversion P2. subst.
    destruct (IHparallel2 _ H4) as [t3 [P3 P4]].
    pick fresh x. spec x.
    exists (open t'1 t3).
    split; eauto using parallel_open. 
  - (* app / app *)
    destruct (IHparallel1 _ H1) as [t2 [P1 P2]].
    destruct (IHparallel2 _ H4) as [t3 [P3 P4]].
    exists (app t2 t3).
    split; auto.
Qed. (* /WORKINCLASS *)

(* ================================================================= *)

(** This next part talks about relations between relations. To make this 
    a bit easier to work with, we'll introduce some notation for when 
    one relation implies another and when one relation is equivalent to 
    another
*)

Module RelationNotation.
  Notation "R1 [<=] R2" := (forall t u, R1 t u -> R2 t u).
  Notation "R1 [=] R2" := (forall t u, R1 t u <-> R2 t u).
End RelationNotation.
Import RelationNotation.

(** ** Lemma 3.2.7 *)

(** Lemma 3.2.7 states that 

               beta_reduction = trans_closure parallel

   To prove this lemma, Barendregt notes that 

           refl_closure (compatible_closure beta) [<=] parallel [<=] beta_reduction

   He then says: 

      Since beta_reduction is the transitive closure of the first, then it is also 
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

(** *** Exercise [parallel_sub_beta_reduction] *)

Lemma parallel_sub_beta_reduction : parallel [<=] beta_reduction.
Proof. (* ADMITTED *)
  intros.
  induction H; unfold beta_reduction in *; unfold R_reduction in *.
  - apply transitivity with (t2:= app (abs t') u').
    eapply compatible_app; eauto.
    eapply embed.
    eapply embed.
    eapply beta_reduct; eauto using lc1, lc2.
  - eauto.
  - pick fresh x. spec x.
    eapply (compatible_abs x); eauto.
  - eapply compatible_app; eauto.
Qed. (* /ADMITTED *)

Lemma beta_reduction_trans_refl_cc : beta_reduction [=] trans_closure (refl_closure (compatible_closure beta)).
Proof.
  unfold beta_reduction, R_reduction in *. 
  split; intros h; dependent induction h; eauto.
  inversion H. eauto. eapply reflexivity. auto.
Qed.

Lemma  beta_reduction_is_trans_closure_parallel : 
   beta_reduction [=] trans_closure parallel.
Proof. 
  intros.
  split.
  - rewrite beta_reduction_trans_refl_cc.
    intros h.
    dependent induction h.
    eapply t_rel. 
    eapply refl_compatible_sub_parallel. auto.
    eapply t_trans; eauto.
  - intros h.
    dependent induction h.
    eapply parallel_sub_beta_reduction; auto. 
    eapply transitivity; eauto.
Qed.

(** To use this result, we also need to show that the diamond
    property respects relational equivalence. This is mostly a matter 
    of unfolding definitions. *)

Lemma diamond_respects : forall R1 R2,
  R1 [=] R2 ->
  diamond_property R1 ->
  diamond_property R2.
Proof.
  intros R1 R2 rr.
  unfold diamond_property. 
  intros db t1 t2 t3 T1 T2.
  rewrite <- rr in T1.
  rewrite <- rr in T2.
  destruct (db t1 t2 t3 T1 T2) as [t4 [b1 b2]].
  exists t4.
  rewrite -> rr in b1.
  rewrite -> rr in b2.
  split; auto.
Qed.

(* ================================================================= *)

(** * Lemma 3.2.8 (Church-Rosser Theorem) *)

Lemma church_rosser_beta : church_rosser beta.
Proof.
  unfold church_rosser.
  fold beta_reduction.
  eapply diamond_respects.
  symmetry.
  eapply beta_reduction_is_trans_closure_parallel.
  apply diamond_property_trans_closure.
  apply diamond_property_parallel.
Qed.

(* ================================================================= *)

(** ** Corollary 3.2.9 (i) *)

Lemma nf_reduce_beta : forall u t, R_nf_of beta u t -> beta_reduction t u.
Proof.
  intros. eapply nf_reduce; eauto.
  typeclasses eauto.
  eapply church_rosser_beta.
Qed.

(** ** Corollary 3.2.9 (ii) *)

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

Lemma joinability t u (H : beta_convertibility t u) :
  exists v, beta_reduction t v /\ beta_reduction u v.
Proof.
  apply convertibility_reduction_diamond.
  apply church_rosser_beta.
  auto.
Qed.

(** ** Main result: different normal forms are not beta convertible. *)

Lemma consistency : forall t u, nf beta t -> nf beta u -> t <> u -> not (beta_convertibility t u).
Proof.
  intros.
  intros h.
  move: (joinability _ _ h) => [v [rtv ruv]].
  move: (nf_noreduction _ H _ rtv) => [EQ nfv].
  move: (nf_noreduction _ H0 _ ruv) => [EQ' nfv'].
  rewrite <- EQ' in EQ.
  contradiction.
Qed.


(** For completness, we will exhibit two different normal forms. *)

(* " \x. \y. x" *)
Definition church_true := abs (abs (var_b 1)).

(* " \x. \y. y" *)
Definition church_false := abs (abs (var_b 0)).

Lemma nf_true : nf beta church_true.
Proof.
  pick fresh x and apply nf_abs.
  pick fresh y and apply nf_abs.
  apply nf_var.
  intro h; inversion h; inversion H.
  intro h; inversion h; inversion H.
  intro h; inversion h; inversion H.
Qed.

Lemma nf_false : nf beta church_false.
Proof.
  pick fresh x and apply nf_abs.
  pick fresh y and apply nf_abs.
  apply nf_var.
  intro h; inversion h; inversion H.
  intro h; inversion h; inversion H.
  intro h; inversion h; inversion H.
Qed.

Lemma not_convertible_true_false : not (beta_convertibility church_true church_false).
Proof.
  apply consistency.
  apply nf_true.
  apply nf_false.
  intro h. inversion h.
Qed.

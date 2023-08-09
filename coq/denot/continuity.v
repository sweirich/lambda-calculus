(*

This section proves that the denotation function is monotonic and continuous.

Monotonicity

   Definition monotone (F : P Value -> P Value) : Set := forall D1 D2, (D1 ⊆
         D2) -> F D1 ⊆ F D2.

   Lemma denot_monotone_one : forall ρ t x, uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot (t ^ x) (x ~ D ++ ρ)).

Continuity:

   A semantic function is continuous if any finite subset of any result of X
   can be produced by a finite and valid subset of X.

   [Alex notes: this is algebraicity, equivalent to continuity for this kind
   of model.  To produce a finite output you only need a finite input.]
   
   If our functions only concerned sets of values, then we might define
   continuous as:

        Definition continuous (F : P Value -> P Value) : Set := 
          forall (X : P Value) (E : Comp (list B)), 
             mem E ⊆ F X -> valid X -> 
                exists (D : list Value), 
                    (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

   However, our denotation function, used in the following lemma,

       Lemma denot_continuous_one { t ρ x } : valid_env ρ 
          -> x `notin` dom ρ
          -> continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).

   has type `P Value -> P (Comp (P Value))`.

   Furthermore, in showing that this function is continuous, we also need to
   reason about the continuity of the 'bind' operator.

Why continuous and monotone?
   
   The payoff for this section is a lemma for understanding how LAMBDA and
   APPLY interact.  The general lemma looks like this:

        Lemma Λ_APPLY_id { F X } : 
             continuous F -> monotone F -> valid X -> 
             (Λ F) ▩ X ≃ F X.

   With the above results, we can instantiate it to reason about the denotation
   function.

        Lemma Λ_denot_APPLY_id : forall t ρ x X, 
            valid X -> 
            valid_env ρ -> x `notin` dom ρ -> 
               ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) 
                 ≃ denot (t ^ x) (x ~ X ++ ρ).

 *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.

Require Import denot.definitions.
Require Import denot.denot.
Require Import denot.congruence_theory.
Require Import denot.valid_theory.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.
Import LCNotations.
Open Scope tm.

Import EnvNotations.

Lemma In_Sub {A}{x:A}{D}: x ∈ D <-> mem (x :: nil) ⊆ D.
Proof. split. intros h y yIn. inversion yIn. subst; auto. inversion H. 
       intros h. cbv in h. specialize (h x). tauto.
Qed.

#[export] Hint Resolve In_Sub:core.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).


Lemma denot_val_lit : forall k ρ,  denot_val (lit k) ρ = (NAT k).
Proof. intros. reflexivity. Qed. 

Lemma denot_val_add : forall ρ,  denot_val add ρ = ADD.
Proof. intros. reflexivity. Qed. 

Lemma denot_val_tnil : forall ρ,  denot_val tnil ρ = NIL.
Proof.  intros. reflexivity. Qed. 


Lemma denot_val_abs : forall x t ρ,
    x `notin` dom ρ \u fv_tm t ->
    denot_val (abs t) ρ = 
      (Λ2 (fun D => denot (t ^ x) (x ~ D ++ ρ))).
Proof.
  intros.
  unfold denot_val,denot. simpl.
  rewrite size_tm_open_tm_wrt_tm_var.
  f_equal. f_equal.
  extensionality D.
  name_binder x0 Frx0.
  simpl_env. 
  rewrite -> (rename_open_denot x0 x); eauto.
Qed.

Lemma denot_val_tcons : forall t u ρ, 
    denot_val (tcons t u) ρ = CONS (denot_val t ρ) (denot_val u ρ).
Proof. 
  intros.
  unfold denot_val. simpl.
  f_equal.
  rewrite size_is_enough_val. lia. auto.
  rewrite size_is_enough_val. lia. auto.
Qed.


#[export] Hint Rewrite denot_val_var denot_val_lit 
  denot_val_add denot_val_tnil denot_val_tcons : denot.

#[export] Instance Proper_sub_denot_val : Proper (eq ==> Env.Forall2 Included ==> Included) denot_val.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: move => ρ1 ρ2 SUB.
  all: autorewrite with denot.
  all: try solve  [ simpl; reflexivity].
  + eapply access_mono_sub; eauto.
  + pick fresh x. 
    repeat rewrite(denot_val_abs x). fsetdec. fsetdec.
    eapply Λ_ext_sub.
    intros X neX.
    have SUBe: (x ~ X ++ ρ1) ⊆e (x ~ X ++ ρ2).
    econstructor; eauto. reflexivity.
    eapply Proper_sub_denot; eauto. 
  + eapply CONS_mono_sub; eauto.
Qed. 

(* Definitions related to continuity 

   For every finite approximation of an output, there is a finite approximation
   of an input.

   If the type is P Value, then the approx is list Value
   If the type is P (Comp (P Value)), then the approx is list (Comp (list Value))

*)

Definition continuous {A} (F : P Value -> P A) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

Definition finite_env : Rho -> Type := Env.ForallT finite.

Definition continuous_In {A} (D:Rho -> P A) (ρ:Rho) (v:A) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env {A} (D:Rho -> P A) (ρ:Rho) : Prop :=
  forall (v : A), continuous_In D ρ v.

(* ----- Definitions for continuity --- functions that return computations *)

(* Note: this is not the same as `inj C ⊆ D`, the sets in c_multi may 
   be subsets of the sets in D. *)
Definition Approx (C : list (Comp (list Value))) (D: P (Comp (P Value))) : Prop :=
  forall c, List.In c C -> Comp_Approx_in c D.

Lemma Comp_Approx_mem {A} : forall (c : Comp (list A)),  Comp_Approx c (fmap mem c).
intros. destruct c. 
all: econstructor; eauto.
induction l.
- simpl; auto.
- simpl. econstructor. reflexivity. auto.
Qed. 

Lemma Comp_inj_Approx : forall C, Approx C (Comp_inj C).
Proof.
  intros. destruct C. cbv. intros. done.
  unfold Approx. intros. destruct H. subst.
  exists (fmap mem c0). split; eauto. unfold Comp_inj. cbn. left.  auto.
  destruct c0. simpl. econstructor; eauto. 
  econstructor; eauto.
  induction l. simpl. auto.
  econstructor; eauto. reflexivity.
  exists (fmap mem c0).
  split.
  cbn. right.
  eapply in_map. auto.
  eapply Comp_Approx_mem; eauto.
Qed.
 
Definition continuous_M (F : P Value -> M (P Value)) : Set :=
  forall X E, Approx E (F X) -> valid X 
         -> exists D, (mem D ⊆ X) /\ (Approx E (F (mem D))) /\ valid_mem D.

(* ----- Definitions for generalized continuty --- any input, any output *)

(* A type can be finitely approximated by another type if there is 
   an injection and a relation. 
   There are probably some properties we need from these definitions,
   but I'm note sure what they are yet.
*)
Class FinApprox (A : Type) := 
  { Finite : Type; 
    inj    : Finite -> A; 
    approx : Finite -> A -> Prop 
  }.

Infix "⊑" := approx (at level 65).

(* Approximate sets of values by lists of values *)
#[global] Instance FAV : FinApprox (P Value) := 
  { Finite := list Value; 
    inj    := mem; 
    approx := fun l X => mem l ⊆ X }.

(* Approximate valid sets of values by valid lists of values *)
#[global] Instance FAVNE : FinApprox { x : P Value & valid x } := 
  { Finite := { x : list Value & valid_mem x }; 
    inj := fun x => match x with
                   | existT _ y z => existT _ (mem y) (valid_mem_valid z)
                 end;
    approx := fun l X => mem (projT1 l) ⊆ (projT1 X) }.

(* Approximate computations *)
#[global] Instance FAC : FinApprox (P (Comp (P Value))) := 
  { Finite := list (Comp (list Value));
    inj    := Comp_inj;
    approx := Approx
  }.

(* Approximate environments by finite environments *)
#[global] Instance FAR : FinApprox Rho := 
  { Finite    := { ρ & finite_env ρ };
    inj       := @projT1 Rho finite_env;
    approx    := fun x y => Env.Forall2 Included (projT1 x) y
  }.

(* A function F is continuous for an argument X, if for all finite approximations 
   of the result, there is a finite approximation of X that returns the same
   result. *)
Definition continuous_For {A B :Type}`{FinApprox A}`{FinApprox B} (F : A -> B)
  (X : A) : Prop :=
  forall (E : Finite), E ⊑ F X -> exists (D : Finite), (D ⊑ X) /\ (E ⊑ F (inj D)).

(* A function F is continuous if it is continuous for every argument. *)
Definition continuous' {A B :Type}`{FinApprox A}`{FinApprox B} (F : A -> B) : Prop :=
  forall X, continuous_For F X.

(* Functions that are continuous for a specific environment. *)
Definition continuous_env' {A}`{FinApprox A}(F : Rho -> A) : Rho -> Prop :=
  continuous_For F.



(* -- monotonicity WRT environments -- *)

(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: 
  monotone_env (denot t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot; auto.
Qed.

Lemma denot_val_monotone {t}: 
  monotone_env (denot_val t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot_val; auto.
Qed.

(* -- monotonicity WRT argument -- *)
(* denot-monotone-one *)
Lemma denot_monotone_one : forall ρ t x, 
    uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  eapply denot_monotone; simpl; auto.
  econstructor; eauto.
Qed.
  

(* ----------------------------------------------------- *)

(* Join environments *)

Lemma join_finite_env {ρ1 ρ2} : 
  same_scope ρ1 ρ2 
  -> finite_env ρ1
  -> finite_env ρ2
  -> finite_env (ρ1 ⊔e ρ2).
Proof.
  move: ρ2.
  induction ρ1 as [|[x1 v1] r1].
  all: intros ρ2 sc h1; destruct ρ2 as [|[x2 v2] r2]; intros h2; simpl; eauto.
  inversion h1; subst; clear h1.
  inversion h2; subst; clear h2.
  destruct (x1 == x2); subst.
  + econstructor; eauto. eapply IHr1; eauto. inversion sc. auto.
    rewrite sub_dom1; auto.
    destruct H3 as [E1 [s1 u1 ]].
    destruct H5 as [E2 [s2 u2 ]].
    exists (E1 ++ E2).
    split.
    rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    ++ intro h.
    apply u2. 
    destruct E1. simpl in h. auto.
    done.
  + assert False. inversion sc. subst. done. done.
Qed.

Lemma join_lub {ρ ρ1 : Rho} :
  same_scope ρ1 ρ ->
  forall ρ2, same_scope ρ2 ρ ->
  ρ1 ⊆e ρ -> ρ2 ⊆e ρ -> (ρ1 ⊔e ρ2) ⊆e ρ.
Proof.
  intro SS1.
  induction SS1; intros ρ2 SS2; inversion SS2; subst.
  simpl. auto.
  intros.
  simpl.
  inversion H1. inversion H2. subst.
  rewrite eq_dec_refl.
  eapply Env.Forall2_cons; eauto.
  rewrite sub_dom1. auto.
  rewrite -> H21.
  rewrite -> H13.
  rewrite union_idem.
  reflexivity.
Qed.
  
Lemma join_sub_left {ρ1 ρ2 : Rho} : 
  same_scope ρ1 ρ2 ->
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros h.
  induction h; simpl; eauto.
  rewrite eq_dec_refl.
  econstructor; eauto. 
Qed.

Lemma join_sub_right {ρ1 ρ2 : Rho} : 
  same_scope ρ1 ρ2 ->
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
  induction 1; simpl; eauto. 
  rewrite eq_dec_refl.
  econstructor; eauto. 
  erewrite Forall2_dom in H0; eauto.
Qed.

(* --------------------------------------- *)

(* Initial environment. *)

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
Definition initial_finite_env (ρ : Rho) (NE : valid_env ρ) : Rho.
  induction NE. exact nil.
  destruct f as [V _].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [v w].  simpl. congruence.
Qed. 

#[export] Hint Rewrite initial_finite_dom : rewr_list.

Lemma finite_singleton : forall {B} (v : B), finite ⌈ v ⌉.
Proof. intros B v.  exists (cons v nil).
       repeat split; eauto. done. 
Qed.

#[export] Hint Resolve finite_singleton : core. 


Lemma initial_fin (ρ : Rho) (NE : valid_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [v w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

#[global] Hint Resolve initial_fin : core. 


Lemma initial_fin_sub (ρ : Rho) (NE : valid_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [v fx].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

#[global] Hint Resolve initial_fin_sub : core. 


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Rho) 
  (NE : valid_env ρ) : Rho :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { X x ρ NE } : 
  finite X ->
  finite_env (single_env x X ρ NE).
Proof.
  induction NE; intro FIN; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. 
  destruct f as [v1 v2].
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. simpl_env. auto. auto.
  + rewrite update_neq_var; eauto.
    econstructor; eauto.
    eapply IHNE; eauto.
    simpl_env. auto.
Qed.

#[global] Hint Resolve single_fin : core. 


Lemma single_sub { ρ x V } :
  forall (NE : valid_env ρ),
    V ⊆ ρ ⋅ x 
  -> x `in` dom ρ
  -> (single_env x V ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) auto. 
  + (* cons case *)
    unfold single_env in *.
    simpl. simpl_env in Indom.
    destruct f as [w h2]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       simpl_env.  eauto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. auto.
Qed.

#[export] Hint Resolve single_sub : core. 


Lemma update_access : forall {x ρ NE X},
  x `in` dom ρ ->
  X ≃ (single_env x X ρ NE) ⋅ x.
Proof.
  intros.
  unfold single_env.
  move: NE.
  induction NE. fsetdec.
  simpl. destruct f as [w h2]. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. reflexivity.
  simpl. rewrite EQ. eapply IHNE; auto. simpl in H. fsetdec.
Qed.  

(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x `in` dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE.
  induction NE; intro h. fsetdec.
  simpl. destruct f as [w h2]. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. econstructor; eauto.
  simpl. rewrite EQ. simpl in h. eapply IHNE; auto. fsetdec.
Qed.  

#[export] Hint Resolve v_single_xvx : core. 



(* continuous-∈⇒⊆ *)

Lemma continuous_In_sub (E : Rho -> (P Value)) ρ (NE : valid_env ρ) :
   monotone_env E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', exists (pf : finite_env ρ') ,  ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
Proof.
  intros me V VE vcont.
  induction V.
  - exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply initial_fin_sub; eauto. 
    done.
  - destruct IHV as [ ρ1 [ fρ1 [ ρ1ρ VEρ1 ]]].
    intros d z. eapply VE; eauto.
    intros v VM. eapply vcont; eauto.
    destruct (vcont a) as [ρ2 [fρ2 [ρ2ρ VEρ2]]].
    econstructor; eauto.
    eapply VE. econstructor; eauto.
    exists (ρ1 ⊔e ρ2).
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto. 
    have SS: same_scope ρ1 ρ2. 
    { transitivity ρ; auto. symmetry; auto. }
    eexists. eapply join_finite_env; eauto.
    repeat split.
    + eapply join_lub; eauto.
    + intros d dm.
    inversion dm; subst.
    eapply me. eapply join_sub_right; eauto. auto. 
    eapply me. eapply join_sub_left; eauto. auto.
Qed.



Lemma continuous_In_sub' (E : Rho -> M (P Value)) ρ (NE : valid_env ρ) :
   monotone_env E
   -> continuous_For E ρ
   -> forall V, V ⊑ E ρ
   -> exists ρ', exists (pf : finite_env ρ') ,  ρ' ⊆e ρ /\ (V ⊑ E ρ').
Proof.
  intros me vcont V VE.
  unfold continuous_For in vcont.
  specialize (vcont V VE).
  move: vcont => [ [ρ' fρ'] [h1 h2]].
  cbn in h1.
  cbn in h2.
  eexists ρ'. eexists. auto.
  split; eauto.
Qed.

(*  induction V.
  - exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply initial_fin_sub; eauto. 
    done.
  - 
    
    destruct IHV as [ ρ1 [ fρ1 [ ρ1ρ VEρ1 ]]].
    intros d D inV inE.
    eapply VE; eauto. simpl. right; auto.

   
    destruct (vcont a) as [ρ2 [fρ2 [ρ2ρ VEρ2]]].
    econstructor; eauto.
    eapply VE. econstructor; eauto.
    exists (ρ1 ⊔e ρ2).
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto. 
    have SS: same_scope ρ1 ρ2. 
    { transitivity ρ; auto. symmetry; auto. }
    eexists. eapply join_finite_env; eauto.
    repeat split.
    + eapply join_lub; eauto.
    + intros d dm.
    inversion dm; subst.
    eapply me. eapply join_sub_right; eauto. auto. 
    eapply me. eapply join_sub_left; eauto. auto.
Qed. *)



(* --------------------------------------- *)

(* Operations are continuous *)

Lemma mem_injective {A} {l1 l2 : list A} : mem l1 = mem l2 -> l1 = l2.
Proof. 
  move: l2. induction l1; intros l2 h; destruct l2; try done.
  unfold mem in h.
Admitted.

Lemma map_mem_injective {A}{l l0 : list (list A)} :
  List.map mem l = List.map mem l0 -> l = l0.
Proof.
  move: l0.
  induction l; intro l0; destruct l0; intro h; try done.
  simpl in h. inversion h.  
  eapply mem_injective in H0.
  eapply IHl in H1; eauto.
  f_equal; auto.
Qed.

Lemma fmap_Comp_mem_injective {w0 w : Comp (list Value)} 
  : fmap_Comp mem w0 = fmap_Comp mem w -> w0 = w.
Proof.
  intro h.
  destruct w0; destruct w; try done.
  inversion h.
  apply map_mem_injective in H0.
  f_equal; auto.
Qed.

Lemma singleton_mem_singleton {A}{w:A}{l} :
 ⌈ w ⌉ = mem l -> l = (w :: nil).
Proof.
  destruct l; unfold mem.
  intro h.
  have h1: ⌈ w ⌉ w = (fun x : A => In x nil) w.
  rewrite h. auto.
  simpl in h1. 
  have h2:  ⌈ w ⌉ w. eapply in_singleton. rewrite h1 in h2. done.
  intro h.
  have h1: ⌈ w ⌉ w = (fun x : A => In x (a :: l)) w.
  rewrite h. done.
  have h2:  ⌈ w ⌉ w. eapply in_singleton. rewrite h1 in h2.
  inversion h2. subst. 
Admitted.

Lemma APPLY_continuous {D E ρ}{w : Comp (list Value)} :
  (valid_env ρ)
  -> fmap mem w ∈ (D ρ ▩ E ρ)
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ' , 
    exists (pf : finite_env ρ') , ρ' ⊆e ρ /\ (fmap mem w ∈ (D ρ' ▩ E ρ')).
Proof.  
  intros NE APP. inversion APP; subst. 
  all: intros IHD IHE mD mE.
  + apply fmap_Comp_mem_injective in H; subst.
    destruct (IHD ( V ↦ w ) ltac:(auto)) (* finite_Singleton (In_Included H)) *) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - have VwDp3 : ⌈ V ↦ w ⌉ ⊆ D (ρ1 ⊔e ρ2).
    { transitivity (D ρ1); auto. eapply mD. 
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { transitivity (E ρ2); auto. eapply mE.
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
 + unfold pure_Comp in H; destruct w; try done.
   destruct l; try destruct l0; try done. 
   simpl in H. inversion H. apply singleton_mem_singleton in H3.
   subst. clear H.
   destruct (IHD (v_list VS) ) as [ρ1 [F1 [h1 h2]]]; auto.
   destruct (IHE (v_nat k) ) as [ρ2 [F2 [h3 h4]]]; auto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
   exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.    
  - eapply join_lub; eauto.
  - cbn. 
    replace (mem (w0 :: nil)) with ⌈ w0 ⌉. 
    eapply PROJ with (VS := VS) (k:=k); eauto.
    eapply mD. eapply join_sub_left; auto. auto.
    eapply mE. eapply join_sub_right; auto. auto.
    eapply Extensionality_Ensembles.
    split; eauto. 
 + destruct w; try done. 
   destruct (IHD x) as [ρ1 [F1 [h1 h2]]]; auto.
    eexists.
    eexists.
    eauto.
    split; eauto.
    eapply APPWRONG with (x:=x); auto.
 + destruct w; try done. 
   destruct (IHE x) as [ρ2 [F1 [h1 h2]]]; auto.
    destruct (IHD (v_list VS)) as [ρ1 [F2 [h01 h02]]]; auto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    - eapply join_finite_env; eauto.    
    - eapply join_lub; eauto.
    - eapply PROJWRONG with (VS := VS); eauto.
    eapply mD. eapply join_sub_left; auto. auto.
    eapply mE. eapply join_sub_right; auto. auto.
Qed.



Lemma env_tail {ρ' x v ρ} :  
  ρ' ⊆e (x ~ v ++ ρ) -> finite_env ρ' -> 
  nonempty_env ρ ->
  exists w, exists ρ'', ρ' = (x ~ w ++ ρ'') /\
                (w ⊆ v) /\
                exists (pf : finite_env ρ''), 
                ρ'' ⊆e ρ.                
Proof.
  intros h k ne.
  inversion h. subst.
  exists a1.  exists E1.
  repeat split; auto. inversion k.  auto.
Qed.

(* Algebraicity.  
   Only need finite information from the environment.
*)

Lemma In_Approx {c : Comp (list Value)}{E : M (P Value)} :
 fmap mem c ∈ E -> Approx (c :: nil) E.
Proof.
  unfold Approx.
  intros. simpl in H0. destruct H0; try done; subst.
  exists (fmap mem c0). 
  split; eauto.
  eapply Comp_Approx_mem.
Qed.

Lemma Lambda_continuous {E ρ x} {NE : valid_env ρ}{v} :
  v ∈ Λ2 (fun D => E (x ~ D ++ ρ)) 
  -> x `notin` dom ρ
  -> (forall V, valid_mem V -> continuous_env' E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\ (v ∈ (Λ2 (fun D => E (x ~ D ++ ρ')))).
Proof.
Admitted.
(*
  induction v.
  all: try solve [intros; cbv in H; done].
  - (* v is l ↦ c *)
    intros [ wEVρ NW ] Fr IH mE.

    have VV: valid_mem l. unfold valid_mem. eauto.
    have NEx: valid_env (x ~ mem l ++ ρ). econstructor; eauto.

    specialize (IH l ltac:(eauto)).

    unfold continuous_env', continuous_For, Finite, FAC, FAR in IH.

    move: (IH (c :: nil)) => h.
    destruct h as [ [ρ' fρ'] [ ρ'Vρ wEρ' ]]. 
    { eapply In_Approx. auto. }

    simpl in wEρ'. unfold Approx in wEρ'.
    specialize (wEρ' c). 
    destruct wEρ' as [d [dIn apx]]. simpl; left; auto.

    inversion ρ'Vρ. simpl in H2. subst. clear ρ'Vρ. 
    inversion fρ'. subst.  clear fρ'.

    exists E1. exists X.
    split. eauto.
    cbn. split; auto.

    have SE: (x ~ a1 ++ E1) ⊆e (x ~ mem l ++ E1).
    econstructor; eauto. eapply Reflexive_sub_env. eapply Forall2_uniq1; eauto.
    eapply mE. eapply SE. clear SE.

    inversion apx; subst. simpl; eauto.
    
    

    unfold continuous_env', continuous_For in IH.
    unfold Finite, FAC, FAR in IH.

    have KK: mem (fmap_Comp mem c :: nil) ⊑ E (x ~ mem l ++ ρ).
    { intros xx xxIn. cbn in xxIn. destruct xxIn; try done. subst. auto. }

    move: (continuous_In_sub E (x ~ mem l ++ ρ) NEx mE (fmap_Comp mem c :: nil) KK) => h.

    move: (IH l ltac:(eauto)) => IH'. 
    

    edestruct IH' as [ρ' fp'].
[ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
hh.
    destruct hh as [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]].
    intros v vIn. eapply IH. auto.
(*    destruct (IH l ltac:(eauto) ⌈ c ⌉ finite_Singleton (In_Included wEVρ)) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]].  *)
    inversion ρ'Vρ. subst. clear ρ'Vρ.
    inversion fρ'. subst. clear fρ'.
    exists E1. exists X.
    repeat split; eauto.
    specialize (wEρ' (fmap mem c)). 
    eapply mE. 2: eapply wEρ'.
    have SS: E1 ⊆e E1. eapply Reflexive_sub_env.  eapply Forall2_uniq1; eauto. 
    auto.
    eauto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.

*)

Lemma In_Included : forall {A}{x:A}{D},  x ∈ D -> ⌈ x ⌉ ⊆ D.
Proof. 
  intros.
  intros y h.
  inversion h. subst. auto.
Qed.

Lemma Included_In : forall {A}{x:A} {D},   ⌈ x ⌉ ⊆ D -> x ∈ D.
Proof. 
  intros.
  apply H. eauto.
Qed.

Lemma finite_Singleton : forall {A}{x:A}, finite ⌈ x ⌉.
Proof.
  econstructor; eauto.
  instantiate (1 := (x :: nil)). split; auto.
  split; eauto using mem_singleton, singleton_mem.
  done.
Qed. 

Lemma CONS_continuous {D E ρ}{w} :
    w ∈ (CONS (D ρ) (E ρ))
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ3 , exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ /\ (w ∈ (CONS (D ρ3) (E ρ3))).
Proof.  
  intros C. unfold CONS, In in C. destruct w.
  all: try done.
  destruct l. try done.
  move: C => [Dv El].
  intros IHD IHE mD mE.
Admitted.
(*
  destruct (IHD ⌈ v ⌉ finite_Singleton (In_Included Dv)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE ⌈ v_list l ⌉ finite_Singleton (In_Included El)) as 
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - eapply mD. instantiate (1:= ρ1). 
    eapply join_sub_left; eauto. auto.
  - eapply mE. instantiate (1:= ρ2).
    eapply join_sub_right; eauto. auto.
Qed. *)


(* ---- RET : P Value -> M (P Value) ----- *)

Lemma RET_continuous {D: Rho -> (P Value)}{ρ}{c} : 
  valid_env ρ ->
  continuous_env' D ρ ->
  monotone_env D ->
  c ∈ RET (D ρ) ->
  forall (x : Comp (list Value)), Comp_Approx x c ->
    exists (ρ' : Rho), 
    exists _ :(finite_env ρ'), (ρ' ⊆e ρ) /\ (fmap mem x ∈ RET (D ρ')).
Proof.
  intros VE CE ME cIn x SU.
  destruct c; try destruct l as [|V l] ; try destruct l; cbn in cIn; try done.
  inversion SU. subst. inversion H1. subst. inversion H4. subst.
  clear H1 H4 SU.
  unfold continuous_env', continuous_For in *.
Admitted.


(*
Lemma BIND_continuous {A B}{D : Rho -> P (Comp (P A))}{K : Rho -> P A -> P (Comp (P B))}{ρ}{v} :
  valid_env ρ ->
  v ∈ BIND (D ρ) (K ρ) -> 
  continuous_env' D ρ ->
  monotone_env D  ->
  (forall v, continuous_env (fun r => K r v) ρ) ->
  (forall v, monotone_env (fun r => K r v)) ->
  exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\ (v ∈ BIND (D ρ') (K ρ')). 
Proof.
  intros VE H IHD mD IHE mE. 
  move: H => [U [h1 [h2 [-> h3]]]].
  unfold continuous_env, continuous_In in IHD.
  edestruct (IHD U ltac:(eauto)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct U.
  + exists ρ1. repeat split; eauto.
    cbn.
    unfold BIND. 
    exists c_wrong. exists (fun x => c_wrong).
    repeat split; eauto.
    intros x h. inversion h.
  + (* need a lemma about all of the VS in the list l. *)
     admit.    
  + exists ρ1. repeat split; eauto.
    cbn.
    unfold BIND. 
    exists c_bottom. exists (fun x => c_bottom).
    repeat split; eauto.
    intros x h. inversion h.
Admitted. 

*)

(* ---------------- Denotation is continuous ----------------- *)

(*
Lemma Included_RET2 {A}{v:M A}{Y}: (v ⊆ RET2 Y) ->  exists X, (v ≃ RET2 X) /\ (X ⊆ Y).
Proof.
  intros.
  cbv in H.
  exists (fun x => Y x /\ v (ret x)).
  repeat split.
  - cbv. intros x vx.
    move: (H x vx) => [b [Yb mm]].
    exists b. repeat split; auto. inversion mm. subst. auto.
  - cbv. intros x [b [[Yb vb] xb]]. 
    inversion xb. subst. auto.
  - intros y Iny.
    destruct Iny. auto.
Qed.
  *)


(*
Lemma denot_val_continuous {t} : forall ρ,
    valid_env ρ
  -> continuous_env (denot_val t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ NE.
  all: intros v vIn.
  all: autorewrite with denot in vIn.
  all: try solve [ exists (initial_finite_env ρ NE); eexists; eauto] .
  - destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
    + exists (single_env x ⌈ v ⌉ ρ NE).
      repeat split.
      eapply single_fin; eauto.
      eapply single_sub; eauto.
      rewrite denot_val_var.
      eapply v_single_xvx; eauto.
    + rewrite access_fresh in vIn; auto.
      inversion vIn.
  - pick fresh x.
    rewrite (denot_val_abs x) in vIn. fsetdec.
    admit. (* Wrong IH. *)
  - rewrite denot_val_tcons in vIn. 
    eapply CONS_continuous in vIn; eauto.
    move: vIn => [ρ' [F' [S' vIn']]].
    exists ρ'. repeat split; auto.
    rewrite denot_val_tcons. auto.
*)

(* ⟦⟧-continuous *)
Lemma denot_continuous {t} : forall ρ,
    valid_env ρ
  -> continuous_env' (denot t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ NE.
  all: intros c cIn.
  all: autorewrite with denot in cIn.
  destruct c; cbn in cIn; unfold Approx in cIn.
Admitted.
(*
   specialize (cIn c ltac:(econstructor; eauto)).
   destruct cIn as [x [h0 h1]]; done.

c(*   all: try solve [ exists (initial_finite_env ρ NE);
    eexists; eauto] . *)
  + cbn. exfalso. edestruct cIn.
  + destruct c; try done.  destruct l as [|V l]; try done. destruct l; try done. 
    cbn in cIn.
    destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
    - 
      exists (single_env x v ρ NE).
      split.
      eapply single_fin; eauto.
      Search finite valid_env.
      split.
      ++ eapply single_sub; auto.
      ++ rewrite denot_var. 
         rewrite E.
         eapply RET2_monotone.

         move: (@v_single_xvx a x ρ NE ltac:(auto)) => h.
         
         transitivity (RET2 (ρ ⋅ x)); auto.
         eapply RET2_monotone.
         intros w wIn.
         eapply v_single_xvx. auto. 
    - exists (initial_finite_env ρ NE).
      eexists; eauto. split. eauto.
      rewrite denot_var.
      rewrite <- ret_In_RET2.
      rewrite access_fresh. simpl_env. auto.
      rewrite access_fresh in h1. auto. done.
  + edestruct (BIND2_continuous NE vIn) as [ρ' [F [SS BB]]]; eauto.
    instantiate (1 :=  (fun ρ v1 => BIND2 (denot t2 ρ) (fun v2 : P Value => v1 ▩ v2))). reflexivity.
    eapply denot_monotone.
    (* edestruct (APPLY_continuous NE vIn) as [ρ' [F SS]]; eauto. *)
    simpl in BB.
    exists ρ'. exists F.
    rewrite denot_app. auto.
  + pick fresh x.
    rewrite (denot_abs x) in vIn. fsetdec.
    move: vIn => [v1 [h1 h2]].
    inversion h2; subst; clear h2.
    move: (@Lambda_continuous _ _ NE v1 x h1) => h.    
    destruct h as [ρ' [Fρ' [S vvIn]]].
    ++ intros V NEV NW.
       move: (valid_nonempty_mem _ NEV) => [w h0]. 
       eapply IH; eauto.
    ++ eapply denot_monotone.
    ++ exists ρ'. exists Fρ'. 
       erewrite <- Forall2_dom in Fr. 2: eapply S.
       rewrite (denot_abs x). fsetdec.
       repeat split; auto.
       erewrite <- ret_In_RET2.
       auto.
  + edestruct (BIND2_continuous NE vIn) as [ρ' [F [SS BB]]]; eauto.
    instantiate (1 :=  (fun ρ v1 => BIND2 (denot t2 ρ) (fun v2 : P Value => RET2 (CONS v1 v2)))). reflexivity.
    eapply denot_monotone.

    edestruct (CONS_continuous vIn) as [ρ' [F SS]]; eauto.

    eapply denot_monotone.
    exists ρ'. exists F.
    rewrite denot_tcons. auto.
Qed.
*)

(* ⟦⟧-continuous-⊆ *) 
(*
Lemma denot_continuous_sub {ρ t} : 
  valid_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
  eapply denot_monotone; eauto.
  intros v InV.
  eapply denot_continuous; auto.
Qed.
*)

Lemma denot_continuous_sub {ρ t} : 
  valid_env ρ
  -> forall E, Approx E (denot t ρ)
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (Approx E (denot t ρ')).
Admitted.

Definition implies (A B : Prop) : Prop := A -> B.

#[global] Instance Proper_Approx : Proper (Logic.eq ==> Ensembles.Included ==> implies) Approx.
intros x1 y1 -> x2 y2 S. 
unfold Approx, implies in *.
- intros h c cIn. specialize (h c cIn). 
unfold Comp_Approx_in in *.
move: h => [d [dIn s]].
exists d. split. eauto. auto.
Qed.

Lemma Approx_sub : forall c X1 X2, X1 ⊆ X2 -> Approx c X1 -> Approx c X2.
intros c X1 X2 S. 
unfold Approx. 
intros h d dIn. specialize (h d dIn). 
unfold Comp_Approx_in in *.
move: h => [e [eIn s]].
exists e. split. eauto. auto.
Qed.

(* This doesn't work, because we need a finite description of the result *)
Definition continuous_M' (F : P Value -> M (P Value)) : Set :=
  forall X E, mem E ⊆ (F X) -> valid X 
         -> exists D, (mem D ⊆ X) /\ (mem E ⊆ (F (mem D))) /\ valid_mem D.


(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ x } :
  valid_env ρ 
  -> x `notin` dom ρ 
  -> continuous_M (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros NE_ρ Fr.
  unfold continuous_M.
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (x ~ X ++ ρ)) as 
    [ρ' [pf [h1 h2]]]. 3: eauto.
  + eapply extend_valid_env; eauto.
  + eauto.
  + inversion h1. subst. inversion pf. subst.
    move: H6 => [D [S NN]].
    exists D. split.
    rewrite <- S. auto.
    split. 
    have SUB: Env.Forall2 Included (x ~ a1 ++ E1) (x ~ mem D ++ ρ).
    econstructor; eauto. 
    rewrite <- S. reflexivity.
    eapply Approx_sub. 2: eapply h2.
    eapply denot_monotone.
    auto.
    eapply valid_sub_valid_mem; eauto. rewrite <- S. auto.
Qed.

(*  Abstraction followed by Application is the identity ------------------- *)

(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous_M F -> monotone F -> valid X
  -> (Λ2 F) ▩ X ≃ F X.
Proof. 
  intros Fcont Fmono NEX.
  split.
  + intros w APP. inversion APP; subst.
    - cbn in H. destruct H as [h1 h2].
      specialize (Fmono (mem V) X ltac:(auto)).
      eauto.
    - cbn in H. try done.
    - destruct x; try done.
    - destruct x; try done.
  + intros w wInFX.

    unfold continuous_M in Fcont.

    destruct w. 
    - admit.
    - 

    have M: mem (cons w nil) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }

    move: (Fcont X (cons w nil) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].


    eapply BETA with (V:=D); eauto.
    repeat split; eauto.
    eapply Forall_sub_mem; eauto.
Qed.


(* Λ⟦⟧-▪-id *)
Lemma Λ_denot_APPLY_id :
  forall t ρ x X,
    valid X
    -> valid_env ρ
    -> x `notin` dom ρ 
    -> ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) ≃
      denot (t ^ x) (x ~ X ++ ρ).
Proof.
  intros.
  move: (@Λ_APPLY_id (fun D => denot (t ^ x) (x ~ D ++ ρ)) X) => h.
  eapply h; auto.
  +  (* continuity *)
    eapply denot_continuous_one; auto.
  + eapply denot_monotone_one; auto.
    eapply ForallT_uniq; eauto.
Qed.

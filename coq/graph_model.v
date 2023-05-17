Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.SetsAsPredicates.
Require Import lc.AssocList.


(* https://github.com/jsiek/denotational_semantics/blob/master/agda/PValueCBV.agda *)

(* Λ  \Lambda
   ▩  \squarecrossfill 
   ↦  \mapsto  
   ⤇ \Mapsto  
   ●  \CIRCLE 
   ⊆  \subseteq   (Included)
*)


Inductive Value : Type :=
  | v_nat : nat -> Value 
  | v_map : list Value -> Value -> Value
    (* trivial function value, evaluated to a value but never applied *)
  | v_fun : Value
.

Infix "↦" := v_map (at level 85, right associativity).

Import SetNotations.
Local Open Scope set_scope.

Definition Λ : (P Value -> P Value) -> P Value :=
  fun f v => match v with 
          | v_nat k => False
          | (V ↦ w) => (w ∈ f (mem V)) /\ V <> nil
          | v_fun => True
          end.

Definition APPLY : P Value -> P Value -> P Value :=
  fun D1 D2 w => 
    exists V, (V ↦ w ∈ D1) /\ (mem V ⊆ D2) /\ V <> nil.

Infix "▩" := APPLY (at level 90).

Definition den_nat : nat -> P Value :=
  fun j v => match v with 
          | v_nat k => j = k
          | (V ↦ w) => False
          | v_fun => False
          end.


(* -- Basic Properties of Denotational Operators --------------------------------- *) 

(* k∈℘k *)
Lemma k_in_den_k : forall k, v_nat k ∈ den_nat k.
Proof. intros. reflexivity. Qed.

Lemma k_in_den_k'_inv : forall k k', v_nat k ∈ den_nat k' -> k = k'.
Proof. intros. inversion H. done. Qed.

Lemma v_in_den_k_inv :  forall v k, v ∈ den_nat k -> v = v_nat k.
Proof. intros. destruct v; inversion H. done. Qed.

(*  Application is a Congruence ------------------------------------------------ *)

Lemma APPLY_mono_sub { D1 D2 D3 D4 } :
    D1 ⊆ D3 -> D2 ⊆ D4 -> ((D1 ▩ D2) ⊆ (D3 ▩ D4)).
Proof.  
  intros D13 D24 w [ V [wvD1 [ VD2 VNE ]]].
  exists V. repeat split; eauto.
  intros d z. eapply D24; eauto.
Qed.

Lemma APPLY_cong { D1 D2 D3 D4 } :
    D1 ≃ D3 -> D2 ≃ D4 -> ((D1 ▩ D2) ≃ (D3 ▩ D4)).
Proof.
  intros [ d13 d31 ] [ d24 d42 ].
  split; eapply APPLY_mono_sub; eauto.
Qed.


(*  Abstraction is Extensional ---- -------------------------------------- *)

(* Λ-ext-⊆  *)
Lemma Λ_ext_sub {F1 F2} :
  (forall {X}, F1 X ⊆ F2 X) -> Λ F1 ⊆ Λ F2.
Proof.
  intros F1F2 v Iv. destruct v eqn:E; inversion Iv.
  - split. eapply F1F2; eauto. eauto.
  - trivial.
Qed.

Lemma Λ_ext {F1 F2} :
  (forall {X}, F1 X ≃ F2 X) -> Λ F1 ≃ Λ F2.
Proof. 
  intros g. split;
  eapply Λ_ext_sub; intro X; destruct (g X); eauto.
Qed.


(*  Abstraction followed by Application is the identity ------------------- *)

Definition continuous (F : P Value -> P Value) : Set :=
  forall X E, mem E ⊆ F X -> nonemptyT X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ D <> nil.

Definition monotone (F : P Value -> P Value) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> nonemptyT X 
  -> (Λ F) ▩ X ≃ F X.
Proof. 
  intros Fcont Fmono NEX.
  split.
  + intros w [ V [ [ wInFV _ ] [ VX _ ]]].
    exact (Fmono (mem V) X VX w wInFV).
  + intros w wInFX.
    have M: mem (cons w nil) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (cons w nil) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    exists D. repeat split; eauto.
Qed.

(*  Primitive Abstraction followed by Application is the identity --------- *)


(* This is about primitive functions, so skip for now *)


(* Environments ---------------------- *)

Definition Env := GEnv (P Value).

Module EnvNotations.
Notation "ρ ⋅ x" := (access (fun _ => False) ρ x) (at level 50).
Infix "⊔e" := (map2 Union) (at level 60).
Infix "⊆e" := (all2 Included) (at level 50).
End EnvNotations.
Import EnvNotations.

(* This cannot be part of the Env module because we need to know the type
   of the domain *)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  constr:(A \u B \u C \u D).

(* ---------------------------------------------------- *)

(* Sub environments *)

Definition sub_env : Env -> Env -> Prop := all2 Included.

Lemma all2_refl {F : P Value -> P Value -> Prop} `{Reflexive _ F} {ρ} : uniq ρ -> all2 F ρ ρ.
Proof. induction 1; eauto. Qed.

#[export] Hint Resolve all2_refl.

Lemma Reflexive_sub_env {ρ:Env} : uniq ρ -> ρ ⊆e ρ.
Proof.
  intros. eapply all2_refl; auto.
Qed.

#[export] Hint Resolve Reflexive_sub_env : core.

#[export] Instance Transitive_sub_env : Transitive sub_env.
Proof. typeclasses eauto. Qed.

Lemma extend_sub_env {ρ ρ':Env}{y X} :
  y `notin` dom ρ ->
  ρ ⊆e ρ' -> (y ~ X ++ ρ) ⊆e (y ~ X ++ ρ' ).
Proof. intros; econstructor; eauto. reflexivity. Qed.

(* ---------------------------------------------------- *)

(* Nonempty environments *)

Definition ne (s : P Value) : Type := { x : Value & x ∈ s }.

Definition nonempty_env : Env -> Type := allT ne.

(* A finite environment has a list of values for 
   each variable. *)
Definition finite (X : P Value) : Prop := exists E, (X ≃ mem E) /\ E <> nil.
Definition finite_env : Env -> Type := allT finite.


Lemma extend_nonempty_env {ρ x X} : 
  x `notin` dom ρ ->
  ne X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply allT_cons; eauto. Qed.

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
    destruct H3 as [E1 [s1 u1]].
    destruct H5 as [E2 [s2 u2]].
    exists (E1 ++ E2).
    split.
    rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    intro h.
    apply u2. 
    destruct E1. simpl in h. auto.
    done.
  + assert False. inversion sc. subst. done. done.
Qed.

Lemma join_lub {ρ ρ1 :Env} :
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
  eapply all2_cons; eauto.
  rewrite sub_dom1. auto.
  rewrite -> H21.
  rewrite -> H13.
  rewrite union_idem.
  reflexivity.
Qed.
  

Lemma join_sub_left {ρ1 ρ2 : Env} : 
  same_scope ρ1 ρ2 ->
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros h.
  induction h; simpl.
Admitted.

Lemma join_sub_right {ρ1 ρ2 : Env} : 
  same_scope ρ1 ρ2 ->
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
Admitted.

(* --- Monotone --------------- *)

Definition monotone_env (D : Env -> P Value) := 
 forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

(* --- Relations on results and products --------------- *)

(* TODO.
   This part seems to be not connected to the rest. 
   Skipping for now.
*)


(* Continuous ----------------------------------------- *)

Definition continuous_In (D:Env -> P Value) (ρ:Env) (v:Value) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env (D:Env -> P Value) (ρ:Env) : Prop :=
  forall v, continuous_In D ρ v.

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
Definition initial_finite_env (ρ : Env) (NE : nonempty_env ρ) : Env.
  induction NE. exact nil.
  destruct f as [V v].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [v w]. simpl. congruence.
Qed. 

#[export] Hint Rewrite initial_finite_dom : rewr_list.

Lemma singleton_mem : forall v : Value,  ⌈ v ⌉ ⊆ mem (v :: nil).
Proof. intro v. econstructor. inversion H. done. Qed.

Lemma mem_singleton : forall v : Value, mem (v :: nil) ⊆ ⌈ v ⌉.
Proof. intro v. cbv. intros. inversion H. subst. econstructor; eauto. done. Qed.

#[global] Hint Resolve singleton_mem mem_singleton : core. 

Lemma finite_singleton : forall v, finite ⌈ v ⌉.
Proof. intro v. unfold finite. exists (cons v nil).
       split. split. eauto. eauto. done.
Qed.

#[global] Hint Resolve finite_singleton : core. 


Lemma initial_fin (ρ : Env) (NE : nonempty_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [v w].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

#[global] Hint Resolve initial_fin : core. 


Lemma initial_fin_sub (ρ : Env) (NE : nonempty_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [v wpx].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

#[global] Hint Resolve initial_fin_sub : core. 


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Env) 
  (NE : nonempty_env ρ) : Env :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { v x ρ NE } : 
  finite_env (single_env x ⌈ v ⌉ ρ NE).
Proof.
  induction NE; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. destruct f.
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. simpl_env. auto. auto.
  + rewrite update_neq_var; eauto. econstructor; eauto. simpl_env. auto.
Qed.    

#[global] Hint Resolve single_fin : core. 


Lemma single_sub { ρ x v } :
  forall (NE : nonempty_env ρ),
    v ∈ ρ ⋅ x 
  -> (single_env x ⌈ v ⌉ ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe. inversion vpe.
  unfold single_env.
  simpl. destruct f. simpl.
  simpl in vpe.
  destruct (x == x0).
  + subst. econstructor; eauto.
    simpl_env. auto.
    intros x h. inversion h. subst. auto.
  + econstructor; eauto. 
    simpl_env. auto.
    intros y h. inversion h. subst. unfold In. auto.
Qed.

#[global] Hint Resolve single_sub : core. 


(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x `in` dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE.
  induction NE; intro h. fsetdec.
  simpl. destruct f. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. econstructor; eauto.
  simpl. rewrite EQ. simpl in h. eapply IHNE; auto. fsetdec.
Qed.  

#[global] Hint Resolve v_single_xvx : core. 



(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub E ρ (NE : nonempty_env ρ) :
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
    have S1: same_scope ρ1 ρ. eapply all2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply all2_same_scope; eauto. 
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

Lemma APPLY_continuous {D E ρ}{NE : nonempty_env ρ}{w} :
    w ∈ ((D ρ) ▩ (E ρ))
    -> continuous_env D ρ 
    -> continuous_env E ρ
    -> monotone_env D 
    -> monotone_env E
    -> exists ρ3 , 
      exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ 
      /\ (w ∈ ((D ρ3) ▩ (E ρ3))).
Proof.  
  intros [V [VwDp [VEp VN]]].
  intros IHD IHE mD mE.
  destruct (IHD (V ↦ w) VwDp) as 
    [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct 
    (continuous_In_sub E ρ NE mE V VEp)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]].
  intros v vV. eapply IHE; eauto.
  have S1: same_scope ρ1 ρ. eapply all2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply all2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
  repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - exists V. 
    have VwDp3 : V ↦ w ∈ D (ρ1 ⊔e ρ2).
    { eapply mD. 2: eapply VwDp1. 
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { intros v vV. eapply mE.
      2: eapply VEp2; auto. 
      eapply join_sub_right.  auto. }
    repeat split.
    + auto.
    + auto.
    + done.
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

Lemma Lambda_continuous {E ρ} {NE : nonempty_env ρ}{ v x} :
  v ∈ Λ (fun D => E (x ~ D ++ ρ)) 
  -> (forall V, V <> nil -> 
          continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\
            (v ∈ (Λ (fun D => E (x ~ D ++ ρ')))).
Proof.
  induction v.
  - intro h. inversion h.
  - intros [ wEVρ VN ] IH mE.
    destruct (IH l VN v wEVρ) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
    inversion ρ'Vρ. subst. clear ρ'Vρ.
    inversion fρ'. subst. clear fρ'.
    exists E1. exists X.
    repeat split; eauto.
    eapply mE. 2: exact wEρ'.
    have SS: E1 ⊆e E1. eapply Reflexive_sub_env.  eapply all2_uniq1; eauto. 
    auto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.

(* -------------------------- *)

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/ISWIMPValue.agda *)

Import LCNotations.
Open Scope tm.

(* The precondition for asking for a denotation of a term with some environment
   is that the term should be well-scoped by that environment.
   The advantage of locally nameless representation is that we are agnostic
   to the order of free variables. However, environments and contexts naturally 
   have such an order.
 *)


Inductive scoped t (ρ : Env) :=
  scoped_intro : fv_tm t [<=] dom ρ -> uniq ρ -> lc_tm t -> scoped t ρ.

#[global] Hint Constructors scoped : core.


(* Find a new variable that isn't in the domain of the environment. *)
Definition fresh_for (VS : atoms) := fresh (AtomSetImpl.elements VS).
Lemma fresh_for_fresh : forall x VS, x = fresh_for VS -> x `notin` VS.
Proof.
  intros. unfold fresh_for in H.
  move: (Atom.fresh_not_in (AtomSetImpl.elements VS)) => Frx0.
  rewrite <- H in Frx0.
  intro h.
  apply AtomSetImpl.elements_1 in h.
  eapply InA_In in h.
  done.
Qed.

#[local] Hint Rewrite size_tm_open_tm_wrt_tm_var : lngen.

(* Denotation function: unbound variables have no denotation. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Env) : P Value :=
  match n with
  | O => fun _ => False
  | S m => 
     match a with 
     | var_b _ => fun _ => False 
     | var_f x => ρ ⋅ x 
     | app t u   => 
         denot_n m t ρ ▩ denot_n m u ρ
     | abs t => 
         let x := fresh_for (dom ρ \u fv_tm t) in 
         Λ (fun D => denot_n m (t ^ x) (x ~ D ++ ρ))
     end
  end.

Lemma size_is_enough : forall n a, n >= size_tm a -> forall ρ, denot_n n a ρ = denot_n (size_tm a) a ρ.
Proof.
  intros n.
  induction n; intros; simpl in *. 
  + destruct a; simpl in H; lia.
  + destruct a; simpl in *; auto.
    - f_equal.
      extensionality D.
      remember (fresh_for (dom ρ \u fv_tm a)) as x.
      rewrite IHn.
      autorewrite with lngen. lia.
      autorewrite with lngen. auto.
    - 
Admitted.


Definition denot (a : tm) := denot_n (size_tm a) a.

Lemma denot_var : forall x ρ, denot (var_f x) ρ = ρ ⋅ x.
Proof.
  intros. reflexivity.
Qed.

Lemma denot_app : forall t u ρ, 
    denot (app t u) ρ = 
      (denot t ρ ▩ denot u ρ).
Proof. 
  intros.
  unfold denot. simpl.
  rewrite size_is_enough. lia. auto.
  rewrite size_is_enough. lia. auto.
Qed.

(* To compute the denotation of an abstraction, we need to first prove a
   renaming lemma. This lemma ensures that the names that we pick for the
   lambda-bound variables don't matter.  *)

Ltac name_binder x0 Frx0 := 
    match goal with 
      [ |- context[fresh_for ?ρ] ] => 
         remember (fresh_for ρ) as x0;
         move: (fresh_for_fresh x0 ρ ltac:(auto)) => Frx0
    end.

Definition access_app_P := @access_app (P Value) (fun _ => False).

(* Renaming property for denotations. Do we need all of these
   scoping constraints? *)

Lemma rename_denot_n : forall n t y w ρ1 ρ2 D, 
  w `notin` dom ρ1 -> 
  y `notin` dom ρ1 \u fv_tm t -> 
(*   fv_tm t [<=] {{ w }} \u dom (ρ1 ++ ρ2) -> *)
  denot_n n t (ρ1 ++ w ~ D ++ ρ2) = 
  denot_n n (t [w ~> var_f y]) (ρ1 ++ y ~ D ++ ρ2).
Proof. 
  induction n;
  intros t y w ρ1 ρ2 D Frw Fry; simpl. auto.
  destruct t; simpl; auto.
  all: simpl_env in Frw.
  all: simpl_env in Fry.
(*   all: simpl in Frt; simpl_env in Frt. *)
  + destruct (x == w).
    ++ subst. 
       simpl_env.       
       rewrite access_app_fresh; auto. rewrite access_eq_var.
       rewrite access_app_fresh; auto. rewrite access_eq_var. auto.
    ++ have NEx: x <> y. simpl in Fry. fsetdec.
       edestruct (@access_app_P ρ1 x).
       repeat rewrite H. auto.
       destruct (H (cons (w, D) ρ2)).
       rewrite H1. 
       destruct (H (cons (y, D) ρ2)).
       rewrite H3.
       simpl. destruct (x == w) eqn:h; try done. rewrite h.
       destruct (x == y) eqn:h1; try done. rewrite h1. auto.
  + f_equal.
    extensionality D0.
    name_binder x0 Frx0.
    name_binder y0 Fry0.

    pick fresh z.
    rewrite (subst_tm_intro z _ (var_f x0)). 
    auto. 
    rewrite (subst_tm_intro z _ (var_f y0)). 
    autorewrite with lngen. auto. 
    replace (t [w ~> var_f y] ^ z) with ((t ^ z) [w ~> var_f y]).
    2: {
      rewrite subst_tm_open_tm_wrt_tm; auto.
      rewrite subst_neq_var. 
      fsetdec.
      auto.
    } 
    rewrite <- cons_app_assoc.

    replace (((x0, D0) :: ρ1) ++ (w, D) :: ρ2) with
      (nil ++ (x0 ~ D0) ++ (ρ1 ++ (w ~ D) ++ ρ2)). 2: { simpl_env; auto. }
    rewrite <- IHn; simpl_env; auto.
    2: { rewrite fv_tm_open_tm_wrt_tm_upper. simpl. 
         clear Fry0 Frw Fry.
         simpl_env in Frx0.
         fsetdec.
    }

    replace ((y0 ~ D0) ++ ρ1 ++ (y ~ D) ++ ρ2) with
      (nil ++ (y0 ~ D0) ++ (ρ1 ++ (y ~ D) ++ ρ2)). 2: { simpl_env; auto. }

    rewrite <- IHn; simpl_env; auto.
    2: { rewrite fv_tm_subst_tm_upper.
         rewrite fv_tm_open_tm_wrt_tm_upper. simpl. 
         clear Frx0 Frw Fry.
         simpl_env in Fry0. 
         rewrite <- fv_tm_subst_tm_lower in Fry0.
         fsetdec.
    }
    
    repeat rewrite <- (app_assoc _ (z ~ D0)).
    eapply IHn.
    simpl_env. auto.
    rewrite fv_tm_open_tm_wrt_tm_upper.
    simpl_env. simpl.

    clear Frx0 Fry0 Frw.
    simpl in Fry.
    fsetdec.
  + simpl_env.
    f_equal.
    apply IHn; simpl_env; auto.
    simpl in Fry. fsetdec.
    apply IHn; simpl_env; auto.
    simpl in Fry. fsetdec.
Qed.


Lemma rename_open_denot : forall w y n t  ρ D, 
  w `notin` fv_tm t -> 
  y `notin` fv_tm t -> 
  denot_n n (t ^ w) (w ~ D ++ ρ) = 
  denot_n n (t ^ y) (y ~ D ++ ρ).
Proof. 
  intros.
  pick fresh z.
  rewrite (subst_tm_intro z _ (var_f w)). auto.
  rewrite (subst_tm_intro z _ (var_f y)). auto.
  rewrite_env (nil ++ w ~ D ++ ρ).
  rewrite <- rename_denot_n; simpl; auto.
  rewrite_env (nil ++ y ~ D ++ ρ).
  rewrite <- rename_denot_n; simpl; auto.
  rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
  rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
Qed.  


Lemma denot_abs : forall x t ρ,
    x `notin` dom ρ \u fv_tm t ->
    denot (abs t) ρ = 
      Λ (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros.
  unfold denot. simpl.
  rewrite size_tm_open_tm_wrt_tm_var.
  f_equal.
  extensionality D.
  name_binder x0 Frx0.
  simpl_env. 
  rewrite -> (rename_open_denot x0 x); eauto.
Qed.


Lemma weaken_denot_n : forall n t ρ ρ1 ρ2, 
    fv_tm t [<=] dom (ρ1 ++ ρ2) ->
    uniq (ρ1 ++ ρ ++ ρ2) ->
    denot_n n t (ρ1 ++ ρ2) = denot_n n t (ρ1 ++ ρ ++ ρ2). 
Proof.
  induction n.
  all: intros t ρ ρ1 ρ2 St U.
  all: destruct t; simpl_env in St; simpl in St; simpl; auto.
  + (* var case *)
    destruct_uniq.
    move: (access_app_P ρ1 x) => [A1|A2].
    rewrite A1. rewrite A1. auto.
    move: (A2 ρ2) => [A21 A22].
    rewrite A22.
    move: (A2 (ρ ++ ρ2)) => [A31 A32].
    rewrite A32.
    rewrite access_app_fresh; auto.
    intro h.
    solve_uniq.
  + (* abs case *)
    f_equal.
    extensionality D.
    name_binder x0 Frx0.
    name_binder y0 Fry0.
    pick fresh z.
    rewrite (rename_open_denot x0 z); auto.
    rewrite (rename_open_denot y0 z); auto.
    rewrite <- app_assoc.
    erewrite IHn. simpl_env; eauto.
    rewrite fv_tm_open_tm_wrt_tm_upper. simpl_env. simpl.
    clear Frx0. clear Fry0. clear Fr. fsetdec.
    solve_uniq.
  + (* app case *)
    f_equal.
    eapply IHn; simpl_env; eauto.
    fsetdec.
    eapply IHn; simpl_env; eauto.
    fsetdec.
Qed.

Lemma weaken_denot : forall t ρ2 ρ,
   fv_tm t [<=] dom ρ2 ->
   uniq (ρ ++ ρ2) ->
   denot t ρ2 = denot t (ρ ++ ρ2). 
Proof.
  intros.
  unfold denot.
  eapply weaken_denot_n with (ρ1 := nil); simpl; auto.
Qed.

Lemma subst_denot_n : forall n, forall t x u ρ1 ρ2, 
    size_tm t <= n ->
    scoped t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) ->
    scoped u ρ2 ->
    denot_n n t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) =
    denot (t [ x ~> u]) (ρ1 ++ ρ2).
Proof.
  induction n.
  intros. destruct t; simpl in H; lia.
  intros t x u ρ1 ρ2 SZ ST SU.
  destruct t; simpl in *. 
  all: move: ST => [FV U LC]; simpl in FV; simpl_env in FV.
  all: move: SU => [FVu Uu LCu].    
  all: destruct_uniq.
  all: inversion LC; clear LC.
  + destruct (x0 == x) eqn:EQ. subst. 
    rewrite access_app_fresh; auto.
    rewrite access_eq_var. 
    apply weaken_denot; auto.
    rewrite denot_var.
    destruct (access_app_P ρ1 x0) as [h1 | h2].
    rewrite h1. rewrite h1. auto.
    move: (h2 ρ2) => [N1 N2]. rewrite N2.
    move: (h2 (x ~ denot u ρ2 ++ ρ2)) => [N3 N4]. rewrite N4.
    simpl. destruct (x0 == x) eqn:h. done. rewrite h. done.
  + name_binder x0 Frx0.  simpl_env in Frx0.
    pick fresh z. (* must be fresh for u too. *)
    rewrite (denot_abs z). 
    simpl_env. rewrite fv_tm_subst_tm_upper. fsetdec. 

    f_equal.
    extensionality D. 
    simpl_env.

    rewrite (rename_open_denot x0 z); simpl; simpl_env; auto.

    replace (t [x ~> u] ^ z) with ((t ^ z)[x ~> u]). 
    2: { 
      rewrite subst_tm_open_tm_wrt_tm; auto. 
      rewrite subst_neq_var. fsetdec. auto. 
    }

    rewrite <- app_assoc.
    rewrite IHn; eauto.
    autorewrite with lngen; lia.

    econstructor.
    rewrite fv_tm_open_tm_wrt_tm_upper. simpl_env. simpl. clear Fr. fsetdec.
    solve_uniq. auto.
  + unfold denot. simpl.
    f_equal.
    rewrite IHn; eauto. lia.
    econstructor; simpl_env; auto. fsetdec. 
    rewrite size_is_enough. lia. reflexivity.
    rewrite IHn; eauto. lia. 
    econstructor; simpl_env; auto. fsetdec. 
    rewrite size_is_enough. lia. reflexivity.
Qed.


Lemma subst_denot : forall t x u ρ2, 
    scoped t (x ~ (denot u ρ2) ++ ρ2) ->
    scoped u ρ2 ->
    denot t (x ~ (denot u ρ2) ++ ρ2) =
    denot (t [ x ~> u]) ρ2.
Proof.
  intros.
  unfold denot.
  eapply subst_denot_n with (ρ1 := nil); eauto.
Qed.

(* ------------------------------------ *)

(* denotational_semantics/agda/SemanticProperties.agda  *)

Lemma denot_monotone {ρ ρ' t} : 
  scoped t ρ ->
  scoped t ρ' ->
  ρ ⊆e ρ' ->
  denot t ρ ⊆ denot t ρ'.
Proof.
  intros.
  unfold denot.
  remember (size_tm t) as n. clear Heqn.
  move: ρ ρ' t H H0 H1.
  induction n.
  all: intros ρ ρ' t [FV1 U1 LC1] [FV2 U2 _] S; simpl; auto.
  reflexivity.
  all: destruct t; inversion LC1; simpl in FV1 ; simpl in FV2.
  + (* var case *)
    subst.
    eapply all2_access; eauto.
  + intro x.
    unfold In , Λ.
    destruct x; try done.
    name_binder y Fry.
    name_binder z Frz.
    pick fresh w.
    simpl_env.
    rewrite -> (rename_open_denot y w); auto.
    rewrite -> (rename_open_denot z w); auto.
    intros [h1 h2].
    split; auto.
    specialize (IHn (w ~ mem l ++ ρ) (w ~ mem l ++  ρ')). 
    eapply IHn; eauto.
    repeat split; eauto.
    rewrite fv_tm_open_tm_wrt_tm_upper; simpl. fsetdec.
    repeat split; eauto.
    rewrite fv_tm_open_tm_wrt_tm_upper; simpl. fsetdec.
    eapply extend_sub_env; eauto.
  + subst.
    eapply APPLY_mono_sub.
    eapply IHn; eauto. econstructor; eauto. fsetdec. econstructor; eauto. fsetdec.
    eapply IHn; eauto. econstructor; eauto. fsetdec. econstructor; eauto. fsetdec.
Qed.


(* ⟦⟧-monotone-one *)
Lemma denot_monotone_one : forall ρ t x, 
    (forall D, scoped t (x ~ D ++ ρ))
    -> monotone (fun D => denot t (x ~ D ++ ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  move: (H D1) => [FV U1 _]. destruct_uniq. simpl_env in FV.
  eapply denot_monotone; simpl; auto.
  eapply H. eapply H.
  econstructor; eauto.
Qed.
  
(* ⟦⟧-continuous *)
Lemma denot_continuous {n t ρ} :
  n >= size_tm t
  -> scoped t ρ 
  -> nonempty_env ρ
  -> continuous_env (denot_n n t) ρ.
Proof.
  move: t ρ.
  induction n.
  all: intros t ρ SZ [FV U LC] NE.
  all: cbn.
  all: unfold continuous_env. 
  all: intros v.
  all: unfold continuous_In. 
  all: intros vIn.
  all: try done.
  destruct t; simpl in FV.
  done.
  + exists (single_env x ⌈ v ⌉ ρ NE).
    exists (@single_fin v x ρ NE).
    split.
    ++ eapply single_sub. auto.
    ++ eapply v_single_xvx. fsetdec.
  + move: vIn. name_binder y Fry.
    simpl in SZ. 
    move=> vIn.
    move: (@Lambda_continuous _ _ NE v y vIn) => h.
    destruct h as [ρ' [F' [S' vv]]].
    ++ intros V NV. 
       eapply IHn. rewrite size_tm_open_tm_wrt_tm_var; try lia.
       { inversion LC; econstructor; simpl_env; 
         autorewrite with lngen; eauto. admit. }
       move: (nonnil_nonempty_mem NV) => h. 
       eapply extend_nonempty_env; auto.
       admit.
    ++ unfold monotone_env.
       intros.
       rewrite size_is_enough. admit.
       rewrite size_is_enough. admit.
       eapply denot_monotone.
       admit. (* The definition of monotone doesn't include a scoping 
                 constraint, and the envs are abstract, so this isn't 
                 satisfiable. Need to fix. *)
       admit.
       auto.
    ++ exists ρ'. exists F'.
       repeat split. auto.
       name_binder z Frz.
       admit. (* rename bound variable *)
  + 
Admitted.

(*
Lambda_continuous:
  forall {E : list (atom * P Value) -> P Value} {ρ : Env},
  nonempty_env ρ ->
  forall (v : Value) (x : atom),
  v ∈ Λ (fun D : P Value => E (x ~ D ++ ρ)) ->
  (forall V : list Value, V <> nil -> continuous_env E (x ~ mem V ++ ρ)) ->
  monotone_env E -> exists (ρ' : Env) (_ : finite_env ρ'), ρ' ⊆e ρ /\ (v ∈ Λ (fun D : P Value => E (x ~ D ++ ρ'))) *)


(* ⟦⟧-continuous-⊆ *) 
Lemma denot_continuous_sub {ρ t} : 
  scoped t ρ
  -> nonempty_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros SC NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
  unfold monotone_env.
  intros r0 r'.
  eapply denot_monotone.
  admit. 
  admit.
  intros v vInV.
  eapply denot_continuous; auto.
Admitted.

(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ x } :
  scoped (abs t) ρ ->
  nonempty_env ρ ->
  x `notin` dom ρ ->
  continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros SC NE_ρ Fr.
  unfold continuous.
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (x ~ X ++ ρ)) as 
    [ρ' [pf [h1 h2]]]. 3: eauto.
  + admit.
  + eapply extend_nonempty_env; eauto.
Admitted.


(* Λ⟦⟧-▪-id *)
Lemma Λ_denot_APPLY_id :
  forall t ρ x X,
    nonempty X
    -> x `notin` dom ρ 
    -> ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) ≃
      denot (t ^ x) (x ~ X ++ ρ).
Proof.
  intros.
  move: (@Λ_APPLY_id (fun D => denot (t ^ x) (x ~ D ++ ρ)) X) => h.
  eapply h.
  + (* continuity *)
Admitted.


(* Soundness of reduction with respect to denotation *)
(* ISWIMPValue.agda *)

Inductive value : tm -> Prop :=
  | v_abs : forall t, value (abs t)
  | v_var : forall x, value (var_f x).

Lemma value_nonempty {t}{ρ} : 
  scoped t ρ ->
  nonempty_env ρ -> value t -> nonempty (denot t ρ).
Proof. 
  intros sc NEρ vv.
  inversion sc. clear sc.
  inversion vv; subst; clear vv; simpl in H.
  + pick fresh x.
    erewrite denot_abs with (x:=x); eauto.
    exists v_fun. cbn. auto.
  + rewrite denot_var.
    unfold nonempty_env in NEρ.
    eapply (@allT_access _ (fun _ => False) _ _) in NEρ.
    2: instantiate (1:= x); auto.
    destruct NEρ. exists x0. auto.
Qed.

Lemma soundness: 
  forall t u, 
    full_reduction t u ->
    forall ρ,
    scoped t ρ ->
    scoped u ρ ->
    nonempty_env ρ ->
    denot t ρ ≃ denot u ρ.
Proof.
  intros t u RED. 
  induction RED; intros ρ SCt SCu NE.
  - (* beta *)
    destruct SCt as [FV U lc]. inversion lc. subst.
    simpl in FV.
    rewrite denot_app.
    pick fresh x.
    erewrite denot_abs with (x:=x).
    rewrite Λ_denot_APPLY_id.
    eapply value_nonempty; auto.
    econstructor; eauto. fsetdec.
    admit. (* value u !! *)
    fsetdec.
    rewrite (subst_tm_intro x t u); auto.
    rewrite subst_denot.
    econstructor; eauto. 
    rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
    admit. (* lc *)
    econstructor; eauto. 
    fsetdec.
    reflexivity.
    fsetdec.
  - (* abs-cong *)
    pick fresh x.
    repeat erewrite denot_abs with (x:=x); try fsetdec.
    specialize (H0 x ltac:(auto)).
    eapply Λ_ext.
    intro X.
    eapply H0.
Admitted.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

(* ------------------------------------------------------- *)
(* More Set stuff *)

(* Sets (could be infinite)    P A  == A -> Prop           *)
(* Nonempty Sets               { X : P A | valid X }       *)
(* Finite sets                 list A                      *)
(* Nonempty finite sets        { X : list A | X <> nil }   *)
(* coercion                    mem : list A -> P A         *)

(* ------------------------------------------------------- *)


Definition vfin (A : Type) : Type := { X : list A | X <> nil }. 
Definition vmem {A : Type} : vfin A -> P A := fun '(exist _ X _) => mem X.

Definition finite {A} (X : P A) : Prop := exists E, (X ≃ mem E).
Definition vfinite {A} (X : P A) : Prop := exists E, (X ≃ vmem E).

(* deprecate *)
Definition valid {A : Type } (V : P A) : Type := nonemptyT V.
Definition valid_mem {A : Type} (V : list A) : Prop := V <> nil.



Definition vfin_Singleton {A : Type } : A -> vfin A.
intro x. exists (x :: nil). intro h.  done. Defined.

Definition vfin_Union {A : Type} : vfin A -> vfin A -> vfin A.
intros [X NEX] [Y NEY]. exists (X ++ Y). destruct X; try done. Defined.

Lemma vmem_Singleton {A:Type}{x : A} :
  vmem (vfin_Singleton x) ≃ ⌈ x ⌉.
Proof.
  cbn. eapply mem_singleton_eq. 
Qed.

Lemma vmem_Union {A:Type}{D1 D2 : vfin A} :
  vmem (vfin_Union D1 D2) = (vmem D1 ∪ vmem D2).
Proof.
  destruct D1. destruct D2.
  cbn.
  eapply union_mem.
Qed.


Lemma finite_singleton : forall {B} (v : B), vfinite ⌈ v ⌉.
Proof. intros B v.  
       have NE: (cons v nil) <> nil. done.
       exists (exist _ (cons v nil) NE).
       cbn. rewrite mem_singleton_eq. reflexivity. 
Qed.

Lemma vfinite_Union {A : Type} : forall (X : P A), vfinite X -> forall Y, vfinite Y -> vfinite (X ∪ Y).
Proof.
  intros X [fX eX] Y [fY eY].
  exists (vfin_Union fX fY).
  destruct fX as [x n].
  destruct fY as [y m].
  cbn. cbn in eX. cbn in eY.
  rewrite union_mem.
  rewrite eX. rewrite eY.
  reflexivity.
Qed.


Lemma union_left {A}{X Y Z: P A} : X ⊆ Z -> Y ⊆ Z -> X ∪ Y ⊆ Z.
Proof. intros h1 h2.
       intros x xIn. destruct xIn; eauto.
Qed.


#[export] Hint Resolve finite_singleton vfinite_Union : core.


Lemma In_mem_Included {A}{d:A}{D} : 
    d ∈ D ->
    mem (d :: nil) ⊆ D.
Proof.
  intros.
  intros y yIn. destruct yIn. subst; auto. done.
Qed.

Lemma Included_mem_In {A}{d:A}{D} : 
    mem (d :: nil) ⊆ D ->
    d ∈ D.

Proof.
  intros.
  specialize (H d). eapply H. eauto.
Qed.

Lemma mem_app_Included {A}{D1 D2 : list A}{w} : 
 mem D1 ⊆ w ->
 mem D2 ⊆ w ->
 mem (D1 ++ D2) ⊆ w.
Proof. 
  intros.
  rewrite union_mem. intros y yIn. induction yIn; eauto.
Qed.

Lemma mem_app_valid {A}{D1 D2 : list A}: 
  valid_mem D1 ->
  valid_mem D2 ->
  valid_mem (D1 ++ D2).
Proof. intros.
 unfold valid_mem in *. destruct D1; try done.
Qed.

#[export] Hint Resolve In_mem_Included Included_mem_In mem_app_Included mem_app_valid : core.


(* ------------------------------------------------------- *)
(* These definitions are independent of a given value type type *)


Definition monotone {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* aka sub_preserving *)
Definition sub_reflecting {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, F D1 ⊆ F D2 -> (D1 ⊆ D2).

(* Note: mem E could be empty *)
Definition continuous {A}{B} (F : P A -> P B) : Set :=
  forall (X : P A), valid X ->
               forall E, mem E ⊆ F X ->
                    exists D, (vmem D ⊆ X) /\ ((mem E) ⊆ F (vmem D)).


(* ------------------------------------------------------- *)


Module EnvNotations.
Notation "ρ ⋅ x" := (Env.access (fun x => False) ρ x) (at level 50).
Infix "⊔e" := (Env.map2 Union) (at level 60).
Infix "⊆e" := (Env.Forall2 Included) (at level 50).
End EnvNotations.
Import EnvNotations.


Section EnvDefinitions.

Context {Value : Type}.
Let Rho := Env (P Value).

Definition monotone_env {A} (D : Rho -> P A) := 
  forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

Definition nonempty_env : Rho -> Type := Env.ForallT nonemptyT.

Definition valid_env : Rho -> Type := Env.ForallT valid. 

Definition sub_env : Rho -> Rho -> Prop := Env.Forall2 Included.

Definition same_env : Rho -> Rho -> Prop := Env.Forall2 Same_set.

Definition finite_env : Rho -> Type := Env.ForallT vfinite.

Definition continuous_In {A} (D:Rho -> P A) (ρ:Rho) (v:A) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env {A} (D:Rho -> P A) (ρ:Rho) : Prop :=
  forall (v : A), continuous_In D ρ v.

Definition continuous_Sub {A} (D:Rho -> P A) (ρ:Rho) (V:list A) : Prop :=
  mem V ⊆ D ρ -> 
  exists ρ', exists (pf : finite_env ρ'),
    ρ' ⊆e ρ  /\ (mem V ⊆ D ρ').

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

Lemma initial_fin (ρ : Rho) (NE : valid_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [v w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

Lemma initial_fin_sub (ρ : Rho) (NE : valid_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [v fx].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Rho) 
  (NE : valid_env ρ) : Rho :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { X x ρ NE } : 
  vfinite X ->
  finite_env (single_env x X ρ NE).
Proof.
  induction NE; intro FIN; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. 
  destruct f as [v1 v2].
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. 
    rewrite initial_finite_dom.
    auto. 
    auto.
  + rewrite update_neq_var; eauto.
    econstructor; eauto.
    eapply IHNE; eauto.
    Search dom update.
    rewrite dom_update.
    rewrite initial_finite_dom.
    auto.
Qed.

Lemma single_sub { ρ : Rho }{ x V } :
  forall (NE : valid_env ρ),
    V ⊆ (ρ ⋅ x)
  -> x `in` dom ρ
  -> (single_env x V ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) cbn. auto. 
  + (* cons case *)
    unfold single_env in *.
    simpl. simpl_env in Indom.
    destruct f as [w h2]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       eapply initial_fin_sub.
       rewrite initial_finite_dom. 
       eauto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. 
       rewrite initial_finite_dom. auto.
       intros h hIn. inversion hIn. subst. auto.
Qed.

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


(* --------------------------------------- *)
(* continuous-∈⇒⊆ *)

Lemma continuous_In_sub {A} (E : Rho -> (P A)) ρ (NE : valid_env ρ) :
   monotone_env E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', exists (pf : finite_env ρ') ,  ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
Proof.
  intros me VS VE vcont.
  induction VS.
  - exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply initial_fin_sub; eauto. 
    done.
  - destruct IHVS as [ ρ1 [ fρ1 [ ρ1ρ VEρ1 ]]].
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

End EnvDefinitions.

#[export] Hint Resolve finite_singleton : core. 
#[export] Hint Resolve initial_fin : core. 
#[export] Hint Resolve initial_fin_sub : core. 
#[export] Hint Resolve single_fin : core. 
#[export] Hint Resolve single_sub : core. 
#[export] Hint Resolve v_single_xvx : core. 

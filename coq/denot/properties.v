Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.
Require Import structures.FSet.
Require Export structures.consistency.


Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.


Definition monotone {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* aka sub_preserving *)
Definition sub_reflecting {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, F D1 ⊆ F D2 -> (D1 ⊆ D2).

Definition finite {B} (X : P B) : Prop := 
  exists E, (X ≃ mem E) /\ nonempty_fset E.


Definition continuous {V}{A} (F : P V -> P A) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.



(* ------------ environments ---------------------- *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P _) => dom x) in
  let E := gather_atoms_with (fun x : Env _ => dom x) in
  constr:(A \u B \u C \u D \u E).


Module EnvNotations.
Notation "ρ ⋅ x" := (Env.access (fun x => False) ρ x) (at level 50).
Infix "⊔e" := (Env.map2 Union) (at level 60).
Infix "⊆e" := (Env.Forall2 Included) (at level 50).
Infix "≃e" := (Env.Forall2 Same_set) (at level 60).
End EnvNotations.

Import EnvNotations.


Section EnvProperties.

Context {Value : Type}.

Definition Rho V := Env (P V).

Definition Bottom : P Value := fun x => False.

Definition monotone_env {A} (XS: atoms) (D : Rho Value -> P A) := 
  forall ρ ρ' , dom ρ [=] XS -> ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

Definition finite_env : Rho Value -> Prop := Env.Forall finite.
  
Definition nonempty_env : Rho Value -> Type := Env.ForallT nonemptyT.

Definition sub_env : Rho Value -> Rho Value -> Prop := Env.Forall2 Included.

Definition same_env : Rho Value -> Rho Value -> Prop := Env.Forall2 Same_set.


Definition continuous_In {A} (D:Rho Value -> P A) (ρ:Rho Value) (v:A) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env {A} (D:Rho Value -> P A) (ρ:Rho Value) : Prop :=
  forall (v : A), continuous_In D ρ v.

Definition continuous_Sub {A} (D:Rho Value -> P A) (ρ:Rho Value) (V:fset A) : Prop :=
  mem V ⊆ D ρ -> 
  exists ρ', exists (pf : finite_env ρ'),
    ρ' ⊆e ρ  /\ (mem V ⊆ D ρ').

End EnvProperties.

Section EnvResults.

Context {Value : Type}.

(* Nonempty environments *)

Lemma extend_nonempty_env {ρ : Rho Value}{x X} : 
  x `notin` dom ρ ->
  nonemptyT X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply ForallT_cons; eauto. Qed.


Lemma join_finite_env {ρ1 ρ2 : Rho Value} : 
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
    match goal with 
    | [ H4 : finite v1 |- _ ] =>  destruct H4 as [E1 [s1 u1 ]] end.
    match goal with 
    | [ H4 : finite v2 |- _ ] =>  destruct H4 as [E2 [s2 u2 ]] end.
    exists (union_fset E1 E2).
    split.
    rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    eauto.
  + assert False. inversion sc. subst. done. done.
Qed.

Lemma join_lub {ρ ρ1 : Rho Value} :
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
  
Lemma join_sub_left {ρ1 ρ2 : Rho Value} : 
  same_scope ρ1 ρ2 ->
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros h.
  induction h; simpl; eauto.
  rewrite eq_dec_refl.
  econstructor; eauto. 
Qed.

Lemma join_sub_right {ρ1 ρ2 : Rho Value} : 
  same_scope ρ1 ρ2 ->
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
  induction 1; simpl; eauto. 
  rewrite eq_dec_refl.
  econstructor; eauto. 
  erewrite Forall2_dom in H0; eauto.
Qed.

Definition initial_finite_env (ρ : Rho Value) (NE : nonempty_env ρ) : Rho Value.
  induction NE. exact nil.
  destruct f as [V _].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [v w].  simpl. congruence.
Qed. 

Lemma finite_singleton : forall {B} (v : B), finite ⌈ v ⌉.
Proof. intros B v. exists (singleton_fset v).
       repeat split; eauto. done. 
Qed.



Lemma initial_fin (ρ : Rho Value) (NE : nonempty_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [v w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
  eapply finite_singleton.
Qed.

Lemma initial_fin_sub (ρ : Rho Value) (NE : nonempty_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [v fx].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Rho Value) 
  (NE : nonempty_env ρ) : Rho Value :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { X x ρ NE } : 
  finite X ->
  finite_env (single_env x X ρ NE).
Proof.
  induction NE; intro FIN; unfold finite_env; eauto.
  unfold single_env. simpl. 
  destruct f as [v1 v2].
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. simpl_env. auto.
    rewrite initial_finite_dom. auto.
    auto.
  + rewrite update_neq_var; eauto.
    econstructor; eauto.
    eapply IHNE; eauto.
    simpl_env. rewrite initial_finite_dom. auto.
    eapply finite_singleton.
Qed.




Lemma single_sub { ρ x V } :
  forall (NE : nonempty_env ρ),
    V ⊆ ρ ⋅ x 
  -> x `in` dom ρ
  -> (single_env x V ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) cbn. eauto.
    
  + (* cons case *)
    unfold single_env in *.
    simpl. simpl_env in Indom.
    destruct f as [w h2]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       simpl_env. eapply initial_fin_sub. rewrite initial_finite_dom. eauto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. rewrite initial_finite_dom. auto.
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

(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub {A} (E : Rho Value -> (P A)) ρ (NE : nonempty_env ρ) :
   monotone_env (dom ρ) E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', exists (pf : finite_env ρ') ,  ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
Proof.
  intros me VS.
  eapply fset_induction with (f := VS).
  Unshelve. 3: exact VS.
  - move=> VE vcont.
    exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply initial_fin_sub; eauto. 
    done.
  - move=> a f IHVS VE vcont.
    rewrite union_mem in VE.
    destruct IHVS as [ ρ1 [ fρ1 [ ρ1ρ VEρ1 ]]]; eauto.
    move=> v vIn. eapply vcont. rewrite union_mem. eapply Union_intror. auto.
    destruct (vcont a) as [ρ2 [fρ2 [ρ2ρ VEρ2]]].
    rewrite union_mem. econstructor; eauto. rewrite mem_singleton_eq. eauto.
    eapply VE. econstructor; eauto. 
    rewrite mem_singleton_eq. eauto.
    exists (ρ1 ⊔e ρ2).
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto. 
    have SS: same_scope ρ1 ρ2. 
    { transitivity ρ; auto. symmetry; auto. }
    eexists. eapply join_finite_env; eauto.
    repeat split.
    + eapply join_lub; eauto.
    + intros d dm.
      rewrite union_mem in dm.
      rewrite mem_singleton_eq in dm.
      inversion dm; subst.
      eapply me with (ρ := ρ2). admit. eapply join_sub_right; eauto. inversion H. subst. auto.
      eapply me with (ρ := ρ1). admit. eapply join_sub_left; eauto. auto.
Admitted.


Lemma access_continuous_env { ρ x } : 
  nonempty_env ρ -> continuous_env (fun ρ0 : Rho Value => ρ0 ⋅ x) ρ.
Proof. 
  move=> NE v vIn.
  cbn in vIn.
  destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
  exists (single_env x ⌈ v ⌉ ρ NE).
  repeat split.
  eapply single_fin; eauto.
  eapply finite_singleton; eauto.
  eapply single_sub; auto.
  eapply v_single_xvx; eauto.
  exists (initial_finite_env ρ NE).
  rewrite access_fresh in vIn. auto. done.
Qed.

(* ⟦⟧-continuous-⊆ *) 
Lemma generic_continuous_sub {A}{ρ}{F : Rho Value -> P A} : 
    continuous_env F ρ 
  -> monotone_env (dom ρ) F
  -> nonempty_env ρ
  -> forall V, mem V ⊆ F ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ F ρ').
Proof.
  intros Fcont Fmono NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
Qed.


End EnvResults.

#[export] Hint Resolve extend_nonempty_env : core.
#[export] Hint Resolve single_sub : core. 
#[export] Hint Resolve single_fin : core. 
#[export] Hint Resolve initial_fin_sub : core. 
#[export] Hint Resolve initial_fin : core. 
#[export] Hint Resolve finite_singleton : core. 
#[export] Hint Rewrite @initial_finite_dom : rewr_list.
#[export] Hint Resolve v_single_xvx : core. 


(* Sub environments ⊆e *)

Section EnvCongruence.

Context {Value : Type}.

Lemma Reflexive_sub_env {ρ:Env (P Value)} : uniq ρ -> ρ ⊆e ρ.
Proof.
  intros. eapply Env.Forall2_refl; eauto.
  typeclasses eauto.
Qed.

Lemma extend_sub_env {ρ ρ': Env (P Value)}{y X} :
  y `notin` dom ρ ->
  ρ ⊆e ρ' -> (y ~ X ++ ρ) ⊆e (y ~ X ++ ρ' ).
Proof. intros; econstructor; eauto. reflexivity. Qed.

Lemma access_mono_sub : forall (ρ1 ρ2 : Env (P Value)) (x : atom),
   ρ1 ⊆e ρ2 ->
   ρ1 ⋅ x ⊆ ρ2 ⋅ x.
intros. 
destruct (FSetDecideAuxiliary.dec_In  x (dom ρ1)).
    + apply Forall2_access with (f := Included); auto.
    + rewrite access_fresh. auto.
      rewrite access_fresh. erewrite Forall2_dom in H0; eauto.
      reflexivity.
Qed. 

Lemma same_env_sub_env : forall (x y : Env (P Value)), x ≃e y <-> (x ⊆e y) /\ (y ⊆e x).
Proof. 
intros x y. split.
induction 1. split; eauto. 
move: H1 => [s1 s2].
move: IHForall2 => [h1 h2]. 
split; econstructor; eauto.
erewrite Forall2_dom; eauto.
unfold same_env.
intros [h1 h2]. 
induction h1. eauto.
inversion h2. subst.
econstructor; eauto.
split; auto.
Qed. 


End EnvCongruence.


#[export] Instance Proper_access_sub {Value} : 
  Proper (sub_env ==> Logic.eq ==> Included) (@access (P Value) (fun x => False)). 
Proof.
  intros x2 y2 S2 x3 y3 ->. eapply access_mono_sub. eauto.
Qed.  

#[export] Instance Proper_access_eq {Value} : 
  Proper (same_env ==> Logic.eq ==> Same_set) (@access (P Value) (fun x => False)). 
Proof.
  intros x2 y2 EQ x3 y3 ->. 
  apply same_env_sub_env in EQ. destruct EQ as [S1 S2].
  split; eapply access_mono_sub; eauto.  
Qed.  

#[export] Instance Transitive_sub_env {Value}  : 
  Transitive (@Env.Forall2 (P Value) (P Value) Included).
Proof. typeclasses eauto. Qed.

#[export] Hint Resolve Reflexive_sub_env : core.
#[export] Hint Resolve extend_sub_env : core.


(* valid sets are inhabited *)
Definition valid_is_nonempty {A} (V : P A) : valid V -> nonemptyT V := id.

Lemma valid_join : forall {A} ( v1 v2 : P A), 
    valid v1 -> 
    valid v2 ->
    valid (v1 ∪ v2).
Proof.
  intros A v1 v2 [x1 h1] [x2 h2].
  exists x1. eapply Union_introl; eauto.
Qed.

Section ValidTheory.

Context {Value : Type}.

Lemma valid_nil : @nonempty_env Value nil.
Proof. unfold nonempty_env. eauto. Qed.


Lemma extend_valid_env {ρ : Env (P Value)}{x X} : 
  x `notin` dom ρ ->
  valid X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX.  eapply ForallT_cons; eauto. Qed.

End ValidTheory.

#[export] Hint Resolve valid_nil : core.
#[export] Hint Immediate valid_is_nonempty : core.
#[export] Hint Resolve extend_valid_env : core.

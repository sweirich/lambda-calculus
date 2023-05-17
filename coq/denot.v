Require Export lc.tactics.
Require Export lc.relations.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Import LCNotations.
Local Open Scope lc_scope.


(* This is a Coq port of https://plfa.github.io/Denotational/ *)
(* It is a filter model of the lambda calculus *)

(* What changes if we want to do CBV instead? *)
(* What if we want to add "WRONG", i.e. for unbound variables? *)
(* What if we want to add other values (i.e. nats, lists, etc)? *)

Inductive Value : Type :=
  | v_bot   : Value
  | v_map   : Value -> Value -> Value
  | v_union : Value -> Value -> Value
.

Notation "⊥" := v_bot.
Infix "↦" := v_map (at level 90, right associativity).
Infix "⊔" := v_union (at level 85, right associativity).

(* Approximate values *)

Reserved Notation "v1 ⊑ v2" (at level 55).
Inductive v_sub : Value -> Value -> Prop :=
  | v_sub_bot : forall v, ⊥ ⊑ v
  | v_sub_conj_L : forall u v w, 
      (v ⊑ u) -> (w ⊑ u) -> ((v ⊔ w) ⊑ u)
  | v_sub_conj_R1 : forall u v w, 
      u ⊑ v -> u ⊑ (v ⊔ w)      
  | v_sub_conj_R2 : forall u v w, 
      u ⊑ w -> u ⊑ (v ⊔ w)
  | v_sub_trans : forall u v w, 
      u ⊑ v -> v ⊑ w -> u ⊑ w
  | v_sub_fun : forall v w v' w', 
      v' ⊑ v
      -> w ⊑ w'
      -> (v ↦ w) ⊑ (v' ↦ w')
  | v_sub_dist : forall v w w', 
      (v ↦ (w ⊔ w')) ⊑ ((v ↦ w) ⊔ (v ↦ w'))
where "v1 ⊑ v2" := (v_sub v1 v2).

#[global] Hint Constructors v_sub : core.

Lemma v_sub_refl : forall v, v ⊑ v.
Proof.
  intro v. induction v; eauto.
Qed.  

#[global] Hint Resolve v_sub_refl : core.

#[global] Instance Refl_v_sub : Reflexive v_sub.
unfold Reflexive. eauto. Qed.

Lemma v_sub_mono : forall (v w v' w': Value), 
    v ⊑ v' -> (w ⊑ w') ->
    (v ⊔ w) ⊑ (v' ⊔ w').
Proof. 
  intros; eauto.
Qed.

(* ⊔↦⊔-dist *)
Lemma v_sub_union_dist : forall (v w v' w': Value), 
    (v ⊔ v' ↦ w ⊔ w') ⊑ ((v ↦ w) ⊔ (v' ↦ w')).
Proof. intros. 
       eapply v_sub_trans.
       eapply v_sub_dist.
       eapply v_sub_mono.
       + eapply v_sub_fun; eauto.
       + eauto.
Qed.

Lemma v_sub_union_invL : forall u v w,
    (u ⊔ v) ⊑ w -> u ⊑ w.
Proof. intros u v w H. dependent induction H; eauto. Qed.

Lemma v_sub_union_invR : forall u v w,
    (u ⊔ v) ⊑ w -> v ⊑ w.
Proof. intros u v w H. dependent induction H; eauto. Qed.


(* Environments are maps of variables to values. We don't 
   index by the current scope to avoid dependently-typed 
   programming in Coq. 
*)

Definition Env := atom -> Value.

Definition empty : Env := fun x => v_bot.

Definition cons : atom -> Value -> Env -> Env := 
  fun x v γ => fun y => match (x == y) with 
                  | left _ => v
                  | right pf => γ y
                  end.

Definition env_sub (γ : Env) (δ : Env) : Prop :=
  forall x, γ x ⊑ δ x.

#[global] Instance Refl_env_sub : Reflexive env_sub.
unfold Reflexive. intros γ. unfold env_sub. intros x. auto.
Qed.

#[global] Instance Trans_env_sub : Transitive env_sub.
unfold Transitive. intros γ1 γ2 γ3. unfold env_sub. intros g1 g2 x. eauto.
Qed.


Lemma cons_cons : forall x y z v γ, 
    z <> y ->
    z <> x ->
    cons y ((cons z v γ) x) (cons z v γ) = cons z v (cons y (γ x) γ).
Proof.
  intros.
  unfold cons.
  extensionality w.
  destruct (y == w) eqn:YW;
  destruct (z == w) eqn:ZW; auto.
  + subst. done. 
  + subst. destruct (z == x). subst. done. done.
Qed.     

(* CBV requires that the value is not bot?? *)
Inductive v_app : Value -> Value -> Value -> Prop :=
  | app_beta : forall v w, 
      (* CBV??      v <> v_bot -> *)
      v_app (v ↦ w) v w
.


Inductive sem : Env -> tm -> Value -> Prop :=
  | sem_var : forall γ x,
      sem γ (var_f x) (γ x)
  | sem_app : forall γ L M u v w,
        sem γ L u
      -> sem γ M v
      -> v_app u v w
      -> sem γ (app L M) w 
  | sem_abs : forall L γ v w N,
      (forall x, x `notin` L ->
          sem (cons x v γ) (N ^ x) w) -> 
      sem γ (abs N) (v ↦ w)
  | bot_intro : forall γ M,
      lc_tm M ->
      sem γ M ⊥
  | union_intro : forall γ M v w,
      sem γ M v
      -> sem γ M w
      -> sem γ M (v ⊔ w)
  | sem_sub : forall γ M v w,
      sem γ M v
      -> w ⊑ v
      -> sem γ M w
.

#[global] Hint Constructors sem : core.

Lemma sem_subst : forall x y γ M v,
    y `notin` fv_tm M ->
    sem γ M v ->
    sem (cons y (γ x) γ) (subst_tm (var_f y) x M) v.
Proof. 
  intros.
  induction H0.
  all: simpl; simpl in H; eauto with lngen.
  - have EQ: y <> x0. fsetdec.
    destruct (x0 == x) eqn:E.
    + subst. 
      replace (γ x) with ((cons y (γ x) γ) y) at 2.
      2: { unfold cons. destruct (y == y). auto. done. }
      eapply sem_var. 
    + replace (γ x0) with ((cons y (γ x) γ) x0) at 1.
      2: { unfold cons. destruct (y == x0). done. done. }
      eapply sem_var.
  - pick fresh z and apply sem_abs.
    spec z.
    rewrite <- cons_cons; auto.
    autorewrite with lngen in H1.
    eapply H1. rewrite fv_tm_open_tm_wrt_tm_upper.  simpl. fsetdec.
Qed.


Lemma sem_rename : forall x y γ M v w,
    x `notin` fv_tm M -> 
    y `notin` fv_tm M ->
    sem (cons x w γ) (M ^ x) v ->
    sem (cons y w γ) (M ^ y) v.
Proof.
  intros x y γ M v w Fr1 Fr2 h.
  destruct (x == y). subst. auto.
  rewrite (subst_tm_intro x); auto.
  remember (cons x w γ) as δ.
  replace (cons y w γ) with (cons y (δ x) δ).
  eapply sem_subst with (x:=x) (y:=y).
  rewrite fv_tm_open_tm_wrt_tm_upper.  simpl. fsetdec.
Admitted.
  

Lemma sem_abs_ex : forall γ x v w N,
      x `notin` fv_tm N ->
      sem (cons x v γ) (N ^ x) w -> 
      sem γ (abs N) (v ↦ w).
Proof.
  intros.
  pick fresh z and apply sem_abs.
  eapply sem_rename; eauto.
Qed.


Definition tm_Id : tm := abs (var_b 0).

Lemma denot_Id : sem empty tm_Id (⊥ ↦ ⊥).
Proof.
  pick fresh x and apply sem_abs.
  cbn. 
  replace ⊥ with ((cons x ⊥ empty) x) at 2.
  eapply sem_var.
  unfold cons. rewrite eq_dec_refl.
  reflexivity.
Qed.

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).

Lemma denot_Delta : forall v w, sem empty tm_Delta (((v ↦ w) ⊔ v) ↦ w).
Proof.
  intros. unfold tm_Delta.
  pick fresh x and apply sem_abs.
  eapply sem_app.
  3: { eapply app_beta. }
  + cbn. eapply sem_sub. eapply sem_var.
    unfold cons. rewrite eq_dec_refl.
    instantiate (1:=v).
    eauto.
  + cbn. eapply sem_sub. eapply sem_var.
    unfold cons. rewrite eq_dec_refl.
    eauto.
Qed. 

(** Denotation **)

Definition Denotation := Env -> Value -> Prop.

Definition E (M : tm) : Denotation := fun γ v => sem γ M v.

Definition den_eq (D1 : Denotation) (D2: Denotation) : Prop :=
  forall γ v, D1 γ v <-> D2 γ v.

#[global] Instance Eq_den : Equivalence den_eq.
constructor.
- split; auto.
- unfold Symmetric. intros x y h. intros γ v. specialize (h γ v). tauto.
- unfold Transitive. intros x y z h1 h2. intros γ v.
  specialize (h1 γ v).
  specialize (h2 γ v).
  tauto.
Defined.

(* Environment strengthening *)

Lemma sub_env : forall γ M v, 
    sem γ M v 
    -> forall δ, env_sub γ δ
    -> sem δ M v.
Proof.
  induction 1; intros; eauto.
  - pick fresh x and apply sem_abs.
    spec x.
    eapply H0.
    unfold env_sub.
    intros y.
    unfold cons.
    destruct (x == y). auto. auto.
Qed.

Lemma ext_le : forall x u1 u2 γ, 
    u1 ⊑ u2 ->
    env_sub (cons x u1 γ) (cons x u2 γ).
Proof.
  intros. unfold env_sub, cons.
  intros y.
  (destruct (x == y)). auto.
  auto.
Qed.

Lemma up_env : forall γ M x u1 u2 v, 
    sem (cons x u1 γ) M v ->
    u1 ⊑ u2  ->
    sem (cons x u2 γ) M v.
Proof.
  intros.
  eapply sub_env; eauto using ext_le.
Qed.

(* ** Value Membership and Inclusion ** *)

Fixpoint v_mem (u : Value) (v: Value) : Prop :=
  match v with 
  | ⊥ => u = ⊥
  | v ↦ w => u = (v ↦ w)
  | v ⊔ w => v_mem u v \/ v_mem u w
  end.

Infix "∈" := v_mem (at level 50).

Definition v_inc v w := forall u, u ∈ v -> u ∈ w.

Infix "⊆" := v_inc (at level 50).

Lemma mem_sub : forall u v, u ∈ v -> u ⊑ v.
Proof. intros. induction v; inversion H; eauto. Qed.

Lemma union_inc : forall u v w, 
    u ⊆ w -> v ⊆ w -> (u ⊔ v) ⊆ w.
Proof.
  unfold v_inc.
  intros.
  simpl in H1.
  destruct H1. eauto. eauto.
Qed.

(* ⊔⊆-inv *)
Lemma union_inc_inv : forall u v w, 
    (u ⊔ v) ⊆ w -> u ⊆ w /\ v ⊆ w.
Proof.    
  intros u v w s. split.
  intros x h1. eapply s. simpl. left. auto.
  intros x h1. eapply s. simpl. right. auto.
Qed.


Lemma inc_sub : forall u v, u ⊆ v -> u ⊑ v.
Proof. intros u v s.
       induction u; eauto.
       + eapply mem_sub.
         eapply s.
         reflexivity.
       + apply union_inc_inv in s. 
         move: s => [s1 s2].
         eauto.
Qed.

(* ↦⊆→∈  *)
Lemma fun_inc_mem : forall v w u, 
    (v ↦ w) ⊆ u -> (v ↦ w) ∈ u.
Proof. 
  intros. eapply H. reflexivity.
Qed.

(** Function values **)

Inductive Fn : Value -> Prop :=
  fn : forall u v w, u = (v ↦ w) -> Fn u.

Definition all_fns (v:Value) : Prop :=
  forall u , u ∈ v -> Fn u.

Lemma bot_not_Fn : ~ (Fn ⊥).
Proof.
  intros h. inversion h. done.
Qed.

Lemma all_fns_mem : forall u,
    all_fns u -> exists v, exists w, (v ↦ w) ∈ u.
Proof.
  intros u f.
  induction u; unfold all_fns in *.
  - specialize (f ⊥ ltac:(reflexivity)).
    apply bot_not_Fn in f. done.
  - exists u1. exists u2. reflexivity.
  - destruct IHu1 as [v [w h]].
    + intros z h.
      specialize (f z (or_introl h)). 
      inversion f. done.
    + exists v. exists w. simpl. auto.
Qed.

(** Domains and Codomains **)

Fixpoint union_dom (u : Value) : Value :=
  match u with 
  | ⊥ => ⊥
  | (v ↦ w) => v
  | (u ⊔ u') => union_dom u ⊔ union_dom u'
  end.


Fixpoint union_cod (u : Value) : Value :=
  match u with 
  | ⊥ => ⊥
  | (v ↦ w) => w
  | (u ⊔ u') => union_cod u ⊔ union_cod u'
  end.

Lemma fn_in_union_dom : forall u v w, 
    all_fns u 
    -> (v↦ w) ∈ u
    -> v ⊆ union_dom u.
Proof.
  intros u. 
  induction u; intros v w fg hin u; inversion hin; subst; auto.
  + intro uinv. simpl.
    left.
    eapply IHu1; eauto.
    intros z hz. 
    unfold all_fns in fg.
    specialize (fg z (or_introl hz)).
    inversion fg. done.
  + intro uv. simpl.
    right.
    eapply IHu2; eauto.
    intros z hz.
    unfold all_fns in fg.
    specialize (fg z (or_intror hz)).
    inversion fg. done.
Qed.

Lemma sub_fn_union_cod : forall u v w, 
     u ⊆ (v↦ w)
    -> union_cod u ⊆ w.
Proof.
  intros u v w s; induction u; simpl in *.
  + intros u' h; inversion h; subst.
    specialize (s ⊥ ltac:(reflexivity)). inversion s.
  + intros u' m. specialize (s (u1 ↦ u2) ltac:(reflexivity)).
    inversion s. subst. auto.
  + intros u' h; inversion h; subst.
    ++ eapply IHu1; auto.  intros C z.  eapply s. simpl. left. auto.
    ++ eapply IHu2; auto.  intros C z.  eapply s. simpl. right. auto.
Qed.

Definition factor := 
  fun (u u' v w : Value) => 
    (all_fns u') /\ (u' ⊆ u) /\ (union_dom u' ⊑ v) /\ (w ⊑ union_cod u').


(* Inversion of less-than for functions, case for trans *)

Lemma sub_inv_trans : forall u' u2 u, 
    all_fns u' -> u' ⊆ u
    -> (forall v' w', (v' ↦ w') ∈ u -> exists u3, factor u2 u3 v' w')
    -> exists u3, factor u2 u3 (union_dom u') (union_cod u').
Proof.
intros u' u2 u fu' hsub IH.
induction u'.
- exfalso. apply bot_not_Fn. 
  eapply fu'. reflexivity.  
- apply IH.
  eapply fun_inc_mem.
  simpl. auto.
- unfold all_fns in *. 
  destruct (union_inc_inv _ _ _ hsub) as [h1' h2'].
  destruct IHu'1 as [u31 [ fu21' [u31u2 [de1du1 cu1cu31]]]]. 2: { exact h1'. }
  intros z h. specialize (fu' z (or_introl h)). inversion fu'. done.
  destruct IHu'2 as [u32 [ fu22' [u32u2 [de1du2 cu1cu32]]]]. 2: { exact h2'. }
  intros z h. specialize (fu' z (or_intror h)). inversion fu'. done.
  exists (v_union u31 u32).
  repeat split.
  + unfold factor, all_fns in *.
    intros v' x. inversion x. eapply fu21'. auto.
    eapply fu22'. auto.
  + eapply union_inc; eauto.
  + simpl. eapply v_sub_mono; auto.
  + simpl. eapply v_sub_mono; auto.
Qed.

(* Inversion of less-than for functions *)

Lemma sub_inv : forall u1 u2, u1 ⊑ u2  
                  -> forall v w, (v ↦ w) ∈ u1
                  -> exists u3, factor u2 u3 v w.
Proof.
  intros u1 u2 h.
  induction h. 
  - intros v1 w1 h1. inversion h1.
  - intros v1 w1 m.
    inversion m; eauto. 
  - intros v1 w1 m.
    destruct (IHh _ _ m) as [u31 [fu31 [u31u21 [domu31v wcodu31]]]].
    exists u31. repeat split.
    + apply fu31.      
    + intros C z. simpl. left. eauto.
    + apply domu31v.
    + apply wcodu31.
  - intros v1 w1 m.
    destruct (IHh _ _ m) as [u31 [fu31 [u31u21 [domu31v wcodu31]]]].
    exists u31. repeat split.
    + apply fu31.
    + intros C z. simpl. right. eauto.
    + apply domu31v.
    + apply wcodu31.
  - (* sub_trans *) 
    intros v1 w1 m. 
    edestruct (IHh1 _ _ m) as [ u' [ fu' [u'u [ domu'v wcodu']]]].
    move: sub_inv_trans => f.
    edestruct (sub_inv_trans _ _ _ fu' u'u IHh2)
      as [ u3 [ fu3 [ u3u2 [ domu3domu' codu'codu3]]]]. 
    exists u3.
    repeat split.
    + exact fu3.
    + exact u3u2.
    + eapply v_sub_trans. exact domu3domu'. exact domu'v.
    + eapply v_sub_trans. exact wcodu'. exact codu'codu3.
  - intros v1 w1 h.  inversion h. subst.
    exists ( v' ↦ w' ). repeat split.
    + unfold all_fns. intros. econstructor. eauto.
    + unfold v_inc. tauto.
    + simpl. auto.
    + simpl. auto.
  - intros. inversion H. subst.
    exists ((v ↦ w) ⊔ (v ↦ w')).
    repeat split.
    + unfold all_fns. intros u h. inversion h. eapply fn. eauto.
      eapply fn. eauto.
    + intros y x. inversion x. eauto. eauto.
    + eapply v_sub_conj_L. eapply v_sub_refl. eapply v_sub_refl.
    + simpl. eapply v_sub_refl.
Qed.

Lemma sub_inv_fun : forall v w u1, 
    (v ↦ w) ⊑ u1
  -> exists u2, all_fns u2 /\ u2 ⊆ u1 /\
            (forall v' w', (v' ↦ w') ∈ u2 -> v' ⊑ v) 
          /\ w ⊑ union_cod u2.
Proof.
  intros v w u1 abc.
  destruct (sub_inv _ _ abc v w) as [u2 [f [u2u1 [db cc]]]]; eauto.
  unfold v_mem. auto.
  exists u2. repeat split.
  + exact f.
  + exact u2u1.
  + intros D E m. eapply v_sub_trans.
    eapply inc_sub. eapply fn_in_union_dom. exact f. exact m. exact db.
  + exact cc.
Qed. 

Lemma sub_fun_inv : forall v w v' w', 
    (v ↦ w) ⊑ (v' ↦ w')
    -> (v' ⊑ v) /\ w ⊑ w'.
Proof.
  intros v w v' w' lt.
  destruct (sub_inv_fun _ _ _ lt) as [ Γ [ f [ Γv34 [ lt1 lt2 ]]]].
  destruct (all_fns_mem _ f) as [ u [ u' uu'Γ]].
  move: (Γv34 _ uu'Γ) => Eq.
  inversion Eq. subst.
  split.
  + eapply lt1; eauto.
  + eapply v_sub_trans. eapply lt2.
    eapply inc_sub. eapply sub_fn_union_cod. eauto.
Qed.

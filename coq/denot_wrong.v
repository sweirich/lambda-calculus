Require Export lc.tactics.
Require Export lc.relations.
Require Import Lia.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Structures.Orders.

Import LCNotations.
Local Open Scope lc_scope.

(* This is a Coq port of https://plfa.github.io/Denotational/ *)

(* However, the denotation is in terms of "option Values"
   so that we can return "wrong" *)

(* How to define the semantics of primitive operators? *)
(* Is this CBN or CBV? What changes if it is CBV? *)
(* And, how do we keep wrong out of it??? *)

Inductive Value : Type :=
  | v_bot   : Value
  | v_map   : Value -> option Value -> Value
  | v_union : Value -> Value -> Value
.

Notation "⊥" := v_bot.
Infix "|->" := v_map (at level 90, right associativity).
Infix "⊔" := v_union (at level 85, right associativity).


Inductive v_sub : Value -> Value -> Prop :=
  | v_sub_bot : forall v, ⊥ [<=] v
  | v_sub_conj_L : forall u v w, 
      (v [<=] u) -> (w [<=] u) -> ((v ⊔ w) [<=] u)
  | v_sub_conj_R1 : forall u v w, 
      u [<=] v -> u [<=] (v ⊔ w)      
  | v_sub_conj_R2 : forall u v w, 
      u [<=] w -> u [<=] (v ⊔ w)
  | v_sub_trans : forall u v w, 
      u [<=] v -> v [<=] w -> u [<=] w
  | v_sub_fun : forall v w v' w', 
      (v |-> w) [<=] (v' |-> w')
  | v_sub_dist : forall v w w', 
      (v |-> Some (w ⊔ w')) [<=] 
        ((v |-> Some w) ⊔ (v |-> Some w'))
where "v1 [<=] v2" := (v_sub v1 v2).

Definition option_sub 
  (o1: option Value) (o2: option Value) : Prop := 
  match o1, o2  with 
  | Some v1 , Some v2 => v_sub v1 v2
  | None , None => True
  | _ , _ => False 
  end.


#[global] Hint Constructors v_sub : core.

Lemma v_sub_refl : forall (v:Value), v [<=] v.
Proof.
  intro v. induction v; eauto.
Qed.  

#[global] Hint Resolve v_sub_refl : core.

Lemma v_sub_mono : forall (v w v' w': Value), 
    v [<=] v' -> (w [<=] w') ->
    (v ⊔ w) [<=] (v' ⊔ w').
Proof. 
  intros; eauto.
Qed.

Lemma v_sub_union_dist : forall (v w v' w': Value), 
    (v ⊔ v' |-> Some (w ⊔ w')) [<=] ((v |-> Some w) ⊔ (v' |-> Some w')).
Proof. eauto. Qed.

Lemma v_sub_union_invL : forall u v w,
    (u ⊔ v) [<=] w -> u [<=] w.
Proof. intros u v w H. dependent induction H; eauto. Qed.

Lemma v_sub_union_invR : forall u v w,
    (u ⊔ v) [<=] w -> v [<=] w.
Proof. intros u v w H. dependent induction H; eauto. Qed.


(* Environments are maps of (in-scope) variables to values.

   With metalib, we'll represent them using association lists.

  *)

Definition v_wrong : option Value := None.

Definition Env := atom -> option Value.

Definition empty : Env := fun x => v_wrong.

Definition cons : atom -> Value -> Env -> Env := 
  fun x v γ => fun y => match (x == y) with 
                  | left _ => Some v
                  | right pf => γ y
                  end.

Definition env_sub (γ : Env) (δ : Env) : Prop :=
  forall x, option_sub (γ x) (δ x).


#[global] Instance Refl_env_sub : Reflexive env_sub.
unfold Reflexive. intros γ. unfold env_sub. intros x.
destruct (γ x); simpl; eauto.
Qed.

#[global] Instance Trans_env_sub : Transitive env_sub.
unfold Transitive. intros γ1 γ2 γ3. unfold env_sub. 
intros g1 g2 x.
specialize (g1 x). 
specialize (g2 x). 
destruct (γ1 x) eqn:E1; destruct (γ2 x) eqn:E2; destruct (γ3 x) eqn:E3; subst; simpl; eauto. done.
Qed.


Inductive v_app : option Value -> option Value -> option Value -> Prop :=
  | app_beta : forall v w, 
      v_app (Some (v |-> w)) (Some v) w
  | app_wrong_fun : forall v,
      v_app v_wrong v v_wrong
  | app_wrong_arg : forall v,
      v_app (Some v) v_wrong v_wrong
.


Inductive sem : Env -> tm -> option Value -> Prop :=
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
      sem γ (abs N) (Some (v |-> w))
  | bot_intro : forall γ M,
      lc_tm M ->
      sem γ M (Some ⊥)
  | union_intro : forall γ M v w,
      sem γ M (Some v)
      -> sem γ M (Some w)
      -> sem γ M (Some (v ⊔ w))
  | sem_sub : forall γ M v w,
      sem γ M (Some v)
      -> w [<=] v
      -> sem γ M (Some w)
.

#[global] Hint Constructors sem.


Lemma cons_cons : forall x y z v γ u, 
    z <> y ->
    z <> x ->
    γ x = Some u ->
    cons y u (cons z v γ) 
    = cons z v (cons y u γ).
Proof.
  intros.
  unfold cons.
  extensionality w.
  destruct (y == w) eqn:YW;
  destruct (z == w) eqn:ZW; auto.
  + subst. done. 
Qed. 


Lemma sem_subst : forall x y γ M v w,
    y `notin` fv_tm M ->
    sem γ M v ->
    γ x = Some w ->
    sem (cons y w γ) (subst_tm (var_f y) x M) v.
Proof. 
  intros.
  induction H0.
  all: simpl; simpl in H; eauto with lngen.
  - have EQ: y <> x0. fsetdec.
    destruct (x0 == x) eqn:E.
    + subst. 
      replace (γ x) with ((cons y w γ) y) at 1.
      2: { unfold cons. destruct (y == y). auto. done. }
      eapply sem_var. 
    +  replace (γ x0) with ((cons y w γ) x0) at 1.
      2: { unfold cons. destruct (y == x0). done. done. }
      eapply sem_var.
  - pick fresh z and apply sem_abs.
    spec z.
    rewrite <- cons_cons with (x:= x); auto.
    autorewrite with lngen in H2.
    eapply H2. rewrite fv_tm_open_tm_wrt_tm_upper.  simpl. fsetdec.
    unfold cons. destruct (z == x). fsetdec. auto.
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
  eapply sem_subst with (x:=x) (y:=y).
  rewrite fv_tm_open_tm_wrt_tm_upper.  simpl. fsetdec.
Admitted.
  

Lemma sem_abs_ex : forall γ x v w N,
      x `notin` fv_tm N ->
      sem (cons x v γ) (N ^ x) w -> 
      sem γ (abs N) (Some (v |-> w)).
Proof.
  intros.
  pick fresh z and apply sem_abs.
  eapply sem_rename; eauto.
Qed.

Definition tm_Id : tm := abs (var_b 0).

Lemma denot_Id : sem empty tm_Id (Some (⊥ |-> Some ⊥)).
Proof.
  pick fresh x and apply sem_abs.
  cbn. 
  replace (Some ⊥) with ((cons x ⊥ empty) x).
  eapply sem_var.
  unfold cons. rewrite eq_dec_refl.
  reflexivity.
Qed.

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).

Lemma denot_Delta : forall v w, 
    sem empty tm_Delta (Some (((v |-> w) ⊔ v) |-> w)).
Proof.
  intros. unfold tm_Delta.
  pick fresh x and apply sem_abs.
  eapply sem_app.
  3: { eapply app_beta. }
  + cbn. eapply sem_sub. 
    remember (cons x ((v |-> w) ⊔ v) empty) as γ.
    instantiate (1:= (v |-> w) ⊔ v).
    replace (Some ((v |-> w) ⊔ v)) with (γ x).      
    eapply sem_var. subst.
    unfold cons. rewrite eq_dec_refl. auto.
    instantiate (1:=v).
    eauto.
  + cbn. eapply sem_sub. 
    remember (cons x ((v |-> w) ⊔ v) empty) as γ.
    instantiate (1:= (v |-> w) ⊔ v).
    replace (Some ((v |-> w) ⊔ v)) with (γ x).      
    eapply sem_var. subst.
    unfold cons. rewrite eq_dec_refl.
    eauto.
    eauto.
Qed. 

Definition Denotation := Env -> option Value -> Prop.

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
  - unfold env_sub in H.
    specialize (H x).
    destruct (γ x); destruct (δ x) eqn:E; try done.
    eapply sem_sub with (v := v0).
    replace (Some v0) with (δ x).
    eauto. eauto. rewrite <- E. eapply sem_var.
  - pick fresh x and apply sem_abs.
    spec x.
    eapply H0.
    unfold env_sub.
    intros y.
    unfold cons.
    destruct (x == y). auto. 
    unfold env_sub in H1. eapply H1.
Qed.

Lemma ext_le : forall x u1 u2 γ, 
    u1 [<=] u2 ->
    env_sub (cons x u1 γ) (cons x u2 γ).
Proof.
  intros. unfold env_sub, cons.
  intros y.
  (destruct (x == y)). auto.
  destruct (γ y); eauto.
Qed.

Lemma up_env : forall γ M x u1 u2 v, 
    sem (cons x u1 γ) M v ->
    u1 [<=] u2  ->
    sem (cons x u2 γ) M v.
Proof.
  intros.
  eapply sub_env; eauto using ext_le.
Qed.

(* ** Value Membership and Inclusion ** *)

Fixpoint v_mem (u : Value) (v: Value) : Prop :=
  match v with 
  | ⊥ => u = ⊥
  | v |-> w => u = (v |-> w)
  | v ⊔ w => v_mem u v \/ v_mem u w
  end.

Infix "∈" := v_mem (at level 50).

#[global] Instance Refl_v_mem : Reflexive v_mem.
Proof. 
  unfold Reflexive. intros v. induction v; simpl; try reflexivity.
  left.
Abort.

Definition v_inc v w := forall u, u ∈ v -> u ∈ w.

Infix "⊆" := v_inc (at level 50).

Lemma mem_sub : forall u v, u ∈ v -> u [<=] v.
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


Lemma inc_sub : forall u v, u ⊆ v -> u [<=] v.
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
    (v |-> w) ⊆ u -> (v |-> w) ∈ u.
Proof. 
  intros. eapply H. reflexivity.
Qed.

(** Function values **)

Inductive Fn : Value -> Prop :=
  fn : forall u v w, u = (v |-> w) -> Fn u.

Definition all_fns (v:Value) : Prop :=
  forall u , u ∈ v -> Fn v.

Lemma bot_not_Fn : ~ (Fn ⊥).
Proof.
  intros h. inversion h. done.
Qed.

Lemma all_fns_mem : forall u,
    all_fns u -> exists v, exists w, (v |-> w) ∈ u.
Proof.
  intros u f.
  induction u; unfold all_fns in *.
  - specialize (f ⊥ ltac:(reflexivity)).
    apply bot_not_Fn in f. done.
  - exists u. exists o. reflexivity.
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
  | (v |-> w) => v
  | (u ⊔ u') => union_dom u ⊔ union_dom u'
  end.

Definition option_ap {A B} (f : option (A -> B)) (o : option A) (o2 : option A) : option B :=
  match f , o with 
  | Some g , Some x => Some (g x)
  | _ , _ => None
  end.
Definition option_map2 {A B C} (f : A -> B -> C)
                       (o1 : option A) 
                       (o2 : option B)
                       : option C :=
  match o1 , o2 with 
  | Some x , Some y => Some (f x y)
  | _ , _ => None
  end.

Notation " x << f >> y" := (option_map2 f x y) (at level 20).

Fixpoint union_cod (u : Value) : option Value :=
  match u with 
  | ⊥ => Some ⊥
  | (v |-> w) => w
  | (u ⊔ u') => union_cod u <<v_union>> union_cod u' 
  end.

Lemma fn_in_union_dom : forall u v w, 
    all_fns u 
    -> (v|-> w) ∈ u
    -> v ⊆ union_dom u.
Proof.
  intros u. 
  induction u; 
    intros v w fg hin u0; inversion hin; subst; auto.
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
     u ⊆ (v|-> w)
    -> union_cod u ⊆ w.
Proof.
  intros u v w s; induction u; simpl in *.
  + intros u' h; inversion h; subst.
    specialize (s ⊥ ltac:(reflexivity)). inversion s.
  + intros u' h; inversion h; subst.
    specialize (s v_wrong ltac:(reflexivity)). inversion s.
  + intros u' m. specialize (s (u1 |-> u2) ltac:(reflexivity)).
    inversion s. subst. auto.
  + intros u' h; inversion h; subst.
    ++ eapply IHu1; auto.  intros C z.  eapply s. simpl. left. auto.
    ++ eapply IHu2; auto.  intros C z.  eapply s. simpl. right. auto.
Qed.

Definition factor := 
  fun (u u' v w : Value) => 
    (all_fns u') /\ (u' ⊆ u) /\ (union_dom u' [<=] v) /\ (w [<=] union_cod u').


(* Inversion of less-than for functions, case for trans *)

Lemma sub_inv_trans : forall u' u2 u, 
    all_fns u' -> u' ⊆ u
    -> (forall v' w', (v' |-> w') ∈ u -> exists u3, factor u2 u3 v' w')
    -> exists u3, factor u2 u3 (union_dom u') (union_cod u').
Proof.
intros u' u2 u fu' hsub IH.
induction u'.
- exfalso. apply bot_not_Fn. 
  eapply fu'. reflexivity.  
- exfalso. apply wrong_not_Fn. 
  eapply fu'. reflexivity.  
- apply IH.
  eapply fun_inc_mem.
  simpl. auto.
- unfold all_fns in *. 
  destruct (union_inc_inv _ _ _ hsub) as [h1' h2'].
  destruct IHu'1 as [u31 [ fu21' [u31u2 [de1du1 cu1cu31]]]]. 2: { exact h1'. }.
  intros z h. specialize (fu' z (or_introl h)). inversion fu'. done.
  destruct IHu'2 as [u32 [ fu22' [u32u2 [de1du2 cu1cu32]]]]. 2: { exact h2'. }.
  intros z h. specialize (fu' z (or_intror h)). inversion fu'. done.
  exists (v_union u31 u32).
  repeat split.
  + unfold factor, all_fns in *.
    admit.
  + eapply union_inc; eauto.
  + simpl. eapply v_sub_mono; auto.
  + simpl. eapply v_sub_mono; auto.
Admitted.

(* Inversion of less-than for functions *)

Lemma sub_inv : forall u1 u2, u1 [<=] u2  
                  -> forall v w, (v |-> w) ∈ u1
                  -> exists u3, factor u2 u3 v w.
Proof.
  intros u1 u2 h.
  induction h. 
  - intros v1 w1 h1. inversion h1.
  - intros v1 w1 h1. inversion h1.
  - intros v1 w1 m.
    inversion m; eauto. 
  - intros v1 w1 m.
    destruct (IHh _ _ m) as [u31 [fu31 [u31u21 [domu31v wcodu31]]]].
    exists u31. repeat split.
    + admit.
    + intros C z. simpl. left. eauto.
    + apply domu31v.
    + apply wcodu31.
  - intros v1 w1 m.
    destruct (IHh _ _ m) as [u31 [fu31 [u31u21 [domu31v wcodu31]]]].
    exists u31. repeat split.
    + admit.
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
  - intros v1 w1 h1. inversion h1. subst.
Admitted.





(*
Definition scope := atoms.

Definition Env : scope -> Type := 
  fun Γ => forall {x}, x `in` Γ -> Value.

Lemma impossible : forall {A : Type} x, x `in` {} -> A.
intros. fsetdec.
Defined.

Definition empty : Env {} :=
  (fun {x} (h : x `in` {}) => impossible x h) : Env {}.

Lemma in_tail : forall {x y : atom}{Γ},
  y `in` ({{x}} \u Γ) -> x <> y -> y `in` Γ.
Proof.
  intros. fsetdec.
Qed.

Definition cons {Γ} (x:atom)  (v : Value) (γ : Env Γ) :
  Env ({{x}} \u Γ) :=
   fun {y : atom} (H : y `in` ({{x}} \u Γ)) =>                    
     match (x == y) with 
     | left _ => v 
     | right pf => γ y (ltac:(fsetdec))
     end
.

Definition rename {Γ} (x y:atom) 
  (γ : Env ({{x}} \u Γ)) : Env ({{y}} \u Γ).
intros z h.  
destruct (z == y). 
+ subst. apply (γ x). eauto.
+ apply (γ z). fsetdec.
Defined.

(*
Definition head {Γ x} (e : Env (x :: Γ)) : Value :=
  e x (in_eq _ _).

Definition tail {Γ x} (e : Env (x :: Γ)) : Env Γ :=
   fun (y : atom) (H : In y Γ) => e y (in_cons _ _ _ H). 

Require Import Coq.Logic.FunctionalExtensionality.

Lemma tail_cons : forall {Γ x} (γ : Env (x :: Γ)), 
    γ = cons (head γ) (tail γ).
Proof.
  intros. 
  extensionality y.
  extensionality H.
Admitted.
*)

(* We extend the sub relation pointwise to environments. *)

Definition env_sub {Γ} (γ : Env Γ) (δ : Env Γ) :=
  forall x h, γ x h [<=] δ x h.

Definition env_bot {Γ} : Env Γ :=
  fun x h => ⊥.

Definition env_union {Γ} (γ : Env Γ) (δ : Env Γ) :=
  fun x h => γ x h ⊔ δ x h.

*)

(* Denotational semantics *)

(* Uses co-finite quantification *)
Inductive sem : forall {Γ}, Env Γ -> tm -> Value -> Prop :=
  | sem_var : forall {Γ}{γ : Env Γ}{x}
      (h : x `in` Γ),
      sem γ (var_f x) (γ x h)
  | sem_app : forall{Γ}{γ: Env Γ}{L M v w},
         sem γ L (v |-> w)
      -> sem γ M v
      -> sem γ (app L M) w
  | sem_abs : forall {L} {Γ}{γ: Env Γ}{v w:Value}{N},
      (forall x, x `notin` L ->
          sem (cons x v γ) (N ^ x) w) -> 
      sem γ (abs N) (v |-> w)
  | bot_intro : forall {Γ}{γ: Env Γ}{M},
      lc_tm M ->
      sem γ M ⊥
  | union_intro : forall {Γ}{γ: Env Γ}{M}{v w:Value},
      sem γ M v
      -> sem γ M w
      -> sem γ M (v ⊔ w)
  | sub : forall {Γ}{γ: Env Γ}{v w:Value} {M}{v w},
      sem γ M v
      -> w [<=] v
      -> sem γ M w
.

Lemma sem_lc : forall {Γ}{γ : Env Γ}{M v}, 
    sem γ M v -> lc_tm M.
Proof.
  intros. induction H; auto.
Qed.

Lemma sem_subst : forall {x y : atom} {Γ}{γ : Env ({{x}} \u Γ)}{v M},
    sem γ M v ->
    forall y, 
    sem (rename x y γ) (subst_tm (var_f y) x M) v.
Proof. 
  intros.
  dependent induction H.
  all: simpl; eauto.
  destruct (x0 == x) eqn:E.
  rewrite E. subst.
Admitted.

Lemma sem_rename : forall {Γ}{γ : Env Γ}{x y v w M},
    x \notin Γ \u fv_tm M ->
    y \notin Γ \u fv_tm M ->
  sem (cons x v γ) (M ^ x) w ->
  sem (cons y v γ) (M ^ y) w.
Proof.
  intros.
  destruct (x == y). subst. auto.
Admitted.

Lemma sem_abs_exists :  forall {Γ}{γ: Env Γ}{v w:Value}{N},
  forall x, x `notin` Γ \u fv_tm N ->
      sem (cons x v γ) (N ^ x) w -> 
      sem γ (abs N) (v |-> w).
Proof.
  intros.
  eapply (@sem_abs (Γ \u fv_tm N) Γ) .
  intros y Fr.
  eapply sem_rename. 
  3: eauto.
  fsetdec.
  fsetdec.
Qed.

Definition Denotation Γ := Env Γ -> Value -> Prop.

Definition E : forall {Γ} M, Denotation Γ := fun {Γ} M γ v => sem γ M v.

Definition den_eq {Γ} : Denotation Γ -> Denotation Γ -> Prop :=
  fun d1 d2 => forall (γ : Env Γ) v, (d1 γ v) <-> d2 γ v.

Infix "[==]" := den_eq (at level 50).

Lemma den_eq_refl : forall {Γ}(d : Denotation Γ), 
    d [==] d.
Proof. 
  intros. split. auto. auto.
Qed.

Lemma den_eq_sym :  forall {Γ}(d1 d2 : Denotation Γ), 
    d1 [==] d2 -> d2 [==] d1.
Proof. 
  intros. split; intros; specialize (H γ v); destruct H; auto.
Qed.

Lemma den_eq_trans :  forall {Γ}(d1 d2 d3 : Denotation Γ), 
    d1 [==] d2 -> d2 [==] d3 -> d1 [==] d3.
Proof. 
  intros. split; intros; specialize (H γ v); destruct H;
    specialize (H0 γ v); destruct H0; auto.
Qed.


(* Local Variables: *)
(* company-coq-local-symbols: (("|->" . ↦)) *)
(* End: *)

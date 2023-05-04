Require Export lc.tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import lc.SetsAsPredicates.

Require Import lc.env.

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/PValueCBV.agda *)


Inductive Value : Type :=
  | v_nat : nat -> Value 
  | v_map : list Value -> Value -> Value
    (* trivial function value, evaluated but never applied *)
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
  forall X E, mem E ⊆ F X -> nonempty X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ D <> nil.

Definition monotone (F : P Value -> P Value) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> nonempty X 
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
    eapply wInFD. cbn. auto.
Qed.

(*  Primitive Abstraction followed by Application is the identity --------- *)


(* This is about primitive functions, so skip for now *)


(* Environments ---------------------- *)

Definition Env := GEnv (P Value).

Definition ne (s : P Value) : Type := { x : Value & s x }.

Definition nonempty_env (ρ : Env) : Type := forall x, ne (ρ x).

(* Definition nonempty_env : Env -> Prop := fun ρ => forall x, Inhabited  _ (ρ x). *)

Definition sub_env ( ρ1 : Env ) (ρ2: Env) : Prop :=
  forall x, ρ1 x ⊆ ρ2 x.

Infix "⊆e" := sub_env (at level 50).

#[global] Instance Transitive_sub_env : Transitive sub_env.
Proof. 
  unfold Transitive. intros x y z S1 S2.
  intros w. specialize (S1 w). specialize (S2 w).
  transitivity (y w); auto.
Qed.

Import EnvNotations.

Lemma extend_nonempty_env {ρ x X} : 
  nonempty_env ρ -> ne X -> nonempty_env (x ⤇ X ● ρ).
Proof.                                                
  intros NEP NEX.
  intro y. unfold env_cons.
  destruct (x == y); eauto.
Qed.

Lemma env_ext {ρ ρ' y X} :
  ρ ⊆e ρ' -> forall x , (y ⤇ X ● ρ) x ⊆ (y ⤇ X ● ρ' ) x.
Proof. 
  intros. unfold env_cons.
  destruct (y == x); eauto. reflexivity.
Qed.

(* A finite environemtn has a list of values for 
   each variable. *)
Definition finite_env (ρ : Env) : Prop :=
  forall x , exists E , (ρ x ≃ mem E) /\ E <> nil.

Definition env_union (ρ1 ρ2 : Env) : Env := 
  fun x v => ρ1 x v \/ ρ2 x v.

Infix "⊔e" := env_union (at level 60).

Lemma join_finite_env {ρ1 ρ2} : 
  finite_env ρ1
  -> finite_env ρ2
  -> finite_env (ρ1 ⊔e ρ2).
Proof. 
  intros f1 f2 x.
  move: (f1 x) => [E1 [ pE1 NE1 ]]. 
  move: (f2 x) => [E2 [ pE2 NE2 ]].
  exists (E1 ++ E2).
  repeat split.
  intros v [ p1x | p2x ].
Admitted.

Lemma join_lub {ρ ρ1 ρ2} :
  ρ1 ⊆e ρ -> ρ2 ⊆e ρ -> (ρ1 ⊔e ρ2) ⊆e ρ.
Proof.
  intros p1p p2p x v [vp1x | vp2x].
  eapply p1p; eauto.
  eapply p2p; eauto.
Qed.

Lemma join_sub_left {ρ1 ρ2} : 
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros x d z. left. eauto.
Qed.

Lemma join_sub_right {ρ1 ρ2} : 
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros x d z. right. eauto.
Qed.

Definition monotone_env (D : Env -> P Value) := 
 forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

(* --- Relations on results and products --------------- *)

(* TODO.
   This part seems to be not connected to the rest. 
   Skipping for now.
*)


(* Continuous ----------------------------------------- *)

Definition continuous_In (D:Env -> P Value) (ρ:Env) (v:Value) : Prop :=
  v ∈ D ρ -> exists ρ' , finite_env ρ' /\ ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env (D:Env -> P Value) (ρ:Env) : Prop :=
  forall v, continuous_In D ρ v.

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
Definition initial_finite_env (ρ : Env) (NE : nonempty_env ρ) : Env :=
  fun x => match (NE x) with 
        | existT _ y _ => ⌈ y ⌉
        end.

Lemma singleton_mem : forall v : Value,  ⌈ v ⌉ ⊆ mem (v :: nil).
Proof. intro v. econstructor. inversion H. done. Qed.

Lemma mem_singleton : forall v : Value, mem (v :: nil) ⊆ ⌈ v ⌉.
Proof. intro v. cbv. intros. inversion H. subst. econstructor; eauto. done. Qed.

#[global] Hint Resolve singleton_mem mem_singleton : core. 

Lemma initial_fin (ρ : Env) (NE : nonempty_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  intros x.
  unfold initial_finite_env.
  unfold nonempty_env in NE.
  move: (NE x) => [ v w ].
  exists (cons v nil).
  repeat split.
  + eauto. 
  + eauto.
  + done.
Qed.



Lemma initial_fin_sub (ρ : Env) (NE : nonempty_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  intros x y vinit.
  unfold initial_finite_env in *.
  unfold nonempty_env in NE.
  destruct (NE x) as [v wpx].
  inversion vinit. subst. auto.
Qed.

(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Env) (NE : nonempty_env ρ) : Env :=
  fun y => match (x == y) with
        | left _ => D
        | right _ => let (v,_) := (NE y) in  ⌈ v ⌉
        end.

Lemma single_fin { v x ρ NE } : 
  finite_env (single_env x ⌈ v ⌉ ρ NE).
Proof.        
  intros y. 
  unfold single_env.
  unfold nonempty_env in NE.
  destruct (x == y).
  + subst. exists (cons v nil).
    repeat split; eauto. done.
  + move: (NE y) => [ w _ ].
    exists (cons w nil).
    repeat split; eauto. done.
Qed.

Lemma single_sub { ρ x v } :
  forall (NE : nonempty_env ρ),
    v ∈ ρ x 
  -> (single_env x ⌈ v ⌉ ρ NE) ⊆e ρ.
Proof.
  intros NE vpx y w sing.
  unfold single_env in sing.
  destruct (x == y).
  + inversion sing. subst.
    auto.
  + destruct (NE y) as [u epy].
    inversion sing. subst.
    auto.
Qed.

(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  v ∈ single_env x ⌈ v ⌉ ρ NE x.
Proof.
  unfold single_env.
  destruct (x == x). reflexivity. done.
Qed.  

Lemma mem_head a (V : list Value) :
   a ∈ mem (a :: V).
Proof. 
  unfold mem. 
  unfold Ensembles.In.
  econstructor. auto.
Qed.

Lemma mem_cons d a (V : list Value) :
    d ∈ mem V ->
    d ∈ mem (a :: V).
Proof. 
  unfold mem. 
  unfold Ensembles.In.
  eapply in_cons.
Qed.

#[global] Hint Resolve mem_cons : core.

(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub E ρ (NE : nonempty_env ρ) :
   monotone_env E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', finite_env ρ' /\ ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
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
    repeat split.
    eapply join_finite_env; eauto.
    eapply join_lub; eauto.
    intros d dm.
    inversion dm; subst.
    eapply me. eapply join_sub_right. eauto. 
    eapply me. eapply join_sub_left. eauto.
Qed.

Lemma APPLY_continuous {D E ρ}{NE : nonempty_env ρ}{w} :
    w ∈ ((D ρ) ▩ (E ρ))
    -> continuous_env D ρ 
    -> continuous_env E ρ
    -> monotone_env D 
    -> monotone_env E
    -> exists ρ3 , 
      finite_env ρ3 /\ ρ3 ⊆e  ρ 
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
  exists (ρ1 ⊔e ρ2).
  repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - exists V. 
    have VwDp3 : V ↦ w ∈ D (ρ1 ⊔e ρ2).
    { eapply mD. 2: eapply VwDp1. 
      intros x v z. left.  auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { intros v vV. eapply mE.
      2: eapply VEp2; auto. 
      intros x m z. right. auto. }
    repeat split.
    + auto.
    + auto.
    + done.
Qed.


Lemma env_tail {ρ' x v ρ} :  
  ρ' ⊆e (x ⤇ v ● ρ) -> finite_env ρ' -> 
  nonempty_env ρ ->
  exists w, exists ρ'', ρ' = (x ⤇ w ● ρ'') /\
                (w ⊆ v) /\
                ρ'' ⊆e ρ /\
                finite_env ρ''.
Proof.
  intros h k ne.
  move: (ne x) => [ vv I ].
  exists (ρ' x). exists (x ⤇ ⌈ vv ⌉ ● ρ'). 
  repeat split.
  + extensionality y.
    unfold env_cons. destruct (x == y). subst. auto. auto.
  + move: (h x) => ll. unfold env_cons in ll. 
    rewrite eq_dec_refl in ll. auto.
  + intros y. move: (h y) => ll.
    unfold env_cons in *.
    destruct (x == y). subst.  
    cbv. intros x hh. inversion hh. subst. auto. auto.
  + unfold finite_env in *.
    intros y.
      unfold env_cons.
      destruct (x == y). subst.
      exists (cons vv nil). split. cbv.
      split. intros x h0. inversion h0. auto.
      intros x h0. destruct h0. subst. reflexivity. done.
      done.
      destruct (k y) as [E [F G]].
      exists E. split; auto.
Qed.

Lemma Lambda_continuous {E ρ} {NE : nonempty_env ρ}{ v x} :
  v ∈ Λ (fun D => E (x ⤇ D ● ρ)) 
  -> (forall V, V <> nil -> 
          continuous_env E (x ⤇ mem V ● ρ))
  -> monotone_env E
  -> exists ρ', finite_env ρ' /\
            ρ' ⊆e ρ /\
            (v ∈ (Λ (fun D => E (x ⤇ D ● ρ')))).
Proof.
  induction v.
  - intro h. inversion h.
  - intros [ wEVρ VN ] IH mE.
    destruct (IH l VN v wEVρ) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
    edestruct (env_tail ρ'Vρ fρ' NE) as 
      [ w [ ρ'' [ EQ [ WV [ S T]]]]].
    exists ρ''. subst.
    repeat split.
    + auto.
    + auto.
    + eapply mE; eauto. 
      intros y.
      unfold env_cons.
      destruct (x == y); auto. reflexivity.
    + done.
  - exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply (initial_fin_sub ρ NE).
Qed.

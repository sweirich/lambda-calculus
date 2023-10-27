Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.scoped.

Require Import structures.Structures.

Import SetNotations.
Local Open Scope set_scope.
Import MonadNotation.
Open Scope monad_scope.

(* Definitions *)
Require Import denot.definitions.

(* Rewrite rules for the definition of the denotation *)
Require Import denot.denot.

(* Weakening *)
Require Import denot.subst.

(* Operators preserve validity *)
Require Import denot.valid_theory. 

(* Congruence: operators respect set equality *)
Require Import denot.congruence_theory.

(* Denotation function is continuous. *)
Require Import denot.continuity.

(* Denotation produces a consistent set *)
(* Require Import denot.consistency. *)

Import EnvNotations.
Import LCNotations.
Local Open Scope tm.

(* ---- -------------------------------------- *)

(* RET is strict *)
Lemma RET_strict {A} : RET (fun (x : A) => False) ≃ fun x => False.
split.
- unfold RET. intros x xIn.
destruct x; try done.
destruct l; try done.
destruct l; try done.
move: xIn => [h1 h2].
destruct f; destruct l; try done.
specialize (h1 a ltac:(left; auto)). done.
- unfold RET.
  intros x xIn. done.
Qed.


Lemma BIND_strict {A}{B} : forall (k : P A -> P (Comp B)), BIND (fun x => False) k ≃ fun x => False.
Proof.
  intros k.
  unfold BIND.
  split.
  - intros x xIn.
    destruct x.
    + move: xIn => [t1 [k1 [h _]]]. done.
    + move: xIn => [t1 [k1 [h _]]]. done.
  - intros x xIn. done.
Qed.

(* k∈℘k *)
Lemma k_in_den_k : forall k, v_nat k ∈ NAT k.
Proof. intros. reflexivity. Qed.

Lemma k_in_den_k'_inv : forall k k', v_nat k ∈ NAT k' -> k = k'.
Proof. intros. inversion H. done. Qed.

Lemma v_in_den_k_inv :  forall v k, v ∈ NAT k -> v = v_nat k.
Proof. intros. destruct v; inversion H. done. Qed.


Lemma NAT_den {k} : NAT k ≃ ⌈ v_nat k ⌉.
split. intros x In. destruct x; try done. inversion In. subst. constructor.
intros x In. inversion In. cbn. auto. Qed.

Lemma den_list : forall i j D, D ⊆ LIST (NAT i :: NAT j :: nil) ->
                 forall x, x ∈ D -> x = v_list (v_nat i :: v_nat j :: nil).
Proof.
  intros.
  specialize (H x H0).
  destruct x; try done. 
  destruct l; try done; inversion H; subst; clear H.
  apply v_in_den_k_inv in H4. subst.
  inversion H6. subst. clear H6.
  apply v_in_den_k_inv in H2. subst.
  inversion H4. subst.
  reflexivity.
Qed.

Lemma CONS_LIST {k1 k2 } : CONS (NAT k1) (CONS (NAT k2) NIL) ≃ LIST (NAT k1 :: NAT k2 :: nil).
Proof.
  intros.
  split.
  + intros w In. destruct w; try done.
    destruct l; try done.
    destruct In as [x In]. apply v_in_den_k_inv in x.
    destruct l; try done.
    destruct In as [y In]. apply v_in_den_k_inv in y.
    destruct l; try done. 
    subst. cbn. 
    econstructor; eauto. reflexivity. 
    econstructor; eauto. reflexivity. 
    cbv in In. inversion In.
  + intros w In.
    eapply den_list in In. 2: { reflexivity.  }
    subst. 
    econstructor; eauto using k_in_den_k.
    econstructor; eauto using k_in_den_k.
    econstructor.
Qed.

Lemma l_equiv_den_k1 {l k} : mem l ≃ ⌈ v_nat k ⌉ -> (mem l ⊆ NAT k) /\ nonempty_fset l.
Proof.
  intros.
  rewrite H.
  split. rewrite NAT_den. reflexivity.
  destruct l. destruct l. cbv in H. destruct H. intro h. eapply (H0 (v_nat k)). eapply in_singleton.
  done.
Qed.

Lemma l_equiv_den_k2 {l k} : (mem l ⊆ NAT k) /\ nonempty_fset l -> mem l ≃ ⌈ v_nat k ⌉.
Proof.
  move=> [h1 h2].
  split.
  rewrite <- NAT_den. done.
  destruct l. destruct l. done.
  have vIn: v ∈ NAT k. specialize (h1 v ltac:(left; auto)). done.
  apply v_in_den_k_inv in vIn. subst.
  intros v0 v0In. inversion v0In. subst.
  left; eauto.
Qed. 

Lemma l_equiv_den_k {l k} : (mem l ⊆ NAT k) /\ nonempty_fset l <-> mem l ≃ ⌈ v_nat k ⌉.
Proof. split. eapply l_equiv_den_k2; eauto. eapply l_equiv_den_k1; eauto. Qed.


Lemma ADD_APPLY_LIST {i j} : 
  ADD ▩ (LIST (NAT i :: NAT j :: nil)) ≃ RET (NAT (i + j)).
Proof.
  split.
  + intros w APP. inversion APP; subst; clear APP.
    all: cbn in H.
    all: try done.
    destruct w; try done.
    - (* contradiction *) 
      destruct H as [NI VM].
      assert False. eapply NI. 
      unfold valid_mem in VM. destruct V. destruct l; try done.
      move: (den_list _ _ _ H0 v ltac:(econstructor; eauto)) => h1. 
      subst.
      exists i. exists j. left; auto. done.
    - destruct l; try done.
      destruct l; try done.
      destruct H as [i0 [j0 [k0 [h0 [h1 h2]]]]]. subst.
      cbn.
      apply l_equiv_den_k1 in h1. destruct h1. 
      split; eauto.
      rewrite h0 in H0.
      move: (den_list _ _ _ H0 (v_list (v_nat i0 :: v_nat j0 :: nil)) ltac:(auto)) => h3. inversion h3. subst. clear h3.
      auto.
    - destruct x; try done.
   + intros w wIn.
     destruct w; try done.
     destruct l; try done.
     destruct l; try done.
     cbn in wIn.
     move: wIn => [wIn VL].
     have EQ: mem f ≃ ⌈ v_nat (i + j) ⌉. eapply l_equiv_den_k2; eauto.
     eapply BETA with (V := singleton_fset (v_list (v_nat i :: v_nat j :: nil))).
     - cbn. exists i. exists j. exists (i+j).
       repeat split. eauto. eauto.
       rewrite EQ. eauto.
       rewrite EQ. eauto.
     - intros x xIn. inversion xIn. subst.
       cbn. eauto using k_in_den_k.
       inversion H.
     - unfold valid_mem. done. 
Qed. 

Lemma ADD_APPLY_CONS {k1 k2} : 
  (ADD ▩ CONS (NAT k1) (CONS (NAT k2) NIL)) ≃ RET (NAT (k1 + k2)).
Proof.
  rewrite CONS_LIST.
  eapply ADD_APPLY_LIST.
Qed. 

(* The semantics for projection is still wrong, so not updating this 
   proof yet. *)

Lemma CONS_APPLY_ZERO1 {D1 D2} : (CONS D1 D2 ▩ NAT 0) ⊆ RET D1.
  intros w APP. inversion APP; try inversion H.
  + subst.
    apply v_in_den_k_inv in H0. inversion H0. subst.
    destruct VS; simpl in H1. done. inversion H1. subst.
    inversion H.
    cbn. split.
Abort.
(*
    rewrite <- H2. eauto. 
    destruct W.  destruct H2 as [h1 h2]. specialize (h1 w0 ltac:(auto)). done.
    done.
  + destruct x; try done.
  + destruct x; try done. 
    apply v_in_den_k_inv in H0.
    subst.
    exfalso. 
    eapply H1; eauto.
Qed. *)

Lemma CONS_APPLY_ZERO2 {D1 D2 VS} : 
  v_list VS ∈ D2 ->
  RET D1 ⊆ (CONS D1 D2 ▩ NAT 0).
Proof.
  intros VV.
  intros c cIn.
  destruct c; try done.
  destruct l; try done.
  destruct l; try done.
  cbn in cIn. move: cIn => [cIn VL].
Abort.
(*
  admit.
  eapply PROJ with (k := 0)(VS := v :: VS)(w:= a); eauto using k_in_den_k.
  
  destruct l.
  + done.
  + clear VL.
    have LH: (v_list (v :: VS) ∈ CONS D1 D2). unfold CONS. cbn; eauto.
    have EQ: (mem (v :: l) ≃ ⌈ v ⌉). 
    induction l.  admit.
    simpl_env. repeat rewrite union_mem.
    unfold CONS in LH.

    unfold mem.
    eapply PROJ with (k := 0)(VS := v :: VS)(w:= a); eauto using k_in_den_k.
  econstructor; eauto.
Admitted. *)

Lemma CONS_APPLY_ZERO {D1 D2 VS} : v_list VS ∈ D2 -> (CONS D1 D2 ▩ NAT 0) ≃ RET D1.
Admitted.

Lemma CONS_APPLY_SUCC {D1 D2 VS k} : v_list VS ∈ D2 -> (CONS D1 D2 ▩ NAT (1 + k)) ≃ (D2 ▩ NAT k).
Admitted.

(*
Lemma CONS_APPLY_SUCC1 {D1 D2 k} : (CONS D1 D2 ▩ NAT (1 + k)) ⊆ (D2 ▩ NAT k).
  intros w APP. inversion APP; try inversion H.
  + subst.
    apply v_in_den_k_inv in H0. inversion H0. subst.
    destruct VS; simpl in H1. done. 
    inversion H.
    eapply PROJ; eauto using k_in_den_k.
  + destruct x; try done.
  + destruct x; try done.
    exfalso; eapply H2; eauto.
Qed.
*)

(* ---------------------------------------------------- *)

(* Nonempty environments *)

Lemma extend_nonempty_env {ρ x X} : 
  x `notin` dom ρ ->
  nonemptyT X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply ForallT_cons; eauto. Qed.

#[export] Hint Resolve extend_nonempty_env : core.

(* ---------------------------------------------------------- *)

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/ISWIMPValue.agda *)

(* ------------------------------------------------------- *)

(* Soundness of reduction with respect to denotation *)
(* ISWIMPValue.agda *)

Ltac invert_value :=
  repeat match goal with 
    | [ H : value (_ _) |- _ ] => inversion H; clear H; subst
    | [ H : value fail |- _ ] => inversion H; clear H; subst
    | [ H : listvalue (_ _) |- _ ] => inversion H; clear H; subst
    | [ H : listvalue fail |- _ ] => inversion H; clear H; subst
  end.

Lemma denot_value_valid {t}{ρ} : 
  fv_tm t [<=] dom ρ -> valid_env ρ 
  -> (value t -> valid (denot_val t ρ)) * 
      (listvalue t -> forall (x : Value), x ∈ (denot_val t ρ) -> { l & v_list l = x }).
Proof.
  induction t.
  all: intros FV; simpl in FV.
  all: intros NEρ.
  all: split.
  all: intros h.
  all: autorewrite with denot.
  all: try solve [ assert False; invert_value; done].  
  + unfold valid_env in NEρ.
    eapply (@ForallT_access _ Bottom _ _) in NEρ.
    2: instantiate (1:= x); auto.
    destruct NEρ.
    exists x0. auto.
  + pick fresh x.
    erewrite denot_val_abs with (x:=x); eauto.
    eapply valid_Λ.
  + eapply valid_NAT; eauto. 
  + eapply valid_ADD; eauto.
  + assert False. inversion h. done.
  + eapply valid_NIL; eauto.
  + (* exists nil. cbv. econstructor. *)
    intros x In. inversion In. exists nil. reflexivity.
  + simpl in FV. 
    move: (IHt1 ltac:(fsetdec) NEρ) => [ih11 _].
    move: (IHt2 ltac:(fsetdec) NEρ) => [ih21 ih22].
    have V2: value t2. invert_value. auto.
    have LV: listvalue t2. invert_value. auto.
    move: (ih21 V2) => [v NW].
    move: (ih22 LV v NW) => [l le].
    eapply valid_CONS; eauto. eapply ih11. invert_value. auto.
    subst. eauto.
  + move: (IHt1 ltac:(fsetdec) NEρ) => [ih11 _].
    move: (IHt2 ltac:(fsetdec) NEρ) => [ih21 ih22].
    have V2: value t2. invert_value. auto.
    have LV: listvalue t2. invert_value. auto.
    move: (ih21 V2) => [v  NW].
    move: (ih22 LV v NW) => [ll ii].
    subst.
    intros x CC. 
    destruct x; try done.
    exists l. reflexivity.
Qed.

Lemma denot_val_RET {ρ}{NE: valid_env ρ} {v} : 
  fv_tm v [<=] dom ρ -> value v -> denot v ρ ≃ RET (denot_val v ρ).
Proof.
  induction v.
  all: intros FV H0.
  all: inversion H0; try inversion H.
  all: autorewrite with denot.
  all: simpl in FV.
  all: try reflexivity. 
  rewrite IHv1; eauto.  fsetdec.
  rewrite BIND_RET.
  solve_continuous.
  eapply BIND_CONS_continuous.
  eapply denot_value_valid; eauto. fsetdec. 
  rewrite IHv2; eauto. fsetdec.
  rewrite BIND_RET.
  solve_continuous.
  eapply RET_CONS_continuous2.
  eapply denot_value_valid; eauto. fsetdec. 
  reflexivity.
Qed.


Definition valid_Comp (C : P (Comp (fset Value))) : Type :=
  (nonemptyT C * not (c_wrong ∈ C) * not (c_multi nil ∈ C))%type.
       
Lemma value_nonempty {t}{ρ} : 
  fv_tm t [<=] dom ρ -> valid_env ρ -> value t -> valid_Comp (denot t ρ).
Proof. 
  intros SC VE VT.
  move: (@denot_val_RET ρ VE t SC VT) => EQ.
  move: (denot_value_valid SC VE) => [h1 h2].
  specialize (h1 VT).
  destruct h1.
  repeat split.
  + unfold nonemptyT.
    exists (c_multi (ret (singleton_fset x))).
    rewrite EQ.
    cbn. repeat split; auto. done.
  + rewrite EQ.
    cbn. done.
  + rewrite EQ.
    cbn. done.
Qed.

(* Scoping predicates *)

Lemma subst_denot : forall t x u ρ1 ρ2, 
    scoped t (ρ1 ++ x ~ (denot_val u ρ2) ++ ρ2) ->
    scoped u ρ2 ->
    value u ->
    valid_env (ρ1 ++ ρ2) ->
    denot t (ρ1 ++ x ~ (denot_val u ρ2) ++ ρ2) ≃
    denot (t [x ~> u]) (ρ1 ++ ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2
  | 
  | move=> t1 t2 IH1 IH2
  | move=> t' IH
  | move=> t1 t2 IH1 IH2 |  move=> t1 t2 IH1 IH2 
  | move=> t1 IH1 
  | move=> t1 IH1 ].

  all: intros x u ρ1 ρ2 ST SU VU NE.
  all: simpl. 
  all: simpl_env. 
  all: autorewrite with denot.
  all: try solve [reflexivity].
  + destruct (y == x) eqn:EQ. subst.
    ++ have NI: x `notin` dom ρ1.
       { inversion ST. destruct_uniq. auto. }
       have D2: fv_tm u [<=] dom ρ2. 
       { inversion SU. auto. }
       have U2: uniq (ρ1 ++ ρ2). 
       { inversion ST. solve_uniq. }
       rewrite access_app_fresh; auto.       
       rewrite access_eq_var.
       rewrite denot_val_RET; simpl_env; auto. fsetdec.
       erewrite weaken_denot_val. reflexivity.
       fsetdec. auto.
    ++ repeat rewrite denot_var.
       eapply Proper_Same_RET; eauto.
       destruct (access_app_P ρ1 y) as [h1 | h2].
       repeat rewrite h1. reflexivity.
       move: (h2 ρ2) => [N1 ->]. 
       move: (h2 (x ~ denot_val u ρ2 ++ ρ2)) => [N3 ->].
       rewrite access_neq_var; auto.
       reflexivity.
  + move: (scoped_app_inv1 _ _ _ _ ST) => S1.
    move: (scoped_app_inv2 _ _ _ _ ST) => S2.
    eapply Proper_Same_BIND.
    eapply IH1; eauto.
    intros v1 v2 ->.
    eapply Proper_Same_BIND.
    eapply IH2; eauto.
    intros w1 w2 ->.
    reflexivity.
  + have LCU: lc_tm u. inversion SU. auto.
    pick fresh z.
    specialize (IH z ltac:(auto) x u).
    simpl. simpl_env.
    repeat rewrite (denot_abs z).
    simpl_env. fsetdec.
    simpl_env. rewrite fv_tm_subst_tm_upper. fsetdec.
    eapply Proper_Same_RET.
    eapply Λ_ext. intros D DV.
    have FZ: z `notin` (dom (ρ1 ++ x ~ denot_val u ρ2 ++ ρ2) \u fv_tm t').
    simpl_env. fsetdec. 
    move: (scoped_abs_inv _ z t' D _ FZ ST) => h.
    rewrite <- app_assoc.
    rewrite IH; auto.
    simpl_env. eapply extend_valid_env; eauto.
    rewrite subst_tm_open_tm_wrt_tm. eauto.
    rewrite subst_neq_var. auto.
    reflexivity.
  + move: (scoped_tcons_inv1 _ _ _ _ ST) => S1.
    move: (scoped_tcons_inv2 _ _ _ _ ST) => S2.
    eapply Proper_Same_BIND.
    eapply IH1; eauto.
    intros v' v ->.
    eapply Proper_Same_BIND.
    eapply IH2; eauto.    
    intros w' w ->. 
    reflexivity.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.

Lemma subst_denot1 :
  forall (t : tm) (x : atom) (u : tm) (ρ : Env (P Value)),
    scoped t (x ~ denot_val u ρ ++ ρ) 
    -> scoped u ρ 
    -> value u
    -> valid_env ρ
    -> denot t (x ~ denot_val u ρ ++ ρ) ≃ denot (t [x ~> u]) ρ.
Proof.
  intros. 
  eapply subst_denot with (ρ1 := nil); auto. 
Qed.



Lemma soundness: 
  forall t u, 
    full_reduction t u ->
    forall ρ,
    scoped t ρ ->
    scoped u ρ ->
    valid_env ρ ->
    denot t ρ ≃ denot u ρ.
Proof.
  intros t u RED. 
  induction RED; intros ρ SCt SCu NE.
  all: autorewrite with denot.
  - (* beta *)
    destruct SCt as [FV U lc]. inversion lc. subst.
    simpl in FV.
    pick fresh x.
    erewrite denot_abs with (x:=x). 2: fsetdec.
    rewrite BIND_RET; solve_continuous.
    eapply valid_Λ; auto.
    rewrite denot_val_RET; eauto. fsetdec.
    rewrite BIND_RET; solve_continuous.
    eapply denot_value_valid; auto. fsetdec.
    rewrite Λ_denot_APPLY_id; auto.
    eapply denot_value_valid; auto. fsetdec.
    rewrite (subst_tm_intro x t v); auto.
    replace ρ with (nil ++ ρ) at 3.
    rewrite <- subst_denot with (ρ1 := nil). reflexivity.
    simpl_env.
    econstructor; eauto. 
    rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
    inversion H; eauto.
    econstructor; eauto. 
    fsetdec.
    auto.
    auto.
    reflexivity.
  - (* abs-cong *)
    pick fresh x.
    repeat erewrite denot_abs with (x:=x); try fsetdec.
    specialize (H0 x ltac:(auto)).
    eapply Proper_Same_RET.
    eapply Λ_ext.
    intros X NEX.
    eapply H0.
    have F1 : x `notin` dom ρ \u fv_tm t. fsetdec.
    eapply (scoped_abs_inv _ x _ X _ F1 SCt).
    have F2 : x `notin` dom ρ \u fv_tm t'. fsetdec.
    eapply (scoped_abs_inv _ x _ X _ F2 SCu).
    eapply extend_valid_env; eauto.
  - (* app1 *) 
    have SC1: scoped t ρ. eapply scoped_app_inv1; eauto.
    have SC2: scoped t' ρ. eapply scoped_app_inv1; eauto.
    have SC3: scoped u ρ. eapply scoped_app_inv2; eauto.
    eapply Proper_Same_BIND. eauto.
    intros v v' ->.
    eapply Proper_Same_BIND. reflexivity.
    intros w w' ->.    
    eapply APPLY_cong. reflexivity. reflexivity.
  - (* app2 *)
    have SC1: scoped t ρ.  eapply scoped_app_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_app_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_app_inv2; eauto.
    eapply Proper_Same_BIND. reflexivity.
    intros v v' ->.
    eapply Proper_Same_BIND. auto.
    intros w w' ->.    
    eapply APPLY_cong. reflexivity. reflexivity.
  - (* cons1 *)
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped t' ρ.  eapply scoped_tcons_inv1; eauto.
    eapply Proper_Same_BIND. eauto.
    intros v v' ->.
    eapply Proper_Same_BIND. reflexivity.
    intros w w' ->.    
    eapply Proper_Same_RET.
    eapply CONS_cong. reflexivity. reflexivity.
  - (* cons2 *)
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_tcons_inv2; eauto.
    eapply Proper_Same_BIND. reflexivity.
    intros v v' ->.
    eapply Proper_Same_BIND. auto.
    intros w w' ->.    
    eapply Proper_Same_RET.
    eapply CONS_cong. reflexivity. reflexivity.
  - (* prj_zero *)

    destruct SCt. simpl in s.
    have Vv : valid (denot_val v ρ). { eapply denot_value_valid; eauto. fsetdec. }
    move: (@denot_value_valid w ρ ltac:(fsetdec) NE) => [h1 h2]. specialize (h2 H0).
    have Vw : valid (denot_val w ρ). eauto. 
    destruct (h1 ltac:(auto)) as [x xIn]. destruct (h2 x xIn) as [l1 <-]. 

    rewrite denot_val_RET; eauto. fsetdec.
    rewrite BIND_RET; solve_continuous.
    eapply BIND_continuous; solve_continuous.

    rewrite denot_val_RET; eauto. fsetdec.
    rewrite BIND_RET; solve_continuous.
    rewrite BIND_RET; solve_continuous.
    eapply valid_CONS; eauto.

    rewrite BIND_RET; solve_continuous.
    eapply valid_NAT.

    eapply CONS_APPLY_ZERO.
    eauto.
  - (* prj_suc *)

    destruct SCt. simpl in s.
    have Vv : valid (denot_val v ρ). { eapply denot_value_valid; eauto. fsetdec. }
    move: (@denot_value_valid w ρ ltac:(fsetdec) NE) => [h1 h2]. specialize (h2 H0).
    have Vw : valid (denot_val w ρ). eauto. 
    destruct (h1 ltac:(auto)) as [x xIn]. destruct (h2 x xIn) as [l1 <-]. 

    rewrite denot_val_RET; eauto. fsetdec.
    rewrite BIND_RET; solve_continuous.
    eapply BIND_continuous; solve_continuous.

    rewrite denot_val_RET; eauto. fsetdec.
    rewrite BIND_RET; solve_continuous.
    rewrite BIND_RET; solve_continuous.
    eapply valid_CONS; eauto.

    rewrite BIND_RET; solve_continuous.
    eapply valid_NAT.

    rewrite BIND_RET; solve_continuous.
    rewrite BIND_RET; solve_continuous.
    eapply valid_NAT.

    eapply CONS_APPLY_SUCC.
    eauto.
  - (* add *) 
    rewrite (BIND_RET ADD); solve_continuous.
    eapply valid_ADD.

    rewrite (BIND_RET (NAT k1)); solve_continuous.
    eapply BIND_continuous; solve_continuous.
    eapply valid_NAT.


    rewrite (BIND_RET (NAT k2)); solve_continuous.
    eapply BIND_continuous; solve_continuous.
    eapply valid_NAT.


    rewrite BIND_RET; solve_continuous.
    eapply valid_NIL.

    rewrite BIND_RET; solve_continuous.
    eapply valid_CONS. eapply valid_NAT. eapply valid_NIL.
    instantiate (1:= nil). cbv. econstructor; eauto.
    
    rewrite BIND_RET; solve_continuous.
    eapply valid_CONS. eapply valid_NAT. eapply valid_CONS. eapply valid_NAT. eapply valid_NIL.
    instantiate (1:= nil). cbv. econstructor; eauto.
    instantiate (1:= v_nat k2 :: nil). cbv. split. auto. econstructor; eauto.
    
    eapply ADD_APPLY_CONS; eauto.
Qed.


(* --------------------------------------------------------------- *)

(* Examples *)

(* Prove that 3 + 4 *)
Definition tm_Add : tm := 
  app add (tcons (lit 3) (tcons (lit 4) tnil)).

Lemma denot_tm : denot tm_Add nil ≃ RET (NAT 7).
Proof.
  unfold tm_Add.
  autorewrite with denot.
  rewrite BIND_RET; solve_continuous. eapply valid_ADD.
  rewrite BIND_RET; solve_continuous. eapply BIND_continuous; solve_continuous. 
  eapply valid_NAT.
  rewrite BIND_RET; solve_continuous. eapply BIND_continuous; solve_continuous.
  eapply valid_NAT.
  rewrite BIND_RET; solve_continuous. eapply valid_NIL.
  rewrite BIND_RET; solve_continuous. eapply valid_CONS. eapply valid_NAT. eapply valid_NIL.
  instantiate (1:=nil). econstructor; eauto.
  rewrite BIND_RET; solve_continuous. eapply valid_CONS. eapply valid_NAT. 
  eapply valid_CONS. eapply valid_NAT. eapply valid_NIL.
  instantiate (1:=nil). econstructor; eauto.
  instantiate (1:= (v_nat 4 :: nil)). repeat econstructor; eauto.
  rewrite ADD_APPLY_CONS.
  reflexivity.
Qed.


(* Denotation of the identity function: we can find any identity mapping we want 
   in the denotation of id. *)

Definition tm_Id : tm := abs (var_b 0).
Definition value_Id (w : Value) : Value := 
  (singleton_fset w) ↦ c_multi (singleton_fset w :: nil).
Definition comp_Id (w : Value) : Comp (fset Value) := 
  c_multi (singleton_fset (value_Id w) :: nil).

Lemma denot_Id {v} : comp_Id v ∈ denot tm_Id nil.
Proof.
  pick fresh x.
  rewrite (denot_abs x); simpl; auto.
  cbn.
  rewrite eq_dec_refl.
  split. 2: done.
  intros y yIn. cbv in yIn. destruct yIn; try done. subst.
  cbn. 
  repeat split. reflexivity.
  done.
  done.
Qed. 

(* 
Definition ConsistentDenot : Comp (fset Value) -> Comp (fset Value) -> Prop :=
   ConsistentComp (List.Forall2_any Consistent).

Lemma c_map : 
     forall (X1 X2 : list Value) (r1 r2 : Comp (list Value)), 
    (List.Forall2_any Consistent X1 X2 -> ConsistentDenot r1 r2) -> Consistent (X1 ↦ r1) (X2 ↦ r2).
Proof.
  intros.
Admitted.

Lemma denot_Id_inv : forall (x : Comp (list Value)) ρ, x ∈ denot tm_Id ρ -> forall w,  ConsistentDenot x (comp_Id w).
Proof.
  intros x ρ.
  unfold tm_Id. 
  pick fresh y.
  rewrite (denot_abs y); auto.
  intro h. 
  destruct x; try done.
  destruct l; try done.
  destruct l0; try done.
  cbn in h. rewrite eq_dec_refl in h.
  move: h => [h0 h1].
  intros w.
  eapply cc_multi.
  econstructor; eauto.
  unfold List.Forall2_any.
  intros x0 y0 I0 I1.
  cbn in I1. destruct I1; try done. subst.
  unfold value_Id.
  specialize (h0 x0 I0).
  destruct x0; try done.
  cbn in h0.
  destruct h0 as [h2 h3].
  destruct c; try done.
  destruct l1; try done.
  destruct l2; try done.
  cbn in h2.
  destruct h2 as [h4 h5].
  eapply c_map. intros h.
  eapply cc_multi.
  econstructor; eauto.
Admitted.
*)
(* Need a better definition of consistency??? *)


(* A term with an unbound variable has no value. *)
Definition tm_IllScoped : tm := app (var_b 1) (var_b 0).

Lemma denot_IllScoped : forall x, not (x ∈ denot tm_IllScoped nil).
Proof.
  unfold tm_IllScoped.
  rewrite denot_app.
  repeat rewrite denot_var_b.
  intros x h.
  rewrite -> RET_strict in h.
  rewrite -> BIND_strict in h.
  done.
Qed.  

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).


#[global] Hint Rewrite access_eq_var : lngen.

(*
Lemma denot_Delta_inv :
  forall x, x ∈ denot tm_Delta nil -> 
       exists v w, Consistent x (((v :: nil ↦ w) :: v :: nil) ↦ w).
Proof.
  intro x. unfold tm_Delta.
  pick fresh y.
  rewrite (denot_abs y); auto.
  cbn. rewrite eq_dec_refl.
  destruct x; try done.
  move=> [h0 [h1 h2]].
  - inversion h0; subst; try done.
    + exfalso. eapply wrong_not_successful; eauto.
    + exfalso. eapply wrong_not_successful; eauto.
    + exists (l ↦ x). exists x.
      eapply c_map2. reflexivity.
    + exists (l ↦ x). exists x.
      eapply c_map2. reflexivity.
    + exists (v_nat 0). exists v_wrong. eauto.
    + exists (v_nat 0). exists v_wrong. eauto.
  - cbn. intros.
      exists v_fun. exists v_fun. eauto.
Qed.

Lemma denot_Delta : forall (v w : Value), success v ->
    (((v :: nil ↦ w) :: v :: nil) ↦ w) ∈ denot tm_Delta nil.
Proof.
  intros v w NW.
  pick fresh x.
  unfold tm_Delta.
  rewrite (denot_abs x); auto.
  cbn. rewrite eq_dec_refl.
  split. 2: { unfold valid_mem. split. intro h. done. 
              econstructor; eauto. done. }
  cbv.
  eapply BETA with (V := v :: nil).
  unfold In. left. auto.
  rewrite -> mem_singleton. 
  intros x0 II. inversion II. subst. cbv. right. left. auto.
  unfold valid_mem.
  split; eauto.
  intro h. done. 
Qed.
  

Definition tm_Omega : tm := app tm_Delta tm_Delta.

Lemma denot_Omega : forall v, not (v ∈ denot tm_Omega nil).
Proof.
unfold tm_Omega.
rewrite denot_app.
intro v.
intro h.
inversion h; subst; clear h.
+ apply denot_Delta_inv in H.
  move: H => [v [w C]]. inversion C.
+ apply denot_Delta_inv in H.
  move: H => [v [w C]]. inversion C.
+ apply denot_Delta_inv in H.
  move: H => [v1 [w2 C]]. 
  inversion C; subst.
Abort.
*)



(* Λ  \Lambda
   ▩  \squarecrossfill 
   ↦  \mapsto  
   ⤇ \Mapsto  
   ●  \CIRCLE 
   ⊆  \subseteq   (Included)
*)

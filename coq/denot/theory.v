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

(* Weakening & substitution for the definition of the denotation *)
Require Import denot.denot.

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


Lemma ADD_APPLY_LIST {i j} : 
  ADD ▩ (LIST (NAT i :: NAT j :: nil)) ≃ RET (NAT (i + j)).
Proof.
  split.
  + intros w APP. inversion APP; subst; clear APP.
    all: cbn in H.
    all: try done.
    destruct w; try done.
    - destruct H as [NI VM].
      assert False. eapply NI. 
      unfold valid_mem in VM. destruct V; try done.
      move: (den_list _ _ _ H0 v ltac:(econstructor; eauto)) => h1. 
      subst.
      exists i. exists j. eauto. done.
    - destruct l; try done.
      destruct l; try done.
      destruct v; try done.
      destruct l; try done.
      destruct l0; try done.
      destruct H as [i0 [j0 [h0 h1]]]. subst.
      move: (den_list _ _ _ H0 _ h0) => h1. inversion h1. subst. clear h1.
      cbn.
      rewrite <- In_Sub.
      eapply k_in_den_k.
    - destruct x; try done.
   + intros w wIn.
     unfold RET in wIn.
     destruct w; try done.
     destruct l; try done.
     destruct l0; try done.
     cbn in wIn.
Admitted. 
(*
     apply v_in_den_k_inv in wIn. subst.
     eapply BETA with (V := v_list (v_nat i :: v_nat j :: nil) :: nil).
     - cbn. eauto.
     - intros x xIn. inversion xIn. subst.
       cbn. eauto using k_in_den_k.
       inversion H.
     - cbn. split. eauto. unfold In, mem. intro h. inversion h. 
       econstructor; eauto. done.
Qed. *)

Lemma ADD_APPLY_CONS {k1 k2} : 
  (ADD ▩ CONS (NAT k1) (CONS (NAT k2) NIL)) ≃ RET (NAT (k1 + k2)).
Proof.
  rewrite CONS_LIST.
  eapply ADD_APPLY_LIST.
Qed. 

Lemma CONS_APPLY_ZERO1 {D1 D2} : (CONS D1 D2 ▩ NAT 0) ⊆ RET D1.
  intros w APP. inversion APP; try inversion H.
  + subst.
    apply v_in_den_k_inv in H0. inversion H0. subst.
    destruct VS; simpl in H1. done. inversion H1. subst.
    inversion H.
    cbn.
    rewrite mem_singleton_eq.
    eauto.
  + destruct x; try done.
  + destruct x; try done. 
    apply v_in_den_k_inv in H0.
    subst.
    exfalso. 
    eapply H1; eauto.
Qed.

(*
Lemma CONS_APPLY_ZERO2 {D1 D2 VS} : 
  v_list VS ∈ D2 ->
  D1 ⊆ (CONS D1 D2 ▩ NAT 0).
Proof.
  intros VV w In.
  eapply PROJ with (k := 0)(VS := w :: VS); eauto using k_in_den_k.
  econstructor; eauto.
Qed. 

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

(*
Definition denot1 (t : tm) (ρ : Rho) : P Value.
  remember (size_tm t) as n.
  have GE: n >= size_tm t. subst. auto. clear Heqn.
  move: t GE ρ.
  induction (lt_wf n) as [n _ denot].
  Print tm.
  intros [ i | x | u | t | k | (* add *) | (* nil *) | t ] SZ; simpl in SZ.
  all: intros ρ.
  - exact ⌈ v_wrong ⌉.
  - exact (ρ ⋅ x).
  - move: (fresh_for (dom ρ \u fv_tm u)) => x.
    have F : P Value -> P Value.
    intro D.
    have LT: size_tm (u ^ x) < n. {  autorewrite with lngen; lia. }
    specialize (denot (size_tm (u ^ x)) LT (u ^ x) ltac:(auto) (x ~ D ++ ρ)).
    exact denot.
    exact (Λ F).
  - move: (denot (size_tm t) ltac:(lia) t ltac:(lia) ρ) => t'.
    move: (denot (size_tm u) ltac:(lia) u ltac:(lia) ρ) => u'.
    exact (t' ▩ u').
  - exact (NAT k). 
  - exact ADD.
  - exact NIL.    
  - move: (denot (size_tm t) ltac:(lia) t ltac:(lia) ρ) => t'.
    move: (denot (size_tm u) ltac:(lia) u ltac:(lia) ρ) => u'.
    exact (CONS t' u').
Defined. 
*)
(* ------------------------------------------------------- *)

(* Soundness of reduction with respect to denotation *)
(* ISWIMPValue.agda *)

Ltac invert_value :=
  repeat match goal with 
    | [ H : value (_ _) |- _ ] => inversion H; clear H; subst
    | [ H : listvalue (_ _) |- _ ] => inversion H; clear H; subst
  end.


Definition valid_Comp (C : P (Comp (list Value))) : Type :=
  (nonemptyT C * not (c_wrong ∈ C) * not (c_multi nil ∈ C))%type.


(* The denotation of syntactic values is valid. *)
(*
Lemma denot_value_valid {t}{ρ} : 
  fv_tm t [<=] dom ρ -> valid_env ρ 
  -> (value t -> valid_Comp (denot t ρ)) * 
      (listvalue t -> forall (x : Comp (list Value)), x ∈ (denot t ρ) -> { l & (c_multi (v_list l :: nil)) = x }) .
Proof. 
  intros FV NEρ.
  induction t.
  all: split.
  all: intros vv.
  all: autorewrite with denot.
  all: try solve [ assert False; invert_value; done].
  + unfold nonempty_env in NEρ.
    eapply (@ForallT_access _ ⌈ v_wrong ⌉ _ _) in NEρ.
    2: instantiate (1:= x); auto.
    destruct NEρ. split; auto.
    simpl in FV. fsetdec.
  + pick fresh x.
    erewrite denot_abs with (x:=x); eauto.
    eapply valid_Λ.
  + eapply valid_NAT; eauto. 
  + eapply valid_ADD; eauto.
  + assert False. inversion vv. done.
  + eapply valid_NIL; eauto.
  + (* exists nil. cbv. econstructor. *)
    intros x In. inversion In. exists nil. reflexivity.
  + simpl in FV. 
    move: (IHt1 ltac:(fsetdec)) => [ih11 _].
    move: (IHt2 ltac:(fsetdec)) => [ih21 ih22].
    have V2: value t2. invert_value. auto.
    have LV: listvalue t2. invert_value. auto.
    move: (ih21 V2) => [[v u] NW].
    move: (ih22 LV v u) => [ll ii].
    eapply valid_CONS; eauto. eapply ih11. invert_value. auto.
    subst. eauto.
  + simpl in FV. 
    move: (IHt1 ltac:(fsetdec)) => [ih11 _].
    move: (IHt2 ltac:(fsetdec)) => [ih21 ih22].
    have V2: value t2. invert_value. auto.
    have LV: listvalue t2. invert_value. auto.
    move: (ih21 V2) => [[v u] NW].
    move: (ih22 LV v u) => [ll ii].
    subst.
    intros x CC. 
    destruct x; try done.
    exists l. reflexivity.
Qed.     
*)
Lemma value_nonempty {t}{ρ} : 
  fv_tm t [<=] dom ρ -> valid_env ρ -> value t -> valid_Comp (denot t ρ).
Proof. 
  intros.
Admitted.
(*   eapply denot_value_valid; eauto.
Qed.  *)

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
    erewrite denot_abs with (x:=x).
    rewrite BIND_RET; auto.  admit. admit. eapply valid_Λ; auto.
    
    rewrite Λ_denot_APPLY_id; auto.
    eapply value_nonempty; auto.
    fsetdec.
    rewrite (subst_tm_intro x t v); auto.
    replace ρ with (nil ++ ρ) at 3.
    rewrite <- subst_denot with (ρ1 := nil). reflexivity.
    simpl_env.
    econstructor; eauto. 
    rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
    inversion H; eauto.
    econstructor; eauto. 
    fsetdec.
    reflexivity.
    fsetdec.
  - (* abs-cong *)
    pick fresh x.
    repeat erewrite denot_abs with (x:=x); try fsetdec.
    specialize (H0 x ltac:(auto)).
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
    eapply APPLY_cong; eauto.
    reflexivity.
  - (* app2 *)
    have SC1: scoped t ρ.  eapply scoped_app_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_app_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_app_inv2; eauto.
    eapply APPLY_cong; eauto.
    reflexivity.
  - (* cons1 *)
    eapply CONS_cong; eauto.
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped t' ρ.  eapply scoped_tcons_inv1; eauto.
    eapply IHRED; eauto.
    reflexivity.
  - (* cons2 *)
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_tcons_inv2; eauto.
    rewrite IHRED; eauto.
    reflexivity.
  - (* prj_zero *)
    destruct SCt. simpl in s.
    move: (@denot_value_valid w ρ ltac:(fsetdec) NE) => [w1 w2].
    move: (w1 (sv_list _ H0)) => [[uu ss] NW].
    move: (w2 H0 uu ss) => [ll tt]. subst.
    split. eapply CONS_APPLY_ZERO1.
    eapply CONS_APPLY_ZERO2; eauto.
  - (* prj_suc *)
    split.
    + eapply CONS_APPLY_SUCC1.
    + intros x In.
      destruct SCt. simpl in s.
      move: (@denot_value_valid v ρ ltac:(fsetdec) NE) => [h1 h2].
      move: (@denot_value_valid w ρ ltac:(fsetdec) NE) => [w1 w2].
      move: (h1 H) => [[vv rr] NW]. clear h1 h2.
      move: (w1 (sv_list _ H0)) => [[uu ss] NW2].
      move: (w2 H0) => mm.  
      inversion In; try done; subst.
      ++ move: (mm _ H1) => [o OO]. done.
      ++ move: (mm _ H1) => [o OO]. done.
      ++ move: (mm _ H1) => [o OO]. 
      inversion H2. subst.
      eapply PROJ. instantiate (1 := (vv :: VS)).
      econstructor; eauto.
      instantiate (1:= (1 + k0)). econstructor.
      simpl.
      auto.
      ++ move: (mm _ H1) => [o OO].  subst. simpl in H3; done.
      ++ destruct x0; try done. exfalso.  eapply H4; eauto. 
  - (* add *) 
    eapply ADD_APPLY_CONS; eauto.
Qed.


(* --------------------------------------------------------------- *)

(* Example semantics *)

(* Prove that 3 + 4 *)
Definition tm_Add : tm := 
  app add (tcons (lit 3) (tcons (lit 4) tnil)).

Lemma denot_tm : denot tm_Add nil ≃ NAT 7.
Proof.
  unfold tm_Add.
  autorewrite with denot.
Admitted.

Definition tm_Id : tm := abs (var_b 0).

Lemma denot_Id {v} : success v  -> (v :: nil ↦ v) ∈ denot tm_Id nil.
Proof.
  intro NE.
  pick fresh x.
  rewrite (denot_abs x); simpl; auto.
  cbn.
  destruct (x == x); try done.
  cbn. split. left. auto. 
  econstructor; eauto. done.
Qed. 


Lemma denot_Id_inv : forall x ρ, x ∈ denot tm_Id ρ ->
                          forall w,  Consistent x (w :: nil ↦ w).
Proof.
  intros x ρ.
  unfold tm_Id. 
  pick fresh y.
  rewrite (denot_abs y); auto.
  intro h. 
  destruct x; try done.
  move: h => [h0 [h1 h2]].
  cbn in h0. rewrite eq_dec_refl in h0.
  intros w.
  destruct (dec_con x w). eauto.
  eapply c_map1.
  exists x. exists w.
  
  repeat split; eauto. 
  unfold In. eauto.
Qed.

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).


#[global] Hint Rewrite access_eq_var : lngen.

Lemma wrong_not_successful {l}: 
  Forall success l -> v_wrong ∈ mem l -> False.
Proof. 
  induction l; intros h1 h2. done.
  inversion h1. subst. 
  inversion h2. subst. done.
  eauto.
Qed.

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

(* A term with an unbound variable has no value. *)
Definition tm_Wrong : tm := app (var_b 1) (var_b 0).

Lemma denot_Wrong : v_wrong ∈ denot tm_Wrong nil.
Proof.
  unfold tm_Wrong.
  rewrite denot_app.
  repeat rewrite denot_var_b.
  eapply FUNWRONG.
  auto.
Qed.  




(* Λ  \Lambda
   ▩  \squarecrossfill 
   ↦  \mapsto  
   ⤇ \Mapsto  
   ●  \CIRCLE 
   ⊆  \subseteq   (Included)
*)



Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Export lc.scoped.
Require Import structures.Structures.
Require Export structures.consistency.

Require Export denot.properties.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

(* This is an  example of the graph model for the pure 
   untyped lambda calculus. 

   In this model, everything is a function.
   
*)


(* ----------------------------------------------------------- *)


(* The denotation of a lambda calculus function is as its "graph" or set of
   input / output pairs.
   
   Each pair in the set (i.e. v_map VS W) declares that if this value is
   applied to any value in VS, the result is W.
   
   

 *)

(* begin Value *)
Inductive Value : Type :=
  | v_map : fset Value -> Value -> Value
  | v_fun : Value.
(* end Value *)

#[export] Hint Constructors Value : core.


(* semantic operators *)

Definition LAMBDA : (P Value -> P Value) -> P Value :=
  fun f => fun v => match v with 
          | v_map V w => (w ∈ (f (mem V))) /\ valid_mem V  (* CBV *)
          | v_fun => True
          end.


(* begin APPLY *)
Inductive APPLY : P Value -> P Value -> (Value -> Prop) :=
  | BETA : forall D1 D2 w V,
     (v_map V w) ∈ D1 ->
     (mem V ⊆ D2) -> valid_mem V ->
     APPLY D1 D2 w.
(* end APPLY *)

(* Denotation function *)

Import EnvNotations.
Import LCNotations.

Open Scope tm.

Definition Rho := Env (P Value).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Env (P Value) => dom x) in
  constr:(A \u B \u C \u D \u E).

(* Denotation function *)
(* `n` is is a termination metric. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Rho) : P Value :=
  match n with
  | O => Bottom
  | S m => 
     match a with 
     | var_b _ => Bottom

     | var_f x => ρ ⋅ x 

     | abs t => 
        let x := fresh_for (dom ρ \u fv_tm t) in 
        (LAMBDA (fun D => (denot_n m (t ^ x) (x ~ D ++ ρ))))

     | app t u   => 
          APPLY (denot_n m t ρ) (denot_n m u ρ)

     | _ => Bottom
     end
end.

Definition denot a := denot_n (size_tm a) a.


Lemma denot_var_b : forall x ρ, denot (var_b x) ρ = Bottom.
Admitted.

Lemma denot_var : forall x ρ, denot (var_f x) ρ = (ρ ⋅ x).
Admitted.

Lemma denot_app : forall t u ρ, 
    denot (app t u) ρ = APPLY (denot t ρ) (denot u ρ).
Admitted.


Lemma denot_abs : forall x t ρ,
    x `notin` dom ρ \u fv_tm t ->
    denot (abs t) ρ = LAMBDA (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Admitted.

Create HintDb denot.
#[export] Hint Opaque denot : denot.
#[export] Hint Rewrite denot_var_b denot_var denot_app : denot.


(* --------------- monotonicity ------------------------------ *)

(* Λ-ext-⊆  *)

(* NOTE: By restricting the hypothesis to only valid sets, we strengthen 
   the result. But this depends on the definition of Λ which quantifies
   over valid sets (i.e. CBV) *)
Lemma LAMBDA_ext_sub {F1 F2} :
  (forall {X : P Value}, valid X -> F1 X ⊆ F2 X) -> LAMBDA F1 ⊆ LAMBDA F2.
Proof.
  intros F1F2 v Iv. destruct v eqn:E; inversion Iv; auto.
  - split; auto. 
    eapply F1F2; eauto. 
Qed.

Lemma LAMBDA_ext {F1 F2} :
  (forall {X}, valid X -> F1 X ≃ F2 X) -> LAMBDA F1 ≃ LAMBDA F2.
Proof. 
  intros g. split;
  eapply LAMBDA_ext_sub; intros X NEX; destruct (g X); eauto.
Qed.

Lemma APPLY_mono_sub { D1 D2 D3 D4 } :
    D1 ⊆ D3 -> D2 ⊆ D4 -> ((APPLY D1 D2) ⊆ (APPLY D3 D4)).
Proof.  
  intros D13 D24 w APP. 
  inversion APP; subst; unfold Included in *.
  apply BETA with (V:=V); eauto.
    intros d z. eauto.
Qed.

Lemma APPLY_cong { D1 D2 D3 D4 } :
    D1 ≃ D3 -> D2 ≃ D4 -> ((APPLY D1 D2) ≃ (APPLY D3 D4)).
Proof.
  intros [ d13 d31 ] [ d24 d42 ].
  split; eapply APPLY_mono_sub; eauto.
Qed.

#[export] Instance Proper_Included_APPLY : Proper (Included ==> Included ==> Included) APPLY. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply APPLY_mono_sub; eauto. Qed.

#[export] Instance Proper_Same_APPLY : Proper (Same_set ==> Same_set ==> Same_set) APPLY. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply APPLY_cong; eauto. Qed.

(* denot *)

#[export] Instance Proper_sub_denot : Proper (eq ==> Env.Forall2 Included ==> Included) denot.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t).
  1: move=>i.
  2: move=>x.
  3: move=>t1 t2 IH1 IH2.
  4: move=> t' IH.
  all: intros.
  all: try move=> ρ1 ρ2 SUB.
  all: autorewrite with denot.
  all: try reflexivity.
  - eapply access_mono_sub; eauto.
  - eapply APPLY_mono_sub; eauto.
  - pick fresh x.
    repeat rewrite(denot_abs x); try fsetdec.
    eapply LAMBDA_ext_sub; eauto.
    move=> X neX.
    eapply IH; eauto.
Qed.

(* The denotation respects ≃ *)
#[export] Instance Proper_denot : Proper (eq ==> same_env ==> Same_set) denot.
Proof.
  intros t1 t -> x y E.
  unfold same_env in E.
  rewrite same_env_sub_env in E. destruct E. 
  split; eapply Proper_sub_denot; auto. 
Qed. 

(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: forall (scope : atoms), 
  monotone_env scope (denot t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot; auto.
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
  eapply denot_monotone with (scope := {{x}} \u dom ρ); simpl; auto.
  fsetdec.
  econstructor; eauto.
Qed.


(* ------------------ valid ---------------------- *)

Lemma valid_LAMBDA : forall F, valid (LAMBDA F).
Proof. 
  intros F. 
  cbv.
  exists v_fun. auto. 
Qed.

(* ------------------ continuity ---------------------- *)


Lemma APPLY_continuous_env {D E : Rho -> P Value}{ρ} :
  (nonempty_env ρ)
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env (dom ρ) D 
  -> monotone_env (dom ρ) E
  -> continuous_env (fun ρ => APPLY (D ρ)(E ρ)) ρ.
Proof.  
  intros NE IHD IHE mD mE.
  intros w APP.
  inversion APP; subst.
  destruct (IHD (v_map V  w ) ltac:(auto)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
  repeat split.
    -- eapply join_finite_env; eauto.
    -- eapply join_lub; eauto.
    -- have VwDp3 : ⌈ v_map V w ⌉ ⊆ D (ρ1 ⊔e ρ2).
    { transitivity (D ρ1); auto. eapply mD. 
      erewrite -> Env.Forall2_dom with (r2 := ρ); eauto. reflexivity.
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { transitivity (E ρ2); auto. eapply mE.
      erewrite -> Env.Forall2_dom with (r2 := ρ); eauto. reflexivity.
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
Qed.

(* Algebraicity.  
   Only need finite information from the environment.
*)

Lemma LAMBDA_continuous_env {E ρ x} {NE : nonempty_env ρ} :
    x `notin` dom ρ
  -> (forall V, valid_mem V -> continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env ({{x}} \u (dom ρ)) E
  -> continuous_env (fun ρ => LAMBDA (fun D => E (x ~ D ++ ρ))) ρ.
Proof.
  intros Fr IH mE.
  intros v vIn.
  destruct v; try done.
  - (* v is l ↦ c *)
    move: vIn => [ wEVρ NW ]. 
    have VV: valid_mem f. unfold valid_mem. eauto.
    have NEx: nonempty_env (x ~ mem f ++ ρ). econstructor; eauto.
    specialize (IH f ltac:(eauto) v wEVρ).
    destruct IH as [ρ' [F' [S' h']]].
    inversion S'. subst. inversion F'. subst.
    exists E1. eexists. eauto.
    repeat split; auto.
    eapply mE with (ρ := x ~ a1 ++ E1); simpl_env; eauto. 
    move: (Env.Forall2_dom _ H3) => EQ. rewrite EQ. reflexivity.
    econstructor; eauto. eapply Reflexive_sub_env. eapply Forall2_uniq1; eauto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.


(* ⟦⟧-continuous *)
Lemma denot_continuous_env {t} : forall ρ,
    nonempty_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  eapply tm_induction with (t := t).
  1: move=>i ρ NE.
  2: move=>x ρ NE.
  3: move=>t1 t2 IH1 IH2 ρ NE.
  4: move=> t' IH ρ NE.
  all: intros.
  all: intros c cIn.
  all: autorewrite with denot in cIn.
  all: try solve [destruct c; try done].  
  - (* var case *)
    eapply access_continuous_env; eauto.
  - (* app *)
    specialize (IH1 _ NE).
    specialize (IH2 _ NE).
    move: (APPLY_continuous_env NE IH1 IH2 (denot_monotone (dom ρ)) (denot_monotone (dom ρ)) c cIn) => [r1 [f1 h]].
    exists r1. exists f1. autorewrite with denot.
    eauto.
  - (* abs *)
    pick fresh x.
    rewrite (denot_abs x) in cIn; auto. 
    specialize (IH x ltac:(auto)).
    destruct (@LAMBDA_continuous_env (denot (t' ^ x)) ρ x NE ltac:(auto) ltac:(eauto)
          ltac:(eauto using denot_monotone) _ cIn) as [ρ' [F' [S' I']]].
    exists ρ'. exists F'. 
    rewrite (denot_abs x). 
    erewrite -> Forall2_dom with (r2 := ρ). fsetdec. eauto.
    eauto.    
Qed.

(* --------------------------------------------------- *)



(* ⟦⟧-continuous-⊆ *) 
Lemma denot_continuous_sub {ρ t} : 
  nonempty_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros NE_ρ V VinEρ.
  eapply generic_continuous_sub;
    eauto using denot_continuous_env, denot_monotone.
Qed.


(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ x } :
  nonempty_env ρ 
  -> x `notin` dom ρ 
  -> continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros NE_ρ Fr.
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (x ~ X ++ ρ)) as 
    [ρ' [pf [h1 h2]]]. 3: eauto.
  + eapply extend_nonempty_env; eauto.
  + eauto.
  + inversion h1. subst. inversion pf. subst.
    match goal with [H6 : finite a1 |- _ ] => move: H6 => [D [S NN]] end.
    exists D. split.
    rewrite <- S. auto.
    split. 
    have SUB: Env.Forall2 Included 
                (x ~ a1 ++ E1) (x ~ mem D ++ ρ).
    econstructor; eauto. 
    rewrite <- S. reflexivity.
    rewrite <- SUB. eapply h2. 
    eapply valid_sub_valid_mem; eauto. rewrite <- S. auto. 
Qed.

(*  ----- Abstraction followed by Application is the identity -------- *)

(* Λ-▪-id *)
Lemma LAMBDA_APPLY_id { F X } :
  continuous F -> monotone F -> valid X
  -> APPLY (LAMBDA F) X ≃ F X.
Proof. 
  intros Fcont Fmono NEX.
  split.
  + intros w APP. inversion APP; subst.
    - cbn in H. destruct H as [h1 h2].
      specialize (Fmono (mem V) X ltac:(auto)).
      eauto.
  + intros w wInFX.
    have M: mem (singleton_fset w) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (singleton_fset w) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    eapply BETA with (V:=D); eauto.
    repeat split; eauto.
Qed.


(* Λ⟦⟧-▪-id *)
Lemma LAMBDA_denot_APPLY_id :
  forall t ρ x X,
    valid X
    -> nonempty_env ρ
    -> x `notin` dom ρ 
    -> (APPLY (LAMBDA (fun D => denot (t ^ x) (x ~ D ++ ρ))) X) ≃
      denot (t ^ x) (x ~ X ++ ρ).
Proof.
  intros.
  move: (@LAMBDA_APPLY_id (fun D => denot (t ^ x) (x ~ D ++ ρ)) X) => h.
  eapply h; auto.
  +  (* continuity *)
    eapply denot_continuous_one; auto.
  + eapply denot_monotone_one; auto.
    eapply ForallT_uniq; eauto.
Qed.

(* ------------------- beta reduction is sound ----------------- *)


Lemma subst_denot1 :
  forall (t : tm) (x : atom) (u : tm) (ρ : Env (P Value)),
    scoped t (x ~ denot u ρ ++ ρ) 
    -> scoped u ρ 
    -> valid (denot u ρ)
    -> nonempty_env ρ
    -> denot t (x ~ denot u ρ ++ ρ) ≃ denot (t [x ~> u]) ρ.
Proof.
Admitted.


Lemma beta_soundness : forall t u ρ, 
  scoped (abs t) ρ ->
  scoped u ρ -> 
  nonempty_env ρ ->
  valid (denot u ρ) -> 
  denot (app (abs t) u) ρ ≃ denot (open_tm_wrt_tm t u) ρ.
Proof.
  intros t u ρ St Su NE V.
  pick fresh x.
  rewrite denot_app.
  rewrite (denot_abs x); auto.
  rewrite (LAMBDA_denot_APPLY_id); auto.
  rewrite subst_denot1; eauto.
  eapply scoped_abs_inv; eauto.
  rewrite (subst_tm_intro x t u); auto.
  reflexivity.
Qed.

(* ------------------------ examples --------------------------- *)


(* Identity function *)

Definition tm_Id : tm := abs (var_b 0).
 
(* begin idset *)
Definition idset : P Value := 
  fun t => match t with 
          | v_fun => True 
          | v_map INPUT OUT => OUT ∈ mem INPUT 
        end.
(* end idset *)

Definition id0 := v_fun.
Example example0 : id0 ∈ idset. done. Qed.
Definition id1 := v_map (FSet (id0 :: nil) ) id0.
Example example1 : id1 ∈ idset. cbn. left. done. Qed.
Definition id2 := v_map (FSet (id0 :: id1 :: nil) ) id1.
Example example2 : id2 ∈ idset. cbn. right. left. done. Qed.
Definition id3 := v_map (FSet (id0 :: id1 :: id2 :: nil) ) id2.
Example example3 : id2 ∈ idset. cbn. right. left. done. Qed.


Lemma denot_Id1 : denot tm_Id nil ⊆ idset.
Proof.
  pick fresh x.
  rewrite (denot_abs x); simpl; auto.
  cbn. rewrite eq_dec_refl. clear x Fr.
  + intros x xIn.
    destruct x; try done.
    destruct xIn as [h1 h2].
    cbn. auto.
Qed.

Lemma denot_Id2 : idset  ⊆  denot tm_Id nil.
Proof. 
  pick fresh x.
  rewrite (denot_abs x); simpl; auto.
  cbn. rewrite eq_dec_refl. clear x Fr.
  move=> x xIn.
  destruct x; try done.
  + cbn in xIn.
    repeat split; auto. 
    destruct f. cbn in xIn.
    intro h. subst.
    done.
Qed.

(* Example: constant function K -- \x. \y. x n *)

Definition tm_K : tm := abs (abs (var_b 1)).  

Definition K_set : P Value := 
  fun t => match t with 
          | v_map V1 w => valid_mem V1 /\
              match w with 
                | v_map V2 v => (valid_mem V2) /\ (v ∈ mem V1)
                | v_fun => True
              end
          | v_fun => True
        end.

Lemma denot_K2 : K_set ⊆ denot tm_K nil.
Proof.
  intros v vIn.
  unfold tm_K.
  pick fresh x. 
  rewrite (denot_abs x); auto.
  destruct v; try done.
  destruct v; cbn in vIn; try done.
  2: { cbn. intuition. }
  cbn.
  rewrite eq_dec_refl.
  remember (fresh_for (union (Metatheory.add x empty) (singleton x))) as y.
  destruct (x == y). subst. admit. (* variable fussiness. *)
  intuition.
Admitted.

Lemma denot_K1 : denot tm_K nil ⊆ K_set.
Proof.
  unfold tm_K.
  pick fresh x. 
  rewrite (denot_abs x); auto.
  replace ((abs (var_b 1)) ^ x) with (abs (var_f x)). 2: { reflexivity. }
    
  intros v vIn.
  destruct v; try done.
  destruct v; try done. 2: { cbn in *. intuition. }
  cbn in *.
  rewrite eq_dec_refl in vIn.
  remember (fresh_for (union (Metatheory.add x empty) (singleton x))) as z.
  destruct (x == z). subst. admit.
  intuition.
Admitted.

(* Delta := \x. x x *)

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).

Definition Delta_set : P Value :=
  fun t => match t with 
          | v_fun => True
          | v_map f y => 
              valid_mem f /\ 
                exists V, (v_map V y ∈ mem f) /\ 
                       (valid_mem V) /\ (mem V ⊆ mem f)
        end.


Lemma denot_Delta2 : Delta_set ⊆ denot tm_Delta nil.
Proof.
  unfold tm_Delta.
  pick fresh x.
  rewrite (denot_abs x). eauto.
  intros y yIn.
  cbn. rewrite eq_dec_refl.
  destruct y; try done.
  cbn in yIn. 
  move: yIn => [VF [V [SF [VV SV]]]]. 
  cbn.
  split; eauto.
  eapply BETA;  eauto.
Qed.

Lemma denot_Delta1 : denot tm_Delta nil ⊆ Delta_set.
Proof.
  unfold tm_Delta.
  pick fresh x.
  rewrite (denot_abs x). eauto.
  intros y yIn.
  cbn in yIn. rewrite eq_dec_refl in yIn.
  destruct y; try done.
  cbn in yIn. destruct yIn as [AP VM].
  inversion AP. subst.
  cbn.
  repeat split. auto.
  exists V. repeat split; auto.
Qed.

Lemma denot_Delta : denot tm_Delta nil ≃ Delta_set.
Proof. split. eapply denot_Delta1. eapply denot_Delta2. Qed.

(* Omega := (\x. x x)(\x. x x) *)

(* For this part, we show that the denotation of an infinite looping 
   term is the empty set. 
   We do this through a proof of contradiction. An inhabitant of 
   this denotation would mean that the Delta_set contains an 
   infinite descending chain of values, each smaller than the 
   previous. However, values are inductively defined, so that 
   is impossible.
*)

Definition tm_Omega : tm := app tm_Delta tm_Delta.

(* the "size" of a value that gets smaller --- the maximum depth
   of the tree. This calculation is stable under fsets... no 
   matter what list represents an fset, the maximum depth 
   of any value in the fset will remain the same. *)

Fixpoint max_list (xs : list nat) : nat := List.fold_right max 0 xs.

Fixpoint depth (v : Value) : nat :=
  match v with 
  | v_fun => 0
  | v_map (FSet VS) W => 1 + max (max_list (List.map depth VS)) (depth W)
  end.

Definition depth_fset (VS : fset Value) := 
  match VS with 
  | FSet l => max_list (List.map depth l)
  end.

Lemma depth_v_map VS w : depth (v_map VS w) =
       1 + max (depth_fset VS) (depth w).
Proof. cbn. destruct VS. done. Qed.

Lemma mem_In {A} {x:A}{XS : fset A}: x ∈ mem XS -> In_fset x XS.
Proof.
  destruct XS.
  induction l; cbn.
  - auto.
  - auto.
Qed.

Lemma In_smaller {x:Value}{XS} :
  In_fset x XS -> depth x <= depth_fset XS.
Proof.
  destruct XS.
  induction l.
  intros h. done.
  intros h. cbn.
  destruct h.
  subst. lia. 
  cbn in IHl.
  specialize (IHl H).
  lia. 
Qed.

Lemma depth_mem V1 V2 : 
  mem V1 ⊆ mem V2 -> 
  depth_fset V1 <= depth_fset V2.
Proof.
  intros.
  unfold depth_fset.
  destruct V1. destruct V2.
  induction l.
  - cbn. lia.
  - cbn.
    have n: mem (FSet l) ⊆ mem (FSet l0).
    { intros x xIn. eapply H; eauto. right. auto. }
    specialize (IHl n).
    specialize (H a ltac:(left; auto)).
    move: ( In_smaller (mem_In H)) => h.
    cbn in h.
    lia.
Qed.

(* description of an infinite descending chain, indexed by 
   the first number in the chain. *)
CoInductive descending_chain : nat -> Prop := 
  | dcons : 
      forall n m, m < n -> descending_chain m -> descending_chain n.

(* we can't have such a thing. *)
Lemma impossible : forall n, descending_chain n -> False.
Proof.
  induction n.
  intros h. inversion h. lia.
  intros h. inversion h. subst.
  apply IHn. destruct m. inversion H0. lia.
  inversion H0. subst.
  have LT : m0 < n. lia.
  eapply dcons with (m := m0); auto.
Qed.

CoFixpoint Delta_chain { V1 w V } : 
  v_map V1 w ∈ mem V -> 
  mem V1 ⊆ mem V ->
  mem V ⊆ Delta_set -> 
  descending_chain (depth_fset V).
Proof.  
  intros h1 h2 h3.
  move: (h3 (v_map V1 w) h1) => [_ [V2 [I2 [K2 M2]]]]. 
  apply dcons with (m := (depth_fset V1)).
  move: (In_smaller (mem_In h1)) => h4.
  rewrite depth_v_map in h4. lia.
  eapply (Delta_chain V2 w V1 I2 M2).
  transitivity (mem V); auto.
Qed.

Lemma denot_Omega : denot tm_Omega nil ⊆ (fun x => False).
Proof. intros x xIn.
       unfold tm_Omega in xIn.
       rewrite denot_app in xIn.
       rewrite denot_Delta in xIn.
       inversion xIn. subst. clear xIn.
       cbv.
       destruct H as [_ [V1 [H [h1 M1]]]].       
       move: (Delta_chain H M1 H0) => chain.
       eapply impossible; eauto.
Qed.

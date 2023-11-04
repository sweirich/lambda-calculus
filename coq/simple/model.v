

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Export lc.scoped.
Require Import structures.Structures.
Require Export structures.consistency.

Require Export denot.list_properties.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

Import EnvNotations.

(* This is an  example of the graph model for the pure 
   untyped lambda calculus plus natural numbers. 
   
*)

Lemma In_mem_fset {A}{v : A} : v ∈ mem (singleton_fset v).
Proof. cbn. left. auto. Qed.
#[export] Hint Resolve In_mem_fset : core.
Lemma  valid_mem_singleton_fset {A}{v:A} :
  valid_mem (singleton_fset v).
Proof. cbn. done. Qed.
#[export] Hint Resolve valid_mem_singleton_fset : core.
(* ----------------------------------------------------------- *)


(* The denotation of a lambda calculus function is as its "graph" or set of
   input / output pairs.
   
   Each pair in the set (i.e. v_map VS W) declares that if this value is
   applied to any value in VS, the result is W.
   
 *)

(* begin Value *)
Inductive Value : Type :=
  | v_nat : nat -> Value
  | v_map : fset Value -> Value -> Value
  | v_fun : Value.
(* end Value *)

#[export] Hint Constructors Value : core.


(* --- semantic operators -------  *)

Inductive LAMBDA (f : P Value -> P Value) : P Value :=
  | s_map : forall V w, 
      w ∈ f (mem V) ->
      valid_mem V ->
      LAMBDA f (v_map V w)
  | s_fun : LAMBDA f v_fun. 

(* begin APPLY *)
Inductive APPLY : P Value -> P Value -> (Value -> Prop) :=
  | BETA : forall D1 D2 w V,
     (v_map V w) ∈ D1 ->
     (mem V ⊆ D2) -> valid_mem V ->
     APPLY D1 D2 w.
(* end APPLY *)

Inductive NAT (k : nat) : P Value :=
  | s_Nat : NAT k (v_nat k).

Inductive ADD : P Value :=
  | s_ADD : forall i j k V1 V2,
      v_nat i ∈ mem V1 ->
      v_nat j ∈ mem V2 -> 
      k = i + j ->
      ADD (v_map V1 (v_map V2 (v_nat k))).

#[export] Hint Constructors Value LAMBDA APPLY NAT ADD : core.

Ltac invert_sem := 
  lazymatch goal with 
  | [ H : ?x ∈ LAMBDA ?f |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ APPLY ?v1 ?v2 |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ NAT ?k |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ ADD |- _ ] => inversion H; subst; clear H
  end.

(* Denotation function *)

Import LCNotations.

Open Scope tm.

Definition Rho := list (P Value).

(* Denotation function *)
Fixpoint denot (a : tm) (ρ : Rho) : P Value :=
     match a with 
     | var_b n => ρ ⋅ n 

     | abs t => LAMBDA (fun D => denot t (D :: ρ))

     | app t u   =>  APPLY (denot t ρ) (denot u ρ)

     | lit i => NAT i

     | add   => ADD

     | _ => Bottom
     end.

(* --------------- monotonicity ------------------------------ *)

(* Λ-ext-⊆  *)

(* NOTE: By restricting the hypothesis to only valid sets, we strengthen 
   the result. But this depends on the definition of Λ which quantifies
   over valid sets (i.e. CBV) *)
Lemma LAMBDA_ext_sub {F1 F2} :
  (forall {X : P Value}, valid X -> F1 X ⊆ F2 X) -> LAMBDA F1 ⊆ LAMBDA F2.
Proof.
  intros F1F2 v Iv.
  invert_sem; econstructor; try eapply F1F2; eauto.
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
  invert_sem.
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

#[export] Instance Proper_sub_denot : Proper (eq ==> List.Forall2 Included ==> Included) denot.
Proof.
  intros t1 t ->.
  induction t.
  1: move=>i.
  2: move=>y.
  3: move=>t1 t2 IH1 IH2.
  4: move=> t' IH.
  all: intros.
  all: try move=> ρ1 ρ2 SUB.
  all: try reflexivity.
  - eapply access_mono_sub; eauto.
  - eapply LAMBDA_ext_sub; eauto.
    move=> X neX.
    eapply IHt; eauto.
  - eapply APPLY_mono_sub; eauto.
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
Lemma denot_monotone {t}: forall (sc : atoms), 
  monotone_env sc (denot t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot; auto.
Qed.

(* -- monotonicity WRT argument -- *)

(* denot-monotone-one *)
Lemma denot_monotone_one : forall ρ t, 
    monotone (fun D => denot t (D :: ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  eapply denot_monotone with (sc := S (dom ρ)); simpl; auto.
Qed.


(* ------------------ valid ---------------------- *)

Lemma valid_LAMBDA : forall F, valid (LAMBDA F).
Proof. intros F. cbv. exists v_fun. auto. Qed.

Lemma valid_NAT : forall k, valid (NAT k).
Proof. intros k. cbv. exists (v_nat k). econstructor; eauto. Qed.

Lemma valid_ADD : valid ADD.
Proof. cbv. exists (v_map (singleton_fset (v_nat 0)) (v_map (singleton_fset (v_nat 0)) (v_nat 0))).
       econstructor; cbv; eauto. 
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
  invert_sem.
  destruct (IHD (v_map V  w ) ltac:(auto)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
  have S1: same_scope ρ1 ρ2.
  { unfold same_scope. rewrite -> ρ1ρ. rewrite -> ρ2ρ. done. }
  have S2: same_scope ρ1 ρ.
  { unfold same_scope. rewrite -> ρ1ρ. done. }
  have S3: same_scope ρ2 ρ.
  { unfold same_scope. rewrite -> ρ2ρ. done. }
  exists (ρ1 ⊔e ρ2).
  repeat split.
    -- eapply join_finite_env; eauto.     
    -- eapply join_lub; eauto.
    -- have VwDp3 : ⌈ v_map V w ⌉ ⊆ D (ρ1 ⊔e ρ2).
    { transitivity (D ρ1); auto. eapply mD; auto.
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { transitivity (E ρ2); auto. eapply mE; auto.
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
Qed.

(* Algebraicity.  
   Only need finite information from the environment.
*)

Lemma LAMBDA_continuous_env {E ρ} {NE : nonempty_env ρ} :
    (forall V, valid_mem V -> continuous_env E (mem V :: ρ))
  -> monotone_env (S (dom ρ)) E
  -> continuous_env (fun ρ => LAMBDA (fun D => E (D :: ρ))) ρ.
Proof.
  intros IH mE.
  intros v vIn.
  inversion vIn as [ f w wEVρ VV EQ | ]. subst; clear vIn.
  - (* v is V ↦ w *)
    have NEx: nonempty_env (mem f :: ρ). econstructor; eauto.
    specialize (IH f ltac:(eauto) w wEVρ).
    destruct IH as [ρ' [F' [S' h']]].
    inversion S'. subst. inversion F'. subst.
    exists l. eexists. eauto.
    repeat split; auto.
    eapply s_map; eauto.
    eapply mE with (ρ := x :: l); simpl_env; eauto. 
    simpl. f_equal. rewrite -> H3. auto.
    econstructor; eauto. 
  - exists (initial_finite_env ρ NE).
    repeat split; eauto. 
    econstructor.
Qed.

(*
Lemma access_continuous_env {A} : 
forall (ρ : list (P A)) (x : nat),
       nonempty_env ρ ->
       continuous_env (fun ρ0  => access (fun _ : A => False) ρ0 x) ρ.
Admitted.



Lemma extend_valid_env {A} {ρ : list (P A)}{X} : 
  valid X -> 
  nonempty_env ρ -> nonempty_env (X :: ρ).
Proof. intros NEP NEX.  eapply List.ForallT_cons; eauto. Qed.
#[export] Hint Resolve extend_valid_env : core.
*)

(* ⟦⟧-continuous *)
Lemma denot_continuous_env {t} : forall ρ,
    nonempty_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  induction t.
  all: intros ρ NE.
  all: intros c cIn.
  all: try solve [destruct c; try done].  
  all: simpl in cIn.
  all: simpl.
  - (* var case *)
    eapply access_continuous_env; eauto.
  - (* abs *)
    eapply LAMBDA_continuous_env; eauto using denot_monotone.
    Unshelve. eauto.
  - (* app *)
    eapply APPLY_continuous_env; eauto using denot_monotone.
  - (* lit *)
    inversion cIn; subst;
    exists (initial_finite_env ρ NE); repeat split; eauto. 
  - (* add *)
    inversion cIn; subst;
    exists (initial_finite_env ρ NE); repeat split; eauto. 
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
Lemma denot_continuous_one { t ρ } :
  nonempty_env ρ 
  -> continuous (fun D => denot t (D :: ρ)).
Proof.
  intros NE_ρ .
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (X :: ρ)) as 
    [ρ' [pf [h1 h2]]].
  + eapply extend_nonempty_env; eauto.
  + eauto.
  + inversion h1. subst. inversion pf. subst.
    match goal with [H6 : finite x |- _ ] => move: H6 => [D [S NN]] end.
    exists D. split.
    rewrite <- S. auto.
    split. 
    have SUB: List.Forall2 Included 
                (x :: l) (mem D :: ρ).
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
    - invert_sem. 
      specialize (Fmono (mem V) X ltac:(auto)).
      eauto.
  + intros w wInFX.
    have M: mem (singleton_fset w) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (singleton_fset w) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    eapply BETA with (V:=D); eauto.
    eapply s_map; eauto.
Qed.


(* Λ⟦⟧-▪-id *)
Lemma LAMBDA_denot_APPLY_id :
  forall t ρ X,
    valid X
    -> nonempty_env ρ
    -> (APPLY (LAMBDA (fun D => denot t  (D :: ρ))) X) ≃
      denot t (X  ::  ρ).
Proof.
  intros.
  eapply @LAMBDA_APPLY_id with (F := (fun D => denot t (D :: ρ))); eauto.
  eapply denot_continuous_one; auto.
  eapply denot_monotone_one; auto.
Qed.

(* ------------------- addition works -------------------------- *)

Ltac invert_sub := 
  let h := fresh in
  match goal with 
  | [ H : mem ?V ⊆ ?X , I : ?v ∈ mem ?V |- _ ] => 
      move: (H _ I) => h ; invert_sem ; clear I
  end.
  

Lemma APPLY_ADD i j : APPLY (APPLY ADD (NAT i)) (NAT j) ≃ (NAT (i+j)).
Proof.
split.
- intros x xIn.
  repeat invert_sem.
  repeat invert_sub.
  econstructor; eauto.
- intros x xIn.
  inversion xIn; subst; clear xIn.
  eapply BETA with (V := singleton_fset (v_nat j)); eauto.
  eapply BETA with (V := singleton_fset (v_nat i)); eauto.
  eapply s_ADD; eauto.
  eapply In_mem_Included. cbv; eauto.
  eapply In_mem_Included. cbv; eauto.
Qed.


(* ------------------- beta reduction is sound ----------------- *)

(*
Lemma subst_denot1 :
  forall (t : tm) (u : tm) (ρ : list (P Value)),
    scoped t (denot u ρ :: ρ) 
    -> scoped u ρ 
    -> valid (denot u ρ)
    -> nonempty_env ρ
    -> denot t (denot u ρ :: ρ) ≃ denot (t [x ~> u]) ρ.
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
*)

(* ------------------------ examples --------------------------- *)

Lemma In_valid_mem {A} {x : A}{f}: x ∈ mem f -> valid_mem f.
Proof. intro xIn.  destruct f.
       intro h. subst. done.
Qed.

#[export] Hint Resolve In_valid_mem : core.

(* 3 + 4 is 7 *)

Definition tm_add_example := app (app add (lit 3)) (lit 4).

Lemma denot_add_example : denot tm_add_example nil ≃ (NAT 7).
Proof.
  unfold tm_add_example. simpl.
  rewrite APPLY_ADD.
  reflexivity.
Qed.

(* Identity function *)

Definition tm_Id : tm := abs (var_b 0).
 
(* begin idset *)
Definition idset : P Value := 
  fun t => match t with 
          | v_fun => True 
          | v_map INPUT OUT => OUT ∈ mem INPUT 
          | _ => False
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
  simpl.
  intros x xIn.
  invert_sem; cbn; auto.
Qed.

Lemma denot_Id2 : idset  ⊆  denot tm_Id nil.
Proof. 
  simpl.
  move=> x xIn.
  destruct x; try done.
  + cbn in xIn.
    eapply s_map; eauto.
Qed.

(* Example: constant function K -- \x. \y. x n *)

Definition tm_K : tm := abs (abs (var_b 1)).  

Definition K_set : P Value := 
  fun t => match t with 
          | v_map V1 w => valid_mem V1 /\
              match w with 
                | v_map V2 v => (valid_mem V2) /\ (v ∈ mem V1)
                | v_fun => True
                | _ => False
              end
          | v_fun => True
          | _ => False
        end.

Lemma denot_K2 : K_set ⊆ denot tm_K nil.
Proof.
  intros v vIn.
  unfold tm_K.
  simpl.
  destruct v; try done.
  destruct v; cbn in vIn; try done.
  all: try solve [cbn; intuition].
Qed.

Lemma denot_K1 : denot tm_K nil ⊆ K_set.
Proof.
  unfold tm_K.
  simpl.
  intros v vIn.
  inversion vIn as [V w wIn h1 h2|]. subst. clear vIn.
  inversion wIn as [V2 w2 w2In h3 h4|]. subst.
  all: try solve [cbn in *; intuition].
Qed.


(* --------------- CBV Y-combinator: Z ---------------------- *)
(* \lambda f.(\lambda x.f(\lambda v.xxv))\ (\lambda x.f(\lambda v.xxv)) *)

Definition xxv : tm := (abs (app (app (var_b 1) (var_b 0)) (var_b 0))).

Definition tm_Z : tm := 
   abs (app (abs  (app (var_b 1) xxv))
            (abs  (app (var_b 1) xxv))).


(* --------------------------------------------------------- *)

(* Delta := \x. x x *)

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).

Definition Delta_set : P Value :=
  fun t => match t with 
          | v_fun => True
          | v_map f y => 
              valid_mem f /\ 
                exists V, (v_map V y ∈ mem f) /\ 
                       (valid_mem V) /\ (mem V ⊆ mem f)
          | _ => False
        end.


Lemma denot_Delta2 : Delta_set ⊆ denot tm_Delta nil.
Proof.
  unfold tm_Delta.
  simpl.
  intros y yIn.
  destruct y; try done.
  cbn in yIn. 
  move: yIn => [VF [V [SF [VV SV]]]]. 
  cbn.
  eapply s_map; eauto.
  eapply BETA;  eauto.
Qed.

Lemma denot_Delta1 : denot tm_Delta nil ⊆ Delta_set.
Proof.
  unfold tm_Delta.
  simpl.
  intros y yIn.
  inversion yIn as [V w wIn h1 h2|]; subst; clear yIn; cbn; eauto. 
  invert_sem; cbn; eauto.
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

Definition max_list := List.fold_right max 0.

Fixpoint depth (v : Value) : nat :=
  match v with 
  | v_fun => 0
  | v_map (FSet VS) W => 1 + max (max_list (List.map depth VS)) (depth W)
  | _ => 0
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
  intros h. cbn. fold max_list.
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
       replace (denot (app tm_Delta tm_Delta) nil) with 
         (APPLY (denot tm_Delta nil) (denot tm_Delta nil)) in xIn. 2: auto.
       rewrite denot_Delta in xIn.
       inversion xIn. subst. clear xIn.
       cbv.
       destruct H as [_ [V1 [H [h1 M1]]]].       
       move: (Delta_chain H M1 H0) => chain.
       eapply impossible; eauto.
Qed.

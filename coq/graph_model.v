Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.

Require Import lc.List.
Require Import lc.Env.

Require Import lc.Sets.
Import SetNotations.
Local Open Scope set_scope.

Require Import lc.Monad.
Import MonadNotation.
Open Scope monad_scope.

Require Import lc.Container.

Require Import lc.Scoped.

(* ------------------------------------------------------------ *)

(* This a "Graph Model" of the CBV lambda calculus based on Jeremy Siek's Agda
   development.

   https://github.com/jsiek/denotational_semantics/blob/master/agda/PValueCBV.agda

   Expressions are mapped to sets of values. The interpretation of a function
   is a set of its mappings. We need an infinite set to fully represent a
   function but any computation only requires a finite approximation of that 
   function.

   This development extends Jeremy's language with (untyped) lists, numbers
   (for accessing the lists by index) and 'wrong' for runtime type errors.

*)

(* The values of the model and when they are consistent with eachother. *)
Require Import lc.Value.

(* The denotation of a lambda-calculus value is `P Value`,
   a set of model values.
   The elements of this set approximate the actual values 
   (and are self consistent).
*)



(* Valid ---- -------------------------------------- *)

(* A `P Value` is the denotation of an actual lambda-calculus value if it is
   inhabited and does not contain wrong (or fail).

   We could also call this "succeeds".
*)

Definition valid (V : P Value) : Type :=
  nonemptyT V * not (v_wrong ∈ V).

(* A valid finite set *)
Definition valid_mem (V : list Value) : Prop :=
  V <> nil /\ not (List.In v_wrong V).

(* valid sets are inhabited *)
Definition valid_is_nonempty V : valid V -> nonemptyT V := fst.

(* And do not contain wrong *)
Lemma valid_not_wrong {X} : valid X -> not (v_wrong ∈ X).
Proof. intros [x h1]; done. Qed.

Lemma valid_mem_valid {V} : valid_mem V -> valid (mem V).
Proof.
  intros [V1 V2].
  destruct V; simpl in *. done.
  split. exists v. auto. eauto.
Qed.

Lemma valid_mem_nonnil {V} : valid_mem V -> V <> nil.
Proof. intros [h _]; auto. Qed.

Lemma valid_mem_not_wrong {V} : valid_mem V -> not (List.In v_wrong V).
Proof. intros [h j]; auto. Qed.

(* A finite, inhabited subset of a valid set is valid *)
Lemma valid_sub_valid_mem {D a} :
  D <> nil -> valid a -> mem D ⊆ a -> valid_mem D.
Proof.
  intros NE [V1 V2] S.
  inversion V1.
  split; auto.
Qed.

#[export] Hint Immediate valid_is_nonempty valid_not_wrong valid_mem_valid valid_mem_nonnil valid_mem_not_wrong valid_sub_valid_mem : core.

Lemma valid_join : forall v1 v2, 
    valid v1 -> 
    valid v2 ->
    valid (v1 ∪ v2).
Proof.
  intros v1 v2 [[x1 I1] h1] [[x2 I2] h2].
  split. 
  exists x1. eapply Union_introl; eauto.
  intro h. inversion h; subst; done.
Qed.

(* ------------ Lists ------------------ *)

Definition LIST : list (P Value) -> P Value  :=
  fun DS w => 
    match w with 
    | v_list WS => Forall2 Ensembles.In DS WS
    | _ => False
    end.

Definition NIL : P Value := ⌈ v_list nil ⌉.

Definition CONS : P Value -> P Value -> P Value := 
  fun V W x => 
    match x with 
    | v_list (v :: w) => (v ∈ V) /\ (v_list w ∈ W)
    | _ => False
    end.
        

Lemma CONS_mono_sub { D1 D2 D3 D4 } :
    D1 ⊆ D3 -> D2 ⊆ D4 -> ((CONS D1 D2) ⊆ (CONS D3 D4)).
Proof.  
  intros D13 D24 w C. 
  unfold CONS, In in C.
  destruct w; simpl in C; try done.
  destruct l; try done.
  move: C => [ d1 d2 ].
  unfold CONS, In. split.
  eapply D13; auto.
  eapply D24; auto.
Qed.

Lemma CONS_cong { D1 D2 D3 D4 } :
    D1 ≃ D3 -> D2 ≃ D4 -> ((CONS D1 D2) ≃ (CONS D3 D4)).
Proof.
  intros [ d13 d31 ] [ d24 d42 ].
  split; eapply CONS_mono_sub; eauto.
Qed.


Lemma valid_NIL : valid NIL.
Proof.
  unfold NIL, valid.
  split. econstructor; eauto. intro h; inversion h.
Qed.

Lemma valid_CONS {x y z} : valid x -> valid y -> v_list z ∈ y -> valid (CONS x y).
Proof.
  intros [[vx h1] nx] [[vl h2] nl] In. unfold CONS.
  split.
  - exists (v_list (vx :: z)). cbv. eauto.
  - intro h. inversion h.
Qed. 

(* ------------ Functions ------------------ *)

Infix "↦" := v_map (at level 85, right associativity).

(* Call by value means that we require the argumnet to 
   be valid. *)
Definition Λ : (P Value -> P Value) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈ f (mem V)) /\ valid_mem V
          | v_fun => True
          | _ => False
          end.

(* Application: 
   1. v_wrong e |-> v_wrong
   2. e v_wrong |-> v_wrong  
         -- should this ensure that e is a function or list?
         
   3. (V |-> w) v |-> w 
   4. <V1 .. Vn> k |-> Vk
 *)
Inductive APPLY : P Value -> P Value -> Value -> Prop :=
  | FUNWRONG : forall D1 D2,
     (v_wrong ∈ D1) ->
     APPLY D1 D2 v_wrong
  | ARGWRONG : forall D1 D2,
     (v_wrong ∈ D2) 
     -> APPLY D1 D2 v_wrong
  | BETA : forall D1 D2 w V,
     (V ↦ w ∈ D1) -> (mem V ⊆ D2) -> valid_mem V ->
     APPLY D1 D2 w
  | PROJ   : forall D1 D2 w VS k, 
     (v_list VS ∈ D1) -> (v_nat k ∈ D2) -> nth_error VS k = Some w
     -> APPLY D1 D2 w.
(* ADD these two for more wrong *)
(*
  | FUNWRONG2 : forall D1 D2 x,
     x ∈ D1 -> (Inconsistent x v_fun /\ forall XS, Inconsistent x (v_list XS)) ->
     APPLY D1 D2 v_wrong
  | ARGWRONG2 : forall D1 D2 VS x, 
     (v_list VS ∈ D1) -> 
     (x ∈ D2) -> 
     (forall k, Inconsistent x (v_nat k)) ->
     APPLY D1 D2 v_wrong. *)

(*  < 1 , 2 > (\x.x)  --> wrong?? 

    want to prove that we go wrong in enough places

*)


Infix "▩" := APPLY (at level 90).

(* ------------ Numbers ------------------ *)

Definition NAT : nat -> P Value :=
  fun j v => match v with 
          | v_nat k => j = k
          | _ => False
          end.

(* 
   Primitive addition function. A set containing all mappings of the 
   form:  
     <i,j> |-> i+j
     V |-> WRONG   where V /= <i,j>
*)
Definition ADD : P Value :=
  fun w => 
    match w with 
    | (V ↦ v_nat k) => 
        exists i j, ((v_list (v_nat i :: v_nat j :: nil)) ∈ mem V) /\ k = i + j
    | V ↦ v_wrong => 
        not (exists i j, v_list (v_nat i :: v_nat j :: nil) ∈ mem V)
    | _ => False
    end.

Lemma valid_NAT : forall k, valid (NAT k).
Proof.
  intros k. unfold NAT, valid. split.
  exists (v_nat k); eauto. cbn. auto.
  intro h; inversion h.
Qed.

Lemma valid_ADD : valid ADD.
Proof. 
  unfold ADD, valid.
  split.
  exists ( (v_list (v_nat 0 :: v_nat 0 :: nil) :: nil) ↦ v_nat 0). 
  cbn.
  exists 0. exists 0. split.  auto. auto.
  intro h. inversion h.
Qed.

(* k∈℘k *)
Lemma k_in_den_k : forall k, v_nat k ∈ NAT k.
Proof. intros. reflexivity. Qed.

Lemma k_in_den_k'_inv : forall k k', v_nat k ∈ NAT k' -> k = k'.
Proof. intros. inversion H. done. Qed.

Lemma v_in_den_k_inv :  forall v k, v ∈ NAT k -> v = v_nat k.
Proof. intros. destruct v; inversion H. done. Qed.

(*  Application is a Congruence ------------------------------------------------ *)
                          

Lemma APPLY_mono_sub { D1 D2 D3 D4 } :
    D1 ⊆ D3 -> D2 ⊆ D4 -> ((D1 ▩ D2) ⊆ (D3 ▩ D4)).
Proof.  
  intros D13 D24 w APP. 
  inversion APP; subst; unfold Included in *.
  + apply FUNWRONG. eauto.
  + apply ARGWRONG. eauto.
  + apply BETA with (V:=V); eauto.
    intros d z. eauto.
  + apply PROJ with (VS := VS) (k := k); eauto.
Qed.

Lemma APPLY_cong { D1 D2 D3 D4 } :
    D1 ≃ D3 -> D2 ≃ D4 -> ((D1 ▩ D2) ≃ (D3 ▩ D4)).
Proof.
  intros [ d13 d31 ] [ d24 d42 ].
  split; eapply APPLY_mono_sub; eauto.
Qed.


(* ---------- meta-operators produce valid results ------------------ *)

Lemma valid_Λ : forall F, valid (Λ F).
Proof. 
  intros F. 
  split. cbv.
  exists v_fun. auto. 
  unfold In. done.
Qed.

 
Lemma valid_LIST : forall D, ForallT valid D -> valid (LIST D).
induction 1. 
split; auto.
exists (v_list nil); done. 
destruct IHX as [[xs nin] h].
destruct p as [[y niny] hy]. 
destruct xs; try done.
split. 
exists (v_list (y :: l0)). econstructor; eauto.
eauto.
Qed.

(*  Abstraction is Extensional ---- -------------------------------------- *)

(* Λ-ext-⊆  *)
(* By restricting the hypothesis to only valid sets, we strengthen 
   the result. But this depends on Λ quantifying over valid sets. *)
Lemma Λ_ext_sub {F1 F2} :
  (forall {X : P Value}, valid X -> F1 X ⊆ F2 X) -> Λ F1 ⊆ Λ F2.
Proof.
  intros F1F2 v Iv. destruct v eqn:E; inversion Iv; auto.
  - split; auto. 
    eapply F1F2; eauto. 
Qed.

Lemma Λ_ext {F1 F2} :
  (forall {X}, valid X -> F1 X ≃ F2 X) -> Λ F1 ≃ Λ F2.
Proof. 
  intros g. split;
  eapply Λ_ext_sub; intros X NEX; destruct (g X); eauto.
Qed.


(*  Abstraction followed by Application is the identity ------------------- *)

Definition continuous (F : P Value -> P Value) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

Definition monotone (F : P Value -> P Value) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> valid X
  -> (Λ F) ▩ X ≃ F X.
Proof. 
  intros Fcont Fmono NEX.
  split.
  + intros w APP. inversion APP; subst. 
    - inversion H.
    - exfalso; eapply valid_not_wrong; eauto. 
    - inversion H.
      eapply (Fmono (mem V) X); eauto. 
    - inversion H.
  + intros w wInFX.
    have M: mem (cons w nil) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (cons w nil) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    move: NEX => [ [x h0] h1].
    eapply BETA with (V:=D); eauto.
    repeat split; eauto.
Qed.

(*  Adding actually adds --------- *)

Lemma den_list : forall i j V, mem V ⊆ LIST (NAT i :: NAT j :: nil) ->
                 forall x, x ∈ mem V -> x = v_list (v_nat i :: v_nat j :: nil).
Proof.
  induction V.  intros. done.
  intros M x xin.
  move: (M x xin) => h.
  destruct x; try done.
  cbv in h.
  inversion h; subst; clear h.
  destruct y; try done. subst.
  inversion H3; subst; clear H3.
  destruct y; try done. subst.
  inversion H4; subst; clear H4.
  auto.
Qed.

Lemma mem_one_inv : forall A (h v : A),  
 h ∈ mem (v :: nil) -> h = v.
Proof. 
  intros. cbn in H. destruct H; try done.
Qed. 

Lemma ADD_APPLY {i j} : 
  ADD ▩ (LIST (NAT i :: NAT j :: nil)) ≃ NAT (i + j).
Proof.
  split.
  + intros w APP. inversion APP; subst; clear APP.
    all: cbn in H.
    all: try done.
    destruct w; try done.
    - destruct H as [i0 [j0 [h0 h1]]]. subst.
      move: (den_list _ _ _ H0 _ h0) => h1. inversion h1. subst. clear h1.
      eapply k_in_den_k.
    - assert False. eapply H.
      destruct V; try done. destruct H1. done.
      move: (den_list _ _ _ H0 v ltac:(auto)) => h1. subst. 
      eauto.
      done.
   + intros w wIn.
     apply v_in_den_k_inv in wIn. subst.
     eapply BETA with (V := v_list (v_nat i :: v_nat j :: nil) :: nil).
     - cbn. eauto.
     - intros x xIn. inversion xIn. subst.
       cbn. eauto using k_in_den_k.
       inversion H.
     - cbn. split. eauto. unfold In, mem. intro h. inversion h. 
       intro h. inversion h; done.
Qed.

(* Environments ---------------------- *)

Definition Rho := Env (P Value).

Definition sub_env : Rho -> Rho -> Prop := Env.Forall2 Included.


Module EnvNotations.
Notation "ρ ⋅ x" := (access ⌈ v_wrong ⌉ ρ x) (at level 50).
Infix "⊔e" := (Env.map2 Union) (at level 60).
Infix "⊆e" := (Env.Forall2 Included) (at level 50).
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

Lemma Reflexive_sub_env {ρ:Env (P Value)} : uniq ρ -> ρ ⊆e ρ.
Proof.
  intros. eapply Env.Forall2_refl; eauto.
  typeclasses eauto.
Qed.

#[export] Hint Resolve Reflexive_sub_env : core.

#[export] Instance Transitive_sub_env : 
  Transitive (@Env.Forall2 (P Value) (P Value) Included).
Proof. typeclasses eauto. Qed.

Lemma extend_sub_env {ρ ρ': Env (P Value)}{y X} :
  y `notin` dom ρ ->
  ρ ⊆e ρ' -> (y ~ X ++ ρ) ⊆e (y ~ X ++ ρ' ).
Proof. intros; econstructor; eauto. reflexivity. Qed.

(* ---------------------------------------------------- *)

(* Nonempty environments *)

Definition nonempty_env : Rho -> Type := Env.ForallT nonemptyT.

Definition valid_env : Rho -> Type := Env.ForallT valid. 

Lemma valid_nil : valid_env nil.
Proof. unfold valid_env. eauto. Qed.

#[export] Hint Resolve valid_nil : core.

Lemma extend_valid_env {ρ x X} : 
  x `notin` dom ρ ->
  valid X -> 
  valid_env ρ -> valid_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX.  eapply ForallT_cons; eauto. Qed.

#[export] Hint Resolve extend_valid_env : core.

(* A finite environments *)

Definition finite (X : P Value) : Prop := exists E, (X ≃ mem E) /\ E <> nil.

Definition finite_env : Rho -> Type := Env.ForallT finite.

Lemma extend_nonempty_env {ρ x X} : 
  x `notin` dom ρ ->
  nonemptyT X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply ForallT_cons; eauto. Qed.

#[export] Hint Resolve extend_nonempty_env : core.

(* ---------------------------------------------------- *)


Definition APPLY_ConsistentSet : forall w1 w2 w1' w2', 
    ConsistentSet w1 w1' -> 
    ConsistentSet w2 w2' -> 
    ConsistentSet (APPLY w1 w2) (APPLY w1' w2'). 
Proof.
  intros w1 w2 w1' w2' C1 C2.
  unfold ConsistentSet in *.
  intros x y h1 h2.

  inversion h1; inversion h2; subst; eauto; clear h1 h2.
  all: try (move: (C1 _ _ H H3) => h; inversion h; subst; auto).
  all: try (move: (C1 _ _ H H5) => h; inversion h; subst; auto).
  all: try (move: (C2 _ _ H H4) => h; inversion h; subst; auto).
  all: try (move: (C2 _ _ H0 H5) => h; inversion h; subst; auto).

  (* Application of a function to "wrong". This case is impossible because
     the map's domain is valid and all elements of w2 are consistent with wrong. *) 
  move: H5 => [NE NW]. 
  exfalso.
  have L: forall y, y ∈ w2' -> Consistent v_wrong y.
  { intros. eauto. }
  destruct V; try done.
  specialize (L v ltac:(eauto)). inversion L. subst; simpl in NW. auto.

  move: H1 => [NE NW]. 
  exfalso.
  have L: forall y, y ∈ w2 -> Consistent y v_wrong.
  { intros. eauto. }
  destruct V; try done.
  specialize (L v ltac:(eauto)). inversion L. subst; simpl in NW. auto.

  move: H3 => [x1 [x2 [I1 [I2 ii]]]].
  have h3 : x1 ∈ w2. eapply H0; eauto.
  have h4 : x2 ∈ w2'. eapply H6; eauto.
  move: (C2 x1 x2 h3 h4) => h5.
  assert False. eapply Consistent_Inconsistent_disjoint; eauto. done.

  move: (C2 _ _ H0 H6)=> c1. inversion c1; subst; clear c1; eauto. 
  clear h H H0 H5 H6.
  move: k0 H1 H7.
  induction H4; intros k0; destruct k0; simpl;  try done.
  + intros h1 h2; inversion h1; inversion h2; subst. auto.
  + intros h1 h2. eauto.
Qed.

Definition APPLY_ConsistentW : forall w1 w2, 
    ConsistentW w1 -> 
    ConsistentW w2 -> 
    ConsistentW (APPLY w1 w2). 
Proof.
  intros.  unfold ConsistentW in *.
  eapply APPLY_ConsistentSet; eauto.
Qed.

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
    destruct H3 as [E1 [s1 u1 ]].
    destruct H5 as [E2 [s2 u2 ]].
    exists (E1 ++ E2).
    split.
    rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    ++ intro h.
    apply u2. 
    destruct E1. simpl in h. auto.
    done.
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

(* --- Monotone --------------- *)

Definition monotone_env (D : Rho -> P Value) := 
 forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.


(* Continuous ----------------------------------------- *)

Definition continuous_In (D:Rho -> P Value) (ρ:Rho) (v:Value) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env (D:Rho -> P Value) (ρ:Rho) : Prop :=
  forall v, continuous_In D ρ v.

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
(* can we make this nonempty_env instead of valid_env *)
Definition initial_finite_env (ρ : Rho) (NE : valid_env ρ) : Rho.
  induction NE. exact nil.
  destruct f as [[V _] _].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [[v _] w].  simpl. congruence.
Qed. 

#[export] Hint Rewrite initial_finite_dom : rewr_list.

Lemma finite_singleton : forall v, finite ⌈ v ⌉.
Proof. intros v.  exists (cons v nil).
       repeat split; eauto. done. 
Qed.

#[export] Hint Resolve finite_singleton : core. 


Lemma initial_fin (ρ : Rho) (NE : valid_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [[v _] w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

#[global] Hint Resolve initial_fin : core. 


Lemma initial_fin_sub (ρ : Rho) (NE : valid_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [[v wpx] _].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

#[global] Hint Resolve initial_fin_sub : core. 


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Rho) 
  (NE : valid_env ρ) : Rho :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { v x ρ NE } : 
  finite_env (single_env x ⌈ v ⌉ ρ NE).
Proof.
  induction NE; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. 
  destruct f as [[v1 I1] v2].
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. simpl_env. auto. auto.
  + rewrite update_neq_var; eauto.
    econstructor; eauto.
    simpl_env. auto.
Qed.

#[global] Hint Resolve single_fin : core. 


Lemma single_sub { ρ x v } :
  forall (NE : valid_env ρ),
    v ∈ ρ ⋅ x 
  -> x `in` dom ρ
  -> (single_env x ⌈ v ⌉ ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) auto. 
  + (* cons case *)
    unfold single_env in *.
    simpl. simpl_env in Indom.
    destruct f as [[w h1] h2]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       simpl_env.  eauto.
       intros x h. inversion h. subst. auto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. auto.
       intros y h. inversion h. subst. unfold In. auto.
Qed.

#[export] Hint Resolve single_sub : core. 


(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x `in` dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE.
  induction NE; intro h. fsetdec.
  simpl. destruct f as [[w h1] h2]. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. econstructor; eauto.
  simpl. rewrite EQ. simpl in h. eapply IHNE; auto. fsetdec.
Qed.  

#[export] Hint Resolve v_single_xvx : core. 



(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub E ρ (NE : valid_env ρ) :
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


Lemma CONS_continuous {D E ρ}{w} :
    w ∈ (CONS (D ρ) (E ρ))
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ3 , 
    exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ 
                             /\ (w ∈ (CONS (D ρ3) (E ρ3))).
Proof.  
  intros C. unfold CONS, In in C. destruct w.
  all: try done.
  destruct l. try done.
  move: C => [Dv El].
  intros IHD IHE mD mE.
  destruct (IHD v Dv) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE (v_list l) El) as 
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - eapply mD. instantiate (1:= ρ1). 
    eapply join_sub_left; eauto. auto.
  - eapply mE. instantiate (1:= ρ2).
    eapply join_sub_right; eauto. auto.
Qed.


Lemma APPLY_continuous {D E ρ}{w} :
  (valid_env ρ)
  -> w ∈ ((D ρ) ▩ (E ρ))
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ3 , 
    exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ 
                             /\ (w ∈ ((D ρ3) ▩ (E ρ3))).
Proof.  
  intros NE APP. inversion APP; subst. 
  all: intros IHD IHE mD mE.
  + destruct (IHD v_wrong H) as
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    exists ρ1. exists fρ1. split. auto.
    eapply FUNWRONG; auto.
  + destruct (IHE v_wrong H) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    exists ρ1. exists fρ1. split. auto.
    eapply ARGWRONG; auto.
  + destruct (IHD (V ↦ w) H) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - have VwDp3 : V ↦ w ∈ D (ρ1 ⊔e ρ2).
    { eapply mD. 2: eapply VwDp1. 
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { intros v vV. eapply mE.
      2: eapply VEp2; auto. 
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
 + destruct (IHD (v_list VS)) as [ρ1 [F1 [h1 h2]]]; auto.
   destruct (IHE (v_nat k)) as [ρ2 [F2 [h3 h4]]]; auto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
   exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.    
  - eapply join_lub; eauto.
  - eapply PROJ with (VS := VS) (k:=k); eauto.
    eapply mD. eapply join_sub_left; auto. auto.
    eapply mE. eapply join_sub_right; auto. auto.
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

(* Algebraicity.  
   Only need finite information from the environment.
*)

Lemma Lambda_continuous {E ρ} {NE : valid_env ρ}{ v x} :
  v ∈ Λ (fun D => E (x ~ D ++ ρ)) 
  -> (forall V, valid_mem V ->
          continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\
            (v ∈ (Λ (fun D => E (x ~ D ++ ρ')))).
Proof.
  induction v.
  all: try solve [intros; cbv in H; done].
  - (* v is l ↦ v *)
    intros [ wEVρ [NW CL] ] IH mE.
    have VV: valid_mem l. unfold valid_mem. split; eauto.
    destruct (IH l ltac:(eauto) v wEVρ) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
    inversion ρ'Vρ. subst. clear ρ'Vρ.
    inversion fρ'. subst. clear fρ'.
    exists E1. exists X.
    repeat split; eauto.
    eapply mE. 2: exact wEρ'.
    have SS: E1 ⊆e E1. eapply Reflexive_sub_env.  eapply Forall2_uniq1; eauto. 
    auto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.

(* ---------------------------------------------------------- *)

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/ISWIMPValue.agda *)

Import LCNotations.
Open Scope tm.

Check lt_wf.

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


(* Denotation function: unbound variables have no denotation. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Rho) : P Value :=
  match n with
  | O => fun _ => False
  | S m => 
     match a with 
     | var_b _ => ⌈ v_wrong ⌉
     | var_f x => ρ ⋅ x 
     | app t u   => 
         denot_n m t ρ ▩ denot_n m u ρ
     | abs t => 
         let x := fresh_for (dom ρ \u fv_tm t) in 
         Λ (fun D => denot_n m (t ^ x) (x ~ D ++ ρ))
     | lit k => NAT k
     | add => ADD
     | tnil => NIL
     | tcons t u => CONS (denot_n m t ρ) (denot_n m u ρ)
     end
  end.

Import Wf_nat.

Lemma size_is_enough : forall n a, n >= size_tm a -> forall ρ, denot_n n a ρ = denot_n (size_tm a) a ρ.
Proof.
  intros n.
  induction (lt_wf n) as [n _ IH].
  intros a h ρ; destruct a; simpl in *.
  all: try destruct n; simpl; auto; try lia.
  all: f_equal.
  all: try rewrite IH; try lia; auto;
    try rewrite IH; try lia; auto.
  - extensionality D.
    remember (fresh_for (dom ρ \u fv_tm a)) as x.
    rewrite IH. lia.
    autorewrite with lngen. lia.
    autorewrite with lngen. auto.
Qed.

Definition denot (a : tm) := denot_n (size_tm a) a.

Lemma denot_var_b : forall x ρ, denot (var_b x) ρ = ⌈ v_wrong ⌉.
Proof.
  intros x ρ. reflexivity.
Qed.

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

Lemma denot_lit : forall k ρ,  denot (lit k) ρ = NAT k.
Proof. intros. reflexivity. Qed. 

Lemma denot_add : forall ρ,  denot add ρ = ADD.
Proof. intros. reflexivity. Qed. 

Lemma denot_tnil : forall ρ,  denot tnil ρ = NIL.
Proof.  intros. reflexivity. Qed. 

Lemma denot_tcons : forall t u ρ, 
    denot (tcons t u) ρ = CONS (denot t ρ) (denot u ρ).
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
         move: (@fresh_for_fresh x0 ρ ltac:(auto)) => Frx0;
         simpl_env in Frx0
    end.    

Definition access_app_P := @access_app (P Value) ⌈ v_wrong ⌉.

(* Renaming property for denotations. *)

Lemma rename_denot_n : forall n t y w ρ1 ρ2 D, 
  w `notin` dom ρ1 -> 
  y `notin` dom ρ1 \u fv_tm t -> 
  denot_n n t (ρ1 ++ w ~ D ++ ρ2) = 
  denot_n n (t [w ~> var_f y]) (ρ1 ++ y ~ D ++ ρ2).
Proof. 
  induction n;
  intros t y w ρ1 ρ2 D Frw Fry; simpl. auto.
  destruct t; simpl; auto.
  all: simpl in Fry.
  + destruct (x == w).
    ++ subst. 
       simpl_env.       
       rewrite access_app_fresh; auto. 
       rewrite access_eq_var.
       rewrite access_app_fresh; auto. 
       rewrite access_eq_var. auto.
    ++ have NEx: x <> y. fsetdec.
       edestruct (@access_app_P ρ1 x).
       repeat rewrite H. auto.
       destruct (H (cons (w, D) ρ2)).
       rewrite H1. 
       destruct (H (cons (y, D) ρ2)).
       rewrite H3.
       rewrite access_neq_var. auto.
       rewrite access_neq_var. auto.
       auto.
  + f_equal.
    extensionality D0.
    name_binder x0 Frx0.
    name_binder y0 Fry0.

    pick fresh z.
    rewrite (subst_tm_intro z _ (var_f x0)). 
    auto. 
    rewrite (subst_tm_intro z _ (var_f y0)). 
    { autorewrite with lngen. simpl.
      clear Frx0 Fry0 Fry Frw. fsetdec. }
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
    2: { autorewrite with lngen. 
         clear Fry0 Frw Fry.
         simpl.
         fsetdec.
    }

    replace ((y0 ~ D0) ++ ρ1 ++ (y ~ D) ++ ρ2) with
      (nil ++ (y0 ~ D0) ++ (ρ1 ++ (y ~ D) ++ ρ2)). 2: { simpl_env; auto. }

    rewrite <- IHn; simpl_env; auto.
    2: { autorewrite with lngen. simpl. 
         clear Frx0 Frw Fry.
         rewrite <- fv_tm_subst_tm_lower in Fry0.
         fsetdec.
         auto.
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
    apply IHn; simpl_env; auto.
  + simpl_env.
    f_equal.
    apply IHn; simpl_env; auto.
    apply IHn; simpl_env; auto. 
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


Create HintDb denot.
#[export] Hint Opaque denot : denot.
#[export] Hint Rewrite denot_var_b denot_var denot_app denot_lit 
  denot_add denot_tnil denot_tcons : denot.
(* no hint for abs, must pick fresh first *)

Lemma weaken_denot1 : forall t ρ ρ1 ρ2, 
    fv_tm t [<=] dom (ρ1 ++ ρ2) ->
    uniq (ρ1 ++ ρ ++ ρ2) ->
    denot t (ρ1 ++ ρ2) = denot t (ρ1 ++ ρ ++ ρ2). 
Proof.
  intro t.
  eapply tm_induction with (t := t).
  1: move=>i. 
  2: move=>x.
  3: move=>t1 t2 IH1 IH2. 
  4: move=> u IH.
  8: move=> t1 t2 IH1 IH2.
  all: intros ρ ρ1 ρ2 FV U.
  all: simpl_env in FV; simpl in FV. 
  all: autorewrite with denot.
  all: try solve [reflexivity].
  + (* var *) 
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
  + (* app *)
    f_equal.
    eapply IH1; simpl_env; eauto.
    fsetdec.
    eapply IH2; simpl_env; eauto.
    fsetdec.
  + pick fresh x.
    repeat rewrite (denot_abs x).
    simpl_env; fsetdec.
    simpl_env; fsetdec.
    f_equal.
    extensionality D.
    rewrite <- app_assoc.
    erewrite IH; simpl_env; eauto.
    rewrite fv_tm_open_tm_wrt_tm_upper; simpl; eauto.
    fsetdec.
  + f_equal.
    eapply IH1; simpl_env; eauto.
    fsetdec.
    eapply IH2; simpl_env; eauto.
    fsetdec.
Qed.

Lemma weaken_denot : forall t ρ2 ρ,
   fv_tm t [<=] dom ρ2 ->
   uniq (ρ ++ ρ2) ->
   denot t ρ2 = denot t (ρ ++ ρ2). 
Proof.
  intros.
  unfold denot.
  eapply weaken_denot1 with (ρ1 := nil); simpl; auto.
Qed.

(* Scoping predicates *)

Lemma subst_denot : forall t x u ρ1 ρ2, 
    scoped t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) ->
    scoped u ρ2 ->
    denot t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) =
    denot (t [x ~> u]) (ρ1 ++ ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros x u ρ1 ρ2 ST SU.
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
       apply weaken_denot; eauto.
    ++ repeat rewrite denot_var.
       destruct (access_app_P ρ1 y) as [h1 | h2].
       repeat rewrite h1. auto.
       move: (h2 ρ2) => [N1 ->]. 
       move: (h2 (x ~ denot u ρ2 ++ ρ2)) => [N3 ->].
       rewrite access_neq_var; auto.
  + move: (scoped_app_inv1 _ _ _ ST) => S1.
    move: (scoped_app_inv2 _ _ _ ST) => S2.
    f_equal.
    eapply IH1; eauto.
    eapply IH2; eauto.
  + have LCU: lc_tm u. inversion SU. auto.
    pick fresh z.
    specialize (IH z ltac:(auto) x u).
    simpl. simpl_env.
    repeat rewrite (denot_abs z).
    simpl_env. fsetdec.
    simpl_env. rewrite fv_tm_subst_tm_upper. fsetdec. 
    f_equal.
    extensionality D.
    have FZ: z `notin` (dom (ρ1 ++ x ~ denot u ρ2 ++ ρ2) \u fv_tm t').
    simpl_env. fsetdec.
    move: (scoped_abs_inv z t' D _ FZ ST) => h.
    rewrite <- app_assoc.
    rewrite IH; auto.
    autorewrite with lngen.
    reflexivity.
    auto.
  + move: (scoped_tcons_inv1 _ _ _ ST) => S1.
    move: (scoped_tcons_inv2 _ _ _ ST) => S2.
    f_equal.
    eapply IH1; eauto.
    eapply IH2; eauto.
Qed.

Lemma subst_denot1 :
  forall (t : tm) (x : atom) (u : tm) (ρ : Rho),
    scoped t (x ~ denot u ρ ++ ρ) 
    -> scoped u ρ 
    -> denot t (x ~ denot u ρ ++ ρ) = denot (t [x ~> u]) ρ.
Proof.
  intros. 
  eapply subst_denot with (ρ1 := nil); auto. 
Qed.


(* ------------------------------------ *)

(* denotational_semantics/agda/SemanticProperties.agda  *)

(* Note: sub_env forces ρ and ρ' to have the same domain *)


Lemma access_monotone {ρ ρ':Rho}{x} : ρ ⊆e ρ' -> ρ ⋅ x ⊆ ρ' ⋅ x.
Proof.
  induction 1. simpl. reflexivity.
  simpl. destruct (x == x0) eqn:E. auto.
  auto. 
Qed.

(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: 
  monotone_env (denot t).
Proof.
  unfold monotone_env.
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
 all: intros ρ ρ' S.
 all: autorewrite with denot.
 all: try solve [reflexivity].
  + eapply access_monotone; auto.
  + eapply APPLY_mono_sub; eauto.
  + pick fresh x.
    repeat rewrite (denot_abs x).
    fsetdec.
    fsetdec.
    eapply Λ_ext_sub.
    intros X NE.
    eapply IH. fsetdec.
    eapply extend_sub_env; eauto. 
  + eapply CONS_mono_sub; eauto.
Qed.


(* ⟦⟧-monotone-one *)
Lemma denot_monotone_one : forall ρ t x, 
    uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot t (x ~ D ++ ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  eapply denot_monotone; simpl; auto.
  econstructor; eauto.
Qed.
  
Lemma valid_nonempty_mem : forall V, 
      valid_mem V -> nonemptyT (mem V).
Proof. intros. eapply valid_is_nonempty. eauto. Qed.

(* ⟦⟧-continuous *)
Lemma denot_continuous {t} : forall ρ,
    valid_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ NE.
  all: intros v vIn.
  all: autorewrite with denot in vIn.
  all: try solve [ exists (initial_finite_env ρ NE);
    eexists; eauto] .
  + destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
    - exists (single_env x ⌈ v ⌉ ρ NE).
      exists (@single_fin v x ρ NE).
      split.
      ++ eapply single_sub; auto.
      ++ eapply v_single_xvx. auto. 
    - exists (initial_finite_env ρ NE).
      eexists; eauto. split. eauto.
      rewrite denot_var.
      rewrite access_fresh. simpl_env. auto.
      rewrite access_fresh in vIn. auto. done.
  + edestruct (APPLY_continuous NE vIn) as [ρ' [F SS]]; eauto.
    eapply denot_monotone.
    eapply denot_monotone.
    exists ρ'. exists F.
    rewrite denot_app. auto.
  + pick fresh x.
    rewrite (denot_abs x) in vIn. fsetdec.
    move: (@Lambda_continuous _ _ NE v x vIn) => h.    
    destruct h as [ρ' [Fρ' [S vvIn]]].
    ++ intros V NEV NW.
       move: (valid_nonempty_mem _ NEV) => [w h0]. 
       eapply IH; eauto.
    ++ eapply denot_monotone.
    ++ exists ρ'. exists Fρ'. 
       erewrite <- Forall2_dom in Fr. 2: eapply S.
       rewrite (denot_abs x). fsetdec.
       split; auto.
  + edestruct (CONS_continuous vIn) as [ρ' [F SS]]; eauto.
    eapply denot_monotone.
    eapply denot_monotone.
    exists ρ'. exists F.
    rewrite denot_tcons. auto.
Qed.


(* ⟦⟧-continuous-⊆ *) 
Lemma denot_continuous_sub {ρ t} : 
  valid_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
  eapply denot_monotone; eauto.
  intros v InV.
  eapply denot_continuous; auto.
Qed.


Definition Same_env : Rho -> Rho -> Prop := Env.Forall2 Same_set.

(* The denotation respects ≃ *)
Instance Proper_denot : Proper (eq ==> Same_env ==> Same_set) denot.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: move => ρ1 ρ2 EQ.
  all: autorewrite with denot.
  all: try solve [reflexivity].
  all: eauto using APPLY_cong, CONS_cong.
  - destruct (FSetDecideAuxiliary.dec_In  x (dom ρ1)).
    + apply Forall2_access with (f := Same_set); auto.
    + rewrite access_fresh. auto.
      rewrite access_fresh. erewrite Forall2_dom in H; eauto.
      reflexivity.
  - pick fresh x. 
    repeat rewrite (denot_abs x). fsetdec. fsetdec.
    eapply Λ_ext.
    intros X neX.
    eapply IH; eauto.
    econstructor; eauto. 
    reflexivity. 
Qed.

(* The denotation respects ⊆ *)
Instance Proper_sub_denot : Proper (eq ==> Env.Forall2 Included ==> Included) denot.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: move => ρ1 ρ2 SUB.
  all: autorewrite with denot.
  all: try solve [reflexivity].
  all: eauto using APPLY_mono_sub, CONS_mono_sub.
  - destruct (FSetDecideAuxiliary.dec_In  x (dom ρ1)).
    + apply Forall2_access with (f := Included); auto.
    + rewrite access_fresh. auto.
      rewrite access_fresh. erewrite Forall2_dom in H; eauto.
      reflexivity.
  - pick fresh x. 
    repeat rewrite(denot_abs x). fsetdec. fsetdec.
    eapply Λ_ext_sub.
    intros X neX.
    eapply IH. fsetdec.
    econstructor; eauto.
    reflexivity.
Qed.


(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ x } :
  valid_env ρ 
  -> x `notin` dom ρ 
  -> continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros NE_ρ Fr.
  unfold continuous.
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (x ~ X ++ ρ)) as 
    [ρ' [pf [h1 h2]]]. 3: eauto.
  + eapply extend_valid_env; eauto.
  + eauto.
  + inversion h1. subst. inversion pf. subst.
    move: H6 => [D [S NN]].
    exists D. split.
    rewrite <- S. auto.
    split. 
    have SUB: Env.Forall2 Included (x ~ a1 ++ E1) (x ~ mem D ++ ρ).
    econstructor; eauto. 
    rewrite <- S. reflexivity.
    rewrite <- SUB.
    auto.
    eapply valid_sub_valid_mem; eauto. rewrite <- S. auto.
Qed.

(* Λ⟦⟧-▪-id *)
Lemma Λ_denot_APPLY_id :
  forall t ρ x X,
    valid X
    -> valid_env ρ
    -> x `notin` dom ρ 
    -> ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) ≃
      denot (t ^ x) (x ~ X ++ ρ).
Proof.
  intros.
  move: (@Λ_APPLY_id (fun D => denot (t ^ x) (x ~ D ++ ρ)) X) => h.
  eapply h; auto.
  +  (* continuity *)
    eapply denot_continuous_one; auto.
  + eapply denot_monotone_one; auto.
    eapply ForallT_uniq; eauto.
Qed.


Lemma Consistent_denot :
  forall t ρ1 ρ2, Env.ForallT2 ConsistentSet ρ1 ρ2 -> valid_env ρ1 -> valid_env ρ2 ->
             ConsistentSet (denot t ρ1) (denot t ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ1 ρ2 CR VR1 VR2.
  all: autorewrite with denot.
  all: intros x1 x2 I1 I2.
  all: try solve [inversion I1; inversion I2; eauto].

  - (* var *) 
    induction CR; simpl in I1, I2.
    ++ inversion I1. inversion I2. subst. auto.
    ++ destruct (x == x0) eqn:E; rewrite E in I1, I2. eapply f; eauto.
       inversion VR1. inversion VR2. eauto.

  - (* app *)
    move: (IH1 ρ1 ρ2 ltac:(eauto) ltac:(eauto) ltac:(eauto)) => C1.
    move: (IH2 ρ1 ρ2 ltac:(eauto) ltac:(eauto) ltac:(eauto)) => C2.

    move: (APPLY_ConsistentSet _ _ _ _ C1 C2) => CA.

    eapply (CA x1 x2 I1 I2).

  - (* abs *)
    pick fresh y.
    rewrite (denot_abs y) in I1; eauto.
    rewrite (denot_abs y) in I2; eauto.
    destruct x1; unfold In, Λ in I1; try done;
    destruct x2; unfold In, Λ in I2; try done.
    move: I1 => [I1 [Vl Cl]].
    move: I2 => [I2 [Vl0 Cl0]].
    destruct (dec_any l (DecSetList l) l0).
    destruct (dec_con x1 x2). eapply c_map2; eauto.
    ++ (* Domains are consistent, ranges are not. Should be a contradiction. *)
      have CS: ConsistentSet (mem l) (mem l0). admit.
      have V1:  valid_env (y ~ mem l ++ ρ1). econstructor; eauto. admit.
      have V2:  valid_env (y ~ mem l0 ++ ρ2). admit.
      move: (IH y ltac:(auto) (y ~ mem l ++ ρ1) (y ~ mem l0 ++ ρ2) ltac:(eauto)      
            ltac:(eauto) ltac:(eauto)) => h.
      move: (h x1 x2 I1 I2) => C12.
      exfalso. eapply Consistent_Inconsistent_disjoint; eauto.
    ++ unfold InconsistentAnyList in i. 
       eapply c_map1; eauto.
  - (* nat *)
    unfold NAT in *. 
    destruct x1; try done.
    destruct x2; try done.
    inversion I1; inversion I2; subst; eauto.
  - (* ADD: need a lemma that ADD is consistent *) 
    admit.
  - (* CONS: need a lemma about CONS *)
    admit.
Admitted.

(* Example semantics *)


Definition tm_Id : tm := abs (var_b 0).

Lemma denot_Id {v} : (v <> v_wrong) -> (v :: nil ↦ v) ∈ denot tm_Id nil.
Proof.
  intro NE.
  unfold tm_Id.
  pick fresh x.
  rewrite (denot_abs x). simpl. auto.
  unfold Λ. unfold Ensembles.In.
  split. 2: { split. done. intro h. inversion h. done. done. }
  cbn.
  destruct (x == x); try done.
  cbn. left. auto.
Qed. 


Lemma denot_Id_inv : forall x ρ, x ∈ denot tm_Id ρ ->
                          forall w,  Consistent x (w :: nil ↦ w).
Proof.
  intros x ρ.
  unfold tm_Id. 
  pick fresh y.
  rewrite (denot_abs y); auto.
  intro h. unfold In in h. 
  unfold Λ in h.
  destruct x; try done.
  move: h => [h0 [h1 h2]].
  cbn in h0. rewrite eq_dec_refl in h0.
  intros w.
  destruct (dec_con x w). eauto.
  eapply c_map1.
  exists x. exists w. 
  repeat split; eauto.
  unfold List.In. eauto.
Qed.

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).


#[global] Hint Rewrite access_eq_var : lngen.

Lemma denot_Delta_inv :
  forall x, x ∈ denot tm_Delta nil -> 
       exists v w, Consistent x (((v :: nil ↦ w) :: v :: nil) ↦ w).
Proof.
  intro x.  unfold In, tm_Delta.
  pick fresh y.
  rewrite (denot_abs y); auto.
  cbn. rewrite eq_dec_refl.
  unfold Λ. destruct x; try done.
  move=> [h0 [h1 h2]].
  inversion h0; subst; try done.
  + exists (l ↦ x). exists x.
    eapply c_map2. reflexivity.
  + exists (l ↦ x). exists x.
    eapply c_map2. reflexivity.
  + cbn. intros.
    exists v_fun. exists v_fun. eauto.
Qed.

Lemma denot_Delta : forall (v w : Value), v <> v_wrong ->
    (((v :: nil ↦ w) :: v :: nil) ↦ w) ∈ denot tm_Delta nil.
Proof.
  intros v w NW.
  pick fresh x.
  unfold tm_Delta.
  rewrite (denot_abs x); auto.
  cbn. rewrite eq_dec_refl.
  split. 2: { unfold valid_mem. split. intro h. done. intro h.
              inversion h; try done. inversion H; try done. }
  cbv.
  eapply BETA with (V := v :: nil).
  unfold In. left. auto.
  rewrite -> mem_singleton. 
  intros x0 II. inversion II. subst. cbv. right. left. auto.
  unfold valid_mem.
  split; eauto.
  intro h. done. 
  intro h; inversion h; try done.
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
Admitted.

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

(* Soundness of reduction with respect to denotation *)
(* ISWIMPValue.agda *)


Lemma value_nonempty {t}{ρ} : 
  fv_tm t [<=] dom ρ
  -> valid_env ρ -> value t -> valid (denot t ρ).
Proof. 
  intros FV NEρ vv.
  induction t.
  all: try solve [assert False; try inversion vv; done].
  all: autorewrite with denot.
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
  + eapply valid_NIL; eauto.
  + simpl in FV. eapply valid_CONS; eauto. 
    eapply IHt1; eauto. fsetdec.
    inversion vv; eauto.
    eapply IHt2; eauto. fsetdec. 
    inversion vv; eauto.
    admit. (* !! *)
Admitted.


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
  - (* beta *)
    destruct SCt as [FV U lc]. inversion lc. subst.
    simpl in FV.
    rewrite denot_app.
    pick fresh x.
    erewrite denot_abs with (x:=x).
    rewrite Λ_denot_APPLY_id.
    eapply value_nonempty; auto.
    fsetdec.
    auto.
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
    eapply (scoped_abs_inv x _ X _ F1 SCt).
    have F2 : x `notin` dom ρ \u fv_tm t'. fsetdec.
    eapply (scoped_abs_inv x _ X _ F2 SCu).
    eapply extend_valid_env.
    fsetdec.
    eauto.
    eauto.
  - have SC1: scoped t ρ. eapply scoped_app_inv1; eauto.
    have SC2: scoped t' ρ. eapply scoped_app_inv1; eauto.
    have SC3: scoped u ρ. eapply scoped_app_inv2; eauto.
    repeat rewrite denot_app.
    eapply APPLY_cong; eauto.
    reflexivity.
  - have SC1: scoped t ρ.  eapply scoped_app_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_app_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_app_inv2; eauto.
    repeat rewrite denot_app.
    eapply APPLY_cong; eauto.
    reflexivity.
  - repeat rewrite denot_tcons; eauto.
    eapply CONS_cong; eauto.
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped t' ρ.  eapply scoped_tcons_inv1; eauto.
    eapply IHRED; eauto.
    reflexivity.

Admitted.



(* Λ  \Lambda
   ▩  \squarecrossfill 
   ↦  \mapsto  
   ⤇ \Mapsto  
   ●  \CIRCLE 
   ⊆  \subseteq   (Included)
*)

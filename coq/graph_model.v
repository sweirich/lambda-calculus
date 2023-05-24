Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.SetsAsPredicates.
Require Import lc.AssocList.


(* This a "Graph Model" of the CBV lambda calculus based on Jeremy Siek's Agda
   development.

   Expressions are mapped to sets of values. The interpretation of a function
   is a set of its mappings. We need an infinite set to fully represent a
   function but any computation only requires a finite approximation.

*)

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/PValueCBV.agda *)

(* Λ  \Lambda
   ▩  \squarecrossfill 
   ↦  \mapsto  
   ⤇ \Mapsto  
   ●  \CIRCLE 
   ⊆  \subseteq   (Included)
*)

Definition result (A:Type) := sum unit A.
Definition wrong {A} : result A := inl tt.
Definition ret {A} : A -> result A := inr.
Definition bind {A} : result A -> (A -> result A) -> result A :=
    fun x f => match x with 
            | inl _ => wrong
            | inr v => f v
            end.


Inductive Value : Type :=
  | v_nat : nat -> Value 
    (* one entry in a function's table *)
  | v_map : list Value -> Value -> Value
    (* trivial function value, evaluated to a value but never applied *)
  | v_fun : Value
    (* tuple of values *)
  | v_list : list Value -> Value
    (* dynamic type error *)
  | v_wrong : Value
.

(* 

A: denot (exists x. x) = fun x => False

B: denot (exists x. x) = [] ∪ [1] ∪ [1,2] ∪ [1 ↦ 3,5] ...
      union of all finite lists of values

Fine-grained CBV -- can only apply values to values
   combined monadic metalanguage with computational lambda calculus

      x = e1 ; e2

*)

(*

 ( fail || X )  == X
 ( wrong || X ) == wrong
 ( X || wrong ) == wrong

all (exists x. x) == Fail
all (exists x. x = 3 || x = 4) == [3, 4]

A || B == exists x. if x == 0 then A if x == 1 then B else Fail


  

(* For nondeterminism *)
Definition Choice (X1 : P (Labeled Value)) (X2 : P Value) := 
  Union (label Left X1) (label Right X2).

Definition One (X : P Value) : P Value.

*)


(* ------------ Functions ------------------ *)

Infix "↦" := v_map (at level 85, right associativity).

Import SetNotations.
Local Open Scope set_scope.

Definition Λ : (P Value -> P Value) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈ f (mem V)) /\ V <> nil /\ not (v_wrong ∈ mem V)
          | v_fun => True
          | _ => False
          end.

Definition LIST : list (P Value) -> P Value  :=
  fun DS w => 
    match w with 
    | v_list WS => Forall2 In DS WS
    | _ => False
    end.

(* 4 possibilities in application: 
   1. v_wrong e |-> v_wrong
   2. e v_wrong |-> v_wrong  -- should this ensure that e is a function or tuple?
   3. (V |-> w) v |-> w 
   4. <V1 .. Vn> k |-> Vk
 *)
Inductive APPLY : P Value -> P Value -> Value -> Prop :=
  | FUNWRONG : forall D1 D2,
     (v_wrong ∈ D1)
     -> APPLY D1 D2 v_wrong
  | ARGWRONG : forall D1 D2,
     (v_wrong ∈ D2) 
     -> APPLY D1 D2 v_wrong
  | BETA : forall D1 D2 w V,
     (V ↦ w ∈ D1) -> (mem V ⊆ D2) -> V <> nil 
     -> APPLY D1 D2 w
  | PROJ   : forall D1 D2 w VS k, 
     (v_list VS ∈ D1) -> (v_nat k ∈ D2) -> nth_error VS k = Some w
     -> APPLY D1 D2 w.


Infix "▩" := APPLY (at level 90).

Definition den_nat : nat -> P Value :=
  fun j v => match v with 
          | v_nat k => j = k
          | _ => False
          end.

(* 
   Primitive addition function. A set containing all mappings of the 
   form:  
     <i,j> |-> i+j
     V |-> WRONG
*)
Definition den_add : P Value :=
  fun w => 
    match w with 
    | (v_list (v_nat i :: v_nat j :: nil) :: nil) ↦ v_nat k => 
        k = i + j
    | _ ↦ v_wrong => True
    | _ => False
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

(* Valid ---- -------------------------------------- *)

Definition valid (V : P Value) : Type :=
  { x : Value & ((x ∈ V) /\ not (v_wrong ∈ V)) }.

Lemma valid_is_nonempty V : valid V -> nonemptyT V.
  intros [x [P _]]. econstructor; eauto. Defined.

(*  Abstraction is Extensional ---- -------------------------------------- *)

(* Λ-ext-⊆  *)
Lemma Λ_ext_sub {F1 F2} :
  (forall {X : P Value}, valid X -> F1 X ⊆ F2 X) -> Λ F1 ⊆ Λ F2.
Proof.
  intros F1F2 v Iv. destruct v eqn:E; inversion Iv.
  - move: H0 => [NN NW]. 
    split. eapply F1F2; eauto. 
    destruct l as [|w l]; try done. 
    econstructor; eauto.
    split. auto. auto.
  - trivial.
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
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ D <> nil.

Definition monotone (F : P Value -> P Value) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* Is there a better word for this? *)
(* Definition strict (F : P Value -> P Value) : Set := 
  forall X, v_wrong ∈ X -> v_wrong ∈ F X. *)


(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> valid X 
  -> (Λ F) ▩ X ≃ F X.
Proof. 
  intros Fcont Fmono NEX .
  split.
  + intros w APP. inversion APP; subst. 
    - inversion H.
    - move: NEX => [x [_ W]]. done.
    - inversion H. eapply (Fmono (mem V) X); eauto. 
    - inversion H.
  + intros w wInFX.
    have M: mem (cons w nil) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (cons w nil) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    eapply BETA with (V:=D); eauto.
    move: NEX => [ x [ h0 h1]].
    split; auto.
Qed.

(*  Primitive Abstraction followed by Application is the identity --------- *)


(* This is about primitive functions, so skip for now *)


(* Environments ---------------------- *)

Definition Env := GEnv (P Value).

Module EnvNotations.
Notation "ρ ⋅ x" := (access ⌈ v_wrong ⌉ ρ x) (at level 50).
Infix "⊔e" := (map2 Union) (at level 60).
Infix "⊆e" := (all2 Included) (at level 50).
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

Definition sub_env : Env -> Env -> Prop := all2 Included.

Lemma all2_refl {F : P Value -> P Value -> Prop} `{Reflexive _ F} {ρ} : uniq ρ -> all2 F ρ ρ.
Proof. induction 1; eauto. Qed.

#[export] Hint Resolve all2_refl : core.

Lemma Reflexive_sub_env {ρ:Env} : uniq ρ -> ρ ⊆e ρ.
Proof.
  intros. eapply all2_refl; auto.
Qed.

#[export] Hint Resolve Reflexive_sub_env : core.

#[export] Instance Transitive_sub_env : Transitive sub_env.
Proof. typeclasses eauto. Qed.

Lemma extend_sub_env {ρ ρ':Env}{y X} :
  y `notin` dom ρ ->
  ρ ⊆e ρ' -> (y ~ X ++ ρ) ⊆e (y ~ X ++ ρ' ).
Proof. intros; econstructor; eauto. reflexivity. Qed.

(* ---------------------------------------------------- *)

(* Nonempty environments *)

(* This is the same as nonemptyT *)
Definition ne (s : P Value) : Type := { x : Value & (x ∈ s) }.

Definition nonempty_env : Env -> Type := allT ne.

Definition valid_env : Env -> Type := allT valid.

(* A finite environment has a list of values for 
   each variable. *)

Definition finite (X : P Value) : Prop := exists E, (X ≃ mem E) /\ E <> nil.

Definition finite_env : Env -> Type := allT finite.


Lemma extend_nonempty_env {ρ x X} : 
  x `notin` dom ρ ->
  ne X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply allT_cons; eauto. Qed.

Lemma extend_valid_env {ρ x X} : 
  x `notin` dom ρ ->
  valid X -> 
  valid_env ρ -> valid_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply allT_cons; eauto. Qed.

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

Lemma join_lub {ρ ρ1 :Env} :
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
  eapply all2_cons; eauto.
  rewrite sub_dom1. auto.
  rewrite -> H21.
  rewrite -> H13.
  rewrite union_idem.
  reflexivity.
Qed.
  
Lemma join_sub_left {ρ1 ρ2 : Env} : 
  same_scope ρ1 ρ2 ->
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros h.
  induction h; simpl; eauto. 
  destruct (x == x); try done.
  econstructor; eauto. 
Qed.

Lemma join_sub_right {ρ1 ρ2 : Env} : 
  same_scope ρ1 ρ2 ->
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
  induction 1; simpl; eauto. 
  destruct (x == x); try done.
  econstructor; eauto. 
  erewrite all2_dom in H0; eauto.
Qed.

(* --- Monotone --------------- *)

Definition monotone_env (D : Env -> P Value) := 
 forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

(* --- Relations on results and products --------------- *)

(* TODO.
   This part seems to be not connected to the rest. 
   Skipping for now.
*)


(* Continuous ----------------------------------------- *)

Definition continuous_In (D:Env -> P Value) (ρ:Env) (v:Value) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env (D:Env -> P Value) (ρ:Env) : Prop :=
  forall v, continuous_In D ρ v.

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
Definition initial_finite_env (ρ : Env) (NE : valid_env ρ) : Env.
  induction NE. exact nil.
  destruct f as [V _].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [v w]. simpl. congruence.
Qed. 

#[export] Hint Rewrite initial_finite_dom : rewr_list.

Lemma finite_singleton : forall v, finite ⌈ v ⌉.
Proof. intros v.  exists (cons v nil).
       repeat split; eauto. done. 
Qed.

#[export] Hint Resolve finite_singleton : core. 


Lemma initial_fin (ρ : Env) (NE : valid_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [v w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

#[global] Hint Resolve initial_fin : core. 


Lemma initial_fin_sub (ρ : Env) (NE : valid_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [v [wpx _]].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

#[global] Hint Resolve initial_fin_sub : core. 


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Env) 
  (NE : valid_env ρ) : Env :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { v x ρ NE } : 
  finite_env (single_env x ⌈ v ⌉ ρ NE).
Proof.
  induction NE; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. destruct f.
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
    destruct f as [w [h1 h2]]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       simpl_env. auto.
       intros x h. inversion h. subst. auto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. auto.
       intros y h. inversion h. subst. unfold In. auto.
Qed.

#[global] Hint Resolve single_sub : core. 


(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x `in` dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE.
  induction NE; intro h. fsetdec.
  simpl. destruct f. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. econstructor; eauto.
  simpl. rewrite EQ. simpl in h. eapply IHNE; auto. fsetdec.
Qed.  

#[global] Hint Resolve v_single_xvx : core. 



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
    have S1: same_scope ρ1 ρ. eapply all2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply all2_same_scope; eauto. 
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
    have S1: same_scope ρ1 ρ. eapply all2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply all2_same_scope; eauto.
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
    have S1: same_scope ρ1 ρ. eapply all2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply all2_same_scope; eauto.
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
  -> (forall V, V <> nil -> not (v_wrong ∈ mem V) ->
          continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\
            (v ∈ (Λ (fun D => E (x ~ D ++ ρ')))).
Proof.
  induction v.
  all: try solve [intros; cbv in H; done].
  - (* v is l ↦ v *)
    intros [ wEVρ [VN NW] ] IH mE.
    destruct (IH l VN NW v wEVρ) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
    inversion ρ'Vρ. subst. clear ρ'Vρ.
    inversion fρ'. subst. clear fρ'.
    exists E1. exists X.
    repeat split; eauto.
    eapply mE. 2: exact wEρ'.
    have SS: E1 ⊆e E1. eapply Reflexive_sub_env.  eapply all2_uniq1; eauto. 
    auto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.

(*
#[export] Instance Proper_in {A : Type} : Proper (Same_set ==> Logic.eq) (@In A).
intros X1 X2 EQ. unfold In. apply Extensionality_Ensembles in EQ. rewrite EQ.
auto. Qed.

#[export] Instance Proper_nonemptyT {A : Type} : Proper (Same_set ==> Logic.eq) (@nonemptyT A).
intros X1 X2 EQ. unfold nonemptyT.  apply Extensionality_Ensembles in EQ. rewrite EQ.
auto. Qed.
*)

(* Exists *)

Definition ExistsFinite (F : P Value -> P Value) : P Value :=
  fun V => exists W , finite W /\ (V ∈ F W).

Lemma ExistsFinite_ext_sub: forall {F1 F2 : P Value -> Ensemble Value}, 
    (forall X : P Value, nonemptyT X -> F1 X ⊆ F2 X) -> ExistsFinite F1 ⊆ ExistsFinite F2.
Proof.
  intros.
  unfold ExistsFinite, Included.
  intros v [W [[L [W1 W2]] h]].
  apply Extensionality_Ensembles in W1. subst.
  have NL: nonemptyT (mem L) by (eauto using nonnil_nonempty_mem).
  exists (mem L).
  split. unfold finite. exists L; split; auto. reflexivity.
  eapply H; eauto.
Qed.

Lemma ExistsFinite_ext: 
  forall {F1 F2 : P Value -> Ensemble Value}, 
    (forall X : P Value, nonemptyT X -> F1 X ≃ F2 X) 
    -> ExistsFinite F1 ≃ ExistsFinite F2.
Proof.
  intros.
  split.
  eapply ExistsFinite_ext_sub. intros X h. destruct (H X); auto.
  eapply ExistsFinite_ext_sub. intros X h. destruct (H X); auto.
Qed.

Lemma ExistsFinite_continuous {E}{ρ}
  {NE : valid_env ρ}{v x} :
  x `notin` dom ρ
  -> uniq ρ
  -> v ∈ ExistsFinite (fun D => E (x ~ D ++ ρ)) 
  -> (forall V, V <> nil -> 
          continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\
            (v ∈ (ExistsFinite (fun D => E (x ~ D ++ ρ')))).
Proof.
  intros Fx Uρ [X [FX inX]] CE ME.
  move: FX => [V [MV NN]].
  specialize (CE V NN).
  unfold continuous_env, continuous_In in CE.
  have SE: (x ~ X ++ ρ) ⊆e (x ~ mem V ++ ρ).
    econstructor; eauto. rewrite MV. reflexivity.
  unfold monotone_env in ME.
  apply ME in SE. 
  move: (SE _ inX) => inV.
  destruct (CE _ inV) as [ρ' [Fp [h1 h2]]].
  inversion h1. subst.
  inversion Fp. subst.
  exists E1.  eexists. eauto.
  split. auto.
  unfold ExistsFinite.
  unfold "∈".
  exists a1.
  split. auto.
  auto.
Qed.




(* ---------------------------------------------------------- *)

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/ISWIMPValue.agda *)

Import LCNotations.
Open Scope tm.

#[global] Hint Rewrite 
  subst_tm_open_tm_wrt_tm 
  fv_tm_open_tm_wrt_tm_upper  
  size_tm_open_tm_wrt_tm_var : lngen.



(* Find a new variable that isn't in a given set. *)
Definition fresh_for (VS : atoms) := fresh (AtomSetImpl.elements VS).
Lemma fresh_for_fresh : forall x VS, x = fresh_for VS -> x `notin` VS.
Proof.
  intros. unfold fresh_for in H.
  move: (Atom.fresh_not_in (AtomSetImpl.elements VS)) => Frx0.
  rewrite <- H in Frx0.
  intro h.
  apply AtomSetImpl.elements_1 in h.
  eapply InA_In in h.
  done.
Qed.


Lemma tm_induction : forall (P : tm -> Prop), 
    (forall i, P (var_b i)) 
    -> (forall x, P (var_f x)) 
    -> (forall t1 t2, P t1 -> P t2 -> P (app t1 t2))
    -> (forall t, 
          (forall x , x `notin` fv_tm t -> P (t ^ x)) 
          -> P (abs t))
    -> forall t, P t.
Proof.
  intros P VARB VARF APP ABS t.
  remember (size_tm t) as n.
  have GE: n >= size_tm t. subst. auto. clear Heqn.
  move: t GE.
  induction (lt_wf n) as [n _ IH].
  intros [ i | x | u | t ] SZ; simpl in SZ; eauto.
  + eapply ABS.
    intros x FV.
    eapply (IH (size_tm u)). lia.
    autorewrite with lngen.
    lia.
  + eapply APP; eapply IH; eauto. lia. lia.
Qed.    


(* Denotation function: unbound variables have no denotation. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Env) : P Value :=
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
     end
  end.

Import Wf_nat.

Lemma size_is_enough : forall n a, n >= size_tm a -> forall ρ, denot_n n a ρ = denot_n (size_tm a) a ρ.
Proof.
  intros n.
  induction (lt_wf n) as [n _ IH].
  intros a h ρ; destruct a; simpl in *.
  all: try destruct n; simpl; auto; try lia.
  - f_equal.
    extensionality D.
    remember (fresh_for (dom ρ \u fv_tm a)) as x.
    rewrite IH. lia.
    autorewrite with lngen. lia.
    autorewrite with lngen. auto.
  - f_equal.
    rewrite IH. lia. lia.
    rewrite IH. lia. lia.
    auto.
    rewrite IH. lia. lia.
    rewrite IH. lia. lia.
    auto.
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

(* To compute the denotation of an abstraction, we need to first prove a
   renaming lemma. This lemma ensures that the names that we pick for the
   lambda-bound variables don't matter.  *)

Ltac name_binder x0 Frx0 := 
    match goal with 
      [ |- context[fresh_for ?ρ] ] => 
         remember (fresh_for ρ) as x0;
         move: (fresh_for_fresh x0 ρ ltac:(auto)) => Frx0;
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
  all: intros ρ ρ1 ρ2 FV U.
  all: simpl_env in FV; simpl in FV. 
  + repeat rewrite denot_var_b.
    reflexivity.
  + repeat rewrite denot_var.
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
  + repeat rewrite denot_app.    
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

Inductive scoped t (ρ : Env) :=
  scoped_intro : 
    fv_tm t [<=] dom ρ -> uniq ρ -> lc_tm t -> scoped t ρ.

#[global] Hint Constructors scoped : core.

Lemma scoped_app : forall t1 t2 ρ,
    scoped t1 ρ -> scoped t2 ρ -> 
    scoped (app t1 t2) ρ.
Proof.
  intros. inversion H. inversion H0. econstructor; eauto.
  simpl. fsetdec.
Qed.

Lemma scoped_app_inv1 : forall t1 t2 ρ,
    scoped (app t1 t2) ρ ->
    scoped t1 ρ.
Proof.
  intros. inversion H.
  simpl in *. inversion H2.
  econstructor; eauto. 
  fsetdec.
Qed.

Lemma scoped_app_inv2 : forall t1 t2 ρ,
    scoped (app t1 t2) ρ ->
    scoped t2 ρ.
Proof.
  intros. inversion H.
  simpl in *. inversion H2.
  econstructor; eauto. 
  fsetdec.
Qed.

Lemma scoped_abs : forall x t1 D ρ, 
  x `notin` dom ρ \u fv_tm t1
  -> scoped (t1 ^ x) (x ~ D ++ ρ)
  -> scoped (abs t1) ρ.
Proof. 
  intros. destruct H0.
  simpl_env in s.
  rewrite <- fv_tm_open_tm_wrt_tm_lower in s.
  destruct_uniq.
  constructor. simpl. fsetdec.
  auto.
  eapply (lc_abs_exists x).
  auto.
Qed.

Lemma scoped_abs_inv : forall x t1 D ρ, 
  x `notin` dom ρ \u fv_tm t1
  -> scoped (abs t1) ρ
  -> scoped (t1 ^ x) (x ~ D ++ ρ).
Proof.
  intros.
  destruct H0. simpl in s. inversion l.
  econstructor; eauto.
  autorewrite with lngen.
  simpl_env.
  subst.
  simpl. fsetdec.
Qed.

Lemma subst_denot : forall t x u ρ1 ρ2, 
    scoped t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) ->
    scoped u ρ2 ->
    denot t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) =
    denot (t [x ~> u]) (ρ1 ++ ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH].
  all: intros x u ρ1 ρ2 ST SU.
  + simpl. repeat rewrite denot_var_b. reflexivity.
  + destruct (y == x) eqn:EQ. subst.
    ++ have NI: x `notin` dom ρ1.
       { inversion ST. destruct_uniq. auto. }
       have D2: fv_tm u [<=] dom ρ2. 
       { inversion SU. auto. }
       have U2: uniq (ρ1 ++ ρ2). 
       { inversion ST. solve_uniq. }
       rewrite subst_eq_var.
       rewrite denot_var.
       rewrite access_app_fresh; auto.       
       rewrite access_eq_var.
       apply weaken_denot; eauto.
    ++ rewrite subst_neq_var; auto.
       repeat rewrite denot_var.
       destruct (access_app_P ρ1 y) as [h1 | h2].
       repeat rewrite h1. auto.
       move: (h2 ρ2) => [N1 ->]. 
       move: (h2 (x ~ denot u ρ2 ++ ρ2)) => [N3 ->].
       rewrite access_neq_var; auto.
  + move: (scoped_app_inv1 _ _ _ ST) => S1.
    move: (scoped_app_inv2 _ _ _ ST) => S2.
    simpl. repeat rewrite denot_app.
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
Qed.

(* ------------------------------------ *)

(* denotational_semantics/agda/SemanticProperties.agda  *)

(* Note: sub_env forces ρ and ρ' to have the same domain *)


Lemma access_monotone {ρ ρ':Env}{x} : ρ ⊆e ρ' -> ρ ⋅ x ⊆ ρ' ⋅ x.
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
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH].
 all: intros ρ ρ' S.
  + repeat rewrite denot_var_b. 
    reflexivity.
  + repeat rewrite denot_var.
    eapply access_monotone; auto.
  + repeat rewrite denot_app.
    eapply APPLY_mono_sub; eauto.
  + pick fresh x.
    repeat rewrite (denot_abs x).
    fsetdec.
    fsetdec.
    eapply Λ_ext_sub.
    intros X NE.
    eapply IH. fsetdec.
    eapply extend_sub_env; eauto. 
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
  
(* ⟦⟧-continuous *)
Lemma denot_continuous {t} : forall ρ,
    valid_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH].
  all: intros ρ NE.
  all: intros v vIn.
  + rewrite denot_var_b in vIn. 
    exists (initial_finite_env ρ NE).
    eexists; eauto.
  + rewrite denot_var in vIn.
    destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
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
  + rewrite denot_app in vIn.
    edestruct (APPLY_continuous NE vIn) as [ρ' [F SS]]; eauto.
    eapply denot_monotone.
    eapply denot_monotone.
    exists ρ'. exists F.
    rewrite denot_app. auto.
  + pick fresh x.
    rewrite (denot_abs x) in vIn. fsetdec.
    move: (@Lambda_continuous _ _ NE v x vIn) => h.    
    destruct h as [ρ' [Fρ' [S vvIn]]].
    ++ intros V NEV NW.
       move: (nonnil_nonempty_mem NEV) => [w h0]. 
       eapply IH; eauto.
       eapply extend_valid_env; eauto.
       econstructor; eauto.
    ++ eapply denot_monotone.
    ++ exists ρ'. exists Fρ'. 
       erewrite <- all2_dom in Fr. 2: eapply S.
       rewrite (denot_abs x). fsetdec.
       split; auto.
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

Definition Same_env : Env -> Env -> Prop := all2 Same_set.

(* The denotation respects ≃ *)
Instance Proper_denot : Proper (eq ==> Same_env ==> Same_set) denot.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH].
  all: move => ρ1 ρ2 EQ.
  - repeat rewrite denot_var_b. reflexivity.
  - repeat rewrite denot_var.
    destruct (FSetDecideAuxiliary.dec_In  x (dom ρ1)).
    + apply all2_access with (f := Same_set); auto.
    + rewrite access_fresh. auto.
      rewrite access_fresh. erewrite all2_dom in H; eauto.
      reflexivity.
  - repeat rewrite denot_app. 
    eauto using APPLY_cong.
  - pick fresh x. 
    repeat rewrite (denot_abs x). fsetdec. fsetdec.
    eapply Λ_ext.
    intros X neX.
    eapply IH; eauto.
    econstructor; eauto. 
    reflexivity. 
Qed.

(* The denotation respects ⊆ *)
Instance Proper_sub_denot : Proper (eq ==> all2 Included ==> Included) denot.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH].
  all: move => ρ1 ρ2 SUB.
  - repeat rewrite denot_var_b. reflexivity.
  - repeat rewrite denot_var.
    destruct (FSetDecideAuxiliary.dec_In  x (dom ρ1)).
    + apply all2_access with (f := Included); auto.
    + rewrite access_fresh. auto.
      rewrite access_fresh. erewrite all2_dom in H; eauto.
      reflexivity.
  - repeat rewrite denot_app.  
    eauto using APPLY_mono_sub.
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
    have SUB: all2 Included (x ~ a1 ++ E1) (x ~ mem D ++ ρ).
    econstructor; eauto. 
    rewrite <- S. reflexivity.
    rewrite <- SUB.
    auto.
    auto.
Qed.

Print monotone.
(* fun F : P Value -> P Value => 
   forall D1 D2 : Ensemble Value, D1 ⊆ D2 -> F D1 ⊆ F D2  *)
Print monotone_env.
(* fun D : Env -> P Value => forall ρ ρ' : list (atom * Ensemble Value), 
   ρ ⊆e ρ' -> D ρ ⊆ D ρ' *)


(*
Lemma denot_strict : forall t, strict (denot t).
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH].
*)

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
    eapply allT_uniq; eauto.
Qed.

(* Example semantics *)


Definition tm_Id : tm := abs (var_b 0).

Lemma denot_Id : ( v_fun :: nil ↦ v_fun) ∈ denot tm_Id nil.
Proof.
  unfold tm_Id.
  pick fresh x.
  rewrite (denot_abs x). simpl. auto.
  cbv.
  destruct (KeySetFacts.eq_dec x x); try done.
  split. left. auto.
  split. intro h. done. 
  intros [v1| v2]; done.
Qed. 

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).

Lemma denot_Delta : forall (v w : Value), v <> v_wrong ->
    (((v :: nil ↦ w) :: v :: nil) ↦ w) ∈ denot tm_Delta nil.
Proof.
  intros v w NW.
  pick fresh x.
  unfold tm_Delta.
  rewrite (denot_abs x); auto.
  cbn.
  destruct (x==x); try done.
  split.
  cbv.
  eapply BETA with (V := v :: nil).
  unfold In. left. auto.
  rewrite -> mem_singleton. 
  intros x0 II. inversion II. subst. cbv. right. left. auto.
  intro h. done.
  split. intro h. done.
  intros [v1|[v2|v3]]; try done.
Qed.

Lemma open_app : forall t1 t2 x, 
    (app t1 t2) ^ x = app (t1 ^ x) (t2 ^ x).
Proof. intros. reflexivity. Qed.

Lemma open_var : forall x, (var_b 0) ^ x = var_f x.
Proof. intros. reflexivity. Qed.


Definition tm_Omega : tm := app tm_Delta tm_Delta.

Lemma denot_Omega : forall v, not (v ∈ denot tm_Omega nil).
Proof.
  intro v.
  unfold tm_Omega.
  rewrite denot_app.
  unfold tm_Delta.
  pick fresh x.
  repeat rewrite (denot_abs x). auto.
  repeat rewrite open_app.
  repeat rewrite open_var.  
  intro h. unfold In in h. inversion h; simpl in *; subst; clear h.
  all: try solve [unfold Λ in H; cbv in H; done].
  destruct V as [|w V]. done.
  rename H into DD. rename H0 into h1.
  unfold "∈" in DD.
  unfold Λ in *.
  rewrite denot_app in DD, h1.
  rewrite denot_var in DD.
  rewrite access_eq_var in DD.
  move: DD => [DD _].
  unfold mem in h1.
  unfold Included in h1.
  specialize (h1 w).
  unfold "∈" in h1.
  specialize (h1 (in_eq _ _)).
  destruct w; try done.
  + rewrite denot_app in h1.
    rewrite denot_var in h1.
    rewrite access_eq_var in h1.
    move: h1 => [h3 h4].
Abort.

Lemma in_singleton {A:Type} {v : A} : 
  v ∈ ⌈ v ⌉.
Proof. unfold In. econstructor. Qed.

#[export] Hint Resolve in_singleton : core.

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
  destruct t.
  all: try solve [assert False; try inversion vv; done].
  + rewrite denot_var.
    unfold nonempty_env in NEρ.
    eapply (@allT_access _ ⌈ v_wrong ⌉ _ _) in NEρ.
    2: instantiate (1:= x); auto.
    destruct NEρ. exists x0. auto.
    simpl in FV. fsetdec.
  + pick fresh x.
    erewrite denot_abs with (x:=x); eauto.
    exists v_fun. cbn. auto.
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
    rewrite (subst_tm_intro x t u); auto.
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
Qed.

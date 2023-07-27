(* Definitions over P Values respect ⊆ and ≃ *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Import structures.Structures.
Require Export lc.tactics.
Require Import lc.scoped.

(* Definitions *)
Require Import denot.definitions.
Require Import denot.denot.
Require Import denot.valid_theory.  

Import SetNotations.
Local Open Scope set_scope.

Import EnvNotations.
Import LCNotations.

(*  Application is a Congruence ------------------------------------------------ *)

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

#[export] Instance Proper_Included_CONS : Proper (Included ==> Included ==> Included) CONS. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply CONS_mono_sub; eauto. Qed.

#[export] Instance Proper_Same_CONS : Proper (Same_set ==> Same_set ==> Same_set) CONS. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply CONS_cong; eauto. Qed.


(*  Application is a Congruence ------------------------------------------------ *)
                          

Lemma APPLY_mono_sub { D1 D2 D3 D4 } :
    D1 ⊆ D3 -> D2 ⊆ D4 -> ((D1 ▩ D2) ⊆ (D3 ▩ D4)).
Proof.  
  intros D13 D24 w APP. 
  inversion APP; subst; unfold Included in *.
  + apply BETA with (V:=V); eauto.
    intros d z. eauto.
  + apply PROJ with (VS := VS) (k := k); eauto.
  + eapply APPWRONG; eauto.
  + eapply PROJWRONG; eauto.
Qed.

Lemma APPLY_cong { D1 D2 D3 D4 } :
    D1 ≃ D3 -> D2 ≃ D4 -> ((D1 ▩ D2) ≃ (D3 ▩ D4)).
Proof.
  intros [ d13 d31 ] [ d24 d42 ].
  split; eapply APPLY_mono_sub; eauto.
Qed.

#[export] Instance Proper_Included_APPLY : Proper (Included ==> Included ==> Included) APPLY. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply APPLY_mono_sub; eauto. Qed.

#[export] Instance Proper_Same_APPLY : Proper (Same_set ==> Same_set ==> Same_set) APPLY. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply APPLY_cong; eauto. Qed.


(*  Abstraction is Extensional ---- -------------------------------------- *)

(* Λ-ext-⊆  *)

(* NOTE: By restricting the hypothesis to only valid sets, we strengthen 
   the result. But this depends on the definition of Λ which quantifies
   over valid sets (i.e. CBV) *)
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

(* ---------------------------------------------------- *)

(* Sub environments ⊆e *)

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

#[export] Hint Resolve extend_sub_env : core.

(* ---------------------------------------------------- *)

(* Why can we not get rid of this???? *)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).


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

(* The denotation respects ⊆ *)
#[export] Instance Proper_sub_denot : Proper (eq ==> Env.Forall2 Included ==> Included) denot.
Proof.
  intros t1 t ->.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: move => ρ1 ρ2 SUB.
  all: autorewrite with denot.
  all: try solve [reflexivity].
  - eapply RET2_monotone. eapply access_mono_sub; eauto.
  - eapply BIND2_mono.
    eapply IH1. auto.
    intros x.
    eapply BIND2_mono.
    eapply IH2. auto.
    intros y.
    eapply APPLY_mono_sub. reflexivity. reflexivity.
  - pick fresh x. 
    repeat rewrite(denot_abs x). fsetdec. fsetdec.
    eapply RET2_monotone.
    eapply Λ_ext_sub.
    intros X neX.
    eapply IH. fsetdec.
    econstructor; eauto.
    reflexivity.
  - eapply BIND2_mono.
    eapply IH1. auto.
    intros x.
    eapply BIND2_mono.
    eapply IH2. auto.
    intros y.
    eapply RET2_monotone.
    eapply CONS_mono_sub. reflexivity. reflexivity.
Qed.

(* TODO: move???*)
Lemma same_env_sub_env : forall x y, same_env x y <-> (x ⊆e y) /\ (y ⊆e x).
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

(* The denotation respects ≃ *)
#[export] Instance Proper_denot : Proper (eq ==> same_env ==> Same_set) denot.
Proof.
  intros t1 t ->.
  intros x y E.
  rewrite same_env_sub_env in E. destruct E. 
  split. eapply Proper_sub_denot; auto. 
  eapply Proper_sub_denot; auto.
Qed. 


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


(* ---------------------------------------------------------------- *)

Lemma RET_mono {A} : forall (U V : P A), 
 U ⊆ V -> RET U ⊆ RET V. 
Proof. 
    intros U V h x xIn.
    unfold Included in h.
    destruct x; simpl in *; eauto.
    destruct l as [| y t]; try done.
    destruct t; try done.
    unfold RET in *. cbn in *.
    unfold Included in xIn.
    intros x. 
    eauto.
Qed.

(*
Lemma RET_sub_reflecting {A} : forall (U V : P A), 
  RET U ⊆ RET V -> U ⊆ V.
Proof. 
  intros U V h x xIn.
  unfold RET in h.
  specialize (h (c_multi ((x :: nil) :: nil))). cbn in h.
  rewrite mem_singleton_eq in h.
Abort. 
*)

#[export] Instance Proper_Included_RET {A} : Proper (Included ==> Included) 
                                               (@RET (P A)).
unfold Proper. intros x1 y1 E1. eapply RET_mono. auto. Qed.

#[export] Instance Proper_Same_RET {A} : Proper (Same_set ==> Same_set) (@RET (P A)).
unfold Proper. intros x1 y1 E1. split. eapply RET_mono. rewrite E1. reflexivity.
eapply  RET_mono. rewrite E1. reflexivity.
Qed.

Lemma BIND_mono {A B} : forall (D1 D2 : P (Comp (list A))) (K1 K2 : P A -> P (Comp B)),
  D1 ⊆ D2 -> (forall x, K1 x ⊆ K2 x) ->
  BIND D1 K1 ⊆ BIND D2 K2.
Proof. 
  intros.
  unfold BIND.
  move=> x [U [h1 [h2 [-> h4]]]].
  destruct U; simpl.
  -  exists c_wrong.
     exists h1.
     split.
     specialize (H _ h2).
     simpl in H. done.
     split.
     cbv.
     done.
     intros a aIn.
     specialize (h4 _ aIn).
     specialize (H0 (mem a)). 
     specialize (H0 (h1 a) h4).
     eauto.
  - exists (c_multi l).
    exists h1. 
    repeat split; eauto.
    eapply H; auto.
    intros a aIn. eapply H0. eapply h4. auto.
Qed.

#[export] Instance Proper_Included_BIND {A B} : 
  Proper (Included ==> Logic.eq ==> Included) (@BIND A B).
intros x1 y1 E1 x2 y2 ->. 
eapply BIND_mono; eauto. reflexivity.
Qed. 

#[export] Instance Proper_Same_BIND {A B} : Proper (Same_set ==> Logic.eq ==> Same_set) (@BIND A B).
unfold Proper. intros x1 y1 E1 x2 y2 ->. split. eapply BIND_mono. rewrite E1. reflexivity. reflexivity.
eapply  BIND_mono. rewrite E1. reflexivity. reflexivity.
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
  - eapply RET_mono. eapply access_mono_sub; eauto.
  - eapply BIND_mono.
    eapply IH1. auto.
    intros x.
    eapply BIND_mono.
    eapply IH2. auto.
    intros y.
    eapply APPLY_mono_sub. reflexivity. reflexivity.
  - pick fresh x. 
    repeat rewrite(denot_abs x). fsetdec. fsetdec.
    eapply RET_mono.
    eapply Λ_ext_sub.
    intros X neX.
    eapply IH. fsetdec.
    econstructor; eauto.
    reflexivity.
  - eapply BIND_mono.
    eapply IH1. auto.
    intros x.
    eapply BIND_mono.
    eapply IH2. auto.
    intros y.
    eapply RET_mono.
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



Lemma monotone_env_denot_val {t} : monotone_env (denot_val t).
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: move => ρ1 ρ2 SUB.
  all: autorewrite with denot.
  all: try solve  [ simpl; reflexivity].
  + eapply access_mono_sub; eauto.
  + pick fresh x. 
    repeat rewrite(denot_val_abs x). fsetdec. fsetdec.
    eapply Λ_ext_sub.
    intros X neX.
    have SUBe: (x ~ X ++ ρ1) ⊆e (x ~ X ++ ρ2).
    econstructor; eauto. reflexivity.
    eapply Proper_sub_denot; eauto. 
  + eapply CONS_mono_sub; eauto.
Qed. 

#[export] Instance Proper_sub_denot_val : Proper (eq ==> Env.Forall2 Included ==> Included) denot_val.
Proof.
  intros t1 t ->.
  eapply monotone_env_denot_val.
Qed.


Require Export lc.tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import lc.SetsAsPredicates.

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



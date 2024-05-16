Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export lc_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme primitive_ind' := Induction for primitive Sort Prop.

Combined Scheme primitive_mutind from primitive_ind'.

Scheme primitive_rec' := Induction for primitive Sort Set.

Combined Scheme primitive_mutrec from primitive_rec'.

Scheme tm_ind' := Induction for tm Sort Prop.

Combined Scheme tm_mutind from tm_ind'.

Scheme tm_rec' := Induction for tm Sort Set.

Combined Scheme tm_mutrec from tm_rec'.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : tmvar) (t1 : tm) {struct t1} : tm :=
  match t1 with
    | var_f x2 => if (x1 == x2) then (var_b n1) else (var_f x2)
    | var_b n2 => if (lt_ge_dec n2 n1) then (var_b n2) else (var_b (S n2))
    | abs t2 => abs (close_tm_wrt_tm_rec (S n1) x1 t2)
    | app t2 u1 => app (close_tm_wrt_tm_rec n1 x1 t2) (close_tm_wrt_tm_rec n1 x1 u1)
    | lit k1 => lit k1
    | prim primitive1 => prim primitive1
    | tnil => tnil
    | tcons t2 u1 => tcons (close_tm_wrt_tm_rec n1 x1 t2) (close_tm_wrt_tm_rec n1 x1 u1)
    | choice t2 t3 => choice (close_tm_wrt_tm_rec n1 x1 t2) (close_tm_wrt_tm_rec n1 x1 t3)
    | fail => fail
    | ex t2 => ex (close_tm_wrt_tm_rec (S n1) x1 t2)
    | seq t2 t3 => seq (close_tm_wrt_tm_rec n1 x1 t2) (close_tm_wrt_tm_rec n1 x1 t3)
    | unify t2 t3 => unify (close_tm_wrt_tm_rec n1 x1 t2) (close_tm_wrt_tm_rec n1 x1 t3)
    | one t2 => one (close_tm_wrt_tm_rec n1 x1 t2)
    | all t2 => all (close_tm_wrt_tm_rec n1 x1 t2)
  end.

Definition close_tm_wrt_tm x1 t1 := close_tm_wrt_tm_rec 0 x1 t1.


(* *********************************************************************** *)
(** * Size *)

Definition size_j (j1 : j) : nat := 1
.

Fixpoint size_primitive (primitive1 : primitive) {struct primitive1} : nat :=
  match primitive1 with
    | p_add => 1
    | p_dec => 1
  end.

Fixpoint size_tm (t1 : tm) {struct t1} : nat :=
  match t1 with
    | var_f x1 => 1
    | var_b n1 => 1
    | abs t2 => 1 + (size_tm t2)
    | app t2 u1 => 1 + (size_tm t2) + (size_tm u1)
    | lit k1 => 1 + (size_j k1)
    | prim primitive1 => 1 + (size_primitive primitive1)
    | tnil => 1
    | tcons t2 u1 => 1 + (size_tm t2) + (size_tm u1)
    | choice t2 t3 => 1 + (size_tm t2) + (size_tm t3)
    | fail => 1
    | ex t2 => 1 + (size_tm t2)
    | seq t2 t3 => 1 + (size_tm t2) + (size_tm t3)
    | unify t2 t3 => 1 + (size_tm t2) + (size_tm t3)
    | one t2 => 1 + (size_tm t2)
    | all t2 => 1 + (size_tm t2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_tm_wrt_tm : nat -> tm -> Prop :=
  | degree_wrt_tm_var_f : forall n1 x1,
    degree_tm_wrt_tm n1 (var_f x1)
  | degree_wrt_tm_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_tm_wrt_tm n1 (var_b n2)
  | degree_wrt_tm_abs : forall n1 t1,
    degree_tm_wrt_tm (S n1) t1 ->
    degree_tm_wrt_tm n1 (abs t1)
  | degree_wrt_tm_app : forall n1 t1 u1,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 u1 ->
    degree_tm_wrt_tm n1 (app t1 u1)
  | degree_wrt_tm_lit : forall n1 k1,
    degree_tm_wrt_tm n1 (lit k1)
  | degree_wrt_tm_prim : forall n1 primitive1,
    degree_tm_wrt_tm n1 (prim primitive1)
  | degree_wrt_tm_tnil : forall n1,
    degree_tm_wrt_tm n1 (tnil)
  | degree_wrt_tm_tcons : forall n1 t1 u1,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 u1 ->
    degree_tm_wrt_tm n1 (tcons t1 u1)
  | degree_wrt_tm_choice : forall n1 t1 t2,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 t2 ->
    degree_tm_wrt_tm n1 (choice t1 t2)
  | degree_wrt_tm_fail : forall n1,
    degree_tm_wrt_tm n1 (fail)
  | degree_wrt_tm_ex : forall n1 t1,
    degree_tm_wrt_tm (S n1) t1 ->
    degree_tm_wrt_tm n1 (ex t1)
  | degree_wrt_tm_seq : forall n1 t1 t2,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 t2 ->
    degree_tm_wrt_tm n1 (seq t1 t2)
  | degree_wrt_tm_unify : forall n1 t1 t2,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 t2 ->
    degree_tm_wrt_tm n1 (unify t1 t2)
  | degree_wrt_tm_one : forall n1 t1,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 (one t1)
  | degree_wrt_tm_all : forall n1 t1,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 (all t1).

Scheme degree_tm_wrt_tm_ind' := Induction for degree_tm_wrt_tm Sort Prop.

Combined Scheme degree_tm_wrt_tm_mutind from degree_tm_wrt_tm_ind'.

#[export] Hint Constructors degree_tm_wrt_tm : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_tm : tm -> Set :=
  | lc_set_var_f : forall x1,
    lc_set_tm (var_f x1)
  | lc_set_abs : forall t1,
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm t1 (var_f x1))) ->
    lc_set_tm (abs t1)
  | lc_set_app : forall t1 u1,
    lc_set_tm t1 ->
    lc_set_tm u1 ->
    lc_set_tm (app t1 u1)
  | lc_set_lit : forall k1,
    lc_set_tm (lit k1)
  | lc_set_prim : forall primitive1,
    lc_set_tm (prim primitive1)
  | lc_set_tnil :
    lc_set_tm (tnil)
  | lc_set_tcons : forall t1 u1,
    lc_set_tm t1 ->
    lc_set_tm u1 ->
    lc_set_tm (tcons t1 u1)
  | lc_set_choice : forall t1 t2,
    lc_set_tm t1 ->
    lc_set_tm t2 ->
    lc_set_tm (choice t1 t2)
  | lc_set_fail :
    lc_set_tm (fail)
  | lc_set_ex : forall t1,
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm t1 (var_f x1))) ->
    lc_set_tm (ex t1)
  | lc_set_seq : forall t1 t2,
    lc_set_tm t1 ->
    lc_set_tm t2 ->
    lc_set_tm (seq t1 t2)
  | lc_set_unify : forall t1 t2,
    lc_set_tm t1 ->
    lc_set_tm t2 ->
    lc_set_tm (unify t1 t2)
  | lc_set_one : forall t1,
    lc_set_tm t1 ->
    lc_set_tm (one t1)
  | lc_set_all : forall t1,
    lc_set_tm t1 ->
    lc_set_tm (all t1).

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop.

Combined Scheme lc_tm_mutind from lc_tm_ind'.

Scheme lc_set_tm_ind' := Induction for lc_set_tm Sort Prop.

Combined Scheme lc_set_tm_mutind from lc_set_tm_ind'.

Scheme lc_set_tm_rec' := Induction for lc_set_tm Sort Set.

Combined Scheme lc_set_tm_mutrec from lc_set_tm_rec'.

#[export] Hint Constructors lc_tm : core lngen.

#[export] Hint Constructors lc_set_tm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_tm_wrt_tm t1 := forall x1, lc_tm (open_tm_wrt_tm t1 (var_f x1)).

#[export] Hint Unfold body_tm_wrt_tm : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

(* #[export] Hint Resolve plus_le_compat : lngen. *)

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_j_min_mutual :
(forall j1, 1 <= size_j j1).
Proof. Admitted.

(* end hide *)

Lemma size_j_min :
forall j1, 1 <= size_j j1.
Proof. Admitted.

#[export] Hint Resolve size_j_min : lngen.

(* begin hide *)

Lemma size_primitive_min_mutual :
(forall primitive1, 1 <= size_primitive primitive1).
Proof. Admitted.

(* end hide *)

Lemma size_primitive_min :
forall primitive1, 1 <= size_primitive primitive1.
Proof. Admitted.

#[export] Hint Resolve size_primitive_min : lngen.

(* begin hide *)

Lemma size_tm_min_mutual :
(forall t1, 1 <= size_tm t1).
Proof. Admitted.

(* end hide *)

Lemma size_tm_min :
forall t1, 1 <= size_tm t1.
Proof. Admitted.

#[export] Hint Resolve size_tm_min : lngen.

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 t1) = size_tm t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 t1) = size_tm t1.
Proof. Admitted.

#[export] Hint Resolve size_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_close_tm_wrt_tm :
forall t1 x1,
  size_tm (close_tm_wrt_tm x1 t1) = size_tm t1.
Proof. Admitted.

#[export] Hint Resolve size_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_mutual :
(forall t1 t2 n1,
  size_tm t1 <= size_tm (open_tm_wrt_tm_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec :
forall t1 t2 n1,
  size_tm t1 <= size_tm (open_tm_wrt_tm_rec n1 t2 t1).
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm :
forall t1 t2,
  size_tm t1 <= size_tm (open_tm_wrt_tm t1 t2).
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var_mutual :
(forall t1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (var_f x1) t1) = size_tm t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var :
forall t1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (var_f x1) t1) = size_tm t1.
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm_var :
forall t1 x1,
  size_tm (open_tm_wrt_tm t1 (var_f x1)) = size_tm t1.
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_tm_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_tm_wrt_tm_S_mutual :
(forall n1 t1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) t1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_tm_S :
forall n1 t1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) t1.
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_S : lngen.

Lemma degree_tm_wrt_tm_O :
forall n1 t1,
  degree_tm_wrt_tm O t1 ->
  degree_tm_wrt_tm n1 t1.
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_O : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm :
forall t1 x1,
  degree_tm_wrt_tm 0 t1 ->
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 t1).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_mutual :
(forall t1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1) ->
  degree_tm_wrt_tm n1 t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv :
forall t1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1) ->
  degree_tm_wrt_tm n1 t1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_inv :
forall t1 x1,
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 t1) ->
  degree_tm_wrt_tm 0 t1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_inv : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_mutual :
(forall t1 t2 n1,
  degree_tm_wrt_tm (S n1) t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec :
forall t1 t2 n1,
  degree_tm_wrt_tm (S n1) t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm :
forall t1 t2,
  degree_tm_wrt_tm 1 t1 ->
  degree_tm_wrt_tm 0 t2 ->
  degree_tm_wrt_tm 0 (open_tm_wrt_tm t1 t2).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_mutual :
(forall t1 t2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1) ->
  degree_tm_wrt_tm (S n1) t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv :
forall t1 t2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1) ->
  degree_tm_wrt_tm (S n1) t1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_inv :
forall t1 t2,
  degree_tm_wrt_tm 0 (open_tm_wrt_tm t1 t2) ->
  degree_tm_wrt_tm 1 t1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj_mutual :
(forall t1 t2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 t1 = close_tm_wrt_tm_rec n1 x1 t2 ->
  t1 = t2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj :
forall t1 t2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 t1 = close_tm_wrt_tm_rec n1 x1 t2 ->
  t1 = t2.
Proof. Admitted.

#[export] Hint Immediate close_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_inj :
forall t1 t2 x1,
  close_tm_wrt_tm x1 t1 = close_tm_wrt_tm x1 t2 ->
  t1 = t2.
Proof. Admitted.

#[export] Hint Immediate close_tm_wrt_tm_inj : lngen.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (var_f x1) t1) = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall t1 x1 n1,
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (var_f x1) t1) = t1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_rec_open_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_open_tm_wrt_tm :
forall t1 x1,
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm x1 (open_tm_wrt_tm t1 (var_f x1)) = t1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_open_tm_wrt_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_open_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  open_tm_wrt_tm_rec n1 (var_f x1) (close_tm_wrt_tm_rec n1 x1 t1) = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  open_tm_wrt_tm_rec n1 (var_f x1) (close_tm_wrt_tm_rec n1 x1 t1) = t1.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_rec_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_rec_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_close_tm_wrt_tm :
forall t1 x1,
  open_tm_wrt_tm (close_tm_wrt_tm x1 t1) (var_f x1) = t1.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj_mutual :
(forall t2 t1 x1 n1,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 (var_f x1) t2 = open_tm_wrt_tm_rec n1 (var_f x1) t1 ->
  t2 = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj :
forall t2 t1 x1 n1,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 (var_f x1) t2 = open_tm_wrt_tm_rec n1 (var_f x1) t1 ->
  t2 = t1.
Proof. Admitted.

#[export] Hint Immediate open_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_inj :
forall t2 t1 x1,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm t2 (var_f x1) = open_tm_wrt_tm t1 (var_f x1) ->
  t2 = t1.
Proof. Admitted.

#[export] Hint Immediate open_tm_wrt_tm_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_of_lc_tm_mutual :
(forall t1,
  lc_tm t1 ->
  degree_tm_wrt_tm 0 t1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_tm_of_lc_tm :
forall t1,
  lc_tm t1 ->
  degree_tm_wrt_tm 0 t1.
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_of_lc_tm : lngen.

(* begin hide *)

Lemma lc_tm_of_degree_size_mutual :
forall i1,
(forall t1,
  size_tm t1 = i1 ->
  degree_tm_wrt_tm 0 t1 ->
  lc_tm t1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_degree :
forall t1,
  degree_tm_wrt_tm 0 t1 ->
  lc_tm t1.
Proof. Admitted.

#[export] Hint Resolve lc_tm_of_degree : lngen.

Ltac j_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac primitive_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac tm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_tm_wrt_tm_of_lc_tm in J1; clear H
          end).

Lemma lc_abs_exists :
forall x1 t1,
  lc_tm (open_tm_wrt_tm t1 (var_f x1)) ->
  lc_tm (abs t1).
Proof. Admitted.

Lemma lc_ex_exists :
forall x1 t1,
  lc_tm (open_tm_wrt_tm t1 (var_f x1)) ->
  lc_tm (ex t1).
Proof. Admitted.

#[export] Hint Extern 1 (lc_tm (abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (ex _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ex_exists x1) : core.

Lemma lc_body_tm_wrt_tm :
forall t1 t2,
  body_tm_wrt_tm t1 ->
  lc_tm t2 ->
  lc_tm (open_tm_wrt_tm t1 t2).
Proof. Admitted.

#[export] Hint Resolve lc_body_tm_wrt_tm : lngen.

Lemma lc_body_abs_1 :
forall t1,
  lc_tm (abs t1) ->
  body_tm_wrt_tm t1.
Proof. Admitted.

#[export] Hint Resolve lc_body_abs_1 : lngen.

Lemma lc_body_ex_1 :
forall t1,
  lc_tm (ex t1) ->
  body_tm_wrt_tm t1.
Proof. Admitted.

#[export] Hint Resolve lc_body_ex_1 : lngen.

(* begin hide *)

Lemma lc_tm_unique_mutual :
(forall t1 (proof2 proof3 : lc_tm t1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_unique :
forall t1 (proof2 proof3 : lc_tm t1), proof2 = proof3.
Proof. Admitted.

#[export] Hint Resolve lc_tm_unique : lngen.

(* begin hide *)

Lemma lc_tm_of_lc_set_tm_mutual :
(forall t1, lc_set_tm t1 -> lc_tm t1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_lc_set_tm :
forall t1, lc_set_tm t1 -> lc_tm t1.
Proof. Admitted.

#[export] Hint Resolve lc_tm_of_lc_set_tm : lngen.

(* begin hide *)

Lemma lc_set_tm_of_lc_tm_size_mutual :
forall i1,
(forall t1,
  size_tm t1 = i1 ->
  lc_tm t1 ->
  lc_set_tm t1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_tm_of_lc_tm :
forall t1,
  lc_tm t1 ->
  lc_set_tm t1.
Proof. Admitted.

#[export] Hint Resolve lc_set_tm_of_lc_tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 t1 = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 t1 = t1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_lc_tm :
forall t1 x1,
  lc_tm t1 ->
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm x1 t1 = t1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_lc_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_lc_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall t2 t1 n1,
  degree_tm_wrt_tm n1 t2 ->
  open_tm_wrt_tm_rec n1 t1 t2 = t2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall t2 t1 n1,
  degree_tm_wrt_tm n1 t2 ->
  open_tm_wrt_tm_rec n1 t1 t2 = t2.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_lc_tm :
forall t2 t1,
  lc_tm t2 ->
  open_tm_wrt_tm t2 t1 = t2.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_lc_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_lc_tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  fv_tm (close_tm_wrt_tm_rec n1 x1 t1) [=] remove x1 (fv_tm t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  fv_tm (close_tm_wrt_tm_rec n1 x1 t1) [=] remove x1 (fv_tm t1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_tm_close_tm_wrt_tm :
forall t1 x1,
  fv_tm (close_tm_wrt_tm x1 t1) [=] remove x1 (fv_tm t1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_lower_mutual :
(forall t1 t2 n1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_tm_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_lower :
forall t1 t2 n1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_tm_rec n1 t2 t1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

Lemma fv_tm_open_tm_wrt_tm_lower :
forall t1 t2,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_tm t1 t2).
Proof. Admitted.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_upper_mutual :
(forall t1 t2 n1,
  fv_tm (open_tm_wrt_tm_rec n1 t2 t1) [<=] fv_tm t2 `union` fv_tm t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_upper :
forall t1 t2 n1,
  fv_tm (open_tm_wrt_tm_rec n1 t2 t1) [<=] fv_tm t2 `union` fv_tm t1.
Proof. Admitted.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

Lemma fv_tm_open_tm_wrt_tm_upper :
forall t1 t2,
  fv_tm (open_tm_wrt_tm t1 t2) [<=] fv_tm t2 `union` fv_tm t1.
Proof. Admitted.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_upper : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_fresh_mutual :
(forall t1 t2 x1,
  x1 `notin` fv_tm t1 ->
  fv_tm (subst_tm t2 x1 t1) [=] fv_tm t1).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_subst_tm_fresh :
forall t1 t2 x1,
  x1 `notin` fv_tm t1 ->
  fv_tm (subst_tm t2 x1 t1) [=] fv_tm t1.
Proof. Admitted.

#[export] Hint Resolve fv_tm_subst_tm_fresh : lngen.
#[export] Hint Rewrite fv_tm_subst_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_lower_mutual :
(forall t1 t2 x1,
  remove x1 (fv_tm t1) [<=] fv_tm (subst_tm t2 x1 t1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_subst_tm_lower :
forall t1 t2 x1,
  remove x1 (fv_tm t1) [<=] fv_tm (subst_tm t2 x1 t1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_subst_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_notin_mutual :
(forall t1 t2 x1 x2,
  x2 `notin` fv_tm t1 ->
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm (subst_tm t2 x1 t1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_subst_tm_notin :
forall t1 t2 x1 x2,
  x2 `notin` fv_tm t1 ->
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm (subst_tm t2 x1 t1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_subst_tm_notin : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_upper_mutual :
(forall t1 t2 x1,
  fv_tm (subst_tm t2 x1 t1) [<=] fv_tm t2 `union` remove x1 (fv_tm t1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_subst_tm_upper :
forall t1 t2 x1,
  fv_tm (subst_tm t2 x1 t1) [<=] fv_tm t2 `union` remove x1 (fv_tm t1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_subst_tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_mutual :
(forall t2 t1 x1 x2 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm t1 ->
  subst_tm t1 x1 (close_tm_wrt_tm_rec n1 x2 t2) = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 t2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_close_tm_wrt_tm_rec :
forall t2 t1 x1 x2 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm t1 ->
  subst_tm t1 x1 (close_tm_wrt_tm_rec n1 x2 t2) = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 t2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_rec : lngen.

Lemma subst_tm_close_tm_wrt_tm :
forall t2 t1 x1 x2,
  lc_tm t1 ->  x1 <> x2 ->
  x2 `notin` fv_tm t1 ->
  subst_tm t1 x1 (close_tm_wrt_tm x2 t2) = close_tm_wrt_tm x2 (subst_tm t1 x1 t2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_degree_tm_wrt_tm_mutual :
(forall t1 t2 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (subst_tm t2 x1 t1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_degree_tm_wrt_tm :
forall t1 t2 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (subst_tm t2 x1 t1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_fresh_eq_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_tm t2 ->
  subst_tm t1 x1 t2 = t2).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_fresh_eq :
forall t2 t1 x1,
  x1 `notin` fv_tm t2 ->
  subst_tm t1 x1 t2 = t2.
Proof. Admitted.

#[export] Hint Resolve subst_tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_fresh_same_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x1 t2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_fresh_same :
forall t2 t1 x1,
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x1 t2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_tm_fresh_mutual :
(forall t2 t1 x1 x2,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x2 t2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_fresh :
forall t2 t1 x1 x2,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x2 t2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_fresh : lngen.

Lemma subst_tm_lc_tm :
forall t1 t2 x1,
  lc_tm t1 ->
  lc_tm t2 ->
  lc_tm (subst_tm t2 x1 t1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_lc_tm : lngen.

(* begin hide *)

Lemma subst_tm_open_tm_wrt_tm_rec_mutual :
(forall t3 t1 t2 x1 n1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm_rec n1 t2 t3) = open_tm_wrt_tm_rec n1 (subst_tm t1 x1 t2) (subst_tm t1 x1 t3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_open_tm_wrt_tm_rec :
forall t3 t1 t2 x1 n1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm_rec n1 t2 t3) = open_tm_wrt_tm_rec n1 (subst_tm t1 x1 t2) (subst_tm t1 x1 t3).
Proof. Admitted.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma subst_tm_open_tm_wrt_tm :
forall t3 t1 t2 x1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm t3 t2) = open_tm_wrt_tm (subst_tm t1 x1 t3) (subst_tm t1 x1 t2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_open_tm_wrt_tm_var :
forall t2 t1 x1 x2,
  x1 <> x2 ->
  lc_tm t1 ->
  open_tm_wrt_tm (subst_tm t1 x1 t2) (var_f x2) = subst_tm t1 x1 (open_tm_wrt_tm t2 (var_f x2)).
Proof. Admitted.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm_var : lngen.

(* begin hide *)

Lemma subst_tm_spec_rec_mutual :
(forall t1 t2 x1 n1,
  subst_tm t2 x1 t1 = open_tm_wrt_tm_rec n1 t2 (close_tm_wrt_tm_rec n1 x1 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_spec_rec :
forall t1 t2 x1 n1,
  subst_tm t2 x1 t1 = open_tm_wrt_tm_rec n1 t2 (close_tm_wrt_tm_rec n1 x1 t1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_spec_rec : lngen.

(* end hide *)

Lemma subst_tm_spec :
forall t1 t2 x1,
  subst_tm t2 x1 t1 = open_tm_wrt_tm (close_tm_wrt_tm x1 t1) t2.
Proof. Admitted.

#[export] Hint Resolve subst_tm_spec : lngen.

(* begin hide *)

Lemma subst_tm_subst_tm_mutual :
(forall t1 t2 t3 x2 x1,
  x2 `notin` fv_tm t2 ->
  x2 <> x1 ->
  subst_tm t2 x1 (subst_tm t3 x2 t1) = subst_tm (subst_tm t2 x1 t3) x2 (subst_tm t2 x1 t1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_subst_tm :
forall t1 t2 t3 x2 x1,
  x2 `notin` fv_tm t2 ->
  x2 <> x1 ->
  subst_tm t2 x1 (subst_tm t3 x2 t1) = subst_tm (subst_tm t2 x1 t3) x2 (subst_tm t2 x1 t1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_subst_tm : lngen.

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall t2 t1 x1 x2 n1,
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm t1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 (open_tm_wrt_tm_rec n1 (var_f x2) t2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall t2 t1 x1 x2 n1,
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm t1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 (open_tm_wrt_tm_rec n1 (var_f x2) t2)).
Proof. Admitted.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma subst_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall t2 t1 x1 x2,
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm t1 ->
  x2 <> x1 ->
  lc_tm t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (var_f x2))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_abs :
forall x2 t2 t1 x1,
  lc_tm t1 ->
  x2 `notin` fv_tm t1 `union` fv_tm t2 `union` singleton x1 ->
  subst_tm t1 x1 (abs t2) = abs (close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_abs : lngen.

Lemma subst_tm_ex :
forall x2 t2 t1 x1,
  lc_tm t1 ->
  x2 `notin` fv_tm t1 `union` fv_tm t2 `union` singleton x1 ->
  subst_tm t1 x1 (ex t2) = ex (close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_ex : lngen.

(* begin hide *)

Lemma subst_tm_intro_rec_mutual :
(forall t1 x1 t2 n1,
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 t2 t1 = subst_tm t2 x1 (open_tm_wrt_tm_rec n1 (var_f x1) t1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_intro_rec :
forall t1 x1 t2 n1,
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 t2 t1 = subst_tm t2 x1 (open_tm_wrt_tm_rec n1 (var_f x1) t1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_intro_rec : lngen.
#[export] Hint Rewrite subst_tm_intro_rec using solve [auto] : lngen.

Lemma subst_tm_intro :
forall x1 t1 t2,
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm t1 t2 = subst_tm t2 x1 (open_tm_wrt_tm t1 (var_f x1)).
Proof. Admitted.

#[export] Hint Resolve subst_tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.

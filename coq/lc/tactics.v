Require Export Metalib.LibTactics.
Require Export ssreflect.
Require Export Coq.Program.Equality.  (* for dependent induction *) 
Require Import Lia.

Require Export lc.lc_ott.
Require Export lc.lc_inf.

Set Implicit Arguments.

(* ------------------------------------------------------------ *)
(* Notation *)
(* ------------------------------------------------------------ *)

(* Notations for working with the untyped lambda calculus. 
   We define these in a submodule so that we can control where
   they are in scope. *)

Module LCNotations.
  Declare Scope lc_scope.
  Delimit Scope lc_scope with tm.
  Notation "t [ x ~> u ]" := (subst_tm u x t) 
    (at level 10, left associativity, x constr) : lc_scope.
  Notation "t ^ x"    := (open_tm_wrt_tm t (var_f x)) : lc_scope.
  Notation open t1 t2 := (open_tm_wrt_tm t1 t2).
  Notation close x t  := (close_tm_wrt_tm x t).
End LCNotations.

Import LCNotations.
Local Open Scope lc_scope.


(* ------------------------------------------------------------ *)
(* AUTOMATION SUPPORT for working with locally nameless terms   *)
(* ------------------------------------------------------------ *)

(* In general, this section supports two forms of automation 
     - Hint Resolve: lemmas to apply automatically with auto/eauto.
     - Hint Rewrite: lemmas to apply with autorewrite.

   The lc_inf file includes many of these hints, using the lngen 
   hint database. This section adds a few more.
*)

(* Resolve Hints for 'lc_tm' proofs. *)

Lemma lc_abs_open : forall t u,
  lc_tm (abs t) -> lc_tm u -> lc_tm (open t u).
Proof. 
  intros. inversion H. apply lc_body_tm_wrt_tm; auto.
Qed.

#[export] Hint Resolve lc_abs_open : lngen.
#[export] Hint Resolve lc_abs_exists : lngen.

(* A relation is something of type "tm -> tm -> Prop".
   Our locally nameless representation means that we should 
   ensure that all related terms are locally closed. 
   We'll define a class of relations where this property holds. *)

Class lc (R : relation) := { 
    lc1 : forall a b, R a b -> lc_tm a ;
    lc2 : forall a b, R a b -> lc_tm b ;
  }.

(* With this overloading, we can add automation hints to automatically
   dispatch local closure preconditions. *)
#[export] Hint Resolve lc1 : lngen.
#[export] Hint Resolve lc2 : lngen.


(* Rewriting Hints *)

(* These two lemmas simplify working with substitutions for 
   variables. *)
Lemma subst_eq_var : forall a x, (var_f x)[x ~> a] = a.
Proof. intros. simpl. destruct (x == x). auto. done. Qed.
Lemma subst_neq_var : forall a x y, y <> x -> (var_f y)[x ~> a] = var_f y.
Proof. intros. simpl. destruct (y == x). done. auto. Qed.

#[export] Hint Rewrite subst_eq_var : lngen.
#[export] Hint Rewrite subst_neq_var using solve [auto] : lngen.
(* This last hint will only be applied via autorewrite when the 
   y <> x can be shown immediately via auto. *)

(* A version of the 'open_tm_wrt_tm_inj' lemma that works with rewriting *)
Lemma open_tm_wrt_tm_inj_eq
     : forall (t2 t1 : tm) (x1 : atom), 
            x1 `notin` fv_tm t2 -> x1 `notin` fv_tm t1 -> 
            (t2 ^ x1 = t1 ^ x1) <-> t2 = t1.
Proof. 
  split; intro h. eapply open_tm_wrt_tm_inj; eauto. rewrite h. auto.
Qed. 
(* This hint is only used when the freshness preconditions can be solved 
   via auto. *)
#[export] Hint Rewrite open_tm_wrt_tm_inj_eq using solve [auto] : lngen.

(* Other rewriting hints. *)
#[export] Hint Rewrite subst_tm_open_tm_wrt_tm using auto : lngen.
#[export] Hint Rewrite fv_tm_subst_tm_upper : lngen.


(* ------------------------------------------------------------ *)
(* TACTICS                                                      *)
(* ------------------------------------------------------------ *)

(* This definition governs the use of the `pick fresh` tactic
   and instructs metalib on where to find free variables in the 
   context. It must be defined for each language specification. *)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  constr:(A \u B \u C).

(* Specialize all assumptions in the context using the given atom, 
   automatically supplying any associated freshness proofs. *)
Ltac spec y := 
  repeat lazymatch goal with 
    | [H0 : forall x : atom, x \notin ?L -> _ |- _ ] => 
     specialize (H0 y ltac:(auto))
    | [H0 : forall x : atom, _ |- _ ] => 
     specialize (H0 y)
    | [H0 : forall x : tmvar, _ |- _ ] => 
     specialize (H0 y)
  end. 

(* Look for an equality comparison for variables and do case analysis. *)
Ltac destruct_var_eq :=     
  match goal with [ y : tmvar, z:tmvar |- context[?y==?z] ] => destruct (y == z) end.

(* When proving substitution lemmas, look for a hypothesis that uses 
   "open" and rewrite it to push the substitution into the term *)
Ltac rewrite_subst_open_hyp := 
  match goal with 
      [ H0 : context [((?t ^ ?y) [?x ~> ?u])] |- _ ] => 
        repeat rewrite subst_tm_open_tm_wrt_tm in H0; auto;
        repeat rewrite subst_neq_var in H0; auto
    end.

(* ------------------------------------------------------------ *)
(* Working with syntax                                          *)
(* ------------------------------------------------------------ *)


Lemma open_app : forall t1 t2 x, 
    (app t1 t2) ^ x = app (t1 ^ x) (t2 ^ x).
Proof. intros. reflexivity. Qed.

Lemma open_var : forall x, (var_b 0) ^ x = var_f x.
Proof. intros. reflexivity. Qed.

#[export] Hint Rewrite 
  subst_tm_open_tm_wrt_tm 
  fv_tm_open_tm_wrt_tm_upper  
  size_tm_open_tm_wrt_tm_var 
  open_app open_var : lngen.

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
    -> (forall k, P (lit k))
    -> (forall p, P (prim p))
    -> P tnil
    -> (forall t1 t2, P t1 -> P t2 -> P (tcons t1 t2))
    -> P fail
    -> (forall t1 t2, P t1 -> P t2 -> P (choice t1 t2))
    -> (forall t, 
          (forall x , x `notin` fv_tm t -> P (t ^ x)) 
          -> P (ex t))
    -> (forall t1 t2, P t1 -> P t2 -> P (seq t1 t2))
    -> (forall t1 t2, P t1 -> P t2 -> P (unify t1 t2))
    -> (forall t, P t -> P (one t))
    -> (forall t, P t -> P (all t))
    -> forall t, P t.
Proof.
  intros P VARB VARF APP ABS LIT ADD NIL CONS FAIL CHOICE EX SEQ UNIFY ONE ALL t.
  remember (size_tm t) as n.
  have GE: n >= size_tm t. subst. auto. clear Heqn.
  move: t GE.
  induction (lt_wf n) as [n _ IH].
  intros [ i | x | u | t | k | (* add *) | (* nil *) | t | t | | u | t | t | t | t] SZ; simpl in SZ; eauto.
  + eapply ABS.
    intros x FV.
    eapply (IH (size_tm u)). lia.
    autorewrite with lngen.
    lia.
  + eapply APP; eapply IH; eauto; lia. 
  + eapply CONS; eapply IH; eauto; lia. 
  + eapply CHOICE; eapply IH; eauto; lia.
  + eapply EX.
    intros x FV.
    eapply (IH (size_tm u)). lia.
    autorewrite with lngen.
    lia.
  + eapply SEQ; eapply IH; eauto; lia. 
  + eapply UNIFY; eapply IH; eauto; lia.

Qed.    

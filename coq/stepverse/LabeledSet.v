
Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Require structures.Option.
Require Import structures.Sets.
Require Import structures.Monad.
Require structures.Vector.

Require Import stepverse.label.
Import LabelNotation.
Require Export stepverse.result.

Require Import Classical.

Set Implicit Arguments.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*      Monadic type                                         *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(** The semantics of computations is a set of labeled results.  These sets
   should be partial functions, i.e. there should be at most one result for
   any label in the set. *)

Definition M (A : Type) := (label * Result A) -> Prop.  

Section PartialFunctions.

Variable A : Type.

Variable R : A -> A -> Prop.

Context `{Equivalence A R} `{PartialOrder A R}.

Import SetNotations.

(** ** entries and entry approximations *)

(* A pair of a label and result is an entry. *)

Definition entry (A:Type) := (label * Result A)%type.

Definition default_label {A} (r : Result A) := 
  if R.isBottom r then Bot else Top.

(* An entry is "finished" if the label does not contain Bot and the result is
   not Bottom. *)

(* this is the same as not containing Bot *)
Definition label_finished (l : label) := 
  forall l', l ⊑ l' -> l = l'.

(* this used to be forall r', R.approx R r r' -> r = r'. 
   However, with the introduction of approximation for values, 
   this is no longer appropriate. *)
(* this is the same as r <> Bottom *)
Definition result_finished (r : Result A) := 
  r <> Bottom.

Definition entry_finished '((l,r) : entry A) := 
  label_finished l /\ result_finished r.

Definition entry_valid '((l,r) : entry A) := 
  label_finished l <-> result_finished r.

(* Entry approximation is pointwise *)

Definition entry_approx '(l1,r1) '(l2, r2) : Prop := 
  Label.approx l1 l2 /\ R.approx R r1 (r2 : Result A).

(** ** set approximatation *)

(* Because we will use these sets as the semantics of computations, we 
   need to say what it means for one set to *approximate* another.

   We have s1 ⊑ s2 when:

      1. for every e in s1 that has finished (i.e. is Value or Wrong), 
          a. e must be in s2 

      2. if e has bottomed 
          a. it could stay bottom, with a potentially bigger label
          b. it could succeed, with a bigger label
          c. it could fail and won't be in s2

      3. if e is not in s1, i.e. fails
          - then it should continue to fail, i.e. all bigger labels shouldn't be in s2

   We can express 1 as is
   Case 2 is trivial
   we can express 3 using the contrapositive:
            everything in s2 should be approximated by something in s1
         
We need (1) to know that successful values do not change with more fuel.
We need (3) for the case of ONE: there won't be new "smaller" elements 
when we add more fuel.
*)

Definition approx (s1 s2 : M A) : Prop := 
  (* (1) We don't lose successful results. 
     Everything that has finished in s1 is still present in s2. *)
  (forall e, e ∈ s1 -> entry_finished e -> (e ∈ s2)) /\
  (* (3) We don't make up results. 
     Every entry in s2 is approximated by something from s1. *)
  (forall e2, e2 ∈ s2 -> exists e1, (e1 ∈ s1) /\ entry_approx e1 e2).


(** ** partial functions *)

(* We can look up values in the set by label. This label can be exactly the 
   same as the label in some entry, or it can be an extension of the label 
   of an unfinished entry. *)

Definition mapsto '(l,r) (s : M A) := 
  exists l', ((l',r) ∈ s) /\ Label.approx l' l.


(** ** !!!!! Classical logic !!!!! *)

Lemma decide_mapsto : forall (s : M A) l,
  (mapsto (l, Bottom) s) \/ not (mapsto (l, Bottom) s).
intros. eapply classic. Qed.

(* A set of pairs is a partial function if there is at most one mapping for
   any key in the set. *)
Definition partial_function (s : M A) := 
  forall l r1 r2, mapsto (l,r1) s -> mapsto (l, r2) s -> r1 = r2.

(* This predicate defines when a key is in the domain of 
   the partial function *)
Definition in_dom (s : M A) (l : label) : Prop := 
  exists l' r, ((l', r) ∈ s) /\ Label.approx l' l.

(** ** entry ordering, by labels only *)
Definition entry_lt : (label * Result A) -> (label * Result A) -> Prop := 
  fun '(l1,_) '(l2, _)=> Label.lt l1 l2.

(* The canonical list of entries in a finite set *)
Definition elements (s : M A) (l : list (label * Result A)) : Prop := 
  (mem l = s) /\                        (* memberships are equal *)
  @Sorted.LocallySorted _ entry_lt l.  (* the list is sorted by the labels *)

(** ** Properties of partial_functions, approx, and labeled sets *)

Lemma smaller_notpresent 
  (a : label * Result A) (w : list (label * Result A)) :
  List.Forall (entry_lt a) w ->  ~(List.In a w).
Proof. destruct a. 
       induction w.
       intros h1 h2. inversion h2.
       intros h1 h2. simpl in h2. 
       inversion h1. subst.
       destruct h2.
       + subst. eapply Label.lt_irreflexive; eauto.
       + apply IHw; eauto.
Qed.

Lemma exact_mapsto e (s : M A) : (e ∈ s) -> mapsto e s.
Proof. 
  move: e => [l r].
  move=> in1.
  exists l. split. auto. eapply Label.approx_refl.
Qed.

Lemma elements_functional {e: M A}{w1 w2 : list (label * Result A)} : 
  elements e w1 -> elements e w2 -> w1 = w2.
Proof.
  unfold elements.
  intros [M1 S1] [M2 S2].
  rewrite <- Sorted.Sorted_LocallySorted_iff in S1.
  rewrite <- Sorted.Sorted_LocallySorted_iff in S2.
  have h: (mem w1 = mem w2). subst. auto.
  clear M1 M2 e.
  move: w2 h S1 S2.
  induction w1.
  - intros w2 h S1 S2.
    destruct w2. auto. 
    unfold mem in h.
    admit.
  - intros w2 h S1 S2.
    destruct w2. admit.
    apply Sorted.Sorted_extends in S1.
    apply Sorted.Sorted_extends in S2.
Admitted.

Lemma partial_function_singleton {k}{r:Result A} : 
   partial_function ⌈ (k , r) ⌉.
 Proof. 
   intros l r1 r2 [l1 [m1 a1]] [l2 [m2 a2]].
   inversion m1. inversion m2. subst. auto.
 Qed.

Lemma entry_approx_label {l1 r1 l2 r2}: 
  entry_approx (l1, r1) (l2, r2) -> Label.approx l1 l2.
destruct r1; simpl; tauto.
Qed.

Lemma entry_approx_refl (e : label * Result A) : entry_approx e e.
Proof. destruct e as [l r].
       destruct r; simpl; split; eauto using Label.approx_refl, 
       Equivalence_Reflexive. 
Qed.

Lemma entry_approx_trans (e1 e2 e3 : label * Result A) : 
  entry_approx e1 e2 -> entry_approx e2 e3 -> entry_approx e1 e3.
Proof. destruct e1 as [l1 r1]. destruct e2 as [l2 r2]. destruct e3 as [l3 r3]. 
       destruct r1; destruct r2; simpl.
Admitted.
(*
       eauto using Label.approx_trans. 
       intros h1 [h2 e]. eauto using Label.approx_trans. 
       intros h1 [h2 e]. eauto using Label.approx_trans. 
       intros [h1 e] h2. discriminate.
       intros [h1 e1] [h2 e2]. eauto using Label.approx_trans. 
       intros [h1 e1] [h2 e2]. discriminate.
       intros [h1 e1] h2. discriminate.
       intros [h1 e1] h2. discriminate.
       intros [h1 e1] [h2 e2]. inversion e1. subst. eauto using Label.approx_trans. 
Qed. *)

Lemma approx_refl (s : M A) : approx s s.
  split. intros e eIn eFin. auto.
  intros e2 e2In. exists e2. split. auto.
  eapply entry_approx_refl.
Qed.

Lemma nonBottomIsFinished (r : Result A) : r <> Bottom -> result_finished r.
  intros NE. unfold result_finished. auto.
(*  intros r' RA.
  destruct r; try done; simpl in RA; destruct r'; try done. f_equal. auto. *)
Qed.

Lemma bottomIsNotFinished : not (result_finished (@Bottom A)).
  intros h. cbv in h. auto. 
  (* have: (@Bottom A) = (@Wrong A). eapply h. simpl. done. done. *)
Qed.

Lemma approx_not_finished l l1 : 
~ label_finished l ->
  l1 ⊑ l ->
  ~ label_finished l1.
Admitted.

Lemma label_finished_Br_inv1 l0 l1: label_finished (l0 ⋈ l1) -> label_finished l0.
Admitted.
Lemma label_finished_Br_inv2 l0 l1: label_finished (l0 ⋈ l1) -> label_finished l1.
Admitted.
Lemma Value_finished {a : A} : result_finished (Value a).
Admitted.

End PartialFunctions.

#[export] Hint Unfold entry : core.

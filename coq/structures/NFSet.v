Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Import structures.Sets.
Require Import structures.List.
Require Export lc.tactics.

Import SetNotations.

(* NONEMPTY FINITE SETS *)

Inductive nfset (A : Type) : Type := 
  | NFSet : A -> list A -> nfset A.
Arguments NFSet {_}.

Definition singleton_nfset {A : Type} (x:A): nfset A := NFSet x nil.

Definition concat_nfset: forall {A : Type}, nfset A -> nfset A -> nfset A :=
  fun {A} '(NFSet x xs) '(NFSet y ys) => NFSet x (xs ++ y :: ys).

Definition union_nfset: forall {A : Type}, nfset A -> nfset A -> nfset A :=
  fun {A} '(NFSet x xs) '(NFSet y ys) => NFSet y (x :: xs ++ ys).

Definition In_nfset {A : Type}(x : A) '(NFSet y ys) : Prop :=
  x = y \/ List.In x ys.
Definition Included_nfset: forall {A : Type}, nfset A -> nfset A -> Prop :=
  fun {A} (s1 s2: nfset A) => forall (x:A), In_nfset x s1 -> In_nfset x s2.
Definition Equal_nfset {A:Type}(s1 s2 : nfset A) := 
  Included_nfset s1 s2 /\ Included_nfset s2 s1.
Definition Forall_nfset: forall {A : Type}, (A -> Prop) -> nfset A -> Prop := 
  fun {A} Pr '(NFSet x xs) => Pr x /\ List.Forall Pr xs.
Definition ForallT_nfset: forall {A : Type}, (A -> Type) -> nfset A -> Type :=
  fun {A} Pr '(NFSet x xs) => (Pr x * List.ForallT Pr xs)%type.
Definition mem : forall {A : Type}, nfset A -> P A := 
  fun {A} (xs : nfset A) (x : A) => In_nfset x xs.

#[export] Instance Symmetric_Equal_nfset: forall {A : Type}, nfset A -> Symmetric (@Equal_nfset A). Admitted.
#[export] Instance Reflexive_Equal_nfset: forall {A : Type}, nfset A -> Reflexive (@Equal_nfset A). Admitted.
#[export] Instance Transitive_Included_nfset: forall {A : Type}, nfset A -> Transitive (@Included_nfset A). Admitted.
#[export] Instance Reflexive_Included_nfset: forall {A : Type}, nfset A -> Reflexive (@Included_nfset A). Admitted.
#[export] Instance Transitive_Equal_nfset: forall {A : Type}, nfset A -> Transitive (@Equal_nfset A). Admitted.

Lemma mem_In: forall {A : Type} {E : nfset A} (x : A), x ∈ mem E -> In_nfset x E. Admitted.
Lemma mem_union: forall {A : Type} {E1 E2 : nfset A}, mem (union_nfset E1 E2) = (mem E1 ∪ mem E2). Admitted.
Lemma mem_union_Included: forall {A : Type} {D1 D2 : nfset A} {w : P A},
  mem D1 ⊆ w -> mem D2 ⊆ w -> mem (union_nfset D1 D2) ⊆ w. Admitted.
Lemma mem_singleton {A}{v : A} : v ∈ mem (singleton_nfset v). Admitted.

Lemma In_mem : forall {A : Type} {E : nfset A} (x : A), In_nfset x E -> x ∈ mem E. Admitted.
Lemma mem_Forall: forall {A : Type} {E : nfset A} {Pr : A -> Prop}, Sets.Forall Pr (mem E) -> Forall_nfset Pr E.  Admitted.


Lemma Forall_mem: forall {A : Type} {E : nfset A} {Pr : A -> Prop}, Forall_nfset Pr E -> Sets.Forall Pr (mem E). Admitted.
Lemma Forall_sub_mem: forall {A : Type} {E : nfset A} (X : P A) (Pr : A -> Prop), mem E ⊆ X -> Sets.Forall Pr X -> Forall_nfset Pr E. Admitted.

Lemma valid_mem_singleton: forall {A : Type}, nfset A -> forall x : A, valid (mem (singleton_nfset x)). Admitted.
Lemma nonemptyT_mem: forall {A : Type} {E : nfset A}, nonemptyT (mem E). Admitted.
Lemma valid_mem: forall {A : Type} {V : nfset A}, valid (mem V). Admitted.


#[export] Hint Resolve 
  Reflexive_Equal_nfset Reflexive_Included_nfset
  mem_In mem_union mem_union_Included mem_singleton Forall_mem Forall_sub_mem 
  In_mem valid_mem_singleton nonemptyT_mem valid_mem : core.


Lemma nfset_induction {A} (Pr : nfset A -> Prop) : 
  (forall x, Pr (singleton_nfset x)) -> 
  (forall x W, Pr W -> Pr (union_nfset (singleton_nfset x) W)) ->
  forall V, Pr V.
Proof. 
  intros S C V.
  destruct V. 
  induction l. 
  - eapply S. 
  - specialize (C a0 (NFSet a l) IHl). cbn in C. auto.
Qed.


(* ---------------------- Notations ------------------------ *)

Declare Scope nfset_scope.
Open Scope nfset_scope.

Module NFSetNotations.
Notation " [ x ] " := (NFSet x nil) : nfset_scope.
Notation " [ x ; y1 ; .. ; yn ] " := (NFSet x (cons y1 .. (cons yn nil) .. )) : nfset_scope.
End NFSetNotations.

Import NFSetNotations.


(* -------------- ordered nfset --------------------- *)

Section OrderedNFSet.

Context 
  { A : Type }
  ( lt : A -> A -> Prop )
  `{ StrictOrder A lt }.

Fixpoint ordered_list (v : A) (xs: list A) : Prop := 
  match xs with 
  | nil => True
  | cons w ys => lt v w /\ ordered_list w ys
  end.

Definition ordered_nfset '(NFSet v vs) := ordered_list v vs.

(* This is the main property that we want from ordered nfsets *)
Lemma ordered_extensional VS WS : 
  ordered_nfset VS -> ordered_nfset WS -> mem VS ≃ mem WS -> VS = WS.
Proof.
  move: VS => [a l].
  move: WS => [a0 l0].
  move: a a0 l0.
  induction l.
  - intros a a0 l0 OL1 OL2 [h1 h2].
    simpl in OL1. simpl in OL2.
    destruct l0 as [|a2 l2].
    + specialize (h1 a ltac:(left; auto)). inversion h1; subst; try done. 
    + move: (h2 a0 ltac:(left; auto)) => h3.
      move: (h2 a2 ltac:(right; left; auto)) => h4.
      inversion h3; subst; try done. inversion h4; subst; try done.
      inversion OL2.
      apply StrictOrder_Irreflexive in H0.
      done.
  - intros a0 a1 l1 OL1 OL2 [h1 h2].
    simpl in OL2. simpl in OL2.
    destruct l1 as [|a2 l2].
    + move: (h1 a0 ltac:(left; auto)) => h3.
      move: (h1 a ltac:(right; left; auto)) => h4.
      inversion h3; subst; try done. inversion h4; subst; try done.
      inversion OL1.
      apply StrictOrder_Irreflexive in H0.
      done.
    + inversion OL1. inversion OL2.
      move: (h1 a0 ltac:(left; auto)) => h3. destruct h3; subst.
      ++ have EQ: mem (NFSet a l) ≃ mem (NFSet a2 l2).
         { admit. }
         specialize (IHl a a2 l2 H1 H3 EQ). 
         inversion IHl. subst; auto.
      ++         
Admitted.

End OrderedNFSet.

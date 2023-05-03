Require Export Ensembles.
Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Program.Equality.  (* for dependent induction *) 


Declare Scope set_scope.
Delimit Scope set_scope with Ensemble.
Bind Scope set_scope with Ensemble.

Arguments In {_}.
Arguments Included {_}.
Arguments Union {_}.
Arguments Intersection {_}.
Arguments Same_set {_}.
Arguments Singleton {_}.
Arguments Empty_set {_}.


Module SetNotations. 
  Notation "∅"  := Empty_set : set_scope.
  Notation "x ∈ s"  := (In s x) (at level 90) : set_scope.
  Notation "⌈ x ⌉" := (Singleton x) : set_scope.
  Infix "⊆"  := Included (at level 90) : set_scope.
  Infix "∪"  := Union (at level 90) : set_scope.
  Infix "∩"  := Intersection (at level 90) : set_scope.
  Infix "≃"  := Same_set (at level 90) : set_scope.
End SetNotations. 

Definition P := Ensemble.

Definition nonempty {A} : P A -> Prop := Inhabited A.
Arguments nonempty {_}.

Import SetNotations.
Open Scope set_scope.

Check (1 ∈ ⌈ 1 ⌉).
Check (∅ ⊆ ⌈ 1 ⌉).
Check (∅ ∪ ⌈ 1 ⌉).
Check (∅ ∪ ⌈ 1 ⌉ ≃ ∅).


#[global] Instance Equivalence_Same_set {A} : Equivalence (@Same_set A) .
constructor.
- unfold Reflexive, Same_set, Included in *. tauto. 
- unfold Symmetric, Same_set, Included in *. tauto.
- unfold Transitive, Same_set, Included in *. intros x y z [h1 h2] [k1 k2]. 
  split; eauto.
Qed.

Require Import Coq.Lists.List.

Definition mem {A} : list A -> P A :=
  fun ls x => In x ls.


(* E≢[]⇒nonempty-mem *)
Lemma nonnil_nonempty_mem : forall{T}{E : list T}, E <> nil -> nonempty (mem E).
Proof. intros. destruct E; cbv. done.
       econstructor.
       econstructor. eauto.
Qed.

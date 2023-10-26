Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.


(* For this version, the type P (Comp (fin A)) is a set of computations, that
   each store a finite list approximation of a set of A values.

   But, we have multiple representations of these sets using lists!

   This type is part of an inductive definition of values, so it needs to be
   "obviously" inductive. That means that we can't use an abstract type 
   of finite sets (based perhaps on ordered lists) to enforce the use 
   of a canonical element.

   Instead, in this part, we define what it means for set membership 
   and set equality to hold.

*)


Section CompList.

Variable A : Type.


Definition Comp_fset_sub : Comp (fset A) -> Comp (fset A) -> Prop :=
  fun c1 c2 => 
    match c1 , c2 with 
    | c_wrong , c_wrong => True 
    | c_multi l1 , c_multi l2 => 
        List.Forall2 Included_fset l1 l2 
    | _ , _ => False
    end.

Definition Comp_fset_eq : Comp (fset A) -> Comp (fset A) -> Prop :=
  fun c1 c2 => 
    match c1 , c2 with 
    | c_wrong , c_wrong => True 
    | c_multi l1 , c_multi l2 => 
        List.Forall2 Equal_fset l1 l2 
    | _ , _ => False
    end.

Definition Comp_fset_In (y : Comp (fset A)) (X : P (Comp (fset A))) : Prop :=
  exists x, Comp_fset_eq x y /\ (x ∈ X).
Definition P_Comp_fset_sub (X Y : P (Comp (fset A))) : Prop := 
  forall x, Comp_fset_In x X -> Comp_fset_In x Y.
Definition P_Comp_fset_eq (X Y : P (Comp (fset A))) : Prop := 
  P_Comp_fset_sub X Y /\ P_Comp_fset_sub Y X.




#[export] Instance Reflexive_Comp_fset_sub : Reflexive Comp_fset_sub.
Admitted.
#[export] Instance Transitive_Comp_fset_sub : Transitive Comp_fset_sub.
Admitted.

#[export] Instance Reflexive_Comp_fset_eq : Reflexive Comp_fset_eq.
Admitted.
#[export] Instance Symmetric_Comp_fset_eq : Symmetric Comp_fset_eq.
Admitted.
#[export] Instance Transitive_Comp_fset_eq : Transitive Comp_fset_eq.
Admitted.

#[export] Instance Proper_Comp_fset_in : Proper (Comp_fset_eq ==> P_Comp_fset_eq ==> Logic.iff) Comp_fset_In.
Proof. 
intros x1 x2 Eqx y1 y2 [S1 S2].
unfold P_Comp_fset_sub in *.
split.
- intro h.
  specialize (S1 _ h).
  destruct S1 as [x1' [h1 h2]].
  exists x1'. split; auto.
  transitivity x1; auto.
- intro h.
  specialize (S2 _ h).
  destruct S2 as [x1' [h1 h2]].
  exists x1'. split; auto.
  transitivity x2; auto.
  symmetry. auto.
Qed.

End CompList.

Arguments Comp_fset_sub {_}.
Arguments Comp_fset_eq {_}.
Arguments Comp_fset_In {_}.
Arguments P_Comp_fset_sub {_}.
Arguments P_Comp_fset_eq {_}.

(* \sim *)
Infix "∼" := P_Comp_fset_eq (at level 85, right associativity).

(* \subsim *)
Infix "⫇" := P_Comp_fset_sub (at level 85, right associativity).

(* this is \epsilon not \in *)
Infix "ϵ" := Comp_fset_In (at level 85, right associativity).


(* If Y is finite, then it must be equal to X. *)
Definition finite {A} (X : P A) := 
  exists x, mem x ≃ X.

Definition APPROX {A} (x : fset A) (Y : P A) := 
  (mem x ⊆ Y) /\ (finite Y -> mem x ≃ Y).

Infix "⊑" := APPROX (at level 85, right associativity).



(* V must be nonempty because RET is strict. If V is empty then the 
   set should be empty. *)

Definition LIFT0 {A} (F : P A) : P (Comp (fset A)) :=
  fun t =>  exists f : fset A, 
      nonempty_fset f  /\ t = ret f /\ (mem f ⊆ F).

Definition LIFT1 {A B} (F : P A -> P B) (U : P (Comp (fset A))) : P (Comp (fset B)) :=
  fun t => 
    exists (u : Comp (fset A)), exists (f : fset A -> fset B),
      (u ϵ U) /\ t = fmap f u /\ (forall a, Comp_In a u -> (f a) ⊑ F (mem a)).

Definition LIFT2 {A1 A2 B} (F : P A1 -> P A2 -> P B) : P (Comp (fset A1)) -> P (Comp (fset A2)) -> P (Comp (fset B)) :=
  fun U1 U2 t => 
    exists u1, exists u2, exists (f : fset A1 -> fset A2 -> fset B), 
      (u1 ϵ U1) /\ (u2 ϵ U2) /\ t = liftA2 f u1 u2 
      /\ (forall a1 , Comp_In a1 u1 -> forall a2, Comp_In a2 u2 -> (f a1 a2) ⊑ F (mem a1) (mem a2)).


(* LIFT0 is the **same** as RET *)

(*
Lemma LIFT0_RET1 {A} {X : P A} : LIFT0 X ⊆ RET X.
Proof.
  intros x [f [h1 [-> h2]]]. 
  unfold RET.
  destruct f. destruct l; cbn. done.
  cbn. split; auto.
Qed.

Lemma LIFT0_RET2 {A} {X : P A} : RET X ⊆ LIFT0 X.
Proof.
  intros x xIn.
  destruct x; unfold LIFT0, RET in *.
  cbn in xIn. done.
  cbn in xIn. 
  destruct l; try done.
  destruct l; try done.
  destruct xIn.
  exists f. split. auto.
  split. auto.
  auto.
Qed. *)

(* LIFT1 is like FMAP *)

Lemma LIFT1_ID1 {A} (X: P (Comp (fset A))) : LIFT1 id X ⫇ id X.
Proof.
  unfold LIFT1, id.
  intros y [u [EQ [y' [f [h3 [-> h4]]]]]].
  
  destruct y'; cbn in EQ.
  all: destruct y; try done.
  destruct h3 as [x' [EQx h3]].
  exists x'. split; auto.
  destruct x'; try done.
  cbn in EQx.
  cbn.
Admitted. (*
  transitivity l; auto.
  transitivity (List.map f l); auto.
  clear EQ EQx l1 h3.
  move: h4.
  induction l; move=> h4.
  simpl. auto.
  simpl.
  econstructor.
  specialize (h4 a ltac:(left; auto)).
  destruct h4.
  unfold mem_eq. symmetry.
  apply H0.
  eexists. reflexivity.
  eapply IHl.
  intros a0 a0In.
  eapply h4. 
  right. simpl in a0In. auto.
Qed.  *)

Axiom fmap_id : forall {A}{x : Comp A}, fmap id x = x.

Lemma LIFT1_ID2 {A} (x: P (Comp (fset A))) : id x ⊆ LIFT1 id x.
Proof.
  unfold LIFT1, id.
  intros c cIn.
  exists c. exists id.
  split. auto.
Admitted. (*
  split. rewrite fmap_id. reflexivity.
  intro a. unfold id. reflexivity.
Qed. *)

(* LIFT2 is like an applicative functor. But what are its laws???

left and right identity

liftA2 (\_ y -> y) (pure x) fy       = fy
liftA2 (\x _ -> x) fx       (pure y) = fx

associativity

liftA2 id           (liftA2 (\x y z -> f x y z) fx fy) fz =
liftA2 (flip id) fx (liftA2 (\y z x -> f x y z)    fy  fz)

naturality

liftA2 (\x y -> o (f x) (g y)) fx fy = liftA2 o (fmap f fx) (fmap g fy)


*)

Axiom liftA2_leftid : forall {A1 A2} (l : A1) (u2 : Comp A2),
    liftA2 (fun _ y => y) (c_multi (l :: nil)) u2 = u2.

Lemma LIFT2_left1 {A} (x : P A) (fy : P (Comp (fset A))) :
  LIFT2 (fun _ y => y) (LIFT0 x) fy ⊆ fy.
Proof.
  unfold LIFT2, LIFT0.
  intros z [u1 [u2 [f [h1 [h2 [-> h3]]]]]].
  destruct u1; try done.
Abort.
(*  destruct l; try done.
  destruct l0; try done.
  move: h1 => [S1 NE].
  specialize (h3 l ltac:(left; auto)).  *)
  (* At this point we need mem (f l a2) = mem a2, not just be a subset. *)


(* Because of the strictness of RET, we need to know that X is inhabited. *)
Lemma LIFT2_left2 {A} (x : A) (X : P A) (fy : P (Comp (fset A))) :
  x ∈ X ->
  fy ⊆ LIFT2 (fun _ y => y) (LIFT0 X) fy.
Proof.
  intros xIn.
  unfold LIFT2, LIFT0.
  intros y yIn.
  exists (c_multi ((singleton_fset x) :: nil)).
  exists y.
  exists (fun _ y => y).
  repeat split; eauto.
Admitted . (*
  rewrite mem_singleton_eq. move=> z zIn. inversion zIn. subst; auto.
  done.
  rewrite liftA2_leftid. reflexivity.
  intros a1 a1In a2 a2In.
  reflexivity.
Qed. *)


Lemma LIFT2_COMP1 {A1 A2 B} (f : P A1 -> P A2 -> P B) (X : P A1) (Y : P A2) x y:
  x ∈ X -> 
  y ∈ Y -> 
  LIFT2 f (LIFT0 X) (LIFT0 Y) ⊆ LIFT0 (f X Y).
Proof.
  move=> xIn yIn.
  intros z zIn.
  destruct zIn as [u1 [u2 [g [h1 [h2 [-> h3]]]]]].
  destruct u1; try done.
Admitted. (*
  destruct l; try done.
  destruct l0; try done.
  move:  h1 => [h1 lNE].
  destruct u2; try done.
  destruct l0; try done.
  destruct l1; try done.
  move: h2 => [h2 l0NE].
  cbn.
  specialize (h3 l ltac:(left; auto)).
  specialize (h3 l0 ltac:(left; auto)).
  rewrite -> h3.
  split.
  (* Need f to be monotonic. *)
  admit.
  (* Don't know what we need here. *)
  (* can't show result of g is nonempty. *)
Abort. *)


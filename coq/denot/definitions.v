(* Definitions related to the denotational semantics.

   This version separates the denotation of computations from that of values.
   
   The semantic domain for values: `P Value` and for computations: `P (Comp
   (list Value))`

   The `Comp A` type is defined in `structures.Comp`. It is isomorphic to
   `maybe (list A)`, where none is a runtime type error and the list includes
   multiple results.  Fail is the empty list.

   The type `P A` is a (potentially) infinite set, represented by its
   characteristic function `(A -> Prop)`. The union of all of the elements of
   the set is the complete denotation of the value/computation. (These
   elements should be consistent with eachother.)

   The denotation of both values and computations includes bottom: the
   denotation of an infinite loop. Therefore, some definitions include
   the predicate

      valid : P Value -> Prop

   which characterizes Values that are nonempty. i.e. do not denote bottom.

   We would have liked the denotation of computations to be `P (Comp (P Value))`,
   i.e. the type `P (Comp A)` instantiated with `P Value`. This former type is
   *almost* a monad: there are reasonable definitions of return and bind, but
   one of the associativity laws for bind fails. This isn't necessarily fatal:
   it just means that we have to be careful about how we represent certain
   computations.

   However, I was unable to prove continuity for the semantic operators using
   this definition. So I have used the types above, and have defined the
   Monad-like operations:

      RET : P A -> P (Comp (list A))

      BIND : (P (Comp (list A))) -> (P A -> P (Comp B)) -> P (Comp B)

   I don't know which of the analogous monad laws these operators satisfy.

   Other semantic operators:

      NAT : nat -> P Value 

      ADD : P Value 

      NIL : P Value 

      CONS : P Value -> P Value -> P Value 

      LIST : list (P Value) -> P Value

      Λ : (P Value -> P (Comp (list Value))) -> P Value     -- note function bodies are computations

      APPLY : P Value -> P Value -> P (Comp (list Value))

   Environments. An `Env A` is an association list, associating each variable with an `A`. 

      This is a call-by-value language, so the environment contains the denotation of values.
   
       Rho := Env (P Value)

   Environment Notations:

       `ρ ⋅ x` -- lookup variable x in the environment, return bottom if not in domain

        x ~ a ++ ρ -- extend an environment with an association.

   Environment predicates:

       valid_env : Rho -> Prop    

       finite_env : Rho -> Prop   -- implies valid

   Denotation functions (mutually defined):

       denot     : tm -> Rho -> P (Comp (list Value))

       denot_val : tm -> Rho -> P Value

 *)


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

(* Sets of Values:   P Value === Value -> Prop *)

Definition finset : Type -> Type := list.

(* Finite sets of Values: fin Value === list Value *)

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

Definition mem_sub : list A -> list A -> Prop :=
  fun x y => mem x ⊆ mem y.

Definition mem_eq : list A -> list A -> Prop :=
  fun x y => mem x ≃ mem y.

Definition Comp_list_sub : Comp (list A) -> Comp (list A) -> Prop :=
  fun c1 c2 => 
    match c1 , c2 with 
    | c_wrong , c_wrong => True 
    | c_multi l1 , c_multi l2 => 
        List.Forall2 mem_sub l1 l2 
    | _ , _ => False
    end.

Definition Comp_list_eq : Comp (list A) -> Comp (list A) -> Prop :=
  fun c1 c2 => 
    match c1 , c2 with 
    | c_wrong , c_wrong => True 
    | c_multi l1 , c_multi l2 => 
        List.Forall2 mem_eq l1 l2 
    | _ , _ => False
    end.

Definition Comp_list_In (y : Comp (list A)) (X : P (Comp (list A))) : Prop :=
  exists x, Comp_list_eq x y /\ (x ∈ X).
Definition P_Comp_list_sub (X Y : P (Comp (list A))) : Prop := 
  forall x, Comp_list_In x X -> Comp_list_In x Y.
Definition P_Comp_list_eq (X Y : P (Comp (list A))) : Prop := 
  P_Comp_list_sub X Y /\ P_Comp_list_sub Y X.



#[export] Instance Reflexive_mem_sub : Reflexive mem_sub.
Admitted.
#[export] Instance Transitive_mem_sub : Transitive mem_sub.
Admitted.


#[export] Instance Reflexive_mem_eq : Reflexive mem_eq.
Admitted.
#[export] Instance Symmetric_mem_eq : Symmetric mem_eq.
Admitted.
#[export] Instance Transitive_mem_eq : Transitive mem_eq.
Admitted.


#[export] Instance Reflexive_Comp_list_sub : Reflexive Comp_list_sub.
Admitted.
#[export] Instance Transitive_Comp_list_sub : Transitive Comp_list_sub.
Admitted.

#[export] Instance Reflexive_Comp_list_eq : Reflexive Comp_list_eq.
Admitted.
#[export] Instance Symmetric_Comp_list_eq : Symmetric Comp_list_eq.
Admitted.
#[export] Instance Transitive_Comp_list_eq : Transitive Comp_list_eq.
Admitted.

#[export] Instance Proper_Comp_list_in : Proper (Comp_list_eq ==> P_Comp_list_eq ==> Logic.iff) Comp_list_In.
Proof. 
intros x1 x2 Eqx y1 y2 [S1 S2].
unfold P_Comp_list_sub in *.
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

Arguments Comp_list_sub {_}.
Arguments Comp_list_eq {_}.
Arguments Comp_list_In {_}.
Arguments P_Comp_list_sub {_}.
Arguments P_Comp_list_eq {_}.

(* \sim *)
Infix "∼" := P_Comp_list_eq (at level 85, right associativity).

(* \subsim *)
Infix "⫇" := P_Comp_list_sub (at level 85, right associativity).

(* this is \epsilon not \in *)
Infix "ϵ" := Comp_list_In (at level 85, right associativity).


(* If Y is finite, then it must be equal to X. *)
Definition finite {A} (X : P A) := 
  exists x, mem x ≃ X.

Definition APPROX {A} (x : list A) (Y : P A) := 
  (mem x ⊆ Y) /\ (finite Y -> mem x ≃ Y).

Infix "⊑" := APPROX (at level 85, right associativity).

Definition strict {A B} (f : P A -> P B) := f (fun x => False) ≃ (fun x => False) . 



(* ------------------------------------------------------- *)


(* `P (Comp A)` is *almost* a Monad *)

Definition RET {A} (X : P A) : P (Comp (list A)) :=
  fun z => match z with 
          | c_multi (V :: nil) => (mem V ⊆ X) /\ V <> nil
          |  _ => False
        end.

(* V must be nonempty because RET is strict. If V is empty then the 
   set should be empty. *)

Definition LIFT0 {A} (F : P A) : P (Comp (list A)) :=
  fun t =>  exists f : list A, 
      f <> nil /\ t = ret f /\ (mem f ⊆ F).

Definition LIFT1 {A B} (F : P A -> P B) (U : P (Comp (list A))) : P (Comp (list B)) :=
  fun t => 
    exists (u : Comp (list A)), exists (f : list A -> list B),
      (u ϵ U) /\ t = fmap f u /\ (forall a, Comp_In a u -> (f a) ⊑ F (mem a)).

Definition LIFT2 {A1 A2 B} (F : P A1 -> P A2 -> P B) : P (Comp (list A1)) -> P (Comp (list A2)) -> P (Comp (list B)) :=
  fun U1 U2 t => 
    exists u1, exists u2, exists (f : list A1 -> list A2 -> list B), 
      (u1 ϵ U1) /\ (u2 ϵ U2) /\ t = liftA2 f u1 u2 
      /\ (forall a1 , Comp_In a1 u1 -> forall a2, Comp_In a2 u2 -> (f a1 a2) ⊑ F (mem a1) (mem a2)).

Definition BIND {A B} (S : P (Comp (list A))) (K : P A -> P (Comp B)) (t : Comp B) : Prop :=
  exists (u : Comp (list A)), exists (k : list A -> Comp B), 
    (u ϵ S) /\ t = bind u k /\ forall a, Comp_In a u -> K (mem a) (k a).

(* RET is strict *)
Lemma strict_RET {A : Type} : strict (@RET A).
unfold strict. split.
- unfold RET. intros x xIn.
destruct x; try done.
destruct l; try done.
destruct l0; try done.
move: xIn => [h1 h2].
destruct l; try done.
specialize (h1 a ltac:(auto)). done.
- unfold RET.
  intros x xIn. done.
Qed.

(* LIFT0 is the **same** as RET *)

Lemma LIFT0_RET1 {A} {X : P A} : LIFT0 X ⊆ RET X.
Proof.
  intros x [f [h1 [-> h2]]]. 
  unfold RET.
  destruct f. cbn. done.
  cbn. split; auto.
Qed.

Lemma LIFT0_RET2 {A} {X : P A} : RET X ⊆ LIFT0 X.
Proof.
  intros x xIn.
  destruct x; unfold LIFT0, RET in *.
  cbn in xIn. done.
  cbn in xIn. 
  destruct l; try done.
  destruct l0; try done.
  destruct xIn.
  exists l. split. auto.
  split. auto.
  auto.
Qed.

(* LIFT1 is like FMAP *)

Lemma LIFT1_ID1 {A} (X: P (Comp (list A))) : LIFT1 id X ⫇ id X.
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
Qed.  

Axiom fmap_id : forall {A}{x : Comp A}, fmap id x = x.

Lemma LIFT1_ID2 {A} (x: P (Comp (list A))) : id x ⊆ LIFT1 id x.
Proof.
  unfold LIFT1, id.
  intros c cIn.
  exists c. exists id.
  split. auto.
  split. rewrite fmap_id. reflexivity.
  intro a. unfold id. reflexivity.
Qed.

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

Lemma LIFT2_left1 {A} (x : P A) (fy : P (Comp (list A))) :
  LIFT2 (fun _ y => y) (RET x) fy ⊆ fy.
Proof.
  unfold LIFT2, RET.
  intros z [u1 [u2 [f [h1 [h2 [-> h3]]]]]].
  destruct u1; try done.
  destruct l; try done.
  destruct l0; try done.
  move: h1 => [S1 NE].
  specialize (h3 l ltac:(left; auto)). 
  (* At this point we need mem (f l a2) = mem a2, not just be a subset. *)
Abort.

(* Because of the strictness of RET, we need to know that X is inhabited. *)
Lemma LIFT2_left2 {A} (x : A) (X : P A) (fy : P (Comp (list A))) :
  x ∈ X ->
  fy ⊆ LIFT2 (fun _ y => y) (RET X) fy.
Proof.
  intros xIn.
  unfold LIFT2, RET.
  intros y yIn.
  exists (c_multi ((x :: nil) :: nil)).
  exists y.
  exists (fun _ y => y).
  repeat split; auto.
  rewrite mem_singleton_eq. move=> z zIn. inversion zIn. subst; auto.
  done.
  rewrite liftA2_leftid. reflexivity.
  intros a1 a1In a2 a2In.
  reflexivity.
Qed.


Lemma LIFT2_COMP1 {A1 A2 B} (f : P A1 -> P A2 -> P B) (X : P A1) (Y : P A2) x y:
  x ∈ X -> 
  y ∈ Y -> 
  LIFT2 f (RET X) (RET Y) ⊆ RET (f X Y).
Proof.
  move=> xIn yIn.
  intros z zIn.
  destruct zIn as [u1 [u2 [g [h1 [h2 [-> h3]]]]]].
  destruct u1; try done.
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
Abort.

(* ----------------------------------------------------------- *)

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table *)
  | v_map : list Value -> Comp (list Value) -> Value

  (* trivial function value, evaluated to a value but never applied *)
  | v_fun : Value

  (* list/tuple of values *)
  | v_list : list Value -> Value.

(* EXAMPLE

Denotation of Identity function (\x.x):  

  any subset of 

 { vfun } `union` 
 { v_map (v_nat vi :: nil) (c_multi (v_nat vi) :: nil)  | for any value vi } 

 *)

#[export] Hint Constructors Value : core.

Infix "↦" := v_map (at level 85, right associativity).

(* ------------ Consistent ------------------ *)

(* Cannot be both consistent and inconsistent. *)
Definition exclusive {A} (f g : A -> A -> Prop) := forall x y, f x y -> g x y -> False.

Definition decidable {A} (f g : A -> A -> Prop) := forall x y, {f x y} + {g x y}.

(* ------------------------------------------------- *)
(* Pointwise lists *)

Definition ConsistentPointwiseList {A} (f : A -> A -> Prop) XS YS := 
  List.Forall2 f XS YS.
Definition InconsistentPointwiseList  {A} (g : A -> A -> Prop) XS YS := 
  length XS <> length YS \/ List.Exists2 g XS YS.

Section Computations.

Context 
  { A : Type }
  ( f : A -> A -> Prop )
  ( g : A -> A -> Prop )
  ( efg : exclusive f g)
  ( dfg : decidable f g).

Inductive ConsistentComp  : Comp A -> Comp A -> Prop :=
  | cc_wrong : ConsistentComp c_wrong c_wrong
  | cc_multi : forall AS BS, 
      ConsistentPointwiseList f AS BS ->
      ConsistentComp (c_multi AS) (c_multi BS).

Inductive InconsistentComp : Comp A -> Comp A -> Prop :=
  | i_wrong_multi : forall AS, InconsistentComp c_wrong (c_multi AS)
  | i_multi_wrong : forall AS, InconsistentComp (c_multi AS) c_wrong
  | i_multi : forall AS BS, InconsistentPointwiseList g AS BS -> InconsistentComp (c_multi AS) (c_multi BS).

End Computations.


#[export] Hint Constructors ConsistentComp InconsistentComp : core.

(* ------------------------------------------------- *)

(* Consistent values: we model function values as a set of approximations

   But now that we have different sorts of values, those approximations should
   all agree with eachother.

   We can define this concept by first identifying the head of a value. 
   Two values will *definitely* be inconsistent if they have different heads.
*)


Inductive v_head := 
    h_nat  : nat -> v_head 
  | h_fun  : v_head
  | h_list : v_head
.

Definition head (v : Value) : v_head := 
  match v with 
  | v_nat k => h_nat k
  | v_map _ _ => h_fun
  | v_fun     => h_fun
  | v_list _ => h_list
  end.

Inductive Consistent : Value -> Value -> Prop :=
  | c_nat : forall i, Consistent (v_nat i) (v_nat i)
  | c_list : forall XS YS, 
      ConsistentPointwiseList Consistent XS YS ->  
      Consistent (v_list XS) (v_list YS)

  | c_fun : Consistent v_fun v_fun
  | c_fun1 : forall X r, Consistent v_fun (X ↦ r)
  | c_fun2 : forall X r, Consistent (X ↦ r) v_fun

  | c_map2 : forall X1 X2 r1 r2, 
      ConsistentComp (List.Forall2_any Consistent) r1 r2 -> 
      Consistent (X1 ↦ r1) (X2 ↦ r2)
  | c_map1 : forall X1 X2 r1 r2, 
      List.Exists2_any Inconsistent X1 X2 ->
      Consistent (X1 ↦ r1) (X2 ↦ r2)

with Inconsistent : Value -> Value -> Prop :=
  | i_head : forall x y, 
      head x <> head y ->
      Inconsistent x y
  | i_list : forall XS YS, 
      InconsistentPointwiseList Inconsistent XS YS ->
      Inconsistent (v_list XS) (v_list YS)
  | i_map : forall X1 X2 r1 r2,
      List.Forall2_any Consistent X1 X2 ->
      ConsistentComp (List.Exists2_any Inconsistent) r1 r2 ->
      Inconsistent (X1 ↦ r1) (X2 ↦ r2).

#[export] Hint Constructors Consistent Inconsistent v_head : core.

(* Two sets are consistent if all of their elements 
   are consistent. *)
Definition ConsistentSets V1 V2 := 
    forall x y, x ∈ V1 -> y ∈ V2 -> Consistent x y.

Definition InconsistentSets V1 V2 := 
  exists x, exists y, (x ∈ V1) /\ (y ∈ V2) /\ (Inconsistent x y).

Definition ConsistentSet V := ConsistentSets V V.


(* ------------ Valid values and computations ------------------ *)


Definition valid (V : P Value) : Type :=
  nonemptyT V.

Definition valid_mem (V : list Value) : Prop :=
  V <> nil.

(* Produces at least one result *)

(*
Definition valid_Comp (C : P (Comp Value)) : Type :=
  (nonemptyT C * not (c_wrong ∈ C) * not (c_multi nil ∈ C))%type.
*)

(* ------------ Semantic Operators ------------------ *)

Definition NAT : nat -> P Value :=
  fun j v => match v with 
          | v_nat k => j = k
          | _ => False
          end.

Definition LIST : list (P Value) -> P Value  :=
  fun DS w => 
    match w with 
    | v_list WS => List.Forall2 Ensembles.In DS WS
    | _ => False
    end.

Definition NIL : P Value := ⌈ v_list nil ⌉.

Definition CONS : P Value -> P Value -> P Value := 
  fun V W x => 
    match x with 
    | v_list (v :: w) => (v ∈ V) /\ (v_list w ∈ W)  (* v should not be wrong *)
    | _ => False
    end.

Definition Λ : (P Value -> P (Comp (list Value))) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈ (f (mem V))) /\ valid_mem V  (* CBV *)
          | v_fun => True
          | _ => False
          end.


(* ------------ APPLY ----------------- *)

(* It is a little easier to specify this as an inductive relation 
   than as a function. The cases don't overlap, but we don't need
   to know that at definition time.
*)


(* When does APPLY diverge? (i.e. there is no w, s.t. APPLY D1 D2 w holds)
    - D1 is empty
    - D2 is empty
    - D1 contains a vfun or V ↦ x, but cannot be applied to D2
           << should this be empty or wrong??? >> 

   When does APPLY propagate wrong?
    - wrong in D1 or D2  (FUNWRONG / ARGWRONG) 
    - V ↦ wrong in D1 and valid V in D2  (BETA case)

   When does APPLY create a new wrong? 
    - D1 contains a successful Value that is not a v_fun, v_map or v_list  (APPWRONG)
    - D1 contains a v_list and D2 contains a successful Value that is not a nat (PROJWRONG)
           
*)

Inductive applicable : Value -> Prop :=
  | a_fun  : applicable v_fun
  | a_list : forall VS, applicable (v_list VS)
  | a_map  : forall V w, applicable (v_map V w).

#[export] Hint Constructors applicable : core.

Inductive APPLY : P Value -> P Value -> (Comp (list Value) -> Prop) :=
  | BETA : forall D1 D2 w V,
      (V ↦ w) ∈ D1 ->
     (mem V ⊆ D2) -> valid_mem V ->
     APPLY D1 D2 w

(* NOTE: this definition is wrong! need to incorporate eta-expansion here to order for exists

  <v1 ... vn > i == (i=0;v1) | .. | (i=n;vn)

*)
 
  | PROJ   : forall D1 D2 w VS k, 
     (v_list VS) ∈ D1 ->
     (v_nat k ∈ D2) -> nth_error VS k = Some w ->
     APPLY D1 D2 (ret (w  :: nil))
  | APPWRONG : forall D1 D2 x, 
      x ∈ D1 ->
      not (applicable x) ->      
      APPLY D1 D2 c_wrong
  | PROJWRONG : forall D1 D2 VS x, 
     (v_list VS) ∈ D1 ->
     (x ∈ D2) -> 
     (forall k, x <> (v_nat k)) ->
     APPLY D1 D2 c_wrong. 

Infix "▩" := APPLY (at level 90).

#[export] Hint Constructors APPLY : core.

Definition ADD : P Value :=
  fun w => 
    match w with 
    | (V ↦ c_multi (K :: nil)) => 
        exists i j k, (mem V ≃ ⌈ v_list (v_nat i :: v_nat j :: nil) ⌉) /\ (mem K ≃ ⌈ v_nat k ⌉) /\ (k = i + j)
    | V ↦ c_wrong => 
        not (exists i j, v_list (v_nat i :: v_nat j :: nil) ∈ mem V) /\ valid_mem V
    | _ => False
    end.



(* ------------ LOGIC PROGRAMMING ----------------- *)

Definition ONE (C : P (Comp (list Value))) : P Value :=
  fun v => exists V, exists l, (c_multi (V  :: l) ∈ C) /\ List.In v V.

Definition ALL (C : P (Comp (list Value))) : P Value :=
  fun v => match v with 
          | v_list l => c_multi (List.map ret l) ∈ C 
          | _ => False
        end.

Definition FAIL : P (Comp (list Value)) := ⌈ c_multi nil ⌉.

Definition CHOICE (C1 : P (Comp (list Value))) (C2 : P (Comp (list Value))) : 
  P (Comp (list Value)) := 
  fun c => 
    match c with 
    | c_multi l => 
        exists l1, exists l2, l = l1 ++ l2 /\ (c_multi l1 ∈ C1) /\ (c_multi l2 ∈ C2)
    | _ => False
    end.

Definition SEQ (C1 : P (Comp (list Value))) (C2 : P (Comp (list Value))) : 
  P (Comp (list Value)) := BIND C1 (fun x => C2).

(* Fails when V and W don't unify. Returns their union when they do. *)
(* Can we replace last line below with "Consistent sets"? *)

Definition UNIFY (V : P Value) (W: P Value) : P (Comp (list Value)) :=
  fun c => match c with 

        | c_multi nil => InconsistentSets V W

        | c_multi (l :: nil) => 
            exists l1, exists l2, l = l1 ++ l2 /\ l1 <> nil /\ l2 <> nil 
           /\ (mem l1 ⊆ V) /\ (mem l2 ⊆ W)
           /\ List.Forall2_any Consistent l1 l2

        | _ => False
  end.
    
(* Questions: Do we make sure the existentially chosen value is consisten? 
   What about the final set? (Can we do that elsewhere?)
*)

Definition EXISTS (f : P Value -> P (Comp (list Value))) : P (Comp (list Value)) :=
  fun c => exists V, (List.Forall2_any Consistent V V) /\ (c ∈ f (mem V)).



(* ------------------------------------------------------- *)

Definition Rho := Env (P Value).

Definition Bottom : P Value := fun x => False.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).

Module EnvNotations.
Notation "ρ ⋅ x" := (Env.access Bottom ρ x) (at level 50).
Infix "⊔e" := (Env.map2 Union) (at level 60).
Infix "⊆e" := (Env.Forall2 Included) (at level 50).
End EnvNotations.
Import EnvNotations.

(* ------------------------------------------------------- *)


Definition monotone {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* aka sub_preserving *)
Definition sub_reflecting {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, F D1 ⊆ F D2 -> (D1 ⊆ D2).

Definition monotone_env {A} (D : Rho -> P A) := 
  forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

Definition finite {B} (X : P B) : Prop := 
  exists E, (X ≃ mem E) /\ E <> nil.

Definition finite_env : Rho -> Prop := Env.Forall finite.
  
(* ------------------------------------------------------- *)

Definition nonempty_env : Rho -> Type := Env.ForallT nonemptyT.

Definition valid_env : Rho -> Type := Env.ForallT valid. 

Definition sub_env : Rho -> Rho -> Prop := Env.Forall2 Included.

Definition same_env : Rho -> Rho -> Prop := Env.Forall2 Same_set.

(* ------------------------------------------------------- *)

Import LCNotations.
Open Scope tm.

Fixpoint exn (n : nat) (t: tm) : tm :=
  match n with 
  | 0 => t
  | S n => ex (exn n t)
  end.

Fixpoint choice_free (t : tm) : bool :=
  match t with 
  | choice t u => false
  | seq t u => choice_free t && choice_free u 
  | unify t u => choice_free t && choice_free u 
  | ex u => choice_free u
  | _ => true
  end.

Inductive CX := CX_hole | CX_seq1 of tm | CX_seq2 of tm | CX_unify1 of tm | CX_unify2 of tm | CX_ex of tm.

(* CX := [] | v = CX ; e | CX ; e | ceq ; CX | exists x. CX *)

(*  CX [ e1 || e2 ] =>  CX [e1] || CX [e2] *)

(* Pull out inner choice expressions, in order *)
(* 
Fixpoint choose  (s : tm) : CX * list tm :=
  match s with 
  | choice t u => CX_hole , t :: u :: nil
  | seq t u => 
  | unify t u => 
  | ex t =>
  | _ => s 
  end *)


(* Denotation function *)
(* `n` is is a termination metric. *)
Fixpoint denot_comp_n (n : nat) (a : tm) (ρ : Rho) : P (Comp (list Value)) :=
  let fix denot_val_n (n : nat) (a : tm) (ρ : Rho) : P Value :=
  match n with
  | O => fun x => False
  | S m => 
     match a with 
     | var_b _ => fun x => False

     | var_f x => ρ ⋅ x 

     | abs t => 
        let x := fresh_for (dom ρ \u fv_tm t) in 
        (Λ (fun D => (denot_comp_n m (t ^ x) (x ~ D ++ ρ))))

     | tcons t u => CONS (denot_val_n m t ρ) (denot_val_n m u ρ)

     | lit k => NAT k

     | add => ADD

     | tnil => NIL

     | _ => fun x => False
     end
  end in
  match n with
  | O => ∅
  | S m => 
      match a with 
       | app t u   => 
           BIND (denot_comp_n m t ρ) (fun v1 =>
             BIND (denot_comp_n m u ρ) (fun v2 =>
             (v1 ▩ v2))) 

       | tcons t u => 
           RET CONS <*> (denot_comp_n m t ρ) <*> (denot_comp_n m u ρ)
(*
           BIND (denot_comp_n m t ρ) (fun v1 =>
           BIND (denot_comp_n m u ρ) (fun v2 => 
           RET (CONS v1 v2 ))) *)

       | fail => FAIL

       | choice t u => CHOICE (denot_comp_n m t ρ) (denot_comp_n m u ρ)

       | ex t => let x := fresh_for (dom ρ \u fv_tm t) in 
                EXISTS (fun D => (denot_comp_n m (t ^ x) (x ~ D ++ ρ)))

       | seq t u =>   
           SEQ (denot_comp_n m t ρ) (denot_comp_n m u ρ)

       | unify t u =>  
           BIND (denot_comp_n m t ρ) (fun v1 =>
           BIND (denot_comp_n m u ρ) (fun v2 =>
           (UNIFY v1 v2)))

       | one t => RET (ONE (denot_comp_n m t ρ))

       | all t => RET (ALL (denot_comp_n m t ρ))
  
       | _ => RET (denot_val_n n a ρ)
     end

  end.

Fixpoint denot_val_n (n : nat) (a : tm) (ρ : Rho) : P Value :=
  match n with
  | O => fun x => False
  | S m => 
     match a with 
     | var_b _ => fun x => False

     | var_f x => ρ ⋅ x 

     | abs t => c
        let x := fresh_for (dom ρ \u fv_tm t) in 
        (Λ (fun D => (denot_comp_n m (t ^ x) (x ~ D ++ ρ))))

     | tcons t u => CONS (denot_val_n m t ρ) (denot_val_n m u ρ)

     | lit k => NAT k

     | add => ADD

     | tnil => NIL

     | _ => fun x => False
     end
  end.

Definition denot (a : tm) := denot_comp_n (size_tm a) a.
Definition denot_val (a : tm) := denot_val_n (size_tm a) a.

#[export] Hint Opaque denot : core.
#[export] Hint Opaque denot_val : core.


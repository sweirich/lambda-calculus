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

   The denotation of both values and computations includes the empty set: the
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
   this definition. 

   So I have used the types above, and have defined the
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

      Λ : (P Value -> P (Comp (list Value))) -> P Value     
             -- note function bodies are computations, so functions can 
             -- produce errors or multiple results

      APPLY : P Value -> P Value -> P (Comp (list Value))
             -- application requires two (valid) values because we can use 
             -- BIND above to sequence the computations first

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
Require Import semantic_notions.
Require Import QuasiMonad.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.


(*
Definition PP (A : Type) : Type := { V : P A |  nonempty V}.

Definition PP_Singleton {A : Type} (x : A) : PP A := 
  exist (fun V : P A => nonempty V) ⌈ x ⌉ (Inhabited_intro A ⌈ x ⌉ x in_singleton).

Definition PP_In {A : Type} (s : PP A) (x : A) : Prop.
destruct s as [x0 _]. exact (x0 x). Defined.

Definition PP_Included {A : Type} (x : PP A) (y : PP A) : Prop := forall z, PP_In x z -> PP_In y z.

Definition PP_Union {A : Type} (x : PP A) (y : PP A) : PP A.
  destruct x. destruct y. exists (Union x x0). 
  destruct n. destruct n0.
  eapply Inhabited_intro with (x := x1).
  econstructor. exact H.
Defined.

Definition PP_Same_set {A : Type} (x : PP A) (y : PP A) : Prop.
  destruct x as [s _]. destruct y as [t _]. 
  exact (Same_set s t). 
Defined.
  
Declare Scope pset_scope.
Delimit Scope pset_scope with PP.
Bind Scope pset_scope with PP.

Module PSetNotations. 
  Notation "x ∈ s" := (PP_In s x) : pset_scope .
  Notation "⌈ x ⌉" := (PP_Singleton x) : pset_scope.
  Infix "⊆" := PP_Included : pset_scope.
  Infix "∪" := PP_Union : pset_scope.
  Infix "≃" := PP_Same_set : pset_scope.
End PSetNotations.

Import PSetNotations.
Open Scope pset_scope.

*)
  
(* ----------------------------------------------------------- *)

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table *)
  | v_map : forall (x: list Value), Comp Value -> Value

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
    | v_list (v :: w) => (v ∈ V) /\ (v_list w ∈ W)  
    | _ => False
    end.

Definition coerce (w : Comp Value) : Comp (vfin Value) := 
  fmap (fun x => 
  match w with 
  | c_wrong => X c_wrong
  | c_multi lw => 
      match c with 
    | c_wrong => False
    | c_multi l => List.Forall2 (fun v vf => v ∈ vmem vf) w l
    end.

Definition Λ : (P Value -> P (Comp (vfin Value))) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈ (f (mem V))) /\ valid_mem V  (* CBV *)
          | v_fun => True
          | _ => False
          end.


(* ------------ LOGIC PROGRAMMING ----------------- *)

Definition ONE (C : P (Comp (list Value))) : P Value :=
  fun v => exists l, c_multi (ret v  :: l) ∈ C.

Definition ALL (C : P (Comp (list Value))) : P Value :=
  fun v => match v with 
          | v_list l => c_multi (List.map ret l) ∈ C 
          | _ => False
        end.

Definition FAIL : P (Comp (list Value)) := ⌈ c_multi nil ⌉.

Definition CHOOSE (C1 : P (Comp (list Value))) (C2 : P (Comp (list Value))) : 
  P (Comp (list Value)) := 
  fun c => 
    match c with 
    | c_multi l => 
        exists l1, exists l2, l = l1 ++ l2 /\ (c_multi l1 ∈ C1) /\ (c_multi l2 ∈ C2)
    | _ => False
    end.

(* Fails when V and W don't unify. Returns their union when they do. *)
(* Need to define inconsistent here.

Definition UNIFY (V : P Value) (W: P Value) : P (Comp (list Value)) :=
  fun c => match c with 

        | c_multi nil => 
            exists v, exists w, v ∈ V /\ w ∈ W /\ Inconsistent v w

        | c_multi (l :: nil) => (mem l ⊆ V ∪ W) /\ l <> nil

        | _ => False
  end.
*)    
  

(* ------------------------------------------ *)

(* This definition includes all values that produce c. *)

Definition EXISTS (f : P Value -> P (Comp (list Value))) : P (Comp (list Value)) :=
  fun c => exists V, c ∈ f (mem V).

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
           BIND (denot_comp_n m t ρ) (fun v1 =>
           BIND (denot_comp_n m u ρ) (fun v2 => 
           RET (CONS v1 v2 )))

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

     | abs t => 
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


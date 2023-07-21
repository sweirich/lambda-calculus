(* Definitions related to the denotational semantics.
   
   The semantic domain: `P Value` 

   Predicates:

      success : Value -> Prop     (Does this result approximate a lambda-calculus value?)

      valid : P Value -> Prop     (is the set nonempty & only contain successful values?)

   Semantic operators:

    WRONG : P Value   

    NAT   : nat -> P Value
    NIL   : P Value
    CONS  : P Value -> P Value -> P Value
    Λ     : (P Value -> P Value) -> P Value :=
    APPLY : P Value -> P Value -> P Value

   Environments:    
   
       Rho := Env (P Value)

   Environment Notations:

   Environment predicates:

       valid_env : Rho -> Prop

   Denotation function:

       denot : tm -> Rho -> P Value

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

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table *)
  | v_map : list Value -> Value -> Value

  (* trivial function value, evaluated to a value but never applied *)
  | v_fun : Value

  (* list/tuple of values *)
  | v_list : list Value -> Value

  (* dynamic type error *)
  | v_wrong : Value

  (* result of failing function *)
  | v_fail : Value

.

#[export] Hint Constructors Value : core.

Infix "↦" := v_map (at level 85, right associativity).

(* A successful value is not wrong, nor a multiple value. *)
Definition success (v : Value) : Prop :=
  match v with 
  | v_wrong => False
  | v_fail => False
  | _ => True
  end.



(* ------------ Valid or a denotation that represents a single value ------------------ *)

Definition valid (V : P Value) : Type :=
  nonemptyT V * Sets.Forall success V.

Definition valid_mem (V : list Value) : Prop :=
  V <> nil /\ List.Forall success V.

(* ------------  Semantic Operators ------------------ *)

Definition WRONG : P Value := ⌈ v_wrong ⌉.

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

(* ------------ LAMBDA ----------------- *)

Definition Λ : (P Value -> P Value) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈ f (mem V)) /\ valid_mem V  (* CBV *)
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

   When does APPLY propagate wrong?
    - wrong in D1 or D2  (FUNWRONG / ARGWRONG) 
    - V ↦ wrong in D1 and valid V in D2  (BETA case)

   When does APPLY create a new wrong? 
    - D1 contains a successful Value that is not a v_fun, v_map or v_list  (APPWRONG)
    - D1 contains a v_list and D2 contains a successful Value that is not a nat (PROJWRONG)

   NOTE: projecting from a tuple with an invalid index should be fail, not go wrong.
           
*)

Inductive applicable : Value -> Prop :=
  | a_fun  : applicable v_fun
  | a_list : forall VS, applicable (v_list VS)
  | a_map  : forall V w, applicable (v_map V w).

#[export] Hint Constructors applicable : core.

Inductive APPLY : P Value -> P Value -> Value -> Prop :=

  | FUNWRONG : forall D1 D2 x,
     (x ∈ D1) ->
     not (success x) ->
     APPLY D1 D2 x

  | ARGWRONG : forall D1 D2 x,
     valid D1 ->              (* don't overlap FUNWRONG *)
     (x ∈ D2) ->
     APPLY D1 D2 x

  | BETA : forall D1 D2 w V,
     (V ↦ w ∈ D1) -> (mem V ⊆ D2) -> valid_mem V ->
     APPLY D1 D2 w

  | PROJ   : forall D1 D2 w VS k, 
     (v_list VS ∈ D1) -> (v_nat k ∈ D2) -> nth_error VS k = Some w ->
     APPLY D1 D2 w

  | APPWRONG : forall D1 D2 x, 
      x ∈ D1 -> success x -> not (applicable x) ->      
      APPLY D1 D2 v_wrong

  | PROJWRONG : forall D1 D2 VS x, 
     (v_list VS ∈ D1) -> 
     (x ∈ D2) -> success x ->
     (forall k, x <> (v_nat k)) ->
     APPLY D1 D2 v_wrong

  | PROJFAIL : forall D1 D2 VS k, 
     (v_list VS ∈ D1) -> 
     (v_nat k ∈ D2) -> 
     nth_error VS k = None ->  (* out of bounds index is fail *)
     APPLY D1 D2 v_fail
. 

Infix "▩" := APPLY (at level 90).


#[export] Hint Constructors APPLY : core.

Definition ADD : P Value :=
  fun w => 
    match w with 
    | (V ↦ v_nat k) => 
        exists i j, ((v_list (v_nat i :: v_nat j :: nil)) ∈ mem V) /\ k = i + j
    | V ↦ v_wrong => 
        not (exists i j, v_list (v_nat i :: v_nat j :: nil) ∈ mem V) /\ valid_mem V
    | _ => False
    end.

Definition GT : P Value :=
  fun w => 
    match w with 
    | (V ↦ v_nat i) => 
        exists i j, ((v_list (v_nat i :: v_nat j :: nil)) ∈ mem V) /\ i > j 
    | (V ↦ v_fail) => 
        exists i j, ((v_list (v_nat i :: v_nat j :: nil)) ∈ mem V) /\ not (i > j)
    | V ↦ v_wrong => 
        not (exists i j, v_list (v_nat i :: v_nat j :: nil) ∈ mem V) /\ valid_mem V
    | _ => False
    end.


(* ------------------------------------------------------- *)

Definition Rho := Env (P Value).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).

Module EnvNotations.
Notation "ρ ⋅ x" := (Env.access ⌈ v_wrong ⌉ ρ x) (at level 50).
Infix "⊔e" := (Env.map2 Union) (at level 60).
Infix "⊆e" := (Env.Forall2 Included) (at level 50).
End EnvNotations.
Import EnvNotations.

(* ------------------------------------------------------- *)

Definition nonempty_env : Rho -> Type := Env.ForallT nonemptyT.

Definition valid_env : Rho -> Type := Env.ForallT valid. 

Definition sub_env : Rho -> Rho -> Prop := Env.Forall2 Included.

Definition same_env : Rho -> Rho -> Prop := Env.Forall2 Same_set.

(* ------------------------------------------------------- *)

Definition M := list.

Definition ONE (ws : M (P Value)) : P Value :=
  fun v => 
    match ws with 
    | nil => v = v_wrong  (* need to make this fail *)
    | w :: _ => v ∈ w
    end.

Definition ALL (ws : M (P Value)) : P Value :=
  fun v => 
    match v with 
    | v_list vs => List.Forall2 Sets.In vs ws
    | _ => False
    end.

(* ------------------------------------------------------- *)

Import LCNotations.
Open Scope tm.

(* Denotation function *)
(* `n` is is a termination metric. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Rho) : M (P Value) :=
  match n with
  | O => ret (fun _ => False)

  | S m => 
     match a with 

       | app t u   => 
           v1 <- denot_n m t ρ ;;
           v2 <- denot_n m u ρ ;;
           ret (v1 ▩ v2)

       | tcons t u => 
           v1 <- denot_n m t ρ ;;
           v2 <- denot_n m u ρ ;;
           ret (CONS v1 v2)

       | _ => ret (denot_v_n m a ρ)
     end
  end
with denot_v_n (n : nat) (a : tm) (ρ : Rho) : P Value :=
  match n with
  | O => fun _ => False
  | S m => 
    match a with 

    | var_f x => ρ ⋅ x

    | lit k => NAT k

    | add => ADD

    | tnil => NIL

    | abs t => 
        let x := fresh_for (dom ρ \u fv_tm t) in 
        (Λ (fun D => ONE (denot_n m (t ^ x) (x ~ D ++ ρ))))

    | _ => fun _ => False

    end
  end.
 

Definition denot (a : tm) := denot_n (size_tm a) a.

Hint Opaque denot.



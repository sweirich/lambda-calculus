Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.Container.

Require Import lc.List.
Require Import lc.Env.

Require Import lc.Monad.
Import MonadNotation.
Open Scope monad_scope.

Require Import lc.Sets.
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
.

#[export] Hint Constructors Value : core.

Infix "↦" := v_map (at level 85, right associativity).

(* A successful value is not wrong. *)
Definition success (v : Value) : Prop :=
  match v with 
  | v_wrong => False
  | _ => True
  end.


(* ------------ Valid or "succeeds" ------------------ *)

Definition valid (V : P Value) : Type :=
  nonemptyT V * Sets.Forall success V.

Definition valid_mem (V : list Value) : Prop :=
  V <> nil /\ List.Forall success V.

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

Definition Λ : (P Value -> P Value) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈ f (mem V)) /\ valid_mem V  (* CBV *)
          | v_fun => True
          | _ => False
          end.

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

Inductive APPLY : P Value -> P Value -> Value -> Prop :=
  | FUNWRONG : forall D1 D2,
     (v_wrong ∈ D1) ->
     APPLY D1 D2 v_wrong
  | ARGWRONG : forall D1 D2,
     (v_wrong ∈ D2) ->
     APPLY D1 D2 v_wrong
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
     APPLY D1 D2 v_wrong. 

Infix "▩" := APPLY (at level 90).


#[export] Hint Constructors APPLY : core.

Definition ADD : P Value :=
  fun w => 
    match w with 
    | (V ↦ v_nat k) => 
        exists i j, ((v_list (v_nat i :: v_nat j :: nil)) ∈ mem V) /\ k = i + j
    | V ↦ v_wrong => 
        not (exists i j, v_list (v_nat i :: v_nat j :: nil) ∈ mem V)
    | _ => False
    end.

(* ------------------------------------------------------- *)

Definition finite (X : P Value) : Prop := 
  exists E, (X ≃ mem E) /\ E <> nil.

Definition continuous (F : P Value -> P Value) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

Definition monotone (F : P Value -> P Value) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

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
Notation "ρ ⋅ x" := (access ⌈ v_wrong ⌉ ρ x) (at level 50).
Infix "⊔e" := (map2 Union) (at level 60).
Infix "⊆e" := (Env.Forall2 Included) (at level 50).
End EnvNotations.
Import EnvNotations.

Definition nonempty_env : Rho -> Type := Env.ForallT nonemptyT.

Definition valid_env : Rho -> Type := Env.ForallT valid. 

Definition finite_env : Rho -> Type := Env.ForallT finite.

Definition monotone_env (D : Rho -> P Value) := 
  forall ρ ρ' , ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

Definition continuous_In (D:Rho -> P Value) (ρ:Rho) (v:Value) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env (D:Rho -> P Value) (ρ:Rho) : Prop :=
  forall v, continuous_In D ρ v.

(* ------------------------------------------------------- *)

Definition sub_env : Rho -> Rho -> Prop := Env.Forall2 Included.

Definition same_env : Rho -> Rho -> Prop := Env.Forall2 Same_set.

(* ------------------------------------------------------- *)

Import LCNotations.
Open Scope tm.

(* Denotation function *)
(* `n` is is a termination metric. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Rho) : P Value :=
  match n with
  | O => fun _ => False
  | S m => 
     match a with 
     | var_b _ => ⌈ v_wrong ⌉
     | var_f x => ρ ⋅ x 
     | app t u   => 
         denot_n m t ρ ▩ denot_n m u ρ
     | abs t => 
         let x := fresh_for (dom ρ \u fv_tm t) in 
         Λ (fun D => denot_n m (t ^ x) (x ~ D ++ ρ))
     | lit k => NAT k
     | add => ADD
     | tnil => NIL
     | tcons t u => CONS (denot_n m t ρ) (denot_n m u ρ)
     end
  end.


(* ------------------------------------------------- *)

(* Consistent values: we model function values as a set of approximations

   But now that we have different sorts of values, those approximations should
   all agree with eachother.

   We can define this concept by first identifying the head of a value. 
   Two values will *definitely* be inconsistent if they have different heads.
   But they could have the same head if inside the value

*)

Inductive v_head := 
   h_nat  : nat -> v_head 
  | h_fun  : v_head
  | h_list : v_head
  | h_wrong : v_head 
.

Definition head (v : Value) : v_head := 
  match v with 
  | v_nat k => h_nat k
  | v_map _ _ => h_fun
  | v_fun => h_fun
  | v_list _ => h_list
  | v_wrong => h_wrong
  end.


Inductive Consistent : Value -> Value -> Prop :=
  | c_nat : forall i, Consistent (v_nat i) (v_nat i)
  | c_list : forall XS YS, List.Forall2 Consistent XS YS ->  Consistent (v_list XS) (v_list YS)
  | c_wrong : Consistent v_wrong v_wrong

  | c_fun : Consistent v_fun v_fun
  | c_fun1 : forall X r, Consistent v_fun (X ↦ r)
  | c_fun2 : forall X r, Consistent (X ↦ r) v_fun

  | c_map2 : forall X1 X2 r1 r2, 
      Consistent r1 r2 -> 
      Consistent (X1 ↦ r1) (X2 ↦ r2)
  | c_map1 : forall X1 X2 r1 r2, 
      Exists2_any Inconsistent X1 X2 ->
      Consistent (X1 ↦ r1) (X2 ↦ r2)

with Inconsistent : Value -> Value -> Prop :=
  | i_head : forall x y, 
      head x <> head y ->
      Inconsistent x y
  | i_list_l : forall XS YS, 
      length XS <> length YS ->
      Inconsistent (v_list XS) (v_list YS)      
  | i_list_e : forall XS YS,
      List.Exists2 Inconsistent XS YS ->
      Inconsistent (v_list XS) (v_list YS)
  | i_map : forall X1 X2 r1 r2,
      Forall2_any Consistent X1 X2 ->
      Inconsistent r1 r2 ->
      Inconsistent (X1 ↦ r1) (X2 ↦ r2).

#[export] Hint Constructors Consistent Inconsistent v_head : core.


(* Two sets are consistent if all of their elements 
   are consistent. *)
Definition ConsistentSets V1 V2 := 
    forall x y, x ∈ V1 -> y ∈ V2 -> Consistent x y.

Definition ConsistentSet V := ConsistentSets V V.

Definition consistent_env : Rho -> Type := Env.ForallT ConsistentSet. 

(* ------------------------------------------------------------------------------- *)


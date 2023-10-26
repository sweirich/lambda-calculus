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


(* 
   Infinite sets of Values:   P Value      (i.e. Value -> Prop)
   Finite sets of Values:     fset Value   (i.e. list Value)

*)

(* ------------------------------------------------------- *)

Definition RET {A} (x : P A) : P (Comp (fset A)) :=
  fun z => match z with 
          | c_multi (V :: nil) => (mem V ⊆ x) /\ nonempty_fset V
          |  _ => False
        end.

Definition BIND {A B} (S : P (Comp (fset A))) (K : P A -> P (Comp B)) (t : Comp B) : Prop :=
  exists (u : Comp (fset A)), exists (k : fset A -> Comp B), 
    (u ∈ S) /\ t = bind u k /\ forall a, Comp_In a u -> K (mem a) (k a).


(* ----------------------------------------------------------- *)

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table *)
  | v_map : fset Value -> Comp (fset Value) -> Value

  (* trivial function value, evaluated to a value but never applied *)
  | v_fun : Value

  (* list/tuple of values *)
  | v_list : list Value -> Value.

(* EXAMPLE

Denotation of Identity function (\x.x):  

  any subset of 

 { vfun } `union` 
 { v_map [v_nat vi] (c_multi ([v_nat vi] :: nil))  | for any value vi } 

 *)

#[export] Hint Constructors Value : core.

Infix "↦" := v_map (at level 85, right associativity).

(* ------------ Consistent ------------------ *)

Class Consistency (A : Type) : Type := 
  { Consistent : A -> A -> Prop ;
    Inconsistent : A -> A -> Prop ;
  }.

Section List.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Definition Consistent_list := List.Forall2 f.
Definition Inconsistent_list := fun XS YS => 
  length XS <> length YS \/ List.Exists2 g XS YS.

End List.

#[export] Instance Consistency_list { A : Type } `{ Consistency A } : Consistency (list A) := 
  { Consistent := Consistent_list (f := Consistent) ;
    Inconsistent := Inconsistent_list (g := Inconsistent) ;
  }.

Section FSet.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Definition Consistent_fset := fun '(FSet XS) '(FSet YS) => List.Forall2_any f XS YS.
Definition Inconsistent_fset := fun '(FSet XS) '(FSet YS) => List.Exists2_any g XS YS.


#[export] Instance Consistency_fset { A : Type}  `{ Consistency A } : Consistency (fset A) := 
  { Consistent := Consistent_fset (f := Consistent) ;
    Inconsistent := Inconsistent_fset (g := Inconsistent) ;
  }.

Section Computations.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Inductive ConsistentComp  : Comp A -> Comp A -> Prop :=
  | cc_wrong : ConsistentComp c_wrong c_wrong
  | cc_multi : forall AS BS, 
      List.Forall2 f AS BS ->
      ConsistentComp (c_multi AS) (c_multi BS).

Inductive InconsistentComp : Comp A -> Comp A -> Prop :=
  | i_wrong_multi : forall AS, InconsistentComp c_wrong (c_multi AS)
  | i_multi_wrong : forall AS, InconsistentComp (c_multi AS) c_wrong
  | i_multi : forall AS BS, 
      (length AS <> length BS \/ List.Exists2 g AS BS) -> 
      InconsistentComp (c_multi AS) (c_multi BS).

End Computations.

#[export] Instance Consistency_Comp {A:Type} `{Consistency A} : Consistency (Comp A) := 
  { Consistent := ConsistentComp (f:=Consistent) ; Inconsistent := InconsistentComp (g := Inconsistent) }.

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

Inductive ConsistentValue : Value -> Value -> Prop :=
  | c_nat  : forall i, ConsistentValue (v_nat i) (v_nat i)
  | c_list : forall (XS YS : list Value), 
      Consistent_list (f := ConsistentValue) XS YS ->      
      ConsistentValue (v_list XS) (v_list YS)

  | c_fun  : ConsistentValue v_fun v_fun
  | c_fun1 : forall X r, ConsistentValue v_fun (X ↦ r)
  | c_fun2 : forall X r, ConsistentValue (X ↦ r) v_fun

  | c_map2 : forall X1 X2 r1 r2, 
      Inconsistent_fset_Value X1 X2 ->
      ConsistentValue (X1 ↦ r1) (X2 ↦ r2)
  | c_map1 : forall X1 X2 r1 r2, 
      Consistent_fset_Value X1 X2 ->
      ConsistentComp (f := Consistent_fset_Value) r1 r2 ->  
      ConsistentValue (X1 ↦ r1) (X2 ↦ r2) 

with InconsistentValue : Value -> Value -> Prop :=
  | i_head : forall x y, 
      head x <> head y ->
      InconsistentValue x y
  | i_list : forall XS YS, 
      Inconsistent_list (g := InconsistentValue) XS YS ->
      InconsistentValue (v_list XS) (v_list YS)
  | i_map : forall X1 X2 r1 r2,
      Consistent_fset_Value X1 X2 ->
      InconsistentComp (g := Inconsistent_fset_Value) r1 r2 -> 
      InconsistentValue (X1 ↦ r1) (X2 ↦ r2)
with Consistent_fset_Value : fset Value -> fset Value -> Prop :=
  | c_fset : forall X1 X2, 
    Consistent_fset (f := ConsistentValue) (FSet X1) (FSet X2) -> 
    Consistent_fset_Value (FSet X1) (FSet X2)
with Inconsistent_fset_Value : fset Value -> fset Value -> Prop :=
  | i_fset : forall X1 X2, 
    Inconsistent_fset (g := InconsistentValue) (FSet X1) (FSet X2) -> 
    Inconsistent_fset_Value (FSet X1) (FSet X2).


#[export] Hint Constructors ConsistentValue InconsistentValue Consistent_fset_Value Inconsistent_fset_Value v_head : core.

Instance Consistency_Value : Consistency Value :=
  { Consistent := ConsistentValue ; Inconsistent := InconsistentValue }.

(* Two sets are consistent if all of their elements 
   are consistent. *)
Definition ConsistentSets {A:Type} `{Consistency A} V1 V2 := 
    forall x y, x ∈ V1 -> y ∈ V2 -> Consistent x y.

Definition InconsistentSets {A:Type} `{Consistency A} V1 V2 := 
  exists x, exists y, (x ∈ V1) /\ (y ∈ V2) /\ (Inconsistent x y).

#[export] Instance Consistency_P {A:Type} `{Consistency A} : Consistency (P A) :=
   { Consistent := ConsistentSets ; Inconsistent := InconsistentSets }.


Definition ConsistentSet {A:Type} `{Consistency A} (V : P A) := ConsistentSets V V.


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

Definition Λ : (P Value -> P (Comp (fset Value))) -> P Value :=
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

Inductive APPLY : P Value -> P Value -> (Comp (fset Value) -> Prop) :=
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
     APPLY D1 D2 (ret (singleton_fset w))
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


Definition ONE (C : P (Comp (fset Value))) : P Value :=
  fun v => exists l, c_multi (singleton_fset v  :: l) ∈ C.

Definition ALL (C : P (Comp (fset Value))) : P Value :=
  fun v => match v with 
          | v_list l => c_multi (List.map singleton_fset l) ∈ C 
          | _ => False
        end.

Definition FAIL : P (Comp (fset Value)) := ⌈ c_multi nil ⌉.

Definition CHOICE (C1 : P (Comp (fset Value))) (C2 : P (Comp (fset Value))) : 
  P (Comp (fset Value)) := 
  fun c => 
    match c with 
    | c_multi l => 
        exists l1, exists l2, l = l1 ++ l2 /\ (c_multi l1 ∈ C1) /\ (c_multi l2 ∈ C2)
    | _ => False
    end.

Definition SEQ (C1 : P (Comp (fset Value))) (C2 : P (Comp (fset Value))) : 
  P (Comp (fset Value)) := BIND C1 (fun x => C2).

(* Fails when V and W don't unify. Returns their union when they do. *)
(* Can we replace last line below with "Consistent sets"? *)

Definition UNIFY (V : P Value) (W: P Value) : P (Comp (fset Value)) :=
  fun c => match c with 

        | c_multi nil => Inconsistent V W

        | c_multi (l :: nil) => 
            exists l1, exists l2, l = union_fset l1 l2 /\ nonempty_fset l1 /\  nonempty_fset l2 
           /\ (mem l1 ⊆ V) /\ (mem l2 ⊆ W)
           /\ Consistent l1 l2

        | _ => False
  end.
    
(* Questions: Do we make sure the existentially chosen value is consisten? 
   What about the final set? (Can we do that elsewhere?)
*)

Definition EXISTS (f : P Value -> P (Comp (fset Value))) : P (Comp (fset Value)) :=
  fun c => exists V, c ∈ f (mem V).


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
  exists E, (X ≃ mem E) /\ nonempty_fset E.

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
Fixpoint denot_comp_n (n : nat) (a : tm) (ρ : Rho) : P (Comp (fset Value)) :=
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
(*           RET CONS <*> (denot_comp_n m t ρ) <*> (denot_comp_n m u ρ) *)

           BIND (denot_comp_n m t ρ) (fun v1 =>
           BIND (denot_comp_n m u ρ) (fun v2 => 
           RET (CONS v1 v2 ))) 

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


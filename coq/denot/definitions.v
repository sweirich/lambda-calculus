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
  (* list Value is Finite set of values here *)
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
Definition success (v : Value) : bool :=
  match v with 
  | v_wrong => false
  | _ => true
  end.

(* ------------------------------------------------------------ *)

Require Import BoolSet.
Require Import Coq.Classes.EquivDec.


Fixpoint Value_rec' (P : Value -> Type)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : list Value) (v : Value),
           List.ForallT P l -> P v -> P (v_map l v)) 
       (f : P v_fun)
       (l : (forall l : list Value, List.ForallT P l -> P (v_list l)))
       (w : P v_wrong) (v : Value) : P v := 
  let rec := Value_rec' P n m f l w 
  in
  let fix rec_list (vs : list Value) : List.ForallT P vs :=
    match vs with 
    | nil => List.ForallT_nil _
    | cons w ws => @List.ForallT_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  match v with 
  | v_nat k => n k
  | v_map X v => 
      m X v (rec_list X) (rec v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  | v_wrong => w 
  end.



Lemma Value_eq_dec' : forall (x y: Value), {x = y} + {x<>y}.
intro x. eapply Value_rec' with (v := x).
all: intros; try destruct y.
all: try destruct (Nat.eq_dec n n0); subst.
all: try solve [left; reflexivity].
all: try solve [right; intro h; inversion h; subst;  done].
all: try (destruct (H0 y); subst).
all: try solve [right; intro h; inversion h; subst;  done].
all: move: l0.
all: try (induction H; try destruct l0).
(* nil cases *)
all: try solve [left; reflexivity].
all: try solve [right; intro h; inversion h; subst;  done].
(* cons cases *)
all: try destruct (p v); subst.
all: try destruct (IHForallT l0). 
all: try (inversion e; subst).
all: try solve [left; reflexivity].
all: try solve [right; intro h; inversion h; subst;  done].
Defined.


#[export] Instance Value_eq_dec : EqDec Value eq.
intros x y. unfold "===". unfold complement. 
eapply Value_eq_dec'. Defined.


(* ------------ Valid or a denotation that "succeeds" ------------------ *)

Definition inb {A} (x : A) (Y : P A) : bool  := Y x.
Infix "∈b"  := inb (at level 90) : set_scope.


(* This part is ***really*** classical  *)
Require Import Coq.Logic.ClassicalEpsilon.

Definition nonempty (V : P Value) : { x : Value & x ∈ V } + ({ x : Value & x ∈ V } -> False).
move: (@classical_indefinite_description Value (fun x => x ∈ V) (inhabits v_fun)) => [w P].
destruct  (excluded_middle_informative (exists x, x ∈ V)).
specialize (P e).
left.  exists w. exact P.
right. intros [v Q]. apply n. exists v. auto.
Qed.

Definition nonemptyb (V : P Value) : bool:= 
  ssrbool.is_inl (nonempty V). 


Definition forallb (f : Value -> bool)(X: P Value) : bool.
move: (excluded_middle_informative (forall x, x ∈ X -> f x = true)) => h.
eapply (ssrbool.is_left h).
Defined.

Definition valid (V : P Value) : bool :=
  nonemptyb V && forallb success V.

Definition is_nil (V : list Value) : bool :=
  match V with | _ :: _ => false | nil => true end.

Definition valid_mem (V : list Value) : bool :=
  negb (is_nil V) && List.forallb success V.


(* ------------ Semantic Operators ------------------ *)

Definition WRONG : P Value := 
  fun x => match x with v_wrong => true | _ => false end.

Definition NAT : nat -> P Value :=
  fun j v => match v with 
          | v_nat k => Nat.eqb j k
          | _ => false
          end.

Definition forallb2 := 
fun (A B : Type) (f : A -> B -> bool) => 
  fix forallb2 (l : list A) (u : list B) : bool :=
  match l , u with
  | nil , nil => true
  | a :: l0, b :: u0 => f a b && forallb2 l0 u0
  | _ , _ => false
  end.

Arguments forallb2 {_}{_}.
Arguments mem {_}{_}{_}.


Definition LIST : list (P Value) -> P Value  :=
  fun DS w => 
    match w with 
    | v_list WS => forallb2 inb WS DS
    | _ => false
    end.

Definition NIL : P Value := ⌈ v_list nil ⌉.

Definition CONS : P Value -> P Value -> P Value := 
  fun V W x => 
    match x with 
    | v_list (v :: w) => (v ∈b V) && (v_list w ∈b W)  
    | v_wrong => (v_wrong ∈b V) && (v_wrong ∈b W)
    | _ => false
    end.

Definition LAMBDA : (P Value -> P Value) -> P Value :=
  fun f => fun v => match v with 
          | (V ↦ w) => (w ∈b (mem V)) && valid_mem V  (* CBV *)
          | v_fun => true
          | _ => false
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

Definition applicable (v : Value) : bool :=
  match v with 
  | v_fun => true
  | v_list _ => true
  | v_map _ _ => true 
  | _ => false
  end.

(*
Inductive applicable : Value -> Prop :=
  | a_fun  : applicable v_fun
  | a_list : forall VS, applicable (v_list VS)
  | a_map  : forall V w, applicable (v_map V w).

#[export] Hint Constructors applicable : core.
*)


Definition APPLY (D1 : P Value) (D2 : P Value) : P Value :=
    match nonempty D1 with 
    | inl (existT _ v1 _) => match v1 with 
                        | v_wrong => WRONG
                        | v_list VS => match nonempty D2 with
                                      | inl (existT _ v_wrong _) => WRONG
                                      | inl (existT _ (v_nat k) _) => 
                                               match nth_error VS k with 
                                               | Some v => ⌈ v ⌉
                                               | None => WRONG
                                               end
                                      | inl _ => WRONG
                                      | inr _ => Empty_set
                                      end
                        | v_map _ _ => WRONG
                        | _ => WRONG
                        end
   | inr _ => Empty_set
   end.

Inductive APPLY : P Value -> P Value -> (Value -> Prop) :=
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

(* Need to add out of bounds *)

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
         v1 <-  valid_mem V  (* CBV *)
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

Import LCNotations.
Open Scope tm.



(* Denotation function *)
(* `n` is is a termination metric. *)
Fixpoint denot_n (n : nat) (a : tm) (ρ : Rho) : M (P Value) :=
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

Definition denot (a : tm) := denot_n (size_tm a) a.

Hint Opaque denot.



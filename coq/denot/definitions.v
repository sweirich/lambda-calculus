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

(* Sets of Values:   P Value === Value -> Prop *)

(* ----------------------------------------------------------- *)

(* Computations that can fail or produce multiple results. *)

Inductive Comp (v : Type) : Type := 
  (* dynamic type error *)
  | c_wrong : Comp v

  (* multiple results *)
  | c_multi : list v -> Comp v.

#[export] Hint Constructors Comp : core.

Arguments c_wrong {_}.
Arguments c_multi {_}.

Definition pure_Comp {A} (x : A) : Comp A := c_multi (x :: nil).

Definition fmap_Comp {A B} (f : A -> B) (m : Comp A) : Comp B :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => c_multi (List.map f xs)
  end.

Definition append_Comp {A} (m : Comp A) (n : Comp A) : Comp A :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => match n with 
                 | c_wrong => c_wrong
                 | c_multi ys => c_multi (xs ++ ys)
                 end
  end.
      
Definition concat_Comp {A} (l : list (Comp A)) : Comp A :=
  fold_right append_Comp (c_multi nil) l.

Definition join_Comp {A} (m : Comp (Comp A)) : Comp A :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => concat_Comp xs
  end.
      
Definition bind_Comp {A B} (m : Comp A) (k : A -> Comp B) : Comp B :=
  join_Comp (fmap_Comp k m).

#[global] Instance Monad_Comp : Monad Comp.
split. exact @pure_Comp. exact @bind_Comp. Defined.

(* ----------------------------------------------------------- *)

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table *)
  | v_map : list Value -> Comp Value -> Value

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


(* ------------ Valid values and computations ------------------ *)


Definition valid (V : P Value) : Type :=
  nonemptyT V.

Definition valid_mem (V : list Value) : Prop :=
  V <> nil.

(* Produces at least one result *)

Definition valid_Comp (C : P (Comp Value)) : Type :=
  (nonemptyT C * not (c_wrong ∈ C) * not (c_multi nil ∈ C))%type.


(* ------------ Semantic Operators ------------------ *)

Definition WRONG : P (Comp Value) := ⌈ c_wrong ⌉.

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


Definition CONS2 : Value -> Value -> P (Comp Value) := 
  fun v w => match w with 
            | v_list u => ⌈ ret (v_list (v :: u)) ⌉
            |  _ => ⌈ c_wrong ⌉
          end.


Definition Λ : (P Value -> P (Comp Value)) -> P Value :=
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

Inductive APPLY : P Value -> P Value -> (Comp Value -> Prop) :=
  | BETA : forall D1 D2 w V,
      (V ↦ w) ∈ D1 ->
     (mem V ⊆ D2) -> valid_mem V ->
     APPLY D1 D2 w
  | PROJ   : forall D1 D2 w VS k, 
     (v_list VS) ∈ D1 ->
     (v_nat k ∈ D2) -> nth_error VS k = Some w ->
     APPLY D1 D2 (ret w)
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
    | (V ↦ c_multi (v_nat k :: nil)) => 
        exists i j, ((v_list (v_nat i :: v_nat j :: nil)) ∈ mem V) /\ k = i + j
    | V ↦ c_wrong => 
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
Notation "ρ ⋅ x" := (Env.access (fun x => False) ρ x) (at level 50).
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

(* ------------------------------------------------------- *)

Definition nonempty_env : Rho -> Type := Env.ForallT nonemptyT.

Definition valid_env : Rho -> Type := Env.ForallT valid. 

Definition sub_env : Rho -> Rho -> Prop := Env.Forall2 Included.

Definition same_env : Rho -> Rho -> Prop := Env.Forall2 Same_set.

(* ------------------------------------------------------- *)

Import LCNotations.
Open Scope tm.

(* Some properties about P and M *)

#[export] Instance Monad_P : Monad P :=
  { ret  := (fun A (x : A) => ⌈ x ⌉);
     bind := fun A B (ca : P A) (k : A -> P B) =>
             fun b => exists a, (a ∈ ca) /\ (b ∈ k a)
   }.

#[export] Instance Functor_P : Functor P :=
  { fmap := fun A B (f : A -> B) (x : A -> Prop) => 
               bind x (fun y => ret (f y)) 
  }.

#[export] Instance Applicative_P : Applicative P :=
  { pure := @ret P _;
     ap   := fun A B (m1 :  P (A -> B)) (m2 : P A) => 
               bind m1 (fun x1 => 
                            bind m2 (fun x2 => 
                                         ret (x1 x2))) 
  }.

#[export] Instance Alternative_P : Alternative P :=
  { empty := fun A (x:A) => False ;
    choose := fun A (p1 p2 : P A) (y : A) => 
                 p1 y \/ p2 y
   }.

Definition M := fun x => P (Comp x).

Definition Comp_In {A} (x : A) (u : Comp A) := 
  match u with 
  | c_wrong => False
  | c_multi vs => List.In x vs
  end.

Definition RET {A} : A -> M A :=
  fun x => ⌈ ret x ⌉.

Definition BIND {A B} (S : M A) (K : A -> M B) (t : Comp B) : Prop :=
  exists (u : Comp A), exists (k : A -> Comp B), 
    S u /\ t = bind u k /\ forall a, Comp_In a u -> K a (k a).

#[export] Instance Monad_M : Monad M.
split. exact @RET. exact @BIND. Defined.




Definition RET2 {A} : P A -> M A := fmap pure_Comp.

(* This K wants a finite set of values from S at once 
   so that the APPLY function can check that the domain is 
   included in the argument. *)
Definition BIND2 {A B} (S : P (Comp A)) (K : P A -> P (Comp B)) (t : Comp B) : Prop :=
  exists V, finite V /\ (RET2 V ⊆ S) /\ K V t.

(* Denotation function *)
(* `n` is is a termination metric. *)
Fixpoint denot_comp_n (n : nat) (a : tm) (ρ : Rho) : M Value :=
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

     | _ => ∅
     end
  end in
  match n with
  | O => ∅
  | S m => 
      match a with 
       | app t u   => 
           BIND2 (denot_comp_n m t ρ) (fun v1 =>
           BIND2 (denot_comp_n m u ρ) (fun v2 =>
           v1 ▩ v2))

       | tcons t u => 
           BIND2 (denot_comp_n m t ρ) (fun v1 =>
           BIND2 (denot_comp_n m u ρ) (fun v2 => 
           RET2 (CONS v1 v2 )))

       | _ => RET2 (denot_val_n n a ρ)
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

     | _ => ∅
     end
  end.

Definition denot (a : tm) := denot_comp_n (size_tm a) a.
Definition denot_val (a : tm) := denot_val_n (size_tm a) a.

#[export] Hint Opaque denot : core.
#[export] Hint Opaque denot_val : core.



Require Import Coq.Logic.PropExtensionality.

Lemma ret_In_RET2 : forall {A} (U : P A) x,
  x ∈ U <-> ret x ∈ RET2 U.
Proof.
  intros. 
  unfold ret, RET2, fmap, Monad_Comp, Functor_P, bind, Monad_P, Ensembles.In.
  split.
  + intros Ux. exists x. split; auto.
    cbv. econstructor.
  + move => [a [Pa r]].
    cbv in r. inversion r. subst. auto.
Qed.

Lemma RET2_monotone : forall {A} (U V : P A), 
 U ⊆ V -> RET2 U ⊆ RET2 V. 
Proof. 
    intros A U V h x xIn.
    destruct xIn as [ a [Ua r]].
    inversion r. subst.
    rewrite <- ret_In_RET2.
    eauto.
Qed.

Lemma RET2_sub_reflecting :  forall {A} (U V : P A), 
  RET2 U ⊆ RET2 V -> U ⊆ V.
Proof. 
  intros A U V h x xIn.
  rewrite -> ret_In_RET2 in xIn.
  specialize (h _ xIn).
  rewrite -> ret_In_RET2.
  auto.
Qed.

#[export] Instance Proper_Included_RET2 {A} : Proper (Included ==> Included) (@RET2 A).
unfold Proper. intros x1 y1 E1. eapply RET2_monotone. auto. Qed.

#[export] Instance Proper_Same_RET2 {A} : Proper (Same_set ==> Same_set) (@RET2 A).
unfold Proper. intros x1 y1 E1. split. eapply RET2_monotone. rewrite E1. reflexivity.
eapply  RET2_monotone. rewrite E1. reflexivity.
Qed.



Lemma BIND2_RET2 : forall {A B} (x : P A) (k : P A -> M B), 
    monotone k 
    -> finite x
    -> BIND2 (RET2 x) k ≃ k x.
Proof. intros. unfold BIND2, RET2.
repeat split.
+ intros y.
  move =>[U [h1 [h2 h3]]]. unfold M in k.
  fold (@RET2 A) in h2.
  eapply RET2_sub_reflecting in h2.
  eapply (H _ _ h2). auto.
+ exists x. repeat split. eauto. reflexivity. auto.
Qed. 


Lemma BIND2_mono {A B} : forall (D1 D2 : M A) (K1 K2 : P A -> M B),
  D1 ⊆ D2 -> (forall x, K1 x ⊆ K2 x) ->
  BIND2 D1 K1 ⊆ BIND2 D2 K2.
Proof. 
  intros.
  unfold BIND2.
  move=> x [U [h1 [h2 h3]]].
  exists U.
  repeat split.
  auto.
  transitivity D1; auto.
  specialize (H0 U x).
  eapply H0. auto.
Qed.

#[export] Instance Proper_Included_BIND2 {A B} : Proper (Included ==> Logic.eq ==> Included) (@BIND2 A B).
intros x1 y1 E1 x2 y2 ->. 
eapply BIND2_mono; eauto. reflexivity.
Qed. 

#[export] Instance Proper_Same_BIND2 {A B} : Proper (Same_set ==> Logic.eq ==> Same_set) (@BIND2 A B).
unfold Proper. intros x1 y1 E1 x2 y2 ->. split. eapply BIND2_mono. rewrite E1. reflexivity. reflexivity.
eapply  BIND2_mono. rewrite E1. reflexivity. reflexivity.
Qed.
  


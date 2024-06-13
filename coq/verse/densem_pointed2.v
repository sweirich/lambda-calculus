Require Import Coq.Vectors.Fin.
Require Coq.Vectors.VectorDef.
Require List.
Import List.ListNotations.

Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Import structures.Sets.
Require structures.Option.

(* This file defines a "denotational" semantics for Verse

   M A := P (option A)

   In this version, the denotation of an expression is a set of lifted values.

   If the set is empty, the expression fails

   What is Bottom? Not sure which is the appropriate answer
     - the singleton set None?
     - a set that contains None?

   Allowing sets to contain both None and Some seems like it will be important 
   to eventually supporting "one"

   
*)


Set Implicit Arguments.

Inductive Op : Type := op_Add | op_Gt | op_Int.

Inductive Val (n: nat) : Type := 
  | Var   : Fin.t n -> Val n
  | Int   : nat -> Val n
  | Prim  : Op -> Val n
  | Pair  : Val n -> Val n -> Val n   (* todo: generalize to n-tuples *)
  | Lam   : Exp (S n) -> Val n

with Exp (n : nat): Type :=
  | Ret    : Val n -> Exp n
  | App    : Val n -> Val n -> Exp n  
  | Seq    : Exp n -> Exp n -> Exp n

  | Unify  : Exp n -> Exp n -> Exp n   
  | Exists : Exp (S n) -> Exp n
  | Or     : Exp n -> Exp n -> Exp n 
  | Fail_  : Exp n
  | One    : Exp n -> Exp n 
  | All    : Exp n -> Exp n  
.

Arguments Int {_}.
Arguments Prim {_}.
Arguments Fail_ {_}.

(* This is our domain of values (W): numbers, primitives, pairs of values 
   and closures *)
Inductive W : Type := 
  | IntV   : nat -> W
  | PrimV  : Op -> W
  | PairV  : W -> W -> W
  | LamV   : forall {n}, VectorDef.t W n -> Exp (S n) -> W   (* closure *)
.

Import SetNotations.


Section Monad.

Definition M (A : Type) := P (option A). 

Definition BOTTOM {A} : M A := ⌈ None ⌉.
Definition WRONG {A} : M A := ∅.
Definition FAIL {A} : M A := ∅.
Definition UNIT  {A} : A -> M A := fun x => ⌈ Some x ⌉.
Definition UNION {A} : M A -> M A -> M A := Union.
Definition INTER {A} : M A -> M A -> M A := Intersection.

Definition SEQ {A} : M A -> M A -> M A := 
  fun s1 s2 => 
    fun x => 
      match x with 
      | None => (None ∈ s1) \/ (None ∈ s2)
      | Some y => (exists z, Some z ∈ s1) /\ not (None ∈ s1) /\ (Some y ∈ s2)
      end.

(* This is still not correct because we cannot pick an element. *)
Definition ONE {A} : M A -> M A := 
  (fun s => s).

(* Note: WEIRD semantics. All pairs of elements in the interpretation. Not 
  a singleton. *)
Definition ALL : M W -> M W := 
  (fun s => (fun y => match y with 
                       | None => None ∈ s
                       | Some (PairV w1 w2) => s (Some w1) /\ s (Some w2)
                       | _ => False
                       end)).

(* Merge togther the result of the function f applied to every w in W. *)
(* - only diverges if *all* f w diverge
   - contains all elements produced by some f w
   - ff all f w fail, then fails
 *)
Definition EXISTS {A} (f : A -> M A) : M A := 
 (fun x => match x with 
          | None => forall w, ⌈ None ⌉ ≃ (f w)
          | Some y => exists w, Some y ∈ f w
        end).

(* Maybe do something special for functions??? *)
Definition EQUAL {A} : M A -> M A -> Prop := fun x y => x ≃ y.

End Monad.


Section Semantics.

Definition Env (n : nat) := VectorDef.t W n.
Definition lookupEnv {n} (e : Env n) (x : Fin.t n) : W := VectorDef.nth e x. 

(* semantics of values *)
Fixpoint evalVal {n} (env : Env n) (V : Val n) : W :=
  match V with 
  | Var v => lookupEnv env v
  | Lam e => LamV env e
  | Pair v1 v2 => PairV (evalVal env v1) (evalVal env v2)
  | Int k => IntV k
  | Prim o => PrimV o
  end.
 
Definition evalPrim (o : Op) (w : W) : M W := 
  match o , w with 
  (* addition *)
  | op_Add , PairV (IntV j) (IntV k) => UNIT (IntV (j+k))
  | op_Add , _ => WRONG
  (* Gt *)
  | op_Gt  , PairV (IntV j) (IntV k) => 
      if Nat.leb k j then UNIT ( IntV j ) else FAIL
  | op_Gt , _ => WRONG
  (* type test: identity function on Int, fails when given a non int value *)
  | op_Int , IntV k => UNIT ( IntV k )
  | op_Int , _ => FAIL
  end.

Import VectorDef.VectorNotations.

(* semantics of expressions *)

Fixpoint evalExp (m:nat) {n : nat} (env: Env n) (e: Exp n) : M W :=  
  match m with 
  | 0 => BOTTOM
  | S m' => match e with 
           | Ret v => 
               UNIT (evalVal env v)

           | Fail_ => FAIL

           | Or e1 e2 => UNION (evalExp m' env e1) (evalExp m' env e2)

           | Unify e1 e2 => INTER (evalExp m' env e1) (evalExp m' env e2)

           | Seq e1 e2 => SEQ (evalExp m' env e1) (evalExp m' env e2)

           | App e v => 
               let w := evalVal env v in
               match evalVal env e with                      
                 | (LamV env1 e1) => evalExp m' (VectorDef.cons _ w _ env1) e1
                 | PrimV p => evalPrim p w
                 | _ => WRONG   (* non-function application *)
               end

           | Exists e => 
               EXISTS (fun w => evalExp m' (VectorDef.cons _ w _ env) e)

           | One e => ONE (evalExp m' env e)

           | All e => ALL (evalExp m' env e)
           end
  end.

End Semantics.


Import VectorDef.VectorNotations.

(* Examples *)

(* exists x. x = 3 ; x *)
Definition ex0 : Exp 0 := 
  Exists (Seq (Unify (Ret (Var F1)) (Ret (Int 3))) (Ret (Var F1))).

Lemma evex0 : exists n, EQUAL (UNIT (IntV 3)) (evalExp n (@VectorDef.nil _) ex0).
exists 4. 
simpl.
split.
- unfold EXISTS.
  intros x xIn. inversion xIn.
  exists (IntV 3). 
  split.
  exists (IntV 3).
  repeat econstructor; eauto.
  repeat econstructor; eauto.
- unfold EXISTS.
  intros x xIn. inversion xIn.
  cbv in H.
  move: H => [[y h1] h2].  inversion h2. subst.
  inversion h1. subst. inversion H. subst. inversion H0. subst.
  auto.
Qed.

(* exists x. x = 3 | x = 4 *)

Definition ex1 : Exp 0 := 
 Exists (Or (Unify (Ret (Var F1)) (Ret (Int 3)))
            (Unify (Ret (Var F1)) (Ret (Int 4)))).

Lemma evex1 : exists n, EQUAL (evalExp n (@VectorDef.nil _) ex1) 
                     (UNION (UNIT (IntV 3)) (UNIT (IntV 4))).
exists 10.
simpl.
unfold EXISTS.
split.
- intros x xIn. inversion xIn. clear xIn.
  inversion H. subst.
  inversion H0. subst.
  inversion H1. inversion H2. subst.
  left. auto.
  inversion H0. inversion H2. inversion H3. subst.
  right. auto.
- intros x xIn. inversion xIn; subst; clear xIn; inversion H; clear H.
  + exists (IntV 3).
    constructor. constructor. auto. auto.
  + exists (IntV 4).
    right. constructor. auto. auto.
Qed.

(* 
    exists x. x 1 = 2 ; x 1 
*)

Definition ex2 : Exp 0 := 
  Exists (Seq (Unify (App (Var F1) (Int 1)) (Ret (Int 2)))
              (App (Var F1) (Int 1))).

(* We can show that "2" is in the meaning of this expression *)
Lemma evex2 : exists n, IntV 2 ∈ evalExp n (@VectorDef.nil _) ex2.
Proof.
  exists 5.
  exists (LamV (@VectorDef.nil _) (Ret (Int 2))).
  cbv.
  split; eauto. exists (IntV 2). constructor; eauto. constructor; eauto.
Qed.

(* if (x=1) then (2 3) else 4; x=(1 2); if (x=1) then 5 else (6 7) *)

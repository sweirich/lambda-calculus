Require Import Coq.Vectors.Fin.
Require Coq.Vectors.VectorDef.
Require List.
Import List.ListNotations.

Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Import structures.Sets.

(* This file defines a "denotational" semantics for Verse as *sets of values*.
   This semantics is not correct, but illustrative of difficulties.

   For example, the denotation of the expression "2 || 3" is the set
   {2,3}. This isn't right (as it loses the order), but using sets makes it
   easy to define the interpretation of "∃".

   The key idea is that the interpretation of "∃ x. e" is the set of all
   values in the interpretation of "e", using any value w for x.  We might
   write that mathematically as:

        { x | x ∈ eval (w :: env) e, for w in W }

   Some points about this file:

    - This semantics uses {} (the emptyset) as the denotation of both FAIL and
      WRONG
  
           what should the semantics of "(true + 1) || 2" be?  should it be
           WRONG or should it be 2?

    - This semantics also uses {} as the denotation of both FAIL and "bottom".

      The denotation function is threaded with a "fuel" value to deal with non
      termination.  If there is not enough fuel, then the denotation is
      bottom.

      The idea is that for any *terminating* expression there should be some
      amount of "fuel" that is enough to fully define its semantics. However,
      there is a twist: with a set based semantics, by giving more fuel, we
      may get a larger set of results. For example,

               " 2 || fact 5"

      will produce the singleton set {2} for small values of fuel and {2, 120}
      with more fuel.

      This is BAD news for "all". If this term gathers all values in the set
      into a tuple, how does it know when to stop? Sometimes the denotation of

             all(2 || fact 5)

      is the set {<2>} and sometimes it is the set {<2,120>}. The first set is
      not a subset of the second, so our denotation is not
      monotonic. Computations may return different results (not more results)
      given more fuel.

    - This is less bad news for "one" (but still not good). In this version,
      we cannot define the semantics for "one" without the axiom of
      choice. And this would probably not be monotonic because as we generate
      larger sets, AC may pick out different elements. But if we can get the
      ordering nailed down, then we may be in better shape.

    - This isn't a good denotational semantics as I'm using closures as the
      denotations of functions. But equality is syntactic, so there are
      functions that are extensionally equal that are distinguished by the
      semantics.  For example, \x. x + 1 would not unify with \x. 1 + x.

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

Definition M (A : Type) := P A.  (* set of values of type A *)

Definition WRONG {A} : M A := ∅.
Definition FAIL {A} : M A := ∅.
Definition UNIT  {A} : A -> M A := fun x => ⌈ x ⌉.
Definition UNION {A} : M A -> M A -> M A := Union. 
Definition INTER {A} : M A -> M A -> M A := Intersection.

Definition SEQ {A} : M A -> M A -> M A := 
  fun s1 s2 => (fun x => (exists y, s1 y) /\ s2 x).

(* Because there is no order, we need something like the axiom of choice 
   to pick a distinguished element of the set. And is AC monotonic? I dunno....

*)
Definition ONE {A} : M A -> M A := 
  fun s => s.

(* Note: since we only have binary pairs, this is a bit odd. ALL works when
   there are two values in the set. However, having n-tuples would also
   produce a non-monotonic operator. As the number of potential results grows,
   then the size of the tuple *also* grows. This is not ideal.
*)
Definition ALL : M W -> M W := 
  fun s => (fun y => match y with 
                       | PairV w1 w2 => s w1 /\ s w2
                       | _ => False
                       end).

(* Merge togther the result of the function f applied to every w in W *)
Definition EXISTS {A} (f : A -> M A) : M A := 
  fun x => exists w, x ∈ f w.

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
  | 0 => FAIL
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
Definition ex0 (y : nat) : Exp 0 := 
  Exists (Seq (Unify (Ret (Var F1)) (Ret (Int y))) (Ret (Var F1))).

Lemma evex0 : forall y, exists n, (UNIT (IntV y)) ≃ evalExp n (@VectorDef.nil _) (ex0 y).
intros y.
exists 4. 
simpl.
split.
- unfold EXISTS.
  intros x xIn. inversion xIn.
  exists (IntV y). 
  econstructor.
  exists (IntV y).
  repeat econstructor; eauto.
  repeat econstructor; eauto.
- unfold EXISTS.
  intros x xIn. inversion xIn.
  cbv in H.
  move: H => [[y' h1] h2].  inversion h2. subst.
  inversion h1. subst. inversion H. subst. inversion H0. subst.
  auto.
Qed.

(* exists x. x = 3 | x = 4 *)

Definition ex1 : Exp 0 := 
 Exists (Or (Unify (Ret (Var F1)) (Ret (Int 3)))
            (Unify (Ret (Var F1)) (Ret (Int 4)))).

Lemma evex1 : exists n, evalExp n (@VectorDef.nil _) ex1 ≃ (⌈ IntV 3 ⌉ ∪ ⌈IntV 4⌉).
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

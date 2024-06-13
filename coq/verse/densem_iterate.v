Require Import Coq.Vectors.Fin.
Require Coq.Vectors.VectorDef.
Require List.
Import List.ListNotations.

Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.

(* This file defines a denotational semantics for Verse as sets of values. 
   This semantics is not correct, but illustrative of the difficulties. 

   The interpretation of any expression is as a set of values. For example, 
   the denotation of " 2 || 3 " is the set {2,3}. This isn't right (as it 
   loses the order) but it is simple.

   The key idea of this semantics is the interpretation of "∃ x. e" 
   In this case, we iterate over all potential values and union them together.

   This semantics iterates over all values in the domain, and then 

*)


(* Tricky examples:

 How do type errors with || ?

     (true + 1) | 2  ---> 2  

   note: if "exists" iterates over all values, then we will naturally get some failures
   in 

      exists x. (x + 1 = 2 ; x | x = 3 ; x )

   one possible x could be "true" which would cause the first alternative to 
   type error. But we don't want to include that type error in the final result.

 How does divergence interact with || ?

     <<diverge>> | 2 ---> ???

 *)


Require Import structures.Sets.
Import SetNotations.

Definition unions {A} : list (P A) -> P A := 
  List.fold_right Union Empty_set.

Lemma unions_In {A} : 
  forall (k : P A) (ks: list (P A)), List.In k ks -> k ⊆ unions ks.
Proof.
  intros k ks.
  induction ks. intros h; simpl in h. done.
  intros h. simpl in h. 
  intros b bIn. simpl.
  destruct h. subst. left. auto.
  right. apply IHks; auto.
Qed.

Lemma unions_app {A} : forall (l1 l2 : list (P A)),
    unions (l1 ++ l2) ≃ (unions l1 ∪ unions l2).
Proof.
  induction l1. intros l1. simpl. admit.
  intros l2. simpl. rewrite IHl1. admit.
Admitted.

Lemma unions_enum_mono {A} : forall (f : A -> P A) l1 l2,  
  unions (List.map f l1) ⊆ unions (List.map f (l1 ++ l2)).
Proof.
  intros f l1 l2.
  rewrite List.map_app. rewrite unions_app.
  eauto.
Qed.


(* This version is trying to approximate the semantics given in the verse-densym draft 
   as closely as possible. *)


(* The idea of the "logical" semantics is to provide a sound interpretation of 
   "lenient" evaluation.

   Then, there would be no need to delay unification steps. They would either succeed or 
   fail.

   This corresponds to an interpretation of a verse program as a nondeterministic set of 
   results.

   To be careful about the order of evaluation, we'll do this in the context of 
   fine-grained CBV language 
   
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
  | App    : Val n -> Val n -> Exp n  (* NOTE ok to make fun an exp *)
  | Seq    : Exp n -> Exp n -> Exp n

  | Unify  : Exp n -> Exp n -> Exp n   
  | Exists : Exp (S n) -> Exp n
  | Or    : Exp n -> Exp n -> Exp n 
  | Fail_ : Exp n
  | One   : Exp n -> Exp n 
  | All   : Exp n -> Exp n 
  
.

Arguments Int {_}.
Arguments Prim {_}.
Arguments Fail_ {_}.

Section Syntax.

Definition Op_eqb := 
  fun o1 o2 => match o1 , o2 with 
            | op_Add , op_Add => true
            | op_Gt  , op_Gt  => true 
            | op_Int , op_Int => true
            | _ , _ => false
            end.

Definition Op_enum : list Op := [ op_Add ; op_Gt ; op_Int ].

End Syntax.

Section W.

Inductive W : Type := 
  | IntV   : nat -> W
  | PrimV  : Op -> W
  | PairV  : W -> W -> W
  | LamV   : forall {n}, VectorDef.t W n -> Exp (S n) -> W   (* closure *)
.

(* equality of domain values is decidable. *)
Fixpoint W_eqb (v1 : W) (v2 : W) : bool := 
  match v1 , v2 with 
  | IntV k1 , IntV k2 => Nat.eqb k1 k2
  | PairV v1 v2, PairV w1 w2 => W_eqb v1 w1 && W_eqb v2 w2
  | PrimV o1 , PrimV o2 => Op_eqb o1 o2
  | LamV _ _ , LamV _ _ => false  (* TODO *)
  | _ , _ => false
  end.

Fixpoint W_size (v : W) : nat  := 
  match v with 
  | IntV k => k
  | PairV v1 v2 => 1 + max (W_size v1) (W_size v2)
  | PrimV o => 1
  | LamV _ _ => 0  (* TODO *)
  end.                                 

Definition isLamV (v : W) := 
  match v with 
  | LamV _ _ => true
  | _ => false
  end.

(* domain values can be effectively enumerated *)
(* TODO: this excludes closures.... *)
Fixpoint W_enum (n : nat) : list W := 
  match n with 
  | 0 => [IntV 0 ; PrimV op_Add ; PrimV op_Gt ; PrimV op_Int ]
  | S n => let prev := W_enum n in 
          prev ++ [IntV (S n)]
               ++ List.flat_map (fun v1 => List.flat_map 
                                          (fun v2 => [PairV v1 v2]%list) prev) prev
  end.


(* every (non-lambda) value is contained in the enumeration. *)
Lemma enum_all : forall (v : W), (isLamV v) = false -> 
                                      exists k, List.In v (W_enum k).
Proof.
  induction v.
  all: intro h; simpl in h.
  exists n. clear h. destruct n. simpl; auto. simpl; auto. admit.
Admitted. 

(* Enumerating more values extends the list. *)
Lemma enum_mono : forall j k, j <= k -> (exists l, W_enum k = (W_enum j) ++ l)%list.
Proof.
  intros. induction H. exists nil. rewrite List.app_nil_r. auto.
  move: IHle => [l E]. simpl.
  eexists.
  rewrite E.
  rewrite <- List.app_assoc. 
  eauto.
Qed.

End W.

Section Monad.
Import SetNotations.

Definition M (A : Type) := P A.  (* set of values of type A *)

Definition WRONG {A} : M A := ∅.
Definition EMPTY {A} : M A := ∅.
Definition UNIT  {A} : A -> M A := fun x => ⌈ x ⌉.
Definition UNION {A} : M A -> M A -> M A := Union. 
Definition INTER {A} : M A -> M A -> M A := Intersection.

Definition SEQ {A} : M A -> M A -> M A := 
  fun s1 s2 => (fun x => (exists y, s1 y) /\ s2 x).

(* NOTE: if the semantics depends on there only being a unique value in the 
   set, then it is *not* monotonic. Running evalExp with a larger n could
   turn a singleton set into a non-singleton set.
*)
Definition ONE {A} : M A -> M A := 
  fun s => (fun y => s ≃ ⌈ y ⌉).

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

(* Merge togther the result of the function f applied to every w in W (up to k) *)
Definition ITERATE (k : nat) (f : W -> M W) : M W := 
  unions (List.map f (W_enum k)).

(* If we iterate more, then we only get larger results. *)
Lemma ITERATE_mono : forall j k f, j <= k -> ITERATE j f ⊆ ITERATE k f.
Proof.
  intros. unfold ITERATE.
  move: (enum_mono H) => [l h].
  rewrite h.
  eapply unions_enum_mono.
Qed.

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
      if Nat.leb k j then UNIT ( IntV j ) else EMPTY
  | op_Gt , _ => WRONG
  (* type test: identity function on Int, fails when given a non int value *)
  | op_Int , IntV k => UNIT ( IntV k )
  | op_Int , _ => EMPTY
  end.

Import VectorDef.VectorNotations.

(* semantics of expressions *)

Fixpoint evalExp (m:nat) {n : nat} (env: Env n) (e: Exp n) : M W :=  
  match m with 
  | 0 => EMPTY
  | S m' => match e with 
           | Ret v => 
               UNIT (evalVal env v)

           | Fail_ => EMPTY

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
               ITERATE m' (fun w => evalExp m' (VectorDef.cons _ w _ env) e)

           | One e => ONE (evalExp m' env e)

           | All e => ALL (evalExp m' env e)
           end
  end.

End Semantics.

(* Examples *)

(* exists x. x = 3 ; x *)
Definition ex : Exp 0 := 
  Exists (Seq (Unify (Ret (Var F1)) (Ret (Int 3))) (Ret (Var F1))).

Lemma evex : exists n, UNIT (IntV 3) ⊆ evalExp n (@VectorDef.nil _) ex.
move: (enum_all (IntV 3) ltac:(reflexivity)) => [k h].
exists (S (S (S (S k)))). 
simpl.
unfold ITERATE.
remember (fun w : W => SEQ (INTER (UNIT w) (UNIT (IntV 3))) (UNIT w)) as f.
apply List.in_map with (f:=f) in h.
move: (unions_In _ _ h) => h1.
have LT: k <= 3+k. econstructor; eauto. apply enum_mono in LT.
move: LT => [l E]. rewrite E.
rewrite <- unions_enum_mono.
rewrite <- h1.
rewrite Heqf. 
intros x xIn. inversion xIn.
cbv. split. exists (IntV 3). 
constructor. auto. auto. constructor.
Qed.

(* exists x. x = 3 | x = 4 *)

Definition ex : Exp 0 := 
 Exists (Or (Unify (Ret (Var F1)) (Ret (Int 3)))
            (Unify (Ret (Var F1)) (Ret (Int 4)))).

Lemma evex : exists n, exists s,  evalExp n [] ex = Some s /\ s (IntV 3) /\ s (IntV 4).
eexists.
eexists.

exists (⌈IntV 3⌉ ∪ ⌈IntV 4⌉).
simpl. unfold ITERATE.

(* exists x. x *)


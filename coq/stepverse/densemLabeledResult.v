(* This file defines a "denotational" semantics for Verse.

   W* == (label * result W) -> Prop

   The label records which branch of an "Or" we are in
   The result records whether that branch diverges, type errors, 
   or returns a value.

   If a branch fails, that label will not be in the set.

   NOTE: the definition of "bind" for P A = (A -> Prop) has type:

      bind :: P A -> (A -> P B) -> P B

   This operation is like a flat map for sets

      bind m f  ===  union_{x ∈ m} (f x)                       
*)

Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Require structures.Option.
Require Import structures.Sets.
Require Import structures.Monad.
Require structures.Vector.

(* autosubst2 "generated" syntax *)
Require Import fintype.
Require Import verse.syntax.
Require Import verse.notations.
Import EqSyntax.

Require Import stepverse.label.
Import LabelNotation.

Require Import Classical.

Set Implicit Arguments.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Result                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Inductive Result (A : Type) : Type := 
  | Bottom : Result A       (* divergence *)
  | Wrong  : Result A       (* runtime type error *)
  | Value  : A -> Result A.

Arguments Bottom {_}.
Arguments Wrong {_}.
Arguments Value  {_}.

(* Note: *failure* is the absence of any result in the set so is not included
   as a constructor in the result type.

   This design simplifies the operation of "One" --- we only need to find the
   result with the smallest label in the set, not the smallest label with a
   nonfailing result.

   The cost for not modelling failure is that it is difficult to say when one
   *set* of results approximates another. Labeled bottoms can disappear when
   given more fuel, because they could fail.
 *)


Module R. 

Definition isWrong {A} (r : Result A) : bool := 
  match r with | Wrong => true | _ => false end.
Definition isBottom {A} (r: Result A) : bool := 
  match r with | Bottom => true | _ => false end.
Definition isValue {A} (r: Result A) : bool := 
  match r with | Value _ => true | _ => false end.

Definition approx {A} (r1 r2 : Result A) : Prop := 
  match r1 , r2 with 
  | Bottom , _ => True
  | Wrong , Wrong => True
  | Value w1 , Value w2 => w1 = w2
  | _ , _ => False
end.

Definition approxb {A} (R : A -> A -> bool) (r1 : Result A) (r2 : Result A) : bool := 
  match r1 , r2 with
  | Value w1 , Value w2 => R w1 w2
  | Wrong , Wrong => true
  | Bottom , _ => true
  | _ , _  => false
  end.

End R.



(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Domain of values                      *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(* The semantics of values (W): numbers, primitives, tuples of values 
   and closures. *)

Inductive W : Type := 
  | IntV    : nat -> W
  | PrimV   : Op -> W
  | TupleV  : list W -> W
  | LamV    : forall {n}, Vector.vec W n -> Exp (S n) -> W   (* a closure *)
.

#[export] Hint Constructors W.

Module W.

(* syntactic equality for values *)
Fixpoint eqb (x : W) (y : W) : bool := 
  let fix eqbs (xs : list W) (ys : list W) : bool :=
    match xs , ys with 
    | (x :: xs)%list , (y :: ys)%list => (eqb x y && eqbs xs ys)%bool
    | nil , nil => true
    | _ , _ => false
    end 
  in match x , y with 
     | IntV x , IntV y => Nat.eqb x y
     | PrimV x , PrimV y => Op.eqb x y
     | TupleV xs , TupleV ys => eqbs xs ys
     | LamV v1 e1 , LamV v2 e2 => false (* todo *)
     | _ , _ => false
     end.

End W.

Section PartialFunctions.

Import SetNotations.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*      Monadic type                                         *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(** The semantics of computations is a set of labeled results.  These sets
   should be partial functions, i.e. there should be at most one result for
   any label in the set. *)

Definition M (A : Type) := (label * Result A) -> Prop.  

(** ** entries *)

(* A pair of a label and result is an entry. An entry is "finished" if 
   the label does not contain Bot and the result is not Bottom. *)

Definition label_finished (l : label) := 
  forall l', l ⊑ l' -> l = l'.

Definition result_finished {A} (r : Result A) := 
  forall r', R.approx r r' -> r = r'.

Definition entry_finished {A} '((l,r) : label * Result A) := 
  label_finished l /\ result_finished r.

(** ** set approximatation *)

(* Because we will use these sets as the semantics of computations, we 
   need to say what it means for one set to *approximate* another.

   We have s1 ⊑ s2 when:

      1. for every e in s1 that has finished (i.e. is Value or Wrong), 
          a. e must be in s2 

      2. if e has bottomed 
          a. it could stay bottom, with a potentially bigger label
          b. it could succeed, with a bigger label
          c. it could fail and won't be in s2

      3. if e is not in s1, i.e. fails
          - then it should continue to fail, i.e. all bigger labels shouldn't be in s2

   We can express 1 as is
   Case 2 is trivial
   we can express 3 using the contrapositive:
            everything in s2 should be approximated by something in s1
         
We need (1) to know that successful values do not change with more fuel.
We need (3) for the case of ONE: there won't be new "smaller" elements 
when we add more fuel.
*)

  
Definition entry_approx {A} '(l1,r1) '(l2, r2) : Prop := 
  Label.approx l1 l2 /\ R.approx r1 (r2 : Result A).

Definition approx {A} (s1 s2 : M A) : Prop := 
  (* (1) We don't lose successful results. 
     Everything that has finished in s1 is still present in s2. *)
  (forall e, e ∈ s1 -> entry_finished e -> (e ∈ s2)) /\
  (* (3) We don't make up results. 
     Every entry in s2 is approximated by something from s1. *)
  (forall e2, e2 ∈ s2 -> exists e1, (e1 ∈ s1) /\ entry_approx e1 e2).

(** ** partial functions *)

(* We can look up values in the set by label. This label can be exactly the 
   same as the label in some entry, or it can be an extension of the label 
   of an unfinished entry. *)

Definition mapsto {A} '(l,r) (s : M A) := 
  exists l', ((l',r) ∈ s) /\ Label.approx l' l.

(* A set of pairs is a partial function if there is at most one mapping for
   any key in the set. *)
Definition partial_function {A} (s : M A) := 
  forall l r1 r2, mapsto (l,r1) s -> mapsto (l, r2) s -> r1 = r2.

(* This predicate defines when a key is in the domain of 
   the partial function *)
Definition in_dom {A} (s : M A) (l : label) : Prop := 
  exists l' r, ((l', r) ∈ s) /\ Label.approx l' l.

(** ** element ordering *)
Definition entry_lt {A} : (label * A) -> (label * A) -> Prop := fun '(l1,_) '(l2, _)=> Label.lt l1 l2.

(* The canonical list of elements in a finite set *)
Definition elements {A} (s : M A) (l : list (label * Result A)) : Prop := 
  (mem l = s) /\                        (* memberships are equal *)
  @Sorted.LocallySorted _ entry_lt l.  (* the list is sorted by the labels *)

(** ** Properties of partial_functions, approx, and labeled sets *)

Lemma smaller_notpresent {A} 
  (a : label * Result A) (w : list (label * Result A)) :
  List.Forall (entry_lt a) w ->  ~(List.In a w).
Proof. destruct a. 
       induction w.
       intros h1 h2. inversion h2.
       intros h1 h2. simpl in h2. 
       inversion h1. subst.
       destruct h2.
       + subst. eapply Label.lt_irreflexive; eauto.
       + apply IHw; eauto.
Qed.

Lemma exact_mapsto {A} e (s : M A) : (e ∈ s) -> mapsto e s.
Proof. 
  move: e => [l r].
  move=> in1.
  exists l. split. auto. eapply Label.approx_refl.
Qed.

Lemma elements_functional {A}{e: M A}{w1 w2} : 
  partial_function e -> 
  elements e w1 -> elements e w2 -> w1 = w2.
Proof.
  move=> pfe.
Admitted.

Lemma partial_function_singleton {A}{k}{r:Result A} : 
   partial_function ⌈ (k , r) ⌉.
 Proof. 
   intros l r1 r2 [l1 [m1 a1]] [l2 [m2 a2]].
   inversion m1. inversion m2. subst. auto.
 Qed.

Lemma entry_approx_label {A:Type} {l1 r1 l2 r2}: 
  entry_approx (A:=A) (l1, r1) (l2, r2) -> Label.approx l1 l2.
destruct r1; simpl; tauto.
Qed.

Lemma entry_approx_refl {A} (e : label * Result A) : entry_approx e e.
Proof. destruct e as [l r]. destruct r; simpl; eauto using Label.approx_refl. Qed.

Lemma entry_approx_trans {A} (e1 e2 e3 : label * Result A) : 
  entry_approx e1 e2 -> entry_approx e2 e3 -> entry_approx e1 e3.
Proof. destruct e1 as [l1 r1]. destruct e2 as [l2 r2]. destruct e3 as [l3 r3]. 
       destruct r1; destruct r2; simpl.
Admitted.
(*
       eauto using Label.approx_trans. 
       intros h1 [h2 e]. eauto using Label.approx_trans. 
       intros h1 [h2 e]. eauto using Label.approx_trans. 
       intros [h1 e] h2. discriminate.
       intros [h1 e1] [h2 e2]. eauto using Label.approx_trans. 
       intros [h1 e1] [h2 e2]. discriminate.
       intros [h1 e1] h2. discriminate.
       intros [h1 e1] h2. discriminate.
       intros [h1 e1] [h2 e2]. inversion e1. subst. eauto using Label.approx_trans. 
Qed. *)

Lemma approx_refl {A} (s : M A) : approx s s.
Admitted.


End PartialFunctions.



(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                Semantic operators                         *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


Section Semantics.

Import LabelNotation.
Import SetNotations.
Import MonadNotation.
Import AlternativeNotation.

Local Open Scope monad_scope.


Context {A : Type} {eqb : A -> A -> bool}.

Definition left : (label * Result A) -> (label * Result A) := 
  fun '(l,w) => (L l, w).
Definition right : (label * Result A) -> (label * Result A) := 
  fun '(l,w) => (R l, w).


Definition BOTTOM : M A := ⌈ (Bot, Bottom) ⌉.

Definition WRONG  : M A := ⌈ (Top, Wrong) ⌉.

Definition FAIL   : M A := ∅.

Definition UNIT (x : A) : M A := ⌈ (Top, Value x) ⌉.

(* { (L𝑙,𝑤) | (𝑙,𝑤) ∈ 𝑠1 } ∪ {(R𝑙,𝑤) | (𝑙,𝑤) ∈ 𝑠2 } *)
Definition UNION (s1 s2 : P (label * Result A)) := 
  (fmap left s1) ∪ (fmap right s2).


(* SEQ:  For sequence we want to have this behavior:

bottom ; r  --> bottom
fail  ; r   --> fail
error ; r   --> error
value ; r   --> r 

But, there is a catch! with bind, if there is a result for the 
first s1 but no result for the second, then the whole expression fails. 
But if that first result is "bottom" or "error", then we want the expression
to loop or error instead. So we need to check to see what that 
result is.

 *)

Definition SEQ (s1 s2 : P (label * Result A)) :  P (label * Result A)%type :=
  '(l1, r1) <- s1 ;;
  match r1 with 
  | Bottom => ⌈ (l1 ⋈ Bot, Bottom) ⌉
  | Wrong =>  ⌈ (l1 ⋈ Top, Wrong) ⌉
  | _ =>  '(l2, r2) <- s2 ;; ⌈ (l1 ⋈ l2, r2) ⌉
         (* corresponds to  {(𝑙1 ⋈ 𝑙2,𝑤2) | (𝑙1,𝑤1) ∈ 𝑠1, (𝑙2,𝑤2) ∈ 𝑠2} *)
  end.


(* ONE: find the *smallest* labelled result *)
Definition ONE (s : P (label * Result A)) : (label * Result A) -> Prop := 
  fun '(l,w) => 

       exists k, ((k,w) ∈ s) 

            (* all other labeled results have larger labels. *)
            /\ (forall k' w', (k', w') ∈ s -> (k <=? k' = true))

            (* if the result is Bottom, then label is Bot. *)
            /\ (l = (if R.isBottom w then Bot else Top)).

    


(** ** EXISTS f: Merge togther the result of the function f applied to every w in W.

   - This operation must ensure that we only have one result per label. 
     If a label has multiple mappings (for any picked value w), then the 
     overall result is WRONG.

      exists X.X -> WRONG
      exists X. [X=3;X | X=4;X] -> { (L Top, 3) ∪ (R Top, 4) }

   - Not every result will be defined for each w. If we have a partial result for 
     any w, then the *whole* result is partial. We have to define exists like 
     this for monotonicity... 

   For example:

      fact = \x. if x = 0 then 1 else x * fact (x - 1) 

      exists x. fact x = 120

   This program must diverge, because fact (-1) goes into an infinite loop.
   To prevent this, must add a guard to the term so that it fails for negative
   inputs.

      exists x. x >= 0 ; fact x = 120

   This program terminates on all inputs, so its meaning is "5"

   - Note: exists must often be we guarded by a type check for base types. 
     For example, the meaning of this program is WRONG

        exists X. X + 1 = 2  

     because if X is not a number then the result is WRONG and that clashes 
     with the case that X is 1.

     Instead, this *must* be written as 

         exists X. (X : int) ; X + 1 = 2
     
   - Note: in this semantics we cannot define functions extensionally. 
     For example, we might want to say:

         exists f. (f : bool -> bool) ; f false = true ; f false = true

     as a way to define the boolean negation function. 

     However, guessing the function "\b.loop" causes that case to 
     diverge, so this term must diverge.
     [Even if this were not the case, we would still be in trouble 
     because there are multiple ways of expressing the negation 
     function, so the result would be wrong instead.]

     Instead, we can only define functions intensionally:
   
         exists f. f = \x. x + 1 ; f 

   Monotonicity + WRONG for disagreement means that we have to wait for all 
   options to continue before providing a result. If, instead, we return the 
   "first" successful answer, we may later learn that the answer should be 
   WRONG instead.


*)
                 
Print mapsto.

Definition all_match {A} l r1 (s : M A) := (forall r2 , (l, r2) ∈ s -> r1 = r2).
                         
Definition EXISTS {A} (f : A -> M A) : M A := 
  fun '(l,r) => 
    match r with 
    | Bottom => 
        (* for some guessed value the expression diverges *)
        exists w', mapsto (l, Bottom) (f w') 

    | Wrong =>

        label_finished l /\          

        (* there are no bottom results for this label. i.e. for 
           all chosen values, we have a nonbottom result *)
        (forall w' r, mapsto (l,r) (f w') -> r <> Bottom) /\

        (* there are two results that do not match *)
        (exists w1 r1, ((l, r1) ∈ (f w1)) /\
        (exists w2 r2, ((l, r2) ∈ (f w2)) /\ r1 <> r2))

    | Value _ =>

        label_finished l /\          

        (* there are no bottom results for this label. i.e. for 
           all chosen values, we have a nonbottom result *)
        (forall w' r, mapsto (l,r) (f w') -> r <> Bottom) /\
        
        (* this is a result for this label, in some world *)
        (exists w1, ((l, r) ∈ (f w1)) /\

        (* all results match r *)
        (forall w, all_match l r (f w)))
    end.


(** ** Intersection fails if its argument fails and diverges if its argument diverges *)
  (* { (l2, 𝑤2) | (𝑙2,𝑤2) ∈ 𝑠2, 𝑤1 = 𝑤2} *)

(* Could value w1 be represented by the entry? *)
Definition keep : W -> (label * Result W) -> bool := 
  fun w1 '(_, r2) => R.approxb W.eqb r2 (Value w1).

Definition INTER (w : W) : M W -> M W := Sets.filter (keep w).

(** ** All *)

(* The 'elements' proposition asserts that a set s is finite and contains the ordered 
   list of entries (i.e. labeled results). *)
Definition ALL : M W -> M W := 
  fun s => fun '(l,r) => 
    match l , r with 
    | Top , Value (TupleV ws) => 
        exists entries , elements s entries 
               /\ (List.map snd entries = List.map Value ws) 
                                            (* all of the results must succeed *)
    | Top , Bottom => exists l, (l , Bottom) ∈ s  (* if any of the results diverge, ALL diverges *)
    | Top , Wrong  => exists l, (l , Wrong) ∈ s   (* if any of the results errors, ALL errors *)
    | _   , _ => False                           (* if there are no results, ALL fails *)
    end.

End Semantics.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                Evaluator                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Section Eval.

Open Scope vec_scope.
Import Vector.VectorNotation.


Definition Env (n : nat) := Vector.vec W n.
Definition lookupEnv {n} (e : Env n) (x : fin n) : W := Vector.nth e x. 

(* semantics of values *)
Fixpoint evalVal {n} (env : Env n) (V : Val n) : W :=
  let evalVals (vs : list (Val n)) : list W := List.map (evalVal env) vs in
  match V with 
  | var_Val v => lookupEnv env v
  | Lam e => LamV env e
  | Tuple vs => TupleV (evalVals vs)
  | Int k => IntV k
  | Prim o => PrimV o
  end.

Definition evalVals {n} (env : Env n) := (List.map (evalVal env)).

Definition evalPrim (o : Op) (w : W) : M W := 
  match o , w with 
  (* addition *)
  | opAdd , TupleV (cons (IntV j) (cons (IntV k) nil)) => UNIT (IntV (j+k))
  | opAdd , _ => WRONG
  (* Gt *)
  | opGt  , TupleV (cons (IntV j) (cons (IntV k) nil)) =>
      if Nat.leb k j then UNIT ( IntV j ) else FAIL
  | opGt , _ => WRONG
  (* type test: identity function on Int, fails when given a non int value *)
  | opInt , IntV k => UNIT ( IntV k )
  | opInt , _ => FAIL
  end.

(* semantics of expressions *)

(* set of (label * Result Value) *)

Fixpoint evalExp (m:nat) {n : nat} (e: Exp n) : Env n -> M W :=  
  match m with 
  | 0 => fun env => BOTTOM
  | S m' => match e with 
           | Ret v => fun env => UNIT (evalVal env v)

           | Fail => fun env => FAIL

           | Or e1 e2 => fun env => UNION (evalExp m' e1 env) (evalExp m' e2 env)

           | Unify v1 e2 => fun env => INTER (evalVal env v1) (evalExp m' e2 env)

           | Seq e1 e2 => fun env => SEQ (evalExp m' e1 env) (evalExp m' e2 env)

           | App e v => fun env =>
               let w := evalVal env v in
               match evalVal env e with                      
                 | LamV env1 e1 => evalExp m' e1 (w :: env1)
                 | PrimV p => evalPrim p w
                 | _ => WRONG   (* non-function application *)
               end

           | Exists e => fun env => EXISTS (fun w => evalExp m' e (w :: env))

           | One e => fun env => ONE (evalExp m' e env)

           | All e => fun env => ALL (evalExp m' e env)
           end
  end.

Lemma eval_Ret {m' n} {v} : evalExp (S m') (Ret v) = fun (env : Env n) => UNIT (evalVal env v).
Proof. reflexivity. Qed.
Lemma eval_Or  {m' n} {e1 e2} : 
   evalExp (S m') (Or e1 e2) = fun (env : Env n) => UNION (evalExp m' e1 env) (evalExp m' e2 env).
Proof. reflexivity. Qed.
Lemma eval_App  {m' n} {e v} : 
   evalExp (S m') (App e v) = fun (env : Env n) => let w := evalVal env v in
               match evalVal env e with                      
                 | LamV env1 e1 => evalExp m' e1 (w :: env1) 
                 | PrimV p => evalPrim p w
                 | _ => WRONG   (* non-function application *)
               end.
Proof. reflexivity. Qed.
Lemma eval_Seq {m' n} {e1 e2} : 
  evalExp (S m') (Seq e1 e2) = fun (env : Env n) => SEQ (evalExp m' e1 env) (evalExp m' e2 env).
Proof. reflexivity. Qed.
Lemma eval_Unify {m' n} {v1 e2} : 
  evalExp (S m') (Unify v1 e2) = fun (env : Env n) => INTER (evalVal env v1) (evalExp m' e2 env).
Proof. reflexivity. Qed.
Lemma eval_Exists {m' n} {e} : 
  evalExp (S m') (Exists e) = fun (env : Env n) => EXISTS (fun w => evalExp m' e (Vector.cons w env)).
Proof. reflexivity. Qed.
Lemma eval_One {m' n} {e} : 
  evalExp (S m') (One e) = fun (env : Env n) => ONE (evalExp m' e env).
Proof. reflexivity. Qed.
Lemma eval_All {m' n} {e} : 
  evalExp (S m') (All e) = fun (env : Env n) => ALL (evalExp m' e env).
Proof. reflexivity. Qed.

End Eval.

Create HintDb evalExp.
Hint Rewrite @eval_Ret @eval_Or @eval_App @eval_Seq @eval_Unify @eval_Exists @eval_One @eval_All : evalExp.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Validity                                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


Section PartialFunction.

Import SetNotations.

(* We want to ensure that all interpretations are "valid". In other words, 
   the sets are all partial functions.
 *)

Lemma partial_function_BOTTOM {A} : partial_function (@BOTTOM A).
  eapply partial_function_singleton; eauto.
Qed.

Lemma partial_function_UNIT {A} (x:A) : partial_function (UNIT x).
  eapply partial_function_singleton; eauto.
Qed.

Lemma partial_function_FAIL {A} : partial_function (@FAIL A).
  intros k v1 v2 in1 in2. inversion in1. destruct H as [h1 h2]. inversion h1.
Qed.

Lemma partial_function_WRONG {A} : partial_function (@WRONG A).
  eapply partial_function_singleton; eauto.
Qed.

Lemma partial_function_UNION {A} (s1 s2 : M A) : partial_function s1 -> partial_function s2 -> partial_function (UNION s1 s2).
intros pf1 pf2 k v1 v2 in1 in2.
unfold UNION in *.
unfold mapsto in in1.
move: in1 => [k1 [in1 a1]].
move: in2 => [k2 [in2 a2]]. 
inversion in1 as [[k1'' r1] [[k1' r1'] [h1 h1']]|[k1'' r1] [[k1' r1'] [h1 h1']]]; 
inversion h1'; subst; clear h1';
inversion in2 as [[k2'' r2] [[k2' r2'] [h2 h2']]|[k2'' r2] [[k2' r2'] [h2 h2']]];
inversion h2'; subst; clear h2';
destruct k; try done; unfold Label.approx in a1,a2.
- eapply pf1; eauto. instantiate (1:= k). exists k1'.
  split; eauto. exists k2'. eauto. 
- eapply pf2; eauto. instantiate (1:= k). exists k1'.
  split; eauto. exists k2'. eauto. 
Qed.

Lemma partial_function_INTER  
  (v : W)(s2 : M W) : partial_function s2 -> partial_function (INTER v s2).
Proof.
  intros pf k v1 v2 in1 in2.
  unfold INTER in *. unfold partial_function in *.
  unfold filter in *.
  move: in1 => [k1 [[in1 h1] a1]].
  move: in2 => [k2 [[in2 h2] a2]].
  eapply pf with (l:= k); eauto.
  eexists; split; eauto.
  eexists; split; eauto.
Qed.

Lemma partial_function_SEQ {A} (s1 s2 : M A) : partial_function s1 -> partial_function s2 -> partial_function (SEQ s1 s2).
Proof.
  move=> pf1 pf2 k v1 v2 in1 in2.
  unfold partial_function in *.
  cbn in in1.
Admitted.
(*
  move: in1 => [[l1 r1] [h1 h1']]. 
  move: in2 => [[l2 r2] [h2 h2']]. 

  destruct r1; inversion h1';
  destruct r2; inversion h2'; subst; auto.
  all: try solve [inversion H2; subst; move: (pf1 _ _ _ h1 h2) => E1; done].
  all: destruct x as [l3 r3]; destruct H as [h3 h4]; inversion h4; clear h4; subst.
  all: try move: (pf1 _ _ _ h1 h2) => E1. 
  all: try done.
  destruct x0 as [l3' r3']. destruct H0 as [h3' h4']. inversion h4'. subst.
  move: (pf2 _ _ _ h3 h3') => E2.
  done.
Qed. *)

(* The IH doesn't help here because it only talks about individual 
   sets f w. But we need to reason about all f w. *)
Lemma partial_function_EXISTS {A} (f : A -> M A) : 
  partial_function (EXISTS f).
Proof.
intros k r r' ein ein'.
unfold EXISTS in ein, ein'.
cbn in ein, ein'.
destruct r eqn:ER.
-  move: ein => [l1 [[w' [l' [in1 a1]]] a2]].
   move: ein' => [l2' h].
   destruct r'. done.
   + move: h => [[fl2 [h1 h2]] a3]. 
   have EQ: (l2' = k). eapply fl2; eauto. subst l2'.
   have a4: (l' ⊑ k). eapply Label.approx_trans; eauto.
   assert ((Bottom : Result A) <> Bottom). eapply (h1 w').
   exists l'. split; eauto. done.
   +  move: h => [[fl2 [h1 h2]] a3]. 
   have EQ: (l2' = k). eapply fl2; eauto. subst l2'.
   have a4: (l' ⊑ k). eapply Label.approx_trans; eauto.
   assert ((Bottom : Result A) <> Bottom). eapply (h1 w').
   exists l'. split; eauto. done.
-  move: ein => [l1 [[h1 [NB1 [r1 [l' [w3 a1]]]]] a2]].
   move: ein' => [l2' h].
   have EQ: l1 = k. eapply h1; eauto. subst l1. 
   destruct r'. 
   -- move: h => [[w'' [l'' [in'' a3]] a4]].
      assert False. eapply NB1. exists l''. split. eapply in''. eapply Label.approx_trans; eauto. done. done.
   -- done.
   -- move: h => [[h3 [NB2 [w4 [a3 h4]]] a4]].
      move: a1 => [w5 [r5 [in5 NE]]].
      have EQ: l2' = k. eapply h3; eauto. subst l2'.

      move: (h4 w5 r5 in5) => E1.
      move: (h4 _ _ w3) => E2.
      rewrite E1 in E2. subst. done.
- move: ein => [l1 [[F1 [NB1 ALL1]] a1]]. 
  have EQ: l1 = k. eapply F1. auto. subst l1.
  move: ein' => [l2 h].
  destruct r'.
  -- move: h => [[w'' [l'' [in'' a3]] a4]].
     assert False. eapply NB1. exists l''. split; eauto. eapply Label.approx_trans; eauto. done. done.
  -- move: h => [[F2 [NB2 DIFF2]] a2].
     have EQ: l2 = k. eapply F2. auto. subst l2.
     move: DIFF2 => [w1 [r1 [in1 [w2 [r2 [in2 NE2]]]]]].
     move: ALL1 => [ w [inw ALL1 ]].
     move: (ALL1 _ _ in1) => E1.
     move: (ALL1 _ _ in2) => E2. subst. done.
  -- move: ALL1 => [ w1 [in1 ALL1 ]].
     move: h => [[F2 [NB2 ALL2]] a2].
     have EQ: l2 = k. eapply F2. auto. subst l2.
     move: ALL2 => [ w2 [in2 ALL2 ]].
     move: (ALL1 _ _ in2) => E1. done.
Qed.  

Lemma partial_function_ONE (e : M W) : partial_function e -> partial_function (ONE e).
Proof.
  intros pf k v1 v2 in1 in2.
  unfold ONE, partial_function in *.
  destruct k; try done.
  all: try solve [move: in1 => [? [h1 [h1' h1'']]];
    move: in2 => [? [h2 [h2' h2'']]];
    destruct v1; destruct v2; try discriminate; auto].
Admitted. 
(*
  + move: in1 => [k1 [h1 [h1' h1'']]].
    move: in2 => [k2 [h2 [h2' h2'']]].
    have LE1: (Label.leb k1 k2 = true); eauto.
    have LE2: (Label.leb k2 k1 = true); eauto.
    move: (Label.leb_antisymmetry _ _ LE1 LE2) => eq. subst.
    apply (pf k2); eauto.
Qed.
*)

Lemma map_Some_inv {A} {l l0 : list A} : list_map Some l = list_map Some l0 -> l = l0.
Proof. move: l0. 
       induction l; intros [|l0] h; inversion h; subst; f_equal.
       eapply IHl; eauto.
Qed.

Lemma partial_function_ALL (e : M W) : partial_function e -> partial_function (ALL e).
Proof.
  intros pfe k v1 v2 in1 in2.
  destruct k; try done.
  destruct v1; try done.
  destruct v2; try done.
  move: in1 => [l1 in1].
  move: in2 => [l2 in2].
Admitted.
(*
  destruct w; try done.
  destruct w0; try done.
  - f_equal. f_equal.
    have EQ : (w1 = w2). eapply elements_functional; eauto. subst.
    rewrite p1 in p2.
    apply map_Some_inv in p2. auto.
  - destruct w; try done. 
    destruct in1 as [xs [h1 h2]].
    destruct in2 as [l' h3].
    move: h1 => [h1 SS]. subst.
    apply mem_In in h3.
    apply List.in_map with (f := snd) in h3. rewrite h2 in h3. simpl in h3.
    rewrite List.in_map_iff in h3.
    move: h3 => [? [h3 _]]. done.
  - destruct v2. destruct w; try done.
    destruct in1 as [l' h3].
    destruct in2 as [xs [h1 h2]].
    move: h1 => [h1 SS]. subst.
    apply mem_In in h3.
    apply List.in_map with (f := snd) in h3. rewrite h2 in h3. simpl in h3.
    rewrite List.in_map_iff in h3.
    move: h3 => [? [h3 _]]. done.
    auto.
Qed. *)

Lemma partial_function_evalPrim {o w} :
   partial_function (evalPrim o w).
Proof.
  destruct o; destruct w; simpl.
  all: try eapply partial_function_WRONG.
  all: try eapply partial_function_UNIT.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try eapply partial_function_WRONG.
  all: try eapply partial_function_UNIT.
  destruct (Nat.leb n0 n).
  all: try eapply partial_function_UNIT.
  all: try eapply partial_function_FAIL.
Qed.

Lemma partial_function_evalExp : forall k n (env : Env n) e , partial_function (evalExp k e env).
intros k. induction k.
- intros. cbn. eapply partial_function_BOTTOM.
- intros.
  destruct e.
  + simpl. eapply partial_function_UNIT.
  + repeat rewrite eval_App.    
    remember (evalVal env v0) as w. cbv zeta.
    destruct (evalVal env v).
    all: try eapply partial_function_WRONG.
    eapply partial_function_evalPrim.
    eapply IHk.
  + repeat rewrite eval_Seq. eapply partial_function_SEQ; eauto.
  + repeat rewrite eval_Unify. eapply partial_function_INTER; eauto.
  + repeat rewrite eval_Exists.
    eapply partial_function_EXISTS. 
  + repeat rewrite eval_Or.
    eapply partial_function_UNION; eauto.
  + simpl.
    eapply partial_function_FAIL; eauto.
  + rewrite eval_One.
    eapply partial_function_ONE; eauto.
  + rewrite eval_All.
    eapply partial_function_ALL; eauto.
Qed.

End PartialFunction.


Section Validity.

Import SetNotations.

(* There is a smallest Bottom value, or no Bottom value *)

Definition Valid {A} (s : M A) : Prop := 
  (exists l, ((l, Bottom) ∈ s) /\ forall k, (k,Bottom) ∈ s -> Label.le l k) \/
  (forall l, not ((l,Bottom) ∈ s)).

Lemma Valid_BOTTOM {A} : Valid (@BOTTOM A).
  unfold BOTTOM.
  left. exists Bot. split; cbn; eauto.
  intros k in1. inversion in1. subst. cbv. auto.
Qed.

Lemma Valid_UNIT {A} (x:A) : Valid (UNIT x).
  right. intros l h. unfold UNIT in h. inversion h.
Qed.

Lemma Valid_FAIL {A} : Valid (@FAIL A).
  unfold FAIL. right. intros l h. inversion h.
Qed.

Lemma Valid_WRONG {A} : Valid (@WRONG A).
  unfold WRONG. right. intros l h. inversion h.
Qed.

Lemma Valid_UNION {A} (s1 s2 : M A) : Valid s1 -> Valid s2 -> Valid (UNION s1 s2).
intros in1 in2. 
unfold UNION in *. unfold Valid in *.
inversion in1 as [[l1 [i1 h1]]|h1]; clear in1. 
- left.
  exists (L l1). repeat split. left. cbn. exists (l1, Bottom). repeat split; eauto.
  intros k kin. cbn in kin. inversion kin; subst.
  -- destruct H as [[l1' w1] [h1' h2']]. 
     inversion h2'. subst.
     move: (h1 l1' h1') => LE. eauto.
  -- destruct H as [[l1' w1] [h1' h2']]. 
     inversion h2'. subst.
     unfold Label.le, Label.leb. simpl. auto.
- inversion in2 as [[l2 [i2 h2]]|h2]; subst; clear in2.
  + left. 
    exists (R l2). split. right. exists (l2, Bottom). repeat split; eauto.
    intros k kin. inversion kin; subst.
    -- destruct H as [[l1' w1] [h1' h2']]. 
       inversion h2'. subst.
       move: (h1 l1' h1') => LE. done.
    -- destruct H as [[l1' w1] [h1' h2']]. 
       inversion h2'. subst.
       move: (h2 l1' h1') => LE. eauto.
  + right.
    intros l h. 
    inversion h. 
    destruct H as [[l1 w1] [h3 h4]]. inversion h4. subst. eapply h1; eauto.
    destruct H as [[l1 w1] [h3 h4]]. inversion h4. subst. eapply h2; eauto.
 Qed.

Lemma Valid_INTER  
  (v : W)(s2 : M W) : Valid s2 -> Valid (INTER v s2).
Proof.
  intros pf. 
  unfold INTER in *. unfold Valid in *.
  destruct pf as [[l [h1 h2]]|pf].
  - left.
    exists l. split. cbv. split; auto.
    intros k kin. cbv in kin. move: kin=> [_ kin]. eapply h2. eauto.
  - right.
    intros l lin. cbv in lin. move: lin=> [_ lin]. eapply pf. eauto.
Qed.

Lemma Valid_SEQ {A} (s1 s2 : M A) : Valid s1 -> Valid s2 -> Valid (SEQ s1 s2).
Proof.
Admitted.

(* The IH doesn't help here because it only talks about individual 
   sets f w. But we need to reason about all f w. *)
Lemma Valid_EXISTS {A} (f : A -> M A) : 
  (forall w, Valid (f w)) -> Valid (EXISTS f).
Proof.
  unfold Valid.
  unfold EXISTS.
  cbn.
Admitted.  

Lemma Valid_ONE (e : M W) : Valid e -> Valid (ONE e).
Proof.
Admitted.

Lemma Valid_ALL (e : M W) : Valid e -> Valid (ALL e).
Proof.
Admitted.

Lemma Valid_evalPrim {o w} :
   Valid (evalPrim o w).
Proof.
  destruct o; destruct w; simpl.
  all: try eapply Valid_WRONG.
  all: try eapply Valid_UNIT.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try destruct w.
  all: try destruct l.
  all: try eapply Valid_WRONG.
  all: try eapply Valid_UNIT.
  destruct (Nat.leb n0 n).
  all: try eapply Valid_UNIT.
  all: try eapply Valid_FAIL.
Qed.

Lemma Valid_evalExp : forall k n (env : Env n) e , Valid (evalExp k e env).
intros k. induction k.
- intros. cbn. eapply Valid_BOTTOM.
- intros.
  destruct e.
  + simpl. eapply Valid_UNIT.
  + repeat rewrite eval_App.    
    remember (evalVal env v0) as w. cbv zeta.
    destruct (evalVal env v).
    all: try eapply Valid_WRONG.
    eapply Valid_evalPrim.
    eapply IHk.
  + repeat rewrite eval_Seq. eapply Valid_SEQ; eauto.
  + repeat rewrite eval_Unify. eapply Valid_INTER; eauto.
  + repeat rewrite eval_Exists.
    eapply Valid_EXISTS. intro w. eauto.
  + repeat rewrite eval_Or.
    eapply Valid_UNION; eauto.
  + simpl.
    eapply Valid_FAIL; eauto.
  + rewrite eval_One.
    eapply Valid_ONE; eauto.
  + rewrite eval_All.
    eapply Valid_ALL; eauto.
Qed.

End Validity.



(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Monotonicity                                              *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


Section Monotonicity.

Import SetNotations.
Import MonadNotation.


Ltac rewrite_approx := 
  match goal with 
  | [ H2 : Label.approxb ?l2 ?l2' = true |- _ ] => rewrite -> H2 
  | [ H2 : Label.approx ?l2 ?l2' |- _ ] => rewrite -> H2 
  end.


Lemma SEQ_monotone {A} {s1 s2 s1' s2' : M A} : 
  approx s1 s1' -> approx s2 s2' -> approx (SEQ s1 s2) (SEQ s1' s2').
Proof.
  intros [A1 A1'] [A2 A2'].
  unfold SEQ. unfold approx in *.
  split.
  - intros l v h ne.
    move: h => [[l0 v0] [h1 h2]].
    destruct v0; cbn in h2.
    + inversion h2. subst. clear h2. done.
    + inversion h2. subst. clear h2. 
      exists (l0, Wrong). split; eauto.
    + move: h2 => [[l1 v1] [h2 h3]].
      inversion h3. subst. clear h3.
      move: (A1 _ _ h1 ltac:(done)) => h1'.
      exists (l0, Value a).
      split; eauto.
      move: (A2 _ _ h2 ltac:(done)) => h2'.
      exists (l1, v). 
      split; eauto.
  - intros [l2 r2] [[l1' r1'] [h1 h2]].
    move: (A1' _ h1) => [[l1 r1] [in1 [a3 h3]]].
    destruct r1'; simpl in a3. 

    + (* bottom *) inversion h2. subst. clear h2.
      destruct r1; try solve [destruct a3; done].
      exists (Br l1 Bot, Bottom).
      split; auto.
      cbn.
      exists (l1, Bottom). repeat split;  auto.
      simpl. unfold Label.approx. simpl. rewrite a3. done.
    + (* wrong *) inversion h2. subst. clear h2.
      destruct r1.
      ++ exists (Br l1 Bot, Bottom). split; simpl; auto.
         exists (l1, Bottom). split; auto.
         unfold Label.approx. simpl. rewrite a3. done.
      ++  
         exists (Br l1 Top, Wrong).
         split; simpl; auto.
         exists (l1, Wrong). split; auto.
         unfold Label.approx. simpl. rewrite a3. done.
      ++ destruct h3. 
    + (* value *)
      destruct r1; try solve [destruct a3; done].
      ++ destruct h2 as [[l2' r2'] [in2 x3]]. inversion x3. subst. clear x3.
         cbn.
         exists (Br l1 Bot, Bottom). split; auto.
         exists (l1, Bottom). split; auto.
         cbn. unfold Label.approx. simpl. rewrite a3. done.
      ++ destruct h3 as [h3 V]. 
         destruct h2 as [[l2' r2'] [in2 x3]]. inversion x3. subst. clear x3.
         move: (A2' _ in2) => [[l2 r3] [x3 a4]].
         have [a4' a5] : (Label.approx l2 l2') /\ (r3 = Bottom \/ r3 = r2).
         { destruct r3; simpl in a4. 
           all: move: a4 => [? ?].
           tauto. destruct r2; try done. tauto. destruct r2; try done. 
           subst. tauto. }
         exists (Br l1 l2, r3).
         split.
         cbn.
         exists (l1, Value a0).
         split; auto.
         exists (l2, r3). 
         split; auto. 
         simpl. unfold Label.approx. simpl. rewrite a4'. rewrite a3.
         move: a5 => [a5|a5]; subst.         
         split; simpl; auto. 
         split; simpl; auto. 
         destruct r2; simpl; auto.
Qed.


Lemma bot_min k : 
  Label.leb Bot k = true.
Proof. 
  destruct k; cbv; auto.
Qed.

Hint Resolve bot_min : label.

Lemma approx_leb k k1 k2 :
  Label.leb k k1 = true -> 
  Label.approx k1 k2 -> Label.leb k k2 = true.
Proof.
  intros.
  unfold Label.approx in H0.
  apply Label.approxb_leb in H0.
  move: (@Label.le_transitive k1 k k2) => h. unfold Label.le in h. eauto.
Qed.

Lemma leb_transitive k1 k2 k3 : 
  Label.leb k1 k2 = true -> Label.leb k2 k3 = true -> Label.leb k1 k3 = true.
Admitted.

Lemma leb_swap l1 l2 : Label.leb l1 l2 = false -> Label.leb l2 l1 = true.
Proof.
  unfold Label.leb.
Admitted.


Lemma bottom_cases {A} (w : Result A) : w = Bottom \/ w <> Bottom.
Proof. destruct w. left. auto. right. done. right. done. Qed. 

Lemma ONE_monotone {s2 s2' : M W} : 
  Valid s2 ->
  approx s2 s2' -> approx (ONE s2) (ONE s2').
Proof.
  intros V2 [A1 A2].
  unfold ONE , approx in *.
  split.
  - intros l1 v1 h nb.
    move: h => [k [h1 [L1 h2]]].
    have EQ: l1 = Top. destruct v1; try done. clear h2.
    move: (A1 _ _ h1 nb) => h3.
    exists k. repeat split; eauto.
    intros k' w' In'.
    move: (A2 _ In') => [[k0 v0] [h4 h5]].
    move: (L1 _ _ h4). 
    move: (entry_approx_label h5).
    clear. intros.
    eapply approx_leb; eauto.
    destruct v1; done.
  - (* everything in s2' is approximated by something in s2 *)
    intros [l w2'] [l2' [h1 [h2 h3]]].
    move: (A2 (l2',w2') h1) => [[l2 w2] [h4 h5]].
    move: (bottom_cases w2') => D.
    destruct D as [->|h6]. 
    + (* w2' diverges, so w2 must diverge *)
      simpl in h2. simpl in h5.
      have [EQ a]: (w2 = Bottom /\ Label.approx l2 l2').
      { destruct w2. split; auto. all: destruct h5; try done. } clear h5. subst.
      exists (Bot, Bottom). split; cbn; auto.
      (* need to know that for all of the (k,Bottom) ∈ s2, there is some minimum one. 
         NOTE: we already know that one exists. *)
      destruct V2 as [[k [hk1 hk2]]|imp]. 2: {  assert False. eapply imp. eauto. done. } 
      move: (hk2 _ h4) => LE.
      apply Label.approxb_le in a.
      exists k. repeat split; auto.
      intros k' w' kin'.
      have EB: (w' = Bottom \/ w' <> Bottom). {  destruct w'. left; auto. all: right; done. }
      destruct EB.
      ++ subst. eapply hk2; auto.
      ++ move: (A1 _ _ kin' H) => h6.
         move: (h2 _ _ h6) => LE2.
         eapply leb_transitive. unfold Label.le in *. eauto.
         eapply leb_transitive. eauto. eauto.
      ++ unfold Label.approx; simpl; split; auto.
    + (* w2' does NOT diverge *)
      have EQ: l = Top. destruct w2'; try done. subst.
      simpl in h5.
      have [a [E1|E2]]: Label.approx l2 l2' /\ (w2 = w2' \/ w2 = Bottom).
      { unfold Label.approx in h5.
        destruct w2; split; auto; 
          try simpl in h5; destruct h5; subst; try done. left; auto. 
        destruct w2'; done. left; auto. 
      destruct w2'; try done. subst.  auto.}
      (* w2 does NOT diverge *)
      ++ clear h5. subst w2'. 
         (* either (l2,w2) has the smallest label or bottom does *)
         have D: (exists k, ((k, Bottom) ∈ s2) /\ forall k' w', ((k', w') ∈ s2) -> Label.le k k') \/
                 (forall k' w', ((k', w') ∈ s2) -> Label.le l2 k').
         { 
           unfold Valid in V2. destruct V2 as [[l1 [h7 h8]]|h7].
           - (* (l1,Bottom) in s2 and l1 is smallest bottom. *)
             destruct (Label.leb l1 l2) eqn:LEl.
             -- (* l1 is smaller than l2 *) 
               left. exists l1. split; auto.
               intros k' w' in'.
               move: (bottom_cases w') => C.
               destruct C as [C|C]. subst. eapply h8; eauto.
               move: (A1 _ _ in' C) => in2'.
               move: (h2 _ _ in2') => LE3.
               (* transitivity: l1 <= l2 [= l2' <= k' *)
               apply Label.approxb_le in a. 
               unfold Label.le in *.
               eapply leb_transitive; eauto.
               eapply leb_transitive; eauto.

             -- (* (l2, w2') is smaller than (l1, Bottom) *)
               right.
               move: (leb_swap _ _ LEl) => LE1.
               intros k' w' in'.
               move: (bottom_cases w') => C.
               destruct C as [C|C]. subst. 
               (* if w' is Bottom, then must have l1 <= k'  *)
               move: (h8 _ in') => LE2. 
               unfold Label.le in *. 
               eauto using leb_transitive.

               (* otherwise transitivity: l2 [= l2' <= k' *)
               move: (A1 _ _ in' C) => in2'.
               move: (h2 _ _ in2') => LE3.               
               apply Label.approxb_le in a. 
               unfold Label.le in *. 
               eauto using leb_transitive.

           - (* no bottoms in s2 *)
             right.
             intros k' w' in'.
             move: (bottom_cases w') => C.
             destruct C as [C|C]. subst. 
             (* if w' is Bottom, then done. *)
             assert False. eapply h7; eauto. done.
             (* otherwise transitivity: l2 [= l2' <= k' *)
             move: (A1 _ _ in' C) => in2'.
             move: (h2 _ _ in2') => LE3.               
             apply Label.approxb_le in a. 
             unfold Label.le in *. 
             eauto using leb_transitive.
         }                

         destruct D as [[k [kin kmin]]|nok].
         -- exists (Bot, Bottom).
            repeat split; auto.
            exists k. repeat split; auto.
         -- exists (Top, w2).
            unfold Label.approx in a.
            repeat split; cbn; auto. 
            exists l2. repeat split; auto.
            unfold Label.approx.
            rewrite EQ. auto.
            destruct w2; reflexivity.
      ++ (* w2 DIVERGES *)
        (* need to know that for all of the (k,Bottom) ∈ s2, there is some minimum one. 
         NOTE: we already know that one exists. *)
        unfold Valid in V2.
        destruct V2 as [[l [lin h7]]|h7].
        +++ subst.
            exists (Bot, Bottom). cbn. repeat split; auto.
            exists l. repeat split; eauto.
            intros k' w' in'.
            move: (bottom_cases w') => C.
            destruct C as [C|C]. subst. eapply h7; eauto.
            move: (A1 _ _ in' C) => in2'.
            move: (h2 _ _ in2') => LE2.
            move: (h7 _ h4) => LE1.
            (* transitivity: l <= l2 <= l2' <= k' *)
            unfold Label.approx in a.
            apply Label.approxb_le in a. unfold Label.le in *.
            eapply leb_transitive. eauto.
            eapply leb_transitive. eauto. auto.
        +++ subst. assert False. eapply h7. eauto. done.
Qed.


      
Lemma INTER_monotone {w}{s2 s2' : M W} : 
  approx s2 s2' -> approx (INTER w s2) (INTER w s2').
Proof.
  intros [A1 A2].
  unfold INTER , approx, filter, In in *. 
  split.
  - intros l1 v1 h nb.
    move: h => [h1 h2].
    split. eauto. eauto.
  - intros [l2 v2][h2 h3].
    move: (A2 _ h3) => [[l1 v1] [h1 A3]].
    exists (l1, v1). split; eauto.
    split; auto.
    destruct v1; simpl in *; auto.
    move:A3 => [h4 EQ].
    destruct v2; try done.
    destruct v2; try done.
    move:A3 => [h4 EQ]. done.
    move:A3 => [h4 EQ]. subst. cbn in h2. done.
Qed.


Lemma notBottom {A}{r:Result A} : r <> Bottom -> R.isBottom r = false.
intro h. destruct r; try done. Qed.


(* This result depends on classical logic. *)
Lemma results_agree {A} (f : A -> M A) (l : label) (r1 : Result A) :
  (forall w2 r2 , mapsto (l, r2) (f w2) -> r1 = r2) \/ (exists w2 r2, mapsto (l, r2) (f w2) /\ r1 <> r2).
Proof.
  remember (forall w2 r2, mapsto (l, r2) (f w2) -> r1 = r2) as P.
  have [h|h]: P \/ not P by apply classic. 
  subst P. left. auto.
  subst P. right.
  apply not_all_ex_not in h.
  move: h => [w h].
  apply not_all_ex_not in h.
  move: h => [r2 h].
  apply imply_to_and in h.
  exists w. exists r2. auto.
Qed.

Lemma do_all_match {A} (f : A -> M A) (l : label) (r1 : Result A) :
  (forall w , all_match l r1 (f w)) \/ (not (forall w, all_match l r1 (f w))).
Proof.
  eapply classic.
Qed.

Lemma proof_case_left {A B C} : A -> B -> (A -> B) /\ (not A -> C).
  intros. split. intros ?. auto.
  intros h. done.
Qed.

Lemma proof_case_right {A B C} : not A -> C -> (A -> B) /\ (not A -> C).
  intros. split.  intros ?. done. 
  intros h. done.
Qed.


Lemma exists_bottom {A} (f : A -> M A) (l : label) : 
  (exists w, mapsto (l, Bottom) (f w)) \/ (forall w, not (mapsto (l, Bottom) (f w))).
Proof. 
  remember (exists w, mapsto (l, Bottom) (f w)) as P.
  have [h|h]: P \/ not P by apply classic.
  subst P. left. auto.
  subst P. right.
  apply not_ex_all_not.
  auto.
Qed.

Lemma EXISTS_monotone {A} {f f' : A -> M A} :
  (forall w, partial_function (f' w)) -> 
  (forall w, approx (f w) (f' w)) ->
  approx (EXISTS f) (EXISTS f').
Proof.
  intros pf hA.
  unfold EXISTS.
  split.
  - (* (1) nonbottoms are preserved *)
    intros l r h0 ne. cbn in h0. cbn.
    (* we know the result r is not Bottom, propagate *)
    move: (notBottom ne) => nb.
    rewrite nb in h0. rewrite nb. move: h0 => [nb0 h0].
    split. 
    + (* wtp that there are no bottoms in f'. *)
      move=> w2 [l2 [in2 a2]].  
      (* in2: suppose there were some (l2, Bottom) ∈ f' w2 
         by (3) it has to come from some bottom in f w2, *)
      move: (hA w2) => [_ hA2]. 
      move: (hA2 _ in2) => [[l1 r1] [in1 [apx1 apx2]]]. 
      cbv in apx2; destruct r1; try done.
      (* then there is some (l1, Bottom) in f w2 where l1 ⊑ l2 *)
      eapply (nb0 w2); eexists; split; eauto.
      eapply Label.approx_trans; eauto.
    + (* wtp that nonbottoms in f are in f' *)
      move: h0 => [w1 [r1 [in1 [Ag1 Dg1]]]].
      (* any random entry (l,r) in f w1 is not bottom *)
      have ne1: r1 <> Bottom. 
      { move: (nb0 w1) => h. intros ->. assert False. apply h. apply in1. done. } 

      (* by (1) it should also be in f' *)
      move: (hA w1) => [hA1 _].
      move: in1 => [l1 [in1 a1]].
      move: (hA1 _ _ in1 ne1) => in1'. clear hA1.

      exists w1. exists r1.      
      split. eauto.

      destruct (do_all_match f l r1) as [h1|h1].
      -- (* all results match in f, we want to show that they all match in f' *)
        eapply proof_case_left; eauto.
        have AM: forall w : A, all_match l r1 (f' w).
        move=>w r2 [l2 [in2 a2]].
        move: (hA w) => [hA1 hA2].
        move: (hA2 (l2,r2) in2) => [[l1' r1'] [in1'' a1']].
        destruct a1' as [a1' ar1].
        have EQ: r1 = r1'. eapply h1. exists l1'. split; eauto. eapply Label.approx_trans; eauto.
        subst r1'. destruct r1; try done; destruct r2; try done. inversion ar1. subst. auto.
        admit.
Admitted.
(*
      -- intros ?. apply not_all_ex_not in H. move: H => [w nam]. 
         assert False. apply nam. eapply h1.

      (* and anything else in f' w2 should be equal to r1 *)
      intros h1. apply Ag1. intros w2 r2' [l' [in2' a2]].
      specialize (h1 w2 r2'). apply h1. exists l'. split; auto.

      (* by (3) they were in f *)
      move: (hA w2) => [_ hA2]. 
      move: (hA2 (l', r2') in2') => [[l1 r2] [in2 [a2 h2]]].
      (* know r2 ⊑ r2', see how this holds *)
      destruct r2 eqn:Er1.
      ++ (* r2 is Bottom, impossible. *)
        assert False. eapply (nb0 w2). exists l1. split; auto. eapply Label.approx_trans; eauto. done.
      ++ (* r2 is Wrong so r2' is Wrong *) destruct r2'; try done.
         eapply (h1 w2 Wrong).
         exists l1. split; auto. eapply Label.approx_trans; eauto.
      ++ (* r2 is Value a *) destruct r2'; try done. inversion h2. subst a0.
         eapply (h1 w2 (Value a)).
         exists l1. split; auto.  eapply Label.approx_trans; eauto.
-  (* (3) everything in EXISTS f' came from EXISTS f *)
  intros [l r] h. cbn in h. (* say (l,r) ∈ EXISTS f' *)
  destruct (R.isBottom r) eqn:IB.
  + (* r is Bottom, must be some (f w') that contains bottom *)
    move: h => [w' [l' [in' a']]].
    move: (hA w') => [_ hA2].
    move: (hA2 _ in') => [[l1 r1] [in1 [a1 a1']]]. 
    (* r1 must be bottom *) destruct r1; try done.    
    exists (l1, Bottom). cbn.
    repeat split. 2: eapply Label.approx_trans; eauto.
    exists w'. exists l1. split; auto. eapply Label.approx_refl; eauto.
  + (* r is not bottom, so no individiual result can be bottom *)
    move: h => [nb [w' [r1' [in' h1]]]].
    (* we have a non bottom result r1' in some f' w' *)
    have nb1': r1' <> Bottom. 
    { intro h. subst. eapply nb. eexists. split. eauto. eapply Label.approx_refl. } 
    (* need to find some entry in some world that has (l, r1') *)
    (* either there is one, or there isn't one. *)
    have [ISB|NB]: (exists w, mapsto (l, Bottom) (f w)) \/ (forall w, not (mapsto (l, Bottom) (f w))).
    admit.
    ++ (* if there is, we use it! *)
      move: ISB => [wb [lb [inb ab]]]. exists (lb, Bottom). cbn.
      repeat split. exists wb. exists lb. split; auto. eapply Label.approx_refl. auto.
    ++ (* if there is not, we use (3) to find (l, r1) in f w' *)
    move: (hA w') => [_ hA2].
    move: (hA2 _ in') => [[l1 r1] [in1 [a1 a1']]].

    destruct (R.isBottom r1) eqn:E.
    { (* r1 cannot be bottom *) destruct r1; try done.
      assert False. eapply NB. exists l1. split. eauto. auto. done. 
    }
    
    (* but do all worlds agree with (l,r1) ? *)
    have [AGREE|DISAGREE]: 
      (forall w2 r2, mapsto (l1, r2) (f w2) -> r1 = r2) \/ 
      (exists w2, exists r2, mapsto (l1, r2) (f w2) /\ r1 <> r2).
    admit.
    --- (* all worlds agree, so need to show that r = r1 *)
        exists (l1, r1). cbn.
        rewrite E.
        repeat split.
        +++ (* no other bottoms in f at any world *)  
          intros w2 [l' [in2' a2']]. 
          eapply NB. exists l'. split; eauto. eapply Label.approx_trans; eauto.
        +++ (* we have a result in some world. *)
          exists w'.  exists r1. split. auto.
          (* in every world, everything agrees with r1 *) 
          intros w2 r2 [l2' [in2' a2']].
          left.
          split. eapply AGREE. exists l2'. split; eauto. auto.
        +++ auto.
        +++ destruct (h1 w' r1') as [[h1' h2']|[h1' ?]]. exists l. split; eauto using Label.approx_refl.
            subst. auto. done.            
    --- (* there is a discrepancy. *)
      move: DISAGREE => [wb [rb [inb ne]]].
      exists (l1, Wrong). cbn.      
      repeat split.
      +++ intros w2 [l' [in2' a2']].
          eapply NB. exists l'. split; eauto. eapply Label.approx_trans; eauto.
      +++ exists w' . exists r1. split. auto.
          intros w2 r2 [l2' [in2' a2']].
          destruct (h1 w2 
          right. split; auto.
          eapply DISAGREE.

          have NB2: (r2 <> Bottom). { intro h. subst. split; eauto.
                                     eapply NB. exists l2'. split; eauto. eapply Label.approx_trans; eauto. }
          move: (hA w2) => [hA1 _].
          move: (hA1 _ _ in2' NB2) => in2''.
          destruct (h1 w2 r2) as [[h3 h4]|[h5 h6]].
        { exists l2'. split. eauto. eapply Label.approx_trans; eauto. } 
        { subst. destruct r1; try done. destruct r; try done. auto.
          destruct r; try done. inversion a1'. auto. } 
        { subst.
          have EQ: (r1 = r1'). { destruct r1; try done. simpl in a1'. destruct r1'; try done.
                                 simpl in a1'. destruct r1'; try done. subst. auto. } 
          subst r1'.
          right. split. auto.
          
Admitted. *)


Lemma evalExp_monotone : forall k n (env : Env n) e , approx (evalExp k e env) (evalExp (S k) e env).
intros k. induction k.
- intros. admit. 
- intros.
  destruct e.
  + simpl. eapply approx_refl.
  + repeat rewrite eval_App.    
    remember (evalVal env v0) as w. cbv zeta.
    destruct (evalVal env v).
    all: try eapply approx_refl.
    eapply IHk.
  + repeat rewrite eval_Seq. eapply SEQ_monotone; eauto.
  + repeat rewrite eval_Unify. eapply INTER_monotone; eauto.
  + repeat rewrite eval_Exists.
    eapply EXISTS_monotone. intro w; eauto.
    admit.
    intro w.
    eapply IHk.
  + repeat rewrite eval_Or.
Admitted.

End Monotonicity.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Finite semantics                                          *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Require Import Logic.PropExtensionality.

Section FiniteSemantics.

Import SetNotations.
Import List.ListNotations.
Import MonadNotation.
Import LabelNotation.

Open Scope list_scope.
Open Scope monad_scope.

Lemma singleton_mem {A}{x:A} : ⌈ x ⌉ = mem ([ x ]%list).
Proof. 
  eapply Extensionality_Ensembles.
  rewrite mem_singleton_eq.
  reflexivity.
Qed.

Lemma fmap_mem {A B}{f : A -> B}{s} :
  mem (List.map f s) = fmap f (mem s).
Proof. 
Admitted.

Lemma filter_mem {A}{f : A -> bool}{s} :
  mem (List.filter f s) = filter f (mem s).
Proof. 
Admitted.

Lemma bind_cong {A B}{m1 m2 : P A}{k1 k2 : A -> P B} : 
  (m1 = m2) -> (forall x, k1 x = k2 x) -> bind m1 k1 = bind m2 k2.
Proof. 
  intros -> R.
  cbv.
  eapply Extensionality_Ensembles.
  split; intros x [a [h1 h2]].
    rewrite -> R in h2; exists a; eauto.
    rewrite <- R in h2; exists a; eauto.
Qed.

Lemma bind_mem {A B} (m : list A) (k : A -> list B) : 
  mem (bind m k) = bind (mem m) (fun y => mem (k y)).
Proof. 
  induction m.
  - eapply Extensionality_Ensembles.
    cbv. split.
    intros x xIn. done.
    intros x [y [z w]]. done.
  - cbn.
    rewrite union_mem.
    rewrite IHm.
    eapply Extensionality_Ensembles.
    split.
    + intros x xIn. inversion xIn; subst; clear xIn.
    ++ exists a. split. left; auto. auto.
    ++ move: H => [a' [aIn xIn]].
       exists a'. split. right. auto. auto.
    + intros x [a' [[h1|h1] h2]]. 
      ++ subst. econstructor; eauto.
      ++ right. exists a'. split; eauto.
Qed.

Lemma UNIT_mem {A} : forall (x : A), 
    UNIT x = mem ([(Top, Value x)]).
Proof.
  intro x. unfold UNIT. eapply singleton_mem.
Qed.

Lemma UNION_mem {A}{l1 l2: list (label * Result A)} : 
  UNION (mem l1) (mem l2) = mem (List.map left l1 ++ List.map right l2).
Proof.
  unfold UNION.
  rewrite union_mem.
  repeat rewrite fmap_mem.
  reflexivity.
Qed.


Lemma INTER_mem {x:W}{xs:list (label * Result W)} : 
  INTER x (mem xs) = mem (List.filter (keep x) xs).
Proof. 
  unfold INTER.
  rewrite filter_mem.
  reflexivity.
Qed.

(*
Lemma SEQ_mem {A}{l1 l2: list (label * Result A)} :
  SEQ (mem l1) (mem l2) = 
    mem ( '(l1, r1) <- l1 ;;
          '(l2, r2) <- l2 ;;
          [ (l1 ⋈ l2, strictly r1 r2) ] ).
Proof.
  unfold SEQ.
  rewrite -> bind_mem.
  apply bind_cong.
  reflexivity.
  intros [l0 r0].
  rewrite -> bind_mem.
  apply bind_cong.
  reflexivity.
  intros [k0 r1].
  rewrite singleton_mem.
  reflexivity.
Qed.


Definition union_map {A B} (m : list A) (k : A -> P B) : P B :=
  List.fold_left Union (List.map k m) Empty_set.

Lemma SEQ_mem' {A}{l1: list (label * Result A)}{s2} :
  SEQ (mem l1) s2 = 
    union_map l1 (fun '(l1 , r1) => 
          '(l2, r2) <- s2 ;;
          ⌈ (l1 ⋈ l2, strictly r1 r2) ⌉).
Proof.
  unfold SEQ.
  induction l1.
  - cbv.
    eapply Extensionality_Ensembles.
    split. intros x [y [h xIn]]. done. intros x xIn. done.
  - 
Admitted.
*)

End FiniteSemantics.

Create HintDb mem.
Hint Rewrite @UNIT_mem @UNION_mem @INTER_mem (* @SEQ_mem *) : mem.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Examples                                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Section Examples.

Import SetNotations.
Import VerseNotations.
Import Vector.VectorNotation.
Import LabelNotation.

Ltac process := 
  repeat match goal with 
  | [H : True |- _ ] => clear H
  | [H : ?a ∈ ⌈ ?a ⌉ |- _ ] => clear H
  | [H : ?a ∈ ⌈ ?b ⌉ |- _ ] => inversion H; clear H; subst
  | [H : ?A /\ ?B |- _ ] => inversion H; clear H; subst
  | [H : ?x ∈ UNIT ?a |- _ ] => inversion H; clear H; subst
  | [H : UNIT ?a ?x |- _ ] => inversion H; clear H; subst
  | [H : Some ?a = Some ?b |- _ ] => inversion H; clear H; subst
  | [H : ⌈ ?a ⌉ ?b |- _ ] => inversion H; clear H; subst
  | [ |- forall x , _ ] => intros ? 
  | [H : (exists h, _ ) |- _ ] => move: H => [? H]
  | [ H : match ?x with _ => _ end |- _ ] => 
      (destruct x; try done; auto; let n:=numgoals in guard n <= 1) + idtac "too many goals"
  end.

Ltac go := process;auto.

Hint Unfold UNIT ONE EXISTS.
Hint Constructors Ensembles.Singleton.

Lemma P_In {A}{f : P A}{x} : (f x) -> x ∈ f. cbv. auto. Qed.
Lemma In_extensionality {A} {s1 s2 : P A} : 
  (forall x, (x ∈ s1) <-> x ∈ s2) -> s1 = s2.
Proof.
  intros h.
  eapply Extensionality_Ensembles.
  split. intros x xIn; eapply h; eauto.
  intros x xIn; eapply h; eauto.
Qed.

Lemma In_mem : forall (A : Type) (x : A) (l : list A), x ∈ mem l <-> List.In x l.
Admitted.
Lemma W_eqb_eq (w1 w2: W) : W.eqb w1 w2 = true <-> w1 = w2.
Admitted.


(* 3 = 3 || 4 = 4 || 5 = 5 *)
Definition ex_one : Exp 0 := Or (Int 3 ≡ Int 3) (Or (Int 4 ≡ Int 4) (Int 5 ≡ Int 5)).

Example ex_one_semantics : evalExp 10 ex_one Vector.nil = 
  mem ((L Top, Value (IntV 3)) :: (R (L Top),Value (IntV 4)) :: (R (R Top),Value (IntV 5)) :: nil).
Proof.
  unfold ex_one. autorewrite with evalExp.
  unfold evalVal.
  autorewrite with mem.
  f_equal.
Qed.

Lemma union2 {A} (v1 v2 : A) : UNION (UNIT v1) (UNIT v2) = mem ((L Top, Value v1) :: (R Top,Value v2) :: nil).
Proof.
  repeat rewrite UNIT_mem.
  rewrite UNION_mem.
  cbv.  
  done.
Qed.

(* ∃ x. x = (1 || 2) ;; x *)
Definition ex_two : Exp 0 := bind1 (Or (Int 1) (Int 2)) x0.
Lemma ev_ex_two1 : evalExp 10 ex_two Vector.nil =
                     mem ((L Top ⋈ Top, Value (IntV 1)) :: (R Top ⋈ Top, Value (IntV 2)) :: nil).
Proof.
unfold ex_two,bind1. asimpl.
autorewrite with evalExp.
unfold evalVal, lookupEnv, Vector.nth, var_zero.
rewrite union2.
(* Want to prove sets are the same, will do so by showing they 
   contain the same elements. *)
eapply In_extensionality.
intros [l r].
(* need to show that (l,r) is in both sets *)
rewrite In_mem.
Opaque INTER SEQ mem. cbn.
Transparent INTER SEQ mem.
destruct (R.isBottom r) eqn:hr.
+ split.
  intros [w' [l' [wIn sl]]].
  cbn in wIn.
  move: wIn => [[l0 r0][h1 h2]]. 
  destruct r0; cbv in h1.
  move: h2 => [l1 [r1 h3]]]].
  inversion h3; subst; clear h3.
  unfold UNIT in h2. inversion h2; subst; clear h2.
  have C: ((w = IntV 1 /\ l0 = L Top) \/ (w = IntV 2 /\ l0 = R Top)).
  { unfold INTER in h1.
    rewrite <- filter_mem in h1.
    rewrite In_mem in h1.
    cbn in h1.
    destruct (W.eqb w (IntV 1)) eqn:E1.
    rewrite W_eqb_eq in E1. subst. cbn in h1. inversion h1; try done. inversion H. subst.
    left. split; auto.
    destruct (W.eqb w (IntV 2)) eqn:E2.
    rewrite W_eqb_eq in E2. subst. inversion h1; try done. inversion H. subst.
    right. auto.
    destruct h1.
  }
  rewrite INTER_mem in h1.
  rewrite In_mem in h1.
  destruct C as [[-> ->]|[-> ->]].
  ++ cbn in h1. inversion h1; try done. inversion H. subst.
     simpl. left; eauto.
  ++ cbn in h1. inversion h1; try done. clear h1. inversion H. subst.
     simpl. right; left; eauto.
+ move=> [h1|[h1|]]; try done; inversion h1; clear h1; subst.
  split.
  ++ exists (IntV 1). exists (L Top, Some (IntV 1)). cbv. split; eauto. econstructor.
Admitted. *)
(*
     exists (Top, Some (IntV 1)). split; try econstructor; eauto.
  ++ intros w' r' h.
     have C : (r' = Some (IntV 1)).
     { cbn in h.
       move: h => [[l0 r0] [h1 h2]].
       move: h2 => [[l1 r1] [h2 h3]].
       inversion h3; subst; clear h3.
       inversion h2; subst; clear h2.
       rewrite INTER_mem in h1.
       rewrite In_mem in h1.
       cbn in h1.
       destruct (W.eqb w' (IntV 1)) eqn:E1. 
       rewrite W_eqb_eq in E1. subst. 
       destruct h1. inversion H. done.
       simpl in H. done.
       destruct (W.eqb w' (IntV 2)) eqn:E2.
       rewrite W_eqb_eq in E2. subst. 
       destruct h1; inversion H. inversion h1.
     } subst.  auto.
  ++ admit.
Admitted. *)

Lemma INTER_two : forall w l1 v1 l2 v2 s, 
  INTER w (mem ((L l1, Value v1) :: (R l2, Value v2) :: nil)) = s -> 
  ((w = v1 /\ s = mem ((L l1, Value v1) :: nil)) \/
   (w = v2 /\ s = mem ((R l2, Value v2) :: nil))).
Proof.
Admitted.

       (* prove that there is only one y 
       rewrite INTER_mem in h.
       rewrite UNIT_mem in h.
       simpl in h.
       destruct (W.eqb w' (IntV 3)) eqn:E1.
       rewrite W_eqb_eq in E1. subst. simpl in h.
       rewrite SEQ_mem in h. simpl in h. inversion h. inversion H. auto.
       inversion H.
       destruct (W.eqb w' (IntV 4)) eqn:E2. 
       rewrite W_eqb_eq in E2. subst.
       rewrite SEQ_mem in h. simpl in h. inversion h. inversion H. auto.
       rewrite SEQ_mem in h. simpl in h. inversion h.  *)


(* ∃ x. x = (1 || 2) ;; exists y. y = (3 || 4) ;; < x , y > *)
Definition ex_four : Exp 0 := 
  bind2 (Or (Int 1) (Int 2)) (Or (Int 3) (Int 4)) (Tuple (cons x1 (cons x0 nil))).

Lemma ev_ex_four1 : (L Top ⋈ (L Top ⋈ Top), 
                      Value (TupleV (cons (IntV 1) (cons (IntV 3) nil))))
                      ∈ evalExp 30 ex_four Vector.nil.
Proof.
  unfold ex_four, bind2.
  autorewrite with evalExp. 
  asimpl.
  autorewrite with evalExp.
  simpl.
  unfold lookupEnv, Vector.nth, var_zero, var_one.
  autorewrite with mem. simpl.
  split.
  - intros w2 h.
    admit.
  - exists (IntV 1).  eexists.
    autorewrite with mem. simpl.
    repeat split.
    exists (L Top, Value (IntV 1)). split; eauto.
    simpl.
    exists (L Top ⋈ Top, Value (TupleV (IntV 1 :: IntV 3 :: nil))). 
    split. 2: econstructor; eauto.
    split.
    -- cbn.
       exists (IntV 3). 
       exists (L Top, Value (IntV 3)). 
       rewrite INTER_mem. rewrite In_mem.
       simpl. split; eauto.
       exists (Top,  Value (TupleV (IntV 1 :: IntV 3 :: nil))). 
       split. econstructor; eauto.
       econstructor; eauto.
    -- intros w' r' h.
       move: (@INTER_two w' Top (IntV 3) Top (IntV 4) _ ltac:(reflexivity)) => [[h0 h1]| [h0 h1]].
       subst. rewrite h1 in h. clear h1.
       rewrite UNIT_mem in h. rewrite SEQ_mem in h. rewrite In_mem in h. simpl in h.
       inversion h; try done. inversion H. done.
       subst. rewrite h1 in h. clear h1.
       autorewrite with mem in h. simpl in h.
       inversion h; try done. 

  - intros w' r' h.
    move: (@INTER_two w' Top (IntV 1) Top (IntV 2) _ ltac:(reflexivity)) => [[h0 h1]| [h0 h1]];
    rewrite h1 in h; clear h1; subst w'.
    unfold SEQ in h. simpl in h.
Admitted.





Eval cbv in evalExp 10 Vector.nil ex_four.

Lemma label_comparable_SEQ {A}{s1 s2 : M A}{ l1 l2 } :
  label_comparable s1 l1 -> label_comparable s2 l2 ->
  label_comparable (SEQ s1 s2) (l1 ⋈ l2).
Proof.
  unfold label_comparable.
  move=> h1 h2.
  move=> k [v h3]. unfold SEQ in h3.
  destruct k; try done.
  simpl.
  rewrite (h1 k1).
  2: 
  rewrite (h2 k2).
  3: 
    destruct v; reflexivity.
  destruct v; cbn in h3.
  go. econstructor; eauto.
  destruct h3. go. econstructor; eauto.
  go. econstructor; eauto.
  destruct v; cbn in h3.
  go. econstructor; eauto.
  destruct h3. go. econstructor; eauto.
  go. econstructor; eauto.
Qed.


  
End Example1.



Module Monotonicity.




Definition contains (w : W) (m : M W ) : Prop := 
  exists l , (l, Value w) ∈ m.



(* Examples *)



(* exists x. x = 3 ; x *)
Definition ex0 : Exp 0 := 
  Exists (Seq (Unify (Ret (var_Val var_zero)) (Ret (Int 3))) (Ret (var_Val var_zero))).

Lemma evex0 : exists n, UNIT (IntV 3) ≃ ONE (evalExp n Vector.nil ex0).
exists 4. 
cbn. unfold ONE, EXISTS, UNIT.
split.
- intros x xIn. go.  
  exists ((Top ⋈ Top) ⋈ Top)%label.
  repeat split.
  -- exists (IntV 3). eexists; repeat econstructor; eauto.
  -- cbn. go.
  -- (* label_comparable *)
    unfold label_comparable, in_dom. go. 
    cbn in H. go.
  -- go. cbn in H. go.
- intros x xIn.
  cbn in xIn.
  destruct x; try done.
  destruct l; try done.
  cbn in xIn.
  go.
Qed.

(* exists x. x = 3 | x = 4 *)

Lemma mem_nil_contra {A}(s : P A): (mem nil ≃ s) -> forall x, (x ∈ s) -> False.
Proof. intros. unfold mem in H. move: H => [h1 h2].
specialize (h2 x H0). inversion h2.
Qed.

Definition ex1 : Exp 0 := 
 Exists (Or (Unify (Ret (var_Val var_zero)) (Ret (Int 3)))
            (Unify (Ret (var_Val var_zero)) (Ret (Int 4)))).

Lemma evex1 : exists n, ALL (evalExp n Vector.nil ex1) ≃ UNIT (TupleV (cons (IntV 3) (cons (IntV 4) nil))).
exists 10.
unfold ALL, EXISTS.
split.
- intros x xIn.
  destruct x as [l sw].
  destruct l; try done. 
  destruct sw as [x|]; cbn in xIn.
  -- destruct x; try done.
     move: xIn => [xs ?]. go.
     have EQ: (l = (IntV 3 :: IntV 4 :: nil)%list).
     { unfold elements in H. 
       go.
       have h1: (List.In (L (Top ⋈ Top), Value (IntV 3)) xs). admit.
       have h2: (List.In (R (Top ⋈ Top), Value (IntV 4)) xs). admit.
       admit.
(*       destruct xs as [|x1 xs].
       + move: (mem_nil_contra H1 (L (Top ⋈ Top), Value (IntV 3))) => h1. 
         exfalso. apply h1.
         cbn.
         repeat split. eexists. repeat split.
         go. inversion H4. done.
         intros. unfold label_comparable. intros k.
         go. unfold in_dom in H. go. cbn in H. destruct k; try done.
         destruct k; try done. go. inversion H3. inversion H4. subst. done.
       + destruct xs as [|x2 xs].
         *)
     } subst l.
     unfold UNIT. econstructor; eauto.
  -- move: xIn => [l h].
     go. 
     destruct l; try done; go. 

- intros x xIn.
  go.
  cbn.
  exists ( (L (Top ⋈ Top), Value (IntV 3)) :: (R (Top ⋈ Top), Value (IntV 4)) :: nil )%list.
  repeat split.
  ++ intros x xIn. cbn in xIn. destruct xIn; try done; subst.
     +++ cbn. repeat split.
         eexists. repeat split. intros. go. 
         intros. unfold label_comparable. intros.
         unfold in_dom in H. go. cbn in H. destruct k; try done.
         destruct k; try done. go. 
     +++ destruct H; try done; subst.
         cbn. repeat split.
         eexists. repeat split. intros. go. 
         intros. unfold label_comparable. intros.
         unfold in_dom in H. go. cbn in H. destruct k; try done.
         destruct k; try done. go. 
  ++ intros x xIn. unfold EXISTS in xIn. destruct x. cbn in xIn. go.
     destruct l; try done. destruct l; try done. go.
     destruct l; try done. go.
  ++ repeat econstructor; eauto.
Admitted.

(* 
    exists x. x 1 = 2 ; x 1 
*)

Definition ex2 : Exp 0 := 
  Exists (Seq (Unify (App (var_Val var_zero) (Int 1)) (Ret (Int 2)))
              (App (var_Val var_zero) (Int 1))).

(* We can show that "2" is in the meaning of this expression *)
Lemma evex2 : exists n, exists l, (l, Value (IntV 2)) ∈ evalExp n Vector.nil ex2.
Proof.
  exists 20.
  eexists. unfold ex2. 
  rewrite -> eval_Exists.
  unfold EXISTS.
  remember (LamV Vector.nil (Ret (Int 2))) as w'.
  remember ((App (var_Val var_zero) (Int 1) ≡ Int 2); App (var_Val var_zero) (Int 1)) as ebody.
  have VE: forall w', Valid (evalExp 19 (Vector.cons w' Vector.nil) ebody). admit.
  have EE: (((Top ⋈ Top) ⋈ Top), Value (IntV 2)) ∈ (evalExp 19 (Vector.cons w' Vector.nil) ebody).
  { subst ebody. subst w'. cbn. eexists. repeat split. }
  repeat split.
  - eexists. eauto.
  - (* need to prove that there is only one possible result *)
    intros w'' v'.
    rewrite eval_Seq. unfold SEQ.
    intro h.
    destruct h as [w1 [h1 [h2 h3]]].
    rewrite eval_Unify in h1.
    unfold INTER in h1.
    destruct h1 as [h4 h5].
    cbn in h5. inversion h5. subst.
    (* here we should know that 
       - evalExp 17 env e ⊆ evalExp 18 env e 
       - evalExp 18 env e is Valid, so a partial function
       - thus v' = Value (IntV 2)
     *)
    admit.
  - (* need to prove that all result labels are compareable with the one that we have. *)
    
    intros w'.
    unfold label_comparable.
    intro k.
    intros x.
    -- unfold WRONG in H. done.
    -- destruct o; cbn in H1; unfold WRONG in H1; try  done.
       go.
    -- unfold WRONG in H. done.
    -- 

  split; eauto. exists (IntV 2). constructor; eauto. constructor; eauto.
Qed.

(* 
What is the meaning of this term?
if (x=1) then (2 || 3) else 4; x=(1 || 2); if (x=1) then 5 else (6 || 7) 

exists x. if (x=1) then (2 || 3) else 4    ==   [2;3] ∪ [4]

exists x. if (x=1) then (2 || 3) else 4 ; if (x = 1) then 5 else (6 || 7)  

            == [5;5] ∪ [6;7]

               

*) 



(* 

(* 
∃x. (if x = 1 then 11 || 22 else 33); x = (1 || 2); (if x= 1 then 44 else 55 || 66)

           < x is 1 >               < x is 2 >
    == ([11, 22] ; <> ; [44])  ∪ ( [33] ; <> ; [66] ) 

    == 44 ∪ 66
*)





Section ProperInstances.

Import SetNotations.
Import MonadNotation.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Proper instances for semantic operators                   *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)


#[export] Instance UNION_Included_Proper {A} :
  Morphisms.Proper (Included ==> Included ==> Included) (@UNION A).
intros s1 t1 R1 s2 t2 R2.
unfold UNION. 
eapply union_left. 
+ eapply (@fmap_Included _ _ left) in R1.
rewrite -> R1.
eapply sub_union_left.
+ eapply (@fmap_Included _ _ right) in R2.
rewrite -> R2.
eapply sub_union_right.
Qed.

#[export] Instance UNION_Same_set_Proper {A} : Morphisms.Proper (Same_set ==> Same_set ==> Same_set) (@UNION A).
intros s1 t1 [R1 S1] s2 t2 [R2 S2].
split; eapply UNION_Included_Proper; eauto.
Qed.


#[export] Instance INTER_Included_Proper : Morphisms.Proper (Logic.eq ==> Included ==> Included) INTER.
intros s1 t1 -> s2 t2 R2.
unfold INTER. 
intros [l w] xIn.
destruct w; cbn in xIn; try done.
Admitted.

#[export] Instance INTER_Same_set_Proper : Morphisms.Proper (Logic.eq ==> Same_set ==> Same_set) INTER.
intros s1 t1 eq s2 t2 [R2 S2]. subst.
split; eapply INTER_Included_Proper; eauto.
Qed.

#[export] Instance SEQ_Included_Proper {A} : Morphisms.Proper (Included ==> Included ==> Included) (@SEQ A).
intros s1 t1 R1 s2 t2 R2.
unfold SEQ. 
apply bind_Included_Proper; auto.
intros [l1 r1].
apply bind_Included_Proper; auto.
intros [l2 r2].
reflexivity.
Qed.

#[export] Instance SEQ_Same_set_Proper {A} : Morphisms.Proper (Same_set ==> Same_set ==> Same_set) (@SEQ A).
intros s1 t1 [R1 S1] s2 t2 [R2 S2].
split; eapply SEQ_Included_Proper; eauto.
Qed.

(* NOTE: ONE is not monotonic. A larger set gives a different answer. *)
#[export] Instance ONE_Included_Proper {A} : Morphisms.Proper (Same_set ==> Included) (@ONE A).
intros s1 t1 [R1 S1].
unfold ONE. 
intros [l w] xIn.
destruct l; cbn in xIn; try done.
move: xIn => [l [h1 h2]].
cbn. exists l. split. eapply R1. auto.
intros k' w' h. apply S1 in h. eauto.
Qed.

#[export] Instance ONE_Same_set_Proper {A} : Morphisms.Proper (Same_set ==> Same_set) (@ONE A).
intros s1 t1 R1.
split; eapply ONE_Included_Proper; eauto. symmetry. auto.
Qed.

#[export] Instance EXISTS_Included_Proper {A} : Morphisms.Proper ((fun f1 f2 => (forall x, Same_set (f1 x) (f2 x))) ==> Included) (@EXISTS A).
intros s1 t1 R.
unfold EXISTS.
intros [l r] xIn.
cbn in xIn. cbn.
move: xIn => [[w h] k].
move: (R w) => [R1 R2].
split.
apply R1 in h. eauto.
intros w' r' h1.
move: (R w') => [R1' R2'].
apply R2' in h1. eauto.
Qed.

#[export] Instance EXISTS_Same_set_Proper {A} : Morphisms.Proper ((fun f1 f2 => (forall x, Same_set (f1 x) (f2 x))) ==> Same_set) (@EXISTS A).
intros s1 t1 R1.
split; eapply EXISTS_Included_Proper; eauto. symmetry. auto.
Qed.

#[export] Instance ALL_Included_Proper : Morphisms.Proper (Same_set ==> Included) ALL.
intros s1 t1 R.
unfold ALL.
intros [l r] xIn.
cbn in xIn. destruct l; try done. cbn.
destruct r. destruct w; try done.
Admitted.

#[export] Instance ALL_Same_set_Proper : Morphisms.Proper (Same_set ==> Same_set) ALL.
intros s1 t1 R.  Admitted.



(*
Definition InUpTo {A}(eqv : A -> A -> Prop) (s : A -> Prop) (w:A)  : Prop := 
  exists w', eqv w w' /\ s w'.
Definition IncludedUpTo {A}(eqv : A -> A -> Prop) (s1 s2 : A -> Prop) : Prop := 
  (forall x, InUpTo eqv s1 x -> InUpTo eqv s2 x).
Definition EqUpTo {A} (eqv : A -> A -> Prop) (s1 s2 : A -> Prop) : Prop := 
  IncludedUpTo eqv s1 s2 /\ IncludedUpTo eqv s2 s1.
*)
  
(*
Definition EqOption {A} (eqv : A -> A -> Prop) : option A -> option A -> Prop := 
  fun o1 o2 =>
    match o1 , o2 with 
    | None , None => True
    | Value a1 , Value a2 => eqv a1 a2 
    | _ , _ => False
    end.
Definition EqPair {A}{B} (eqa : A -> A -> Prop) (eqb : B -> B -> Prop) : A * B -> A * B -> Prop := 
  fun '(a1,y1) '(a2,y2) => eqa a1 a2 /\ eqb y1 y2.
*)

(*
Inductive EqV : W -> W -> Prop := 
  | EqV_IntV : forall k, EqV (IntV k) (IntV k)
  | EqV_LamV : forall m1 (env1 : Env m1) e1 m2 (env2 : Env m2) e2,
      (forall w, exists n, 
          EqUpTo (EqPair (fun l1 l2 => Label.eqb l1 l2 = true) (EqOption EqV)) 
            (evalExp n (Vector.cons w env1) e1) (evalExp n (Vector.cons w env2) e2)) ->
      EqV (LamV env1 e1) (LamV env2 e2).
*)

End ProperInstances.

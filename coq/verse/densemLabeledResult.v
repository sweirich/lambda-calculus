Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Require structures.Option.
Require Import structures.Sets.
Require Import structures.Monad.

(* autosubst2 "generated" syntax *)
Require Import fintype.
Require Import verse.syntax.

Set Implicit Arguments.

(* This file defines a "denotational" semantics for Verse.

   W* == (label * result W) -> Prop

   The label records which branch of an "Or" we are in
   The option records whether that branch diverges or not
   If a branch fails, that label will not be in the set

   NOTE: In Coq, the type A -> Prop represents a set of "A"s. In 
   this semantics, we have an invariant that for any l, there is at most *one*
   x in the set. So really instead of a set of values, we have 
   a partial mapping of labels to values.

   W* == Set of (label * option W) 

   Can we capture this invariant in the type some how? I'm not sure

     o  W* == label -> option A   
 
        is not the same because it requires a deciable function, not a relation

     o  W* == label -> option W -> Prop 

        doesn't enforce the invariant, because it is just currying the above

     o  W* == { S : P (label * option W) | partial_function S }

        enforces invariant but is annoying to work with

*)

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* "deriving" Eq for syntax                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Module EqSyntax.

Module Op. 

Definition eqb (x y : Op) : bool :=
  match  x , y with
  | opAdd , opAdd => true
  | opGt , opGt => true
  | opInt , opInt => true
  | _ , _ => false
  end.

Lemma eqb_eq : forall x y, 
  eqb x y = true <-> x = y.
Proof.
  intros x y. split; destruct x; destruct y; simpl; done.
Qed. 

Lemma eqb_neq : forall x y, 
  eqb x y = false <-> x <> y.
Proof. 
  intros x y. split; destruct x; destruct y; simpl; done.
Qed.

End Op.

Fixpoint fin_eqb {n} := 
  match n return fin n -> fin n -> bool with 
  | 0 => fun x y => match x with end
  | S m => fun x y =>
      match x , y with 
      | Some x' , Some y' => fin_eqb x' y'
      | None , None => true
      | _ , _ => false
      end
  end.

Fixpoint Val_eqb {n} (x y : Val n) : bool := 
  let fix Vals_eqb {n} (xs ys : list (Val n)) := 
  match xs , ys with
  | cons x xs , cons y ys => (Val_eqb x y && Vals_eqb xs ys)%bool
  | nil , nil => true
  | _ , _ => false
  end in
  match x , y with 
  | var_Val f1 , var_Val f2 => fin_eqb f1 f2
  | Int n1 , Int n2 => Nat.eqb n1 n2
  | Prim o1 , Prim o2 => Op.eqb o1 o2
  | Tuple vs1 , Tuple vs2 => Vals_eqb vs1 vs2
  | Lam e1 , Lam e2 => Exp_eqb e1 e2
  | _ , _ => false
  end
with Exp_eqb {n} (x y : Exp n) : bool := 
  match x, y with 
  | Ret v1 , Ret v2 => Val_eqb v1 v2
  | App v1 u1 , App v2 u2 => Val_eqb v1 v2 && Val_eqb u1 u2
  | Seq e1 e2 , Seq e1' e2' => Exp_eqb e1 e1' && Exp_eqb e2 e2'
  | Unify v1 e2 , Unify v1' e2' => Val_eqb v1 v1' && Exp_eqb e2 e2'
  | Exists e1 , Exists e1' => Exp_eqb e1 e1'
  | Or e1 e2 , Or e1' e2' => Exp_eqb e1 e1' && Exp_eqb e2 e2'
  | Fail , Fail => true
  | One e1 , One e1' => Exp_eqb e1 e1'
  | All e1 , All e1' => Exp_eqb e1 e1'
  | _ , _ => false
  end.


End EqSyntax.
Import EqSyntax.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Syntactic sugar                                           *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Definition var_one {n : nat} : fin (S (S n)) := Some None. 
Definition var_two {n : nat} : fin (S (S (S n))) := Some (Some None). 

Definition bind1 {n} : Exp n -> Exp (S n) -> Exp n := 
  fun e1 e2 =>
    Exists (Seq (Unify (var_Val var_zero) (ren_Exp shift e1)) e2).

Definition bind2 {n} : Exp n -> Exp n -> Exp (S (S n)) -> Exp n := 
  fun e1 e2 e3 =>
    Exists (Seq (Unify (var_Val var_zero) (ren_Exp shift e1))
                (Exists (Seq (Unify (var_Val var_zero) (ren_Exp (shift >> shift) e2))
                          e3))).

Definition app {n} : Exp n -> Exp n -> Exp n := 
  fun e1 e2 => bind2 e1 e2 (App (var_Val var_one) (var_Val var_zero)).


Module VerseNotations.

Declare Scope verse_syntax.
Delimit Scope verse_syntax with Exp.
Open Scope verse_syntax.

Notation x0 := (var_Val var_zero).
Notation x1 := (var_Val var_one).
Notation x2 := (var_Val var_two).

Notation "⟨⟩" := (Tuple nil) : verse_syntax.

Infix ";;" := Seq (at level 100, right associativity) : verse_syntax.

Infix "≡" := Unify (at level 100, right associativity) : verse_syntax.

Coercion Ret : Val >-> Exp.

Infix "@" := app (at level 71, left associativity) : verse_syntax.

Definition ifthenelse {n} (e1 e2 e3 : Exp n) : Exp n := 
  One ( Or ( e1 ;; Lam ( ⟨⟩ ≡ x0 ;; ren_Exp shift e2 ) )
                 ( Lam ( ⟨⟩ ≡ x0 ;; ren_Exp shift e3 ) )) @ ⟨⟩.

Notation "e1 ?? e2 :: e3" := (ifthenelse e1 e2 e3) (at level 70) : verse_syntax.

End VerseNotations.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Length indexed vectors *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Module Vector. 

Inductive vec (A:Type) : nat -> Type := 
  | nil : vec A 0
  | cons : forall {n}, A -> vec A n -> vec A (S n)
.

Arguments nil {_}.
Arguments cons {_}{_}.

Fixpoint nth {A}{n} (v : vec A n) : fin n -> A := 
  match v in vec _ n return fin n -> A with 
        | nil => null
        | cons x xs => fun f => match f with 
                            | Some g => nth xs g
                            | None => x
                            end
        end.

(* 
Fixpoint eqb {A} {n} (eqA : A -> A -> bool) := 
  match n return vec _ n -> vec A n -> bool with 
  | 0 => fun v1 v2 => true
  | S m => fun v1 v2 => 
            match v1 , v2 in vec _ m with 
            | cons x xs , cons y ys => (eqA x y && eqb eqA xs ys)%bool
            | nil , nil => true
            | _ , _ => false
            end
  end.
*)

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Bind Scope vec_scope with vec.

Open Scope vec_scope.

Module VectorNotation.
Infix "::" := cons (at level 60, right associativity) : vec_scope.
Notation "[ ]" := nil (format "[ ]") : vec_scope.
Notation "[ x ]" := (cons x nil) : vec_scope.
(*
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : vec_scope.
*)
End VectorNotation.

End Vector.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Labels                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Module Label.

Declare Scope label_scope.
Delimit Scope label_scope with label.
Open Scope label_scope.

Inductive label : Type := 
   | Top : label
   | Br  : label -> label -> label   (* sequenced choices *)
   | L   : label -> label           (* inside a left choice *)
   | R   : label -> label           (* inside a right choice *)
.

Module Label.

  Fixpoint compare (l m : label) : comparison := 
    match l , m with 
    | L l0 , L m0 => compare l0 m0
    | R l0 , R m0 => compare l0 m0 
    | L _  , R _  => Lt
    | R _ , L _   => Gt

    | Top , Top => Eq

    | Br l1 l2 , Br l3 l4 => 
        match compare l1 l3 with
        | Eq => compare l2 l4
        | o  => o
        end

    (* these don't matter, we will only compare comparable things *)
    | L _ , _  => Lt
    | _   , L _  => Gt
    | Top , _ => Lt
    | _   , Top => Gt
    | Br _ _ , _ => Lt
    | _   , Br _ _ => Gt
   
    end.

  Fixpoint comparable (l1 l2 : label) : bool :=
    match l1 , l2 with 
    | L l0 , L m0 => comparable l0 m0
    | R l0 , R m0 => comparable l0 m0 
    | L _  , R _  => true
    | R _ , L _   => true
    | Top , Top => true
    | Br l1 l2 , Br l3 l4 => comparable l1 l3 && comparable l2 l4
    | _ , _ => false
    end.

  (* During computation, a partial result will have label "Top". However, 
     if we give the evaluator more fuel, the expression may make 
     choices, so the label will grow more structure.

          Top ⊑ L Top
              ⊑ L (R Top) 
              ⊑ L (R (Top ⋈ Top))
              ⊑ L (R (L Top ⋈ Top))
              ⊑ L (R (L Top ⋈ R Top))
   *)
  Fixpoint approx (l1 l2 : label) : bool := 
    match l1 , l2 with 
    | Top , _ => true 
    | L l0 , L l1 => approx l0 l1 
    | R l0 , R l1 => approx l0 l1 
    | Br l1 l2 , Br l3 l4 => approx l1 l3 && approx l2 l4            
    | _ , _ => false
    end.

  Lemma approx_refl : forall l, approx l l = true.
  Proof. induction l; eauto. simpl. rewrite IHl1. rewrite IHl2. auto. Qed.

  Lemma approx_trans : forall l2 l1 l3, 
      approx l1 l2 = true -> approx l2 l3 = true -> approx l1 l3 = true.
  Proof. induction l2. all: intros l1 l3. 
         all: destruct l1; destruct l3.
         all: simpl; intros h1 h2; try done. 
         all: try (apply andb_prop in h1; move: h1 => [h1 h1']).
         all: try (apply andb_prop in h2; move: h2 => [h2 h2']).
         all: try (apply andb_true_intro; split; eauto 3).
         eauto.
         eauto.
  Qed.

  Definition eqb l m : bool := 
    match compare l m with 
    | Eq => true
    | _ => false
    end.

  Definition ltb l m : bool := 
    match compare l m with 
    | Lt => true
    | _ => false
    end.

  Fixpoint leb l m : bool := 
    match compare l m with 
    | Lt => true
    | Eq => true
    | _ => false
    end.

Lemma compare_refl: forall x, compare x x = Eq.
Proof. induction x.
       cbv. done. 
       simpl. rewrite IHx1. rewrite IHx2. done.
       simpl; auto.
       simpl; auto.
Qed.


Lemma compare_eq : forall x y, compare x y = Eq <-> x = y.
Proof. 
intros x y.
split.
- move: y. 
  induction x; intros y; destruct y.
  all: simpl.
  all: try done.
  all: try (destruct (compare x1 y1) eqn:c1).
  all: intro c2.
  all: try done.
  all: try rewrite (IHx1 y1); auto. 
  all: try rewrite (IHx2 y2); auto. 
  all: try rewrite (IHx y); auto. 
- move: y. induction x; intros y; destruct y.
  all: simpl.
  all: try done.
  all: try (destruct (compare x1 y1) eqn:c1).
  all: intro c2.
  all: try (inversion c2; subst; clear c2).
  all: try rewrite (IHx1 y1); auto. 
  all: rewrite IHx1 in c1; auto.
Qed.


Lemma compare_transitive: forall y x z o, 
    compare x y = o -> compare y z = o -> compare x z = o.
Proof. 
  move=> y. induction y; intros x z o h1 h2.
  all: destruct x; destruct z; simpl in *; subst; auto.
  all: try solve [inversion h2; auto].
  destruct (compare y1 z1) eqn: c1;
  destruct (compare x1 y1) eqn: c2.
  all: try (rewrite compare_eq in c1; subst).
  all: try (rewrite compare_eq in c2; subst).
  all: try (rewrite compare_refl).
  all: try rewrite c2; auto.
  all: try rewrite c1; auto.
  all: try solve [inversion h2].
  + erewrite IHy1 with (o := Lt); auto.
  + erewrite IHy1 with (o := Gt); auto.
Qed.

Lemma ltb_notreflexive: forall x, not (ltb x x = true).
intros x. unfold ltb. rewrite compare_refl. done.
Qed.

End Label.

Module LabelNotation.
Infix "⋈" := Br (at level 70, right associativity) : label_scope.
Infix "=?" := Label.eqb (at level 70) : label_scope.
Infix "<=?" := Label.leb (at level 70) : label_scope.
Infix "<?" := Label.ltb (at level 70) : label_scope.
End LabelNotation.
  
Instance LtStrict : StrictOrder (fun x y : label => (Label.ltb x y) = true).
constructor.
- intros l h. eapply Label.ltb_notreflexive; eauto.
- intros x y z. move: z. 
  induction y; intros z h1 h2; destruct x; destruct z; 
    cbn in *; try done.
  + unfold Label.ltb in *.
    simpl in *.
    specialize (IHy1 z1). 
    specialize (IHy2 z2).
Admitted.

Lemma leb_antisymmetry k1 k2 : 
  Label.leb k1 k2 = true -> Label.leb k2 k1 = true -> k1 = k2.
Proof. 
  move: k2.
  induction k1; intros k2; destruct k2.
  all: simpl.
  all: try done.
Admitted.


End Label.

Import Label.


Section PartialFunctions.

Import SetNotations.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*      partial functions as sets of pairs                   *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(* A set of pairs is a partial function if there is at most one 
   mapping for any key in the set. NOTE: this definition uses 
   syntactic equality for values. That means that for values 
   with multiple representations (i.e. functions) this definition 
   is too rigid. 
*)
Definition partial_function {K}{V}  (S : P (K * V)) := 
  forall k v1 v2, (k , v1) ∈ S -> (k , v2) ∈ S -> v1 = v2.

(* This predicate defines when a key is in the domain of 
   the partial function *)
Definition in_dom {K}{V} (s : P (K * V)) (k : K) : Prop := 
  exists v, (k,v) ∈ s.

(* Access the canonical list of elements in a finite mapping *)
Definition elements {K}{V} (R : K -> K -> Prop) (s : P (K * V)) (l : list (K * V)) : Prop := 
  let LT := fun '(l1,_) '(l2, _)=> R l1 l2 in
  (mem l = s) /\                        (* memberships are equal *)
  @Sorted.LocallySorted _ LT l.        (* the list is sorted by the labels *)


(*
Lemma app_cong {A B} {f g : A -> B} : f = g -> forall x, f x = g x.
intro h. rewrite h. auto. Qed. 
*)

Lemma smaller_notpresent {K}{V}{R : K -> K -> Prop}`{StrictOrder _ R} (a : K * V) (w : list (K * V)) :
  List.Forall (let '(l1, _) := a in fun '(l2, _) => R l1 l2) w ->
  ~(List.In a w).
Proof. destruct a. 
       induction w.
       intros h1 h2. inversion h2.
       intros h1 h2. simpl in h2. 
       inversion h1. subst.
       destruct h2.
       + rewrite H0 in H2. destruct H. 
         unfold Irreflexive, complement, Reflexive in *. 
         eauto.
       + apply IHw; eauto.
Qed.

Lemma elements_functional {K}{V}{R : K -> K -> Prop}
  `{StrictOrder _ R}{e: P (K * V) }{w1 w2} : 
  partial_function e -> 
  elements R e w1 -> elements R e w2 -> w1 = w2.
Proof.
  move=> pfe.
  have TR: Transitive (fun '(l1, _) '(l2, _) => R l1 l2).
  { intros t. unfold Transitive.
    intros [l1 _][l2 _][l3 _]. eapply H. }
  unfold elements in *.
  repeat rewrite <- Sorted.Sorted_LocallySorted_iff.
  move=> [m1 S1].
  move=> [m2 S2]. rewrite <- m1 in m2. 
  apply Sorted.Sorted_StronglySorted in S1; try apply TR.
  apply Sorted.Sorted_StronglySorted in S2; try apply TR.
  remember ((fun '(l1, _) '(l2, _) => R l1 l2) : (K * V) -> (K * V) -> Prop) as Rl.
  move: S1 w2 m2 S2.
  induction w1.
  - intros S1 w2 m2 s2. destruct w2. done.
Admitted.
(*    
    unfold mem in m2. 
    
    move: m2 => [m21 _].
    specialize (m21 p ltac:(left; eauto)).
    inversion m21.
  - intros S1 w2 m2 S2. destruct w2. 
    -- move: m2 => [_ m22].
       specialize (m22 a ltac:(left; eauto)).
       inversion m22.
    -- inversion S1. subst.
       inversion S2. subst.
       move: (@smaller_notpresent K V R H a w1 H3) => ni1.
       move: (@smaller_notpresent K V R H p w2 H5) => ni2.
       have: (a = p). admit. move => h. subst a.
       apply Sets.mem_cons_inv in m2.
       f_equal. eapply IHw1; eauto.
Admitted. *)

End PartialFunctions.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Result                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(* Note: failure is the absence of a result. We don't want it 
   to be a specific result, because terms will fail in LOTs 
   of ways and we don't want to keep track of that. *)
Inductive Result (A : Type) : Type := 
  | Bottom : Result A
  | Wrong  : Result A 
  | Value  : A -> Result A.

Arguments Bottom {_}.
Arguments Wrong {_}.
Arguments Value  {_}.

Module R. 

Definition isWrong {A} (r : Result A) : bool := 
  match r with | Wrong => true | _ => false end.
Definition isBottom {A} (r: Result A) : bool := 
  match r with | Bottom => true | _ => false end.
Definition isValue {A} (r: Result A) : bool := 
  match r with | Value _ => true | _ => false end.

Definition strict {A} (r1 r2 : Result A) : Result A  := 
  match r1 , r2 with
  | Bottom , _ => Bottom
  | Wrong , _ => Wrong
  | Value _ , r2 => r2
  end.

Definition approx {A} (r1 r2 : Result A) : Prop := 
  match r1 , r2 with 
  | Bottom , _ => True
  | Wrong , Wrong => True
  | Value w1 , Value w2 => w1 = w2
  | _ , _ => False
end.

Definition keep {A} (R : A -> A -> bool) (w1 : A) (r : Result A) : bool := 
  match r with
  | Value w2 => R w1 w2
  | Bottom => true
  | Wrong => false
  end.

End R.



(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Domain of values                      *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(* This is our domain of values (W): numbers, primitives, tuples of values 
   and closures *)

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

Definition left {A} : (label * A) -> (label * A) := 
  fun '(l,w) => (L l, w).
Definition right {A} : (label * A) -> (label * A) := 
  fun '(l,w) => (R l, w).


Definition M (A : Type) := (label * Result A) -> Prop.  

Definition BOTTOM {A} : P (label * Result A) := ⌈ (Top, Bottom) ⌉.

Definition WRONG {A} : P (label * Result A) := ⌈ (Top, Wrong) ⌉.

Definition FAIL {A} : P (label * Result A) := ∅.

Definition UNIT {A} (x : A) : P (label * Result A) := ⌈ (Top, Value x) ⌉.

(* { (L𝑙,𝑤) | (𝑙,𝑤) ∈ 𝑠1 } ∪ {(R𝑙,𝑤) | (𝑙,𝑤) ∈ 𝑠2 } *)
Definition UNION {A} (s1 s2 : P (label * Result A)) := 
  fmap left s1 ∪ fmap right s2.


(* 
If the second expression fails, then the whole expression fails, no matter 
what the first expression is. 
If the first expression is fail, loop or error, that is the result of the 
entire expression.
If the first expression succeeds, then the result is the second expression.

r ; fail    --> fail
r ; fail    --> fail
fail  ; r   --> fail
loop  ; r   --> loop
error ; r   --> error
value ; r   --> r 

 *)
  (* {(𝑙1 ⋈ 𝑙2,𝑤2) | (𝑙1,𝑤1) ∈ 𝑠1, (𝑙2,𝑤2) ∈ 𝑠2} *)
Definition SEQ {A} s1 s2 :  P (label * Result A)%type :=
  '(l1, r1) <- s1 ;;
  '(l2, r2) <- s2 ;;
  ⌈ (l1 ⋈ l2, R.strict r1 r2) ⌉
(* add this to make loop ; fail --> loop *)
    ∪
  (fun '(l1, r1) => match (l1, r1) with 
                | (l ⋈ Top, Bottom) => (l, Bottom) ∈ s1
                | _ => False
                end).

(* Find the result associated with the *smallest* entry in the set. *)
Definition ONE {A} (s : P (label * Result A)) : (label * Result A) -> Prop := 
  fun '(l,w) => 
    match l , w with 
    | Top , w => exists k, ((k,w) ∈ s) 
                /\ (forall k' w', (k', w') ∈ s -> (k <=? k' = true))
    | _ , _ => False
    end.

(* Merge togther the result of the function f applied to every w in W.

   - Ensure that we only have one nonfailing result per label. If a label has
     a different mapping (for any picked value), then do not include it in the
     set. (TODO: make it WRONG instead?)  *)
                                          
Definition EXISTS {A} (f : A -> M A) : M A := 
  fun '(l,r) => (exists w, (l,r1) ∈ f w) 
           /\ ((forall w' r2, (l, r2) ∈ f w' -> (r1 = r2 -> r = r1))      (* all agree *)
            \/ (exists w' r2, (l, r2) ∈ f w' -> (r1 <> r2 /\ r = WRONG)))  (* some discrepancy *)
              (* make ∃x.x fail *)
.


(* Could value w1 be represented by the entry? *)
Definition keep (w1 : W) (entry : label * Result W) : bool := 
  match entry with
  | (l, Some w2) => W.eqb w1 w2
  | (l, None) => true
  end.
(*  Intersection fails if its argument fails
    and diverges if its argument diverges *)
  (* { (l2, 𝑤2) | (𝑙2,𝑤2) ∈ 𝑠2, 𝑤1 = 𝑤2} *)
Definition INTER (w : W) : M W -> M W := Sets.filter (keep w).


(* The 'elements' proposition asserts that a set s is finite and contains the ordered 
   list of entries (i.e. labeled results). *)
Definition ALL : M W -> M W := 
  fun s => fun '(l,r) => 
    match l , r with 
    | Top , Some (TupleV ws) => 
        exists entries , elements (fun x y => x <? y = true) s entries 
               /\ (List.map snd entries = List.map Some ws) 
                                          (* all of the results must succeed *)
    | Top , None => exists l, (l , None) ∈ s    (* if any of the results diverge, ALL diverges *)
    | _   , _ => False                         (* if there are no results, ALL fails *)
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


Section Validity.

Import SetNotations.

(* We want to ensure that all interpretations are "valid". In other words, 
   the sets are all partial functions. *)

Definition Valid {A} : M A -> Prop := partial_function.

Lemma partial_function_BOTTOM {A} : partial_function (@BOTTOM A).
  intros k v1 v2 in1 in2. inversion in1. inversion in2. done.
Qed.

Lemma partial_function_UNIT {A} (x:A) : partial_function (UNIT x).
  intros k v1 v2 in1 in2. inversion in1. inversion in2. done.
Qed.

Lemma partial_function_FAIL {A} : partial_function (@FAIL A).
  intros k v1 v2 in1 in2. inversion in1. 
Qed.

Lemma partial_function_WRONG {A} : partial_function (@WRONG A).
  intros k v1 v2 in1 in2. inversion in1. 
Qed.

Lemma partial_function_UNION {A} (s1 s2 : M A) : partial_function s1 -> partial_function s2 -> partial_function (UNION s1 s2).
intros pf1 pf2 k v1 v2 in1 in2.
unfold UNION in *. unfold partial_function in *.
inversion in1 as [? h1|? h1]; inversion in2 as [? h2|? h2]; subst; clear in1 in2.
cbv in h1,h2.
all: move: h1 => [[l1 r1] [h1 h1']]; inversion h1'; subst; clear h1'.
all: move: h2 => [[l2 r2] [h2 h2']]; inversion h2'; subst; clear h2'.
eauto.
eauto.
Qed.

Lemma partial_function_INTER  
  (v : W)(s2 : M W) : partial_function s2 -> partial_function (INTER v s2).
Proof.
  intros pf k v1 v2 in1 in2.
  unfold INTER in *. unfold partial_function in *.
  unfold filter in *.
  move: in1 => [k1 in1].
  move: in2 => [k2 in2].
  eauto.
Qed.

Lemma partial_function_SEQ {A} (s1 s2 : M A) : partial_function s1 -> partial_function s2 -> partial_function (SEQ s1 s2).
Proof.
  move=> pf1 pf2 k v1 v2 in1 in2.
  unfold partial_function in *.
  cbn in in1.
  move: in1 => [[l1 r1] [h1 [[l1' r1'] [h1' h]]]]. inversion h. subst. clear h.
  move: in2 => [[l2 r2] [h2 [[l2' r2'] [h2' h]]]]. inversion h. subst. clear h.
  move: (pf1 _ _ _ h1 h2) => E1.
  move: (pf2 _ _ _ h1' h2') => E2.
  subst.
  auto.
Qed.

(* The IH doesn't help here because it only talks about individual 
   sets f w. But we need to reason about all f w. *)
Lemma partial_function_EXISTS {A} (f : A -> M A) : 
  (forall w, partial_function (f w)) -> partial_function (EXISTS f).
Proof.
intros ih k v1 v2 in1 in2.
move: in1 => [[w1 in1] p1].
move: in2 => [[w2 in2] p2].
eapply p1; eauto.    
Qed.

Lemma partial_function_ONE (e : M W) : partial_function e -> partial_function (ONE e).
Proof.
  intros pf k v1 v2 in1 in2.
  unfold ONE, partial_function in *.
  destruct k; try done.
  move: in1 => [k1 [h1 h1']].
  move: in2 => [k2 [h2 h2']].
  have LE1: (Label.leb k1 k2 = true); eauto.
  have LE2: (Label.leb k2 k1 = true); eauto.
  move: (Label.leb_antisymmetry _ _ LE1 LE2) => eq. subst.
  eauto.
Qed.

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
  destruct w; try done.
  destruct w0; try done.
  move: in1 => [w1 [in1 p1]].
  move: in2 => [w2 [in2 p2]].
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
Qed.

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
    eapply partial_function_EXISTS. intro w; eauto.
  + repeat rewrite eval_Or.
    eapply partial_function_UNION; eauto.
  + simpl.
    eapply partial_function_FAIL; eauto.
  + rewrite eval_One.
    eapply partial_function_ONE; eauto.
  + rewrite eval_All.
    eapply partial_function_ALL; eauto.
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

(* one interpretation approximates another when

   for each entry in s1: 
      1. if it has succeeded, 
          a. it continues to succeed in s2 with the same label
      2. if it has bottomed, 
          a. it could stay bottom, with a potentially bigger label
          b. it could succeed, with a potentially bigger label
          c. it could fail and won't be in s2
          (( this condition is trivial ))
      3. if it fails (i.e. is not in the first set)
          - it should continue to fail and all bigger labels shouldn't be in s2
         we can express this using the contrapositive:
            everything in s2 should be approximated by something in s1
         

We need (1) to know that successful values do not change with more fuel.
We need (3) for the case of ONE
  We need to know that there are no new "smaller" elements when we add more fuel.


 *)


Definition entry_approx {A}(e1 e2 : label * Result A) : Prop := 
  match e1 , e2 with 
  | (l1 , Some v1), (l2, Some v2) => Label.approx l1 l2 = true /\ v1 = v2
  | (l1 , None), (l2 , _) => Label.approx l1 l2 = true
  | _ , _ => False
  end.

Lemma entry_approx_label {A:Type} {l1 r1 l2 r2}: 
  entry_approx (A:=A) (l1, r1) (l2, r2) -> Label.approx l1 l2 = true.
destruct r1; destruct r2; simpl; eauto.
tauto.
Qed.

Definition approx {A} (s1 s2 : M A) : Prop := 
  (forall l1 v, (l1, Some v) ∈ s1 -> ((l1, Some v) ∈ s2)) /\
  (forall e2, e2 ∈ s2 -> exists e1, (e1 ∈ s1) /\ entry_approx e1 e2).


(*
  (forall l1,   ((l1, None) ∈ s1 -> exists l2, ((exists v, (l2, Some v) ∈ s2) \/ (l2, None) ∈ s2)
                                    /\ Label.approx l1 l2 = true)) /\  (* 2bc *)
  (forall l2 v, (l2 , Some v) ∈ s2 -> (exists l1, ((l1 ,Some v) ∈ s1) /\ Label.approx l1 l2 = true) \/  (* 1a *)
                                 exists l1, ((l1, None) ∈ s1)   /\ Label.approx l1 l2 = true) /\  (* 2c *)
  (forall l2, (l2 , None) ∈ s2 -> exists l1, Label.approx l1 l2 = true /\ ((l1, None) ∈ s1)).          (* 2b *)
*)

(*
Definition approx {A} (s1 s2 : M A) : Prop := 
  (forall l1 v, ((l1, Some v) ∈ s1 -> exists l2, ((l2, Some v) ∈ s2) /\ Label.approx l1 l2 = true)) /\  (* 1a *)
  (forall l1,   ((l1, None) ∈ s1 -> exists l2, ((exists v, (l2, Some v) ∈ s2) \/ (l2, None) ∈ s2)
                                    /\ Label.approx l1 l2 = true)) /\  (* 2bc *)
  (forall l2 v, (l2 , Some v) ∈ s2 -> (exists l1, ((l1 ,Some v) ∈ s1) /\ Label.approx l1 l2 = true) \/  (* 1a *)
                                 exists l1, ((l1, None) ∈ s1)   /\ Label.approx l1 l2 = true) /\  (* 2c *)
  (forall l2, (l2 , None) ∈ s2 -> exists l1, Label.approx l1 l2 = true /\ ((l1, None) ∈ s1)).          (* 2b *)
*)

Lemma approx_refl {A} : forall (s : M A), approx s s.
Proof. intros s. unfold approx. repeat split. 
       eauto using Label.approx_refl. 
       intros e2 In2.
       exists e2. split; auto. destruct e2. destruct o; simpl;        eauto using Label.approx_refl.        
Qed.
Lemma approx_trans {A} : forall (s1 s2 s3 : M A), approx s1 s2 -> approx s2 s3 -> approx s1 s3.
Proof. 
Admitted.
(*
intros s1 s2 s3 [a11 [a12 a13]] [a21 [a22 a23]]. 
       repeat split. 
       - intros l1 v inV. admit.
       - intros l v inV. 
Admitted. 
         destruct (a22 l v inV) as [|[l2 [h3 h4]]].
         destruct (a12 l v H) as [|[l1 [h1 h2]]]. 
         left; auto.
         right. exists l1. split; auto.
         right.
         destruct (a13 l2 h4) as [l1 [h5 h6]].
         exists l1. split. eapply Label.approx_trans; eauto. auto.
       - intros l3 l3N.
         destruct (a23 l3 l3N) as [l2 [h1 l2N]].
         destruct (a13 l2 l2N) as [l1 [h2 l1N]].
         exists l1. split. eapply Label.approx_trans; eauto. auto.
Qed. *)


Ltac rewrite_approx := 
  match goal with 
  [ H2 : Label.approx ?l2 ?l2' = true |- _ ] => rewrite -> H2 ; clear H2
  end.


Lemma SEQ_monotone {A} {s1 s2 s1' s2' : M A} : 
  approx s1 s1' -> approx s2 s2' -> approx (SEQ s1 s2) (SEQ s1' s2').
Proof.
  intros [A1 A1'] [A2 A2'].
  unfold SEQ. unfold approx in *.
  split.
  + intros l v h.
    move: h => [[l0 v0] [h1 h2]].
    move: h2 => [[l1 v1] [h2 h3]].
    destruct v0 as [v0|].
  - simpl in h3. inversion h3. subst. clear h3.
    move: (A1 _ _ h1) => h1'.
    move: (A2 _ _ h2) => h2'.
    eexists. split; eauto.
    eexists. split; eauto.
    econstructor; eauto.
  - simpl in h3. inversion h3.
  + intros e h.
    move: h => [[l0' v0'] [h1 h2]].
    move: h2 => [[l1' v1'] [h2 h3]].
    inversion h3. subst. clear h3.
    move: (A1' _ h1) => [e1' [h1' h1'']].
    move: (A2' _ h2) => [e2' [h2' h2'']].
    destruct e1' as [l0 v0]. 
    destruct e2' as [l1 v1].
    destruct v1. destruct v1'.
    all: destruct v0. 
    all: destruct v0'; try done.
    all: simpl in h1''; try done.
    destruct h2''. subst.
    destruct h1''. subst.
    ++ eexists. split. 
       eexists. split; eauto. simpl.
       eexists. split; eauto. simpl.
       eauto.
       simpl. rewrite H0. rewrite H. auto.
    ++ destruct h2''. subst. 
      eexists. split.
       eexists. split; eauto.
       eexists. split; eauto. simpl. auto.
       simpl. rewrite h1''. 
       rewrite H. auto.
    ++ destruct h2''. subst. eexists. split.
       eexists. split; eauto. simpl.
       eexists. split; eauto. simpl. eauto.
       simpl. rewrite h1''. rewrite H. auto.
    ++ simpl in h2''. subst. destruct h1''. subst.
       eexists. split.
       eexists. split; eauto. simpl.
       eexists. split; eauto. simpl.
       eauto.
       simpl. rewrite H. rewrite h2''. auto.
    ++ simpl in h2''.       
       eexists. split.
       eexists. split; eauto. simpl.
       eexists. split; eauto. simpl.
       eauto.
       simpl. rewrite h1''. rewrite h2''. auto.
    ++ simpl in h2''.
       eexists. split.
       eexists. split; eauto. simpl.
       eexists. split; eauto. simpl.
       eauto.
       simpl. rewrite h1''. rewrite h2''. auto.
Qed.

(*
  repeat split.
  - (* some s => some s' *)
    intros l v lIn.
    destruct l; cbv in lIn; try done. 
    move: lIn => [w1 ?]. go. 
    unfold approx in *. go. 
    specialize (H3 _ _ H2). move: H3 => [l2' h2].
    specialize (H4 _ _ H1). move: H4 => [l1' h1]. clear H0 H5 H7 H.
    go.
    exists (l1' ⋈ l2'). split.
    eexists.
    repeat split; eauto.
    simpl. rewrite H0. rewrite H4. auto.
  - (* some s' => some s \/ none *)
    intros l2 v lIn. 
    destruct l2; try done. cbn in lIn.
    move: lIn => [x lIn]. go.
    unfold approx in *. go.
    destruct (H0 _ _ H2) as [h2|h2];
    destruct (H _ _ H1) as [h1|h1].
    all: move: h1 => [l1' h1]; move: h2 => [l2' h2]; go.
    + left. cbn.
      exists (l1' ⋈ l2').
      repeat split.
      eexists. split; eauto.
      rewrite H8. rewrite H10. done.
    + right.
      exists (l1' ⋈ l2'). 
      cbn.
      repeat split. 
      right.
      eexists. repeat split; eauto.
      rewrite H8. rewrite H10. done.
    + right.
      exists (l1' ⋈ l2').  
      cbn.
      repeat split.  
      left.
      eexists. repeat split; eauto.
      simpl. rewrite H8. rewrite H10. done.
    + right.
      exists (l1' ⋈ l2').  
      cbn.
      repeat split. 
      right.
      eexists. repeat split; eauto.
      rewrite H8. rewrite H10. done.
  - intros l2 l2I. 
    destruct l2; try done.
    cbn in l2I.
    destruct l2I as [h2|h2].
    all: try (move: h2 => [w2 h2]; go).
    all: unfold approx in *; go.
    all: try (destruct w2).
    all: try (destruct (H7 _ H1) as [l1' h7]).
    all: try (destruct (H _ _ H1) as [h1|h1]).
    all: try (move: h1 => [l1' h1]).
    all: try (destruct (H5 _ H2) as [l2' h5]).
    all: try (destruct (H0 _ _ H2) as [h2|h2]).
    all: try (move: h2 => [l2' h2]).
    all: go.
    all: exists (l1' ⋈ l2'); repeat split; simpl; cbn.
    all: try rewrite H6; try rewrite H10; try reflexivity.
    all: try rewrite H8; try rewrite H9; try reflexivity.
    all: try solve [left; eauto].
    all: try solve [right; eauto].
Qed. *)

(*
Ltac ind1 l1' h2 := 
    match goal with 
      | [ H1 : (?l1 , Some ?v) ∈ ?s1 ,
          H2 : forall l v, (l, Some v) ∈ ?s1 -> _ |- _ ] => 
          move: (H2 _ _ H1) => [l1' h1] ; clear H2
    end.
*)


Lemma ONE_monotone {s2 s2' : M W} : 
  approx s2 s2' -> approx (ONE s2) (ONE s2').
Proof.
  intros [A1 A2].
  unfold ONE , approx in *.
  split.
  - intros l1 v1 h. destruct l1; try done. 
    move: h => [k [h1 h2]].
    move: (A1 _ _ h1) => h3.
    exists k. split; eauto.
    intros k' w' In'. 
    move: (A2 _ In') => [[k0 v0] [h4 h5]].
    move: (h2 _ _ h4).
    move: (entry_approx_label h5).
    clear.
    move: k0 k'.
    induction k.
    all: move=> k0 k' h1 h2.
    all: destruct k0 eqn:E0; simpl in h2; try done.
    all: destruct k' eqn:E'; simpl in h1; try done.
    all: simpl.
Abort.
(*  - intros [l2 v2][h2 h3].
    move: (A2 _ h3) => [[l1 v1] [h1 A3]].
    exists (l1, v1). split; eauto.
    split; auto.
    destruct v1; destruct v2; simpl in *; auto.
    move:A3 => [h4 ->]. auto.
Qed.
*)

      
Lemma INTER_monotone {w}{s2 s2' : M W} : 
  approx s2 s2' -> approx (INTER w s2) (INTER w s2').
Proof.
  intros [A1 A2].
  unfold INTER , approx, filter, In in *. 
  split.
  - intros l1 v1 h.
    move: h => [h1 h2].
    split. eauto. eauto.
  - intros [l2 v2][h2 h3].
    move: (A2 _ h3) => [[l1 v1] [h1 A3]].
    exists (l1, v1). split; eauto.
    split; auto.
    destruct v1; destruct v2; simpl in *; auto.
    move:A3 => [h4 ->]. auto.
Qed.

(*
  repeat split.
  all: intros.
  + destruct l1; cbn in *; try done.
    go. 
    ind1 l1' h1.
    match goal with 
      | [ H1 : (?l1 , Some ?v) ∈ s2 ,
          H2 : forall l v, (l, Some v) ∈ s2 -> _ |- _ ] => 
          move: (H2 _ _ H1) => [l2' h2] ; clear H2
    end.
    exists (l1' ⋈ l2').
    go.
    repeat split; eauto.
    simpl.
    rewrite_approx.
    rewrite_approx.
    reflexivity.
  + (* some s' => some s \/ none *)
    destruct l2; cbn in *; try done.
    go.
    match goal with 
      | [ H1 : (?l1 , Some ?v) ∈ s1' ,
          H2 : forall l v, (l, Some v) ∈ s1' -> _ |- _ ] => 
          specialize (H2 _ _ H1); destruct H2 as [[l1' h1]|h1] end.
    match goal with 
      | [ H1 : (?l1 , Some ?v) ∈ s2' ,
          H2 : forall l v, (l, Some v) ∈ s2' -> _ |- _ ] => 
          specialize (H2 _ _ H1); destruct H2 as [[l2' h2]|h2] end.
    all: go.
    ++ left. 
       exists (l1' ⋈ l2'). 
       repeat split; eauto.
       rewrite_approx.
       rewrite_approx.
       auto.
    ++ 
      match goal with 
      | [ H1 : (?l1 , Some ?v) ∈ s2' ,
          H2 : forall l v, (l, Some v) ∈ s2' -> _ |- _ ] => 
          specialize (H2 _ _ H1) end.

Qed. *)

Lemma EXISTS_monotone {A} {f f' : A -> M A} :
  (forall w, approx (f w) (f' w)) ->
  approx (EXISTS f) (EXISTS f').
Proof.
  intros hA.
  unfold EXISTS, approx in *.
  split.
  - intros l v h0.
    move: h0 => [[w h0] h1].
    move: (hA w) => [hA1 hA2].
    split.
    exists w. eauto.
    intros w' r' wIn'.
    

    eapply h1. 
Admitted.


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
    UNIT x = mem ([(Top, Some x)]).
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

End FiniteSemantics.

Create HintDb mem.
Hint Rewrite @UNIT_mem @UNION_mem @INTER_mem @SEQ_mem : mem.


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

(*
Lemma f_equal_mem {A}{l1 l2 : list A}: l1 = l2 -> mem l1 ≃ mem l2.
Admitted. *)
Lemma P_In {A}{f : P A}{x} : (f x) -> x ∈ f. cbv. auto. Qed.


(* 3 = 3 || 4 = 4 || 5 = 5 *)
Definition exb : Exp 0 := Or (Int 3 ≡ Int 3) (Or (Int 4 ≡ Int 4) (Int 5 ≡ Int 5)).

Example exb_example : evalExp 10 exb Vector.nil = 
  mem ((L Top, Some (IntV 3)) :: (R (L Top), Some (IntV 4)) :: (R (R Top),Some (IntV 5)) :: nil).
unfold exb. autorewrite with evalExp.
unfold evalVal.
autorewrite with mem.
f_equal.
Qed.

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

(* ∃ x. x = (1 || 2) ;; x *)
Definition ex_two : Exp 0 := bind1 (Or (Int 1) (Int 2)) x0.

Lemma W_eqb_eq (w1 w2: W) : W.eqb w1 w2 = true <-> w1 = w2.
Admitted.

Lemma ev_ex_two1 : evalExp 10 ex_two Vector.nil =
                     mem ((L Top ⋈ Top, Some (IntV 1)) :: (R Top ⋈ Top, Some (IntV 2)) :: nil).
Proof.
unfold ex_two,bind1. asimpl.
autorewrite with evalExp.
unfold evalVal, lookupEnv, Vector.nth, var_zero.
eapply In_extensionality.
intros [l r].
rewrite In_mem.
repeat rewrite UNIT_mem.
rewrite UNION_mem.
Opaque INTER SEQ mem. cbn.
Transparent INTER SEQ mem.
split.
+ move=>[[w wIn] _].
  cbn in wIn.
  move: wIn => [[l0 r0][ h1 [[l1 r1] [h2 h3]]]].
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
Admitted.
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
  INTER w (mem ((L l1, Some v1) :: (R l2, Some v2) :: nil)) = s -> 
  ((w = v1 /\ s = mem ((L l1, Some v1) :: nil)) \/
   (w = v2 /\ s = mem ((R l2, Some v2) :: nil))).
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
                      Some (TupleV (cons (IntV 1) (cons (IntV 3) nil))))
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
  - exists (IntV 1). 
    autorewrite with mem. simpl.
    exists (L Top, Some (IntV 1)). split; eauto.
    simpl.
    exists (L Top ⋈ Top, Some (TupleV (IntV 1 :: IntV 3 :: nil))). 
    split. 2: econstructor; eauto.
    split.
    -- cbn.
       exists (IntV 3). 
       exists (L Top, Some (IntV 3)). 
       rewrite INTER_mem. rewrite In_mem.
       simpl. split; eauto.
       exists (Top,  Some (TupleV (IntV 1 :: IntV 3 :: nil))). 
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
  exists l , (l, Some w) ∈ m.



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
       have h1: (List.In (L (Top ⋈ Top), Some (IntV 3)) xs). admit.
       have h2: (List.In (R (Top ⋈ Top), Some (IntV 4)) xs). admit.
       admit.
(*       destruct xs as [|x1 xs].
       + move: (mem_nil_contra H1 (L (Top ⋈ Top), Some (IntV 3))) => h1. 
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
  exists ( (L (Top ⋈ Top), Some (IntV 3)) :: (R (Top ⋈ Top), Some (IntV 4)) :: nil )%list.
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
Lemma evex2 : exists n, exists l, (l, Some (IntV 2)) ∈ evalExp n Vector.nil ex2.
Proof.
  exists 20.
  eexists. unfold ex2. 
  rewrite -> eval_Exists.
  unfold EXISTS.
  remember (LamV Vector.nil (Ret (Int 2))) as w'.
  remember ((App (var_Val var_zero) (Int 1) ≡ Int 2); App (var_Val var_zero) (Int 1)) as ebody.
  have VE: forall w', Valid (evalExp 19 (Vector.cons w' Vector.nil) ebody). admit.
  have EE: (((Top ⋈ Top) ⋈ Top), Some (IntV 2)) ∈ (evalExp 19 (Vector.cons w' Vector.nil) ebody).
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
       - thus v' = Some (IntV 2)
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
    | Some a1 , Some a2 => eqv a1 a2 
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

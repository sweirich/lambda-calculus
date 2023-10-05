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

(* Sets of Values:   P Value === Value -> Prop *)

(* Some lists are finite representations of sets. Others 
   are sequences of results. Use a newtype
   to distingiush. *)

Inductive fset (A:Type) := FSet : (list A) -> fset A.
Arguments FSet {_}.
Definition In_fset {A: Type} (x: A) : fset A -> Prop := fun '(FSet X) => List.In x X.
Definition singleton_fset {A:Type} (x : A) : fset A := FSet (x :: nil).
Definition union_fset {A:Type} '(FSet x) '(FSet y) : fset A := FSet (x ++ y).
Definition nonempty_fset {A:Type} : fset A -> Prop := fun '(FSet xs) => xs <> nil.
Definition Forall_fset {A:Type} (f : A -> Prop) : (fset A) -> Prop := 
  fun '(FSet xs) => List.Forall f xs.

Definition mem {A: Type} : fset A -> P A := fun xs => fun x => In_fset x xs.

Section FSetTheory.

Context {A : Type} {E : fset A}.

Lemma mem_one_inv : forall (h v : A),  h ∈ mem (singleton_fset v) -> h = v.
Proof. intros. cbn in H. destruct H; try done. Qed. 

Lemma nonnil_nonempty_mem : nonempty_fset E -> nonemptyT (mem E).
Proof. intros. destruct E; destruct l; cbv. done.
       econstructor. econstructor. eauto.
Qed.

Lemma In_Sub {x:A}{D : P A} : x ∈ D <-> mem (singleton_fset x) ⊆ D.
Proof. split. intros h y yIn. inversion yIn. subst; auto. inversion H. 
       intros h. cbv in h. specialize (h x). tauto.
Qed.


Lemma union_mem {E1 E2 : fset A} : mem (union_fset E1 E2) = (mem E1 ∪ mem E2).
Proof. unfold mem, union_fset. destruct E1 as [E1], E2 as [E2].
       eapply Extensionality_Ensembles.
       split.
       + intros x.
         induction E1. 
         ++ simpl. intro h. right. auto.
         ++ simpl. intro h. inversion h.
            left. unfold In. econstructor; eauto.
            apply IHE1 in H.
            inversion H. subst.
            left. unfold In. eapply in_cons. auto.
            subst. right. auto.
       + intros x.
         induction E1. 
         ++ intro h. inversion h. subst. done. subst. auto.
         ++ simpl. intro h. inversion h; subst.
            destruct H.  left. auto.
            lapply IHE1. intro h2. right. eauto.
            left. eauto. right. apply in_or_app. right. auto.
Qed.


Lemma singleton_mem : forall v : A,  ⌈ v ⌉ ⊆ mem (singleton_fset v).
Proof. intro v. econstructor. inversion H. done. Qed.

Lemma mem_singleton : forall v : A, mem (singleton_fset v) ⊆ ⌈ v ⌉.
Proof. intro v. cbv. intros. inversion H. subst. econstructor; eauto. done. Qed.

Lemma mem_singleton_eq {x:A} : mem (singleton_fset x) ≃ ⌈ x ⌉.
Proof. split; eauto using mem_singleton, singleton_mem. Qed.


Lemma Forall_mem {Pr} : Forall_fset Pr E -> Sets.Forall Pr (mem E).
Proof.
  destruct E as [V].
  induction V; intro h; intros y yIn. 
  inversion yIn. 
  inversion h. subst.
  inversion yIn. subst. auto. eapply IHV; eauto.
Qed.

Lemma Forall_sub_mem : forall  X Pr, 
    mem E ⊆ X -> 
    Sets.Forall Pr X ->
    Forall_fset Pr E.
Proof.
  destruct E as [D].
  induction D; intros X Pr SUB F.
  eauto.
  econstructor; eauto. simpl.
  unfold mem in SUB.
  econstructor. eapply F. eapply SUB. cbn. left; auto.
  eapply IHD with (X:=X); auto. intros x xIn. 
  unfold mem in xIn. eapply SUB; eauto. 
  cbn. right. eapply xIn.
Qed.

Lemma mem_In : forall (x:A), x ∈ mem E -> In_fset x E.
Proof. intros. destruct E as [l]. induction l. cbv in H. done.
       destruct H. subst. econstructor. auto. 
       simpl. right. eauto. Qed.

End FSetTheory.

#[export] Hint Resolve mem_one_inv nonnil_nonempty_mem In_Sub : core.
#[export] Hint Resolve singleton_mem mem_singleton : core. 

(* ------------------------------------------------------- *)

(* `P (Comp (P A))` is *almost* a Monad *)

Definition RET {A} (x : P A) : P (Comp (fset A)) :=
  fun z => match z with 
          | c_multi (V :: nil) => (mem V ⊆ x) /\ nonempty_fset V
          |  _ => False
        end.

(* V must be nonempty because RET is strict. If V is empty then the 
   set should be empty. *)

Definition BIND {A B} (S : P (Comp (fset A))) (K : P A -> P (Comp B)) (t : Comp B) : Prop :=
  exists (u : Comp (fset A)), exists (k : fset A -> Comp B), 
    S u /\ t = bind u k /\ forall a, Comp_In a u -> K (mem a) (k a).

(* ----------------------------------------------------------- *)

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table: the list Value in the result Comp should be fset,
     but this causes trouble with Coq's termination checker *)
  | v_map : fset Value -> Comp (fset Value) -> Value

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

(* ------------ Consistent ------------------ *)

Class Consistency (A : Type) : Type := 
  { Consistent : A -> A -> Prop ;
    Inconsistent : A -> A -> Prop ;
  }.

Class ConsistencyTheory (A : Type) `{Consistency A} := 
  {  exclusive : forall x y, Consistent x y -> Inconsistent x y -> False ;
     decidable : forall x y, {Consistent x y} + {Inconsistent x y}
  }.


Definition Exclusive {A} (f g : A -> A -> Prop) :=  forall x y, f x y -> g x y -> False .
Definition Decidable {A} (f g : A -> A -> Prop) :=  forall x y, {f x y} + {g x y}.

Section List.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Definition Consistent_list := List.Forall2 f.
Definition Inconsistent_list := fun XS YS => 
  length XS <> length YS \/ List.Exists2 g XS YS.

Lemma exclusive_list :
  Exclusive f g -> 
  Exclusive Consistent_list Inconsistent_list.
Proof.
  intros efg. intros x y FF. 
  induction FF; intros EG; inversion EG; eauto.
  - inversion H.
  - move: (Forall2_length _ _ FF) => eq. 
    simpl in H0. rewrite eq in H0. done.
  - inversion H0; subst. eauto.
    eapply IHFF. right. eauto.
Qed.

Lemma exclusive_list2: forall l, 
  List.Forall (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, Consistent_list l YS -> Inconsistent_list l YS -> False.
Proof.
  induction l; intros h YS h1 h2.
  - inversion h1. subst. inversion h2. done.
    inversion H.
  - inversion h1. subst. inversion h. subst.
    specialize (IHl H4 l' H3).
    destruct h2. unfold Consistent_list in h1. 
    apply Forall2_length in h1. done.
    inversion H; subst; eauto.
    eapply IHl. right. auto.
Qed.    

Lemma decidable_list : 
  Decidable f g ->
  Decidable Consistent_list Inconsistent_list.
Proof.
  intros dfg. intros x.
  induction x; intros y; destruct y.
  - left; eauto. econstructor.
  - right; eauto. left. done.
  - right; eauto. left. done.
  - destruct (IHx y). destruct (dfg a a0).
    left. econstructor; eauto.
    right. right. econstructor; eauto.
    right. destruct i. left. eauto. right. eauto.
Qed.


End List.

#[export] Instance Consistency_list { A : Type } `{ Consistency A } : Consistency (list A) := 
  { Consistent := Consistent_list (f := Consistent) ;
    Inconsistent := Inconsistent_list (g := Inconsistent) ;
  }.


#[export] Instance Consistency_list_theory { A : Type } `{ ConsistencyTheory A } : ConsistencyTheory (list A) := 
  { exclusive := exclusive_list (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_list (f := Consistent)(g := Inconsistent) decidable ;
  }.

Section FSet.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Definition Consistent_fset := fun '(FSet XS) '(FSet YS) => List.Forall2_any f XS YS.
Definition Inconsistent_fset := fun '(FSet XS) '(FSet YS) => List.Exists2_any g XS YS.


Lemma exclusive_fset :
  Exclusive f g ->
  Exclusive Consistent_fset Inconsistent_fset.
Proof.
  intros efg. intros x. destruct x as [x].
  induction x; intros y FF EG; destruct y as [y]; destruct y; 
    unfold Consistent_fset, List.Forall2_any in FF;
    unfold Inconsistent_fset, List.Exists2_any in EG.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h1.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h1.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h2.
  - destruct EG as [x0 [y0 [h1 [h2 gg]]]]. 
    specialize (FF x0 y0 h1 h2).
    eapply efg; eauto.
Qed.

Lemma decidable_fset :
  Decidable f g ->
  Decidable Consistent_fset Inconsistent_fset.
Proof.
  intros dfg. intros x. destruct x as [x].
  induction x; intros y; destruct y as [y].
     unfold Consistent_fset, List.Forall2_any;
     unfold Inconsistent_fset, List.Exists2_any.
  - left. done.
  - destruct (IHx (FSet y)). 
    + simpl in c. simpl.
      induction y. unfold List.Forall2_any in c.
      left. intros x0 y0 h1 h2. inversion h2. 
      have CE: (List.Forall2_any f x y). { intros x0 y0 h1 h2. eapply c; eauto. simpl. eauto. }
      specialize (IHy CE). destruct IHy.
      ++ destruct (dfg a a0).
         left.
         { intros x0 y0 i1 i2.
           destruct i1; destruct i2; subst. 
           -- auto.
           -- apply f0; eauto. simpl; auto.
           -- apply c; eauto. simpl; auto.
           -- apply CE; eauto.
         }
         right.
         exists a. exists a0. simpl. split; auto.
      ++ right. destruct e as [x0 [y0 [h1 [h2 h3]]]].
         exists x0. exists y0. simpl. eauto.
    + right. destruct i as [x0 [y0 [i1 [i2 h]]]]. 
      exists x0. exists y0. 
      repeat split; try right; auto. 
Qed.

Lemma exclusive_fset2: forall l, 
  Forall_fset (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, Consistent_fset l YS -> Inconsistent_fset l YS -> False.
Proof.
  intro l. destruct l. 
  move=> h YS. destruct YS as [l']. simpl in *.
  move: h l'.
  induction l; intros h l' h1 h2;  unfold List.Forall2_any in h1; destruct h2 as [x0 [y0 [I0 [I1 IC]]]]. 
  - inversion I0.
  - inversion h. subst. 
    specialize (IHl H2).
    rewrite Forall_forall in H2.
    destruct I0; subst.
    -- specialize (h1 x0 y0 ltac:(left; auto) I1).
       eauto.
    -- eapply (IHl l').
       intros x1 y1 I3 I4. eapply  h1. right; eauto. eauto.
       exists x0. exists y0. repeat split; eauto.
Qed. 

End FSet.

#[export] Instance Consistency_fset { A : Type}  `{ Consistency A } : Consistency (fset A) := 
  { Consistent := Consistent_fset (f := Consistent) ;
    Inconsistent := Inconsistent_fset (g := Inconsistent) ;
  }.

#[export] Instance ConsistencyTheory_fset { A : Type}  `{ ConsistencyTheory A } : ConsistencyTheory (fset A) := 
  { exclusive := exclusive_fset (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_fset (f := Consistent)(g := Inconsistent) decidable ;
  }.


(*
Definition ConsistentPointwiseList {A} (f : A -> A -> Prop) (XS YS : seq A) :=  
  List.Forall2 f XS YS.
Definition InconsistentPointwiseList  {A} (g : A -> A -> Prop) (XS YS : seq A) := 
  length XS <> length YS \/ List.Exists2 g XS YS.
*)

(* ------------------------------------------------- *)



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

Lemma exclusive_Comp : 
  Exclusive f g ->
  Exclusive ConsistentComp InconsistentComp.
Proof.
  intros efg x y CC IC.
  induction CC; inversion IC.
  eapply exclusive_list; eauto.
Qed.


Lemma exclusive_Comp2: forall l, 
  Comp.Forall (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, ConsistentComp l YS -> InconsistentComp l YS -> False.
Proof.
  destruct l. intros.
Admitted.

Lemma decidable_Comp : 
  Decidable f g ->
  Decidable ConsistentComp InconsistentComp.
Proof.
  intros dfg x y.
  destruct x eqn:EX; destruct y eqn:EY.
  - left; econstructor.
  - right; econstructor.
  - right; econstructor.
  - destruct (decidable_list dfg l l0).
    left; econstructor; eauto.
    right; econstructor; eauto.
Qed.


End Computations.

#[export] Instance Consistency_Comp {A:Type} `{Consistency A} : Consistency (Comp A) := 
  { Consistent := ConsistentComp (f:=Consistent) ; Inconsistent := InconsistentComp (g := Inconsistent) }.


#[export] Instance ConsistencyTheory_Comp { A : Type}  `{ ConsistencyTheory A } : ConsistencyTheory (Comp A) := 
  { exclusive := exclusive_Comp (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_Comp (f := Consistent)(g := Inconsistent) decidable ;
  }.


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

Fixpoint Value_ind' (P : Value -> Prop)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : fset Value) (c : Comp (fset Value)), 
           Forall_fset P l -> Comp.Forall (Forall_fset P) c -> P (v_map l c)) 
       (f : P v_fun)
       (l : (forall l : list Value, List.Forall P l -> P (v_list l)))
       (v : Value) : P v := 
  let rec := Value_ind' P n m f l  
  in
  let fix rec_list (vs : list Value) : List.Forall P vs :=
    match vs with 
    | nil => List.Forall_nil _
    | cons w ws => @List.Forall_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  let fix rec_fset (fs : fset Value) : Forall_fset P fs :=
    match fs with 
      | FSet xs => rec_list xs
    end in
  let fix rec_list_fset (vs : list (fset Value)) : List.Forall (Forall_fset P) vs :=
    match vs with 
    | nil => List.Forall_nil _
    | cons w ws => @List.Forall_cons (fset Value) (Forall_fset P) w ws (rec_fset w) (rec_list_fset ws)
    end
  in 

  let rec_comp (c : Comp (fset Value)) : Comp.Forall (Forall_fset P) c :=
    match c as c1 return Comp.Forall (Forall_fset P) c1 with 
    | c_wrong => I
    | c_multi vs => rec_list_fset _
    end
  in
  match v with 
  | v_nat k => n k
  | v_map X v => m X v (rec_fset X) (rec_comp v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  end.

Lemma Consistent_not_Inconsistent : Exclusive ConsistentValue InconsistentValue.
Proof.
  intros x.
  eapply Value_ind' with (P := fun x => forall y : Value, ConsistentValue x y -> InconsistentValue x y -> False).
  all: intros.
  all: try solve [inversion H; inversion H0; subst; done].
  + inversion H2; inversion H1; subst; clear H2 H1.
    all: try simpl in H3; try done.
    - clear H0 H7.
      inversion H9. subst. clear H9.
      inversion H5. subst. clear H5.
      inversion H11. subst. clear H11.
      simpl in *.
      rewrite Forall_forall in H.
      have IH: (Forall_fset (fun x0 : Value => forall y : Value, ConsistentValue x0 y -> InconsistentValue x0 y -> False) (FSet X1)).
      { unfold Forall_fset. rewrite Forall_forall. eapply H. }
      eapply (exclusive_fset2 (FSet X1) IH (FSet X0)); simpl; auto.
    - inversion H11. subst. clear H11.
      move: (@exclusive_Comp2 (fset Value)) => h.
      specialize h with (l := c) (YS:= r2).
      eapply h; try eassumption.
      destruct c; simpl in *; auto.
      eapply Forall_impl; eauto.
      intros.
      inversion H2. inversion H3. subst. inversion H11. inversion H13. subst.
      eapply exclusive_fset2; eauto.
  + inversion H0; subst. clear H0.
    inversion H1; subst. done.
    eapply exclusive_list2; eauto.
Qed.


(* We do the same thing for Value_rect *)


Fixpoint Value_rec' (P : Value -> Type)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : list Value) (c : Comp (list Value)), 
           List.ForallT P l -> Comp.ForallT (List.ForallT P) c -> P (v_map l c)) 
       (f : P v_fun)
       (l : (forall l : list Value, List.ForallT P l -> P (v_list l)))
       (v : Value) : P v := 
  let rec := Value_rec' P n m f l  
  in
  let fix rec_list (vs : list Value) : List.ForallT P vs :=
    match vs with 
    | nil => List.ForallT_nil _
    | cons w ws => @List.ForallT_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  let fix rec_list_list (vs : list (list Value)) : List.ForallT (List.ForallT P) vs :=
    match vs with 
    | nil => List.ForallT_nil _
    | cons w ws => @List.ForallT_cons (list Value) (List.ForallT P) w ws (rec_list w) (rec_list_list ws)
    end
  in 

  let rec_comp (c : Comp (list Value)) : Comp.ForallT (List.ForallT P) c :=
    match c as c1 return Comp.ForallT (List.ForallT P) c1 with 
    | c_wrong => I
    | c_multi vs => rec_list_list _
    end
  in
  match v with 
  | v_nat k => n k
  | v_map X v => 
      m X v (rec_list X) (rec_comp v)
  | v_fun => f
  | v_list X => l X (rec_list X)
  end.



(* Two sets are consistent if all of their elements 
   are consistent. *)
Definition ConsistentSets {A:Type} `{Consistency A} V1 V2 := 
    forall x y, x ∈ V1 -> y ∈ V2 -> Consistent x y.

Definition InconsistentSets {A:Type} `{Consistency A} V1 V2 := 
  exists x, exists y, (x ∈ V1) /\ (y ∈ V2) /\ (Inconsistent x y).

#[export] Instance Consistency_P {A:Type} `{Consistency A} : Consistency (P A) :=
   { Consistent := ConsistentSets ; Inconsistent := InconsistentSets }.


Definition ConsistentSet {A:Type} `{Consistency A} V := ConsistentSets V V.


(* ------------ Valid values and computations ------------------ *)


Definition valid (V : P Value) : Type :=
  nonemptyT V.

Definition valid_mem (V : fset Value) : Prop :=
  match V with FSet XS => XS <> nil end.

(* Produces at least one result *)

(*
Definition valid_Comp (C : P (Comp Value)) : Type :=
  (nonemptyT C * not (c_wrong ∈ C) * not (c_multi nil ∈ C))%type.
*)

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

Definition CHOOSE (C1 : P (Comp (fset Value))) (C2 : P (Comp (fset Value))) : 
  P (Comp (fset Value)) := 
  fun c => 
    match c with 
    | c_multi l => 
        exists l1, exists l2, l = l1 ++ l2 /\ (c_multi l1 ∈ C1) /\ (c_multi l2 ∈ C2)
    | _ => False
    end.

(* Fails when V and W don't unify. Returns their union when they do. *)


Definition UNIFY (V : P Value) (W: P Value) : P (Comp (fset Value)) :=
  fun c => match c with 

        | c_multi nil => Inconsistent V W

        | c_multi (l :: nil) => 
            exists l1, exists l2, l = union_fset l1 l2 /\ nonempty_fset l1 /\  nonempty_fset l2 
           /\ (mem l1 ⊆ V) /\ (mem l2 ⊆ W)
           /\ Consistent l1 l2

        | _ => False
  end.
    
  

(* This definition includes all values that produce c. *)

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
           BIND (denot_comp_n m t ρ) (fun v1 =>
           BIND (denot_comp_n m u ρ) (fun v2 => 
           RET (CONS v1 v2 )))

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


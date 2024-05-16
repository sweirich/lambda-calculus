Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.

Require Import Lia.

Require Export lc.tactics.
Require Export lc.scoped.
Require Import structures.Structures.
Require Export structures.consistency.

Require Import structures.NFSet.
Require Export denot.nelist_properties.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

Create HintDb examples.

(* 
   This is an  example of the graph model for the pure 
   untyped lambda calculus plus natural numbers. 
*)


(* 
The denotation of a lambda calculus function is as its "graph" or set of
input / output pairs.
   
   Each pair in the set (i.e. v_map VS WS) declares that if this value is
   applied to any value in VS, the result is W.
   
 *)

Open Scope nfset_scope.
Import NFSetNotations.


(* begin Value *)
Inductive Value : Type :=
  | v_nat : nat -> Value
  | v_map : nfset Value -> Value -> Value
  | v_fun : Value.
(* end Value *)

#[export] Hint Constructors Value : core.


Infix "↦" := v_map (right associativity, at level 80).
Notation "∘" := v_fun.

(* Here are some example values *)

Definition f1  : Value  := [ ∘ ] ↦ ∘ .
Definition f1' : Value  := [ f1 ] ↦ ∘.
Definition f2  : Value  := [ ∘ ; f1 ] ↦ ∘.
Definition f2' : Value  := [ f1' ] ↦ ∘. 
Definition f3  : Value  := [ ∘ ; f1 ; f2 ] ↦ ∘.

Definition g1  : Value  := [ ∘ ] ↦ f1 .
Definition g1' : Value  := [ ∘ ] ↦ f1'.
Definition g2  : Value  := [ ∘ ] ↦ f2.
Definition g2' : Value  := [ ∘ ] ↦ f2'.
Definition g3  : Value  := [ ∘ ] ↦ f3.

(* 
" \f. f 0 + f 1 " 
   "{0 |-> 0, 1 -> 1} |-> 1"
*)


Fixpoint Value_ind' (P : Value -> Prop)
       (n : forall n : nat, P (v_nat n))  
       (m : forall (l : nfset Value) (w : Value), 
           Forall_nfset P l -> P w -> P (v_map l w))
       (f : P v_fun)
       (v : Value) : P v := 
  let rec :=  Value_ind' P n m f 
  in
  let fix rec_list (vs : list Value) : List.Forall P vs :=
    match vs with 
    | nil => List.Forall_nil _
    | cons w ws => @List.Forall_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  let rec_nfset (f : nfset Value) : Forall_nfset P f :=
    match f with 
    | NFSet v vs => conj (rec v) (rec_list vs)
    end
  in 
  match v with 
  | v_nat k => n k
  | v_map X w => m X w (rec_nfset X) (rec w)
  | v_fun => f
  end.

Fixpoint Value_rec' (P : Value -> Type)
       (n : forall n : nat, P (v_nat n))  
       (m : forall (l : nfset Value) (w : Value), 
           ForallT_nfset P l -> P w -> P (v_map l w))
       (f : P v_fun)
       (v : Value) : P v := 
  let rec :=  Value_rec' P n m f 
  in
  let fix rec_list (vs : list Value) : List.ForallT P vs :=
    match vs with 
    | nil => List.ForallT_nil _
    | cons w ws => @List.ForallT_cons Value P w ws (rec w) (rec_list ws)
    end
  in 
  let rec_nfset (f : nfset Value) : ForallT_nfset P f :=
    match f with 
    | NFSet v vs => (rec v , rec_list vs)
    end
  in 
  match v with 
  | v_nat k => n k
  | v_map X w => m X w (rec_nfset X) (rec w)
  | v_fun => f
  end.


Fixpoint Value_lt (v1 : Value) (v2 : Value) : Prop := 
  let fix list_Value_lt (X : list Value) (Y : list Value) : Prop := 
    match X , Y with 
    | _   , nil => False
    | nil , _   => True 
    | cons x xs, cons y ys => Value_lt x y \/ (x = y /\ list_Value_lt xs ys)
    end in
  let fix nfset_lt (X : nfset Value) (Y : nfset Value) : Prop :=
    match X , Y with 
    | NFSet v1 vs1, NFSet v2 vs2 => 
        Value_lt v1 v2 \/ (v1 = v2 /\ list_Value_lt vs1 vs2)
    end in
  match v1 , v2 with 
  | v_nat k1 , v_nat k2 => Nat.lt k1 k2
  | _ , v_nat _ => False
  | v_nat _ , _ => True
  | _ , v_fun => False
  | v_fun  , _ => True
  | v_map V1 w1 , v_map V2 w2 => 
      nfset_lt V1 V2 \/ (V1 = V2 /\ Value_lt w1 w2)
  end.

Example lt1 : Value_lt ∘ f1. simpl; auto. Qed.
Example lt2 : Value_lt f1 f2. simpl; auto. Qed.
Example lt3 : Value_lt f2 f3. simpl; auto. tauto. Qed.
 
#[export] Instance Irreflexive_Value_lt : Irreflexive Value_lt. Admitted.
#[export] Instance Transitive_Value_lt : Transitive Value_lt. Admitted.

(*
Lemma eq_dec_list {A} : forall (l : list A), 
 (List.ForallT (fun x : A => forall y : A, {x = y} + {x <> y}) l) -> 
 forall f, { l = f } + { l <> f }.
Proof.
  intros l IH.
  induction IH; intro f; destruct f.
  - left; auto.
  - right; done.
  - right; done.
  - destruct (p a); subst.
    destruct (IHIH f); subst.
    left; auto.
    right. intro h. inversion h. done.
    right. intro h. inversion h. done.
Defined.
*)

Lemma eq_dec_Value : forall (x y : Value), { x = y } + { x <> y }.
Proof.
  intro x.
  eapply Value_rec' with (v := x).
  1: move=> n.
  2: move=> l w IHl IHw.
  all: move=> y; destruct y.
  all: try solve [right; intro h; done].
  all: try solve [left; auto].
  - move: (eq_nat_dec n n0) => h. destruct h; subst. left; auto. 
    right. intro h. inversion h. done.
  - destruct (IHw y); subst.
    destruct l as [l].
    simpl in IHl.
Admitted.

#[export] Instance EqDec_eq_Value : EqDec_eq Value := eq_dec_Value.



(* -------------------------------------------------------------- *)


(* But there is a complication. We want to define application as follows:

      APPLY D1 D2 = { w | (V ↦ w) in D1 /\ V ⊆ D2 }

   In other words, the set of all results such that there is some mapping in
   the function that matches the argument.

   However, there is some redundancy in this definition.  If D1 is a set of
   Values, such as
   
       { ∘, f1 , f1', f2 , f2', f3 }

  then no matter what D2 we use, we will get the the *same* result from
  application as if we had instead used the singleton set D1'

       { f3 }

   Why? because all applications that we can do with elements of this set, we
   can do with f3.

   This means that D1 and D1' are "observationally equal". So we would like
   our definition of equality on sets to equate these two sets.

   [ We also need to think about how approximation works with the codomain
     type. ]

   To capture this idea, we define an approximation between values (⊑) that
   says when one value is superceded by another. (See below.) This relation is
   a partial order: reflexive, transitive and (for canonical values)
   antisymmetric.

   For example, we have

         ∘ ⊑ f1 ⊑ f2

   We can extend this approximation to an ordering on sets with

      D1 ⊑ D2 when forall x ∈ D1, exists y in D2 such that x ⊑ y

   Our definition of equality for sets of values is the usual one:

      D1 ≃ D2 when D1 ⊆ D2 and D2 ⊆ D1

   It it is important that we can reason about equality of sets just by
   reasoning about their contents. In other words, we have this extensional
   reasoning principle:

      forall X, D1 X <-> D2 X implies that D1 ≃ D2
   
   So we can't change our definition of set equality. But that means
   application needs to produce equal sets with approximately equal arguments.

   In other words, a property that we want is:

      D1' ⊑ D1 -> APPLY D1' D2 ⊆ APPLY D1 D2

  *)

Definition approx_set approx (D1 : P Value) (D2 : P Value) : Prop :=
  forall x, x ∈ D1 -> exists y, (y ∈ D2) /\ approx x y.

Inductive approx : Value -> Value -> Prop := 
  | a_nat : forall i, approx (v_nat i) (v_nat i)
  | a_fun2 : approx v_fun v_fun
  | a_fun1 : forall V w, 
      approx v_fun (v_map V w)
  | a_map : forall (V1 V2 : nfset Value) w1 w2,
      approx_set approx (mem V1) (mem V2) ->
      approx w1 w2 ->
      approx (v_map V1 w1) (v_map V2 w2).

#[export] Hint Constructors approx : core.

Declare Scope Value_scope.
Infix "⊑V" := approx (at level 80) : Value_scope.
Open Scope Value_scope.

Infix "⊑" := (approx_set approx) (at level 80).


Ltac invert := 
  repeat match goal with 
  | [ H : _ ∈ mem (NFSet _ _) |- _ ] => inversion H; try done; subst; clear H 
  | [ H : approx _ v_fun |- _ ] => inversion H; subst; clear H
  | [ H : approx _ (_ _) |- _ ] => inversion H; subst; clear H
  | [ H : In _ (_ :: _) |- _ ] => destruct H as [<- | ?]; subst; try done
(*  | [ H : ?D1 ⊑ ?D2 , x : Value, xIn : x ∈ ?D1 |- _ ] => 
      destruct (H x xIn) as [ y [ yIn h ]] *)
  end.


(* Some properties. *)

Lemma Reflexive_approx {v} : approx v v.
(*
eapply Value_ind' with (P := fun x => approx x x); intros; eauto.
econstructor; eauto.
destruct l as [l].  simpl in H.
rewrite Forall_forall in H. destruct H as [h1 h2].
intros v1 v1In.
inversion H1. subst. clear H1.
destruct H5 as [h3 h4].
rewrite Forall_forall in h4.
destruct v1In; subst; try done.
exists l. split; eauto. left. eauto.
exists v1. split; eauto. right. auto.
inversion H1. subst. clear H1.
eauto.
Qed.  *) Admitted.

Instance Transitive_approx : Transitive approx.
Admitted.

#[export] Hint Resolve Reflexive_approx : core.

Lemma Reflexive_approx_set {D} : D ⊑ D.
Proof. intros x xIn. exists x. split; eauto. Qed.

#[export] Hint Resolve Reflexive_approx_set : core.

(* This is not true: our notion of approximation for nfsets is 
   extensional. So we need to restrict this to canonical 
   values below. *)
Lemma antisymmetry_approx : forall x y, approx x y -> approx y x -> x = y.
Proof.
  intro x.
  eapply Value_ind' with (P := fun x => forall y, approx x y -> approx y x -> x = y); eauto.
  1: intro k.
  2: intros V w IHV IHw.
  all: intros y Axy Ayx.
  all: inversion Ayx; try done; subst; clear Ayx.
  all: inversion Axy; subst; clear Axy.
  f_equal.
  destruct V as [v1 VS1].
  destruct V1 as [v2 VS2].
  move: IHV => [IHv IHVS].
Abort.


(* ----- approx examples ------ *)
  

Lemma example_approx_nfset : forall V, mem V ⊑ mem [∘] -> (mem V ≃ mem [∘]).
Proof. intros V A. destruct V as [y l]. 
       split; intros z zIn.
       - destruct zIn; subst.
         move: (A y ltac:(left;eauto)) => [w [wIn h]].
         inversion wIn; subst. inversion h. eauto. done.
         move: (A z ltac:(right; eauto)) => [w [wIn h]].
         inversion wIn; subst. inversion h. eauto. done.
       - inversion zIn; subst; try done.
         left.
         move: (A y ltac:(left; eauto)) => [w [wIn h]].
         inversion wIn; subst; try done. inversion h. auto.
Qed.

Lemma ordered_mem_circ : forall V1,
  mem V1 ≃ mem [∘] ->
  Forall_nfset (fun x => x = ∘) V1.
Proof.
  intros V1 EQ.
  destruct V1.
  move: v EQ.
  induction l.
  + intros v [h1 h2]. econstructor; eauto.
    specialize (h1 v ltac:(left; eauto)). inversion h1. auto. done.
  + intros v [h1 h2].  econstructor; eauto.
    specialize (h1 v ltac:(left; eauto)). inversion h1. auto. done.
    econstructor; eauto.
    specialize (h1 a ltac:(right; left; eauto)). inversion h1. auto. done.
    have h:  mem (NFSet v l) ≃ mem [∘].
    { clear IHl. split.
      intros z zIN. destruct zIN; subst. eapply h1. left; eauto.
      eapply h1. right; right; eauto.
      intros z zIn. destruct zIn; try done. subst.
      move: (h2 ∘ ltac:(left; eauto)) => h3.
      destruct h3 as [E1 | E2].  subst; left; eauto.
      destruct E2; subst.
      move: (h1 v ltac:(left; eauto)) => h4. destruct h4; try done. subst.
      left; eauto.
      right; eauto.
    }
    specialize (IHl v h). simpl in IHl. move: IHl => [h3 h4]. auto.
Qed.




(* Some examples of approx *)

Example approx1 : approx ∘ f1 . cbv. eauto. Qed.

Example approx2 : approx f1 f2. cbv. 
econstructor; eauto with examples. 
move=> v1 v1In. cbv in v1In. destruct v1In; try done. subst.
exists ∘. split; cbn; eauto. Qed.

Example approx1' : approx f1 f1'. cbv. econstructor; eauto with examples. 
intros v1 v1In. cbv in v1In. destruct v1In; try done. subst.
eexists. split. cbn. left; eauto. econstructor; eauto with examples. Qed.

Example approx2' : approx f1' f2. cbv. econstructor; eauto with examples.
move=> v1 v1In. cbv in v1In. destruct v1In; try done. subst.
exists f1. split; cbv; eauto with examples. Qed.

#[local]Hint Resolve approx1 approx2 approx1' approx2' : examples.



(* --------------- maximal / complete --------------- *)

(* The other issue that we need to address is that there are several 
   representations for the same value. *)

(* From this point on, we will work with *canonical* values only. *)

(* A maximal set does not contain any strict approximations *)
Definition maximal (D : P Value) :=
  forall x y, x ∈ D -> y ∈ D -> (approx x y) -> x = y.

Example maximal_singleton v : maximal (mem [v]).
Proof. intros x y xIn yIn A. invert. Qed.

#[export] Hint Resolve maximal_singleton : core.


(* --------------- canonical values --------------- *)

(* A canonical value is one where the nfset is 
   strictly ordered

   A complete canonical value is one where the nfset 
   is also complete. We have to build this up in two steps 
   because we want to be complete only over canonical 
   values, not all values.
 *)

Inductive restricted (Pr : nfset Value -> Prop) : Value -> Prop := 
  | restricted_v_nat : forall k, restricted Pr (v_nat k)
  | restricted_v_fun : restricted Pr v_fun
  | restricted_v_map : 
    forall X w v VS, 
      X = NFSet v VS ->
      Pr X -> 
      Forall_nfset (restricted Pr) (NFSet v VS) -> 
      restricted Pr w -> 
      restricted Pr (v_map X w).


#[export] Hint Constructors restricted : core.

Lemma restricted_impl : forall (P1 P2 : nfset Value -> Prop), 
  (forall x, P1 x -> P2 x) -> forall v, restricted P1 v -> restricted P2 v.
Proof. 
  intros P1 P2 IM v.
  eapply Value_ind' with (P := fun v => restricted P1 v -> restricted P2 v).
  1: move=> i.
  2: move=> l w IHl IHw.
  all: move=> h; inversion h; subst; clear h.
  all: eauto.
  econstructor; eauto.
  eapply mem_Forall.
  rewrite Sets.Forall_forall.
  intros x xIn.
  apply Forall_mem in IHl.
  apply Forall_mem in H3.
  rewrite Sets.Forall_forall in IHl.
  rewrite Sets.Forall_forall in H3.
  eauto.
Qed.

(*
Fixpoint ordered_list (v : Value) (xs: list Value) : Prop := 
  match xs with 
  | nil => True
  | cons w ys => Value_lt v w /\ ordered_list w ys
  end.

Definition ordered_nfset '(NFSet v vs) := ordered_list v vs.

(* This is the main property that we want from ordered nfsets *)
Lemma ordered_extensional VS WS : 
  ordered_nfset VS -> ordered_nfset WS -> mem VS ≃ mem WS -> VS = WS.
Proof.
Admitted.
*)

#[export] Instance StrictOrder_Value : StrictOrder Value_lt.
Admitted.

(* A canonical value orders all of the elements in v_map *)
Definition canonical : Value -> Prop := restricted (ordered_nfset Value_lt).

Definition canonical_nfset := Forall_nfset canonical.

Definition canonical_set D := forall x, x ∈ D -> canonical x.

Lemma mem_canonical {X} : canonical_nfset X -> canonical_set (mem X).
Proof. destruct X as [v VS]. intros [h1 h2] x xIn.
       destruct xIn as [->|h3]; auto. rewrite Forall_forall in h2. eauto. Qed.


(* A complete set means that 
   everything that approximates an element in V is already in V. *)
Definition complete_nfset (V : nfset Value) := 
  Forall_nfset (fun y => forall x, canonical x -> approx x y -> In_nfset x V) V.

(* A complete set contains all of its approximations *)
Definition complete_set (D : P Value) := forall D', Sets.Forall canonical D' -> D' ⊑ D -> D' ⊆ D.

Lemma mem_complete {X} : complete_nfset X -> complete_set (mem X).
Proof.
  unfold complete_nfset, complete_set.
  intros CX D' CD' APPROX. 
  move: (Forall_mem CX) => CMX.
  rewrite Sets.Forall_forall in CMX.
  rewrite Sets.Forall_forall in CD'.
  intros x xIn.
  specialize (CD' x xIn).
  move: (APPROX x xIn) => [y [yIn h]].
  specialize (CMX y yIn x CD' h).
  eapply In_mem. auto.
Qed.


(* complete/canonical values and sets *)
Definition cc : Value -> Prop := 
  restricted (fun X => ordered_nfset Value_lt X /\ complete_nfset X).

Definition cc_nfset (V : nfset Value) := Forall_nfset cc V /\ complete_nfset V.

Definition cc_set (D : P Value) := 
  Sets.Forall cc D /\ forall D', Sets.Forall cc D' -> D' ⊑ D -> D' ⊆ D.

Lemma mem_cc {X} : cc_nfset X -> cc_set (mem X).
Proof.
  unfold cc_nfset, cc_set, complete_nfset.
  move=> [CCX CX].
  split.
  eauto.
  intros D' ccD' APPROX.
  intros x xIn.
  eapply mem_complete; eauto.
  rewrite Sets.Forall_forall.
  rewrite Sets.Forall_forall in ccD'.
  intros y yIn.
  move: (ccD' y yIn) => h. unfold cc in h. unfold canonical.
  eapply restricted_impl. 2: eapply h.
  intros z [h1 h2]. done.
Qed. 

(* Two complete sets that approximate eachother are equal. *)
Definition cc_approx_equality D1 D2 : 
  cc_set D1 -> cc_set D2 
  -> D1 ⊑ D2 -> D2 ⊑ D1 -> D1 ≃ D2.
Proof.  unfold cc_set. intros [h1 h2][h3 h4] h5 h6. split; eauto. 
Qed.


(* Closure operation to force cc (sets). *)
Definition close (D : P Value) : P Value :=
  fun x => cc x /\ exists y, (y ∈ D) /\ approx x y.


(* closed sets are cc *)
Lemma cc_close D : cc_set (close D).      
Proof.
  split.
  - unfold close. 
    rewrite -> Sets.Forall_forall.
    intros x xIn. destruct xIn. auto.
  - intros D' CAN APP.
    intros x xIn.
    move: (APP x xIn) => [w [wIn h]].
    move: wIn => [cw [y [yIn h3]]].
    split. 
    rewrite -> Sets.Forall_forall in CAN. eauto.
    exists y. split; eauto. transitivity w; auto.
Qed.

Lemma close_mono : forall D1 D2, D1 ⊆ D2 -> close D1 ⊆ close D2.
Proof.
  intros D1 D2 SUB.
  intros x [h1 [y [yIn h2]]].
  split; auto. exists y.  split. eapply SUB; eauto. auto.
Qed.  


(* Two cc elements that approximate eachother are equal. *)

Lemma approx_antisymmetry x:
  forall y, cc x -> cc y -> 
       approx x y -> approx y x -> x = y.
Proof.
  eapply Value_ind' with (P := fun x =>   forall y, cc x -> cc y -> approx x y -> approx y x -> x = y).
  1: intros n.
  2: intros V w IHV IHw.
  all: intros y Cx Cy Axy Ayx.
  all: inversion Ayx; subst; clear Ayx.
  all: auto.
  - inversion Axy.
  - inversion Axy. subst. clear Axy.
    inversion Cx. subst. clear Cx.
    inversion Cy. subst. clear Cy.
    f_equal. 2: eauto.
    match goal with 
    | [ H7 : ordered_nfset Value_lt (NFSet v VS) /\ complete_nfset _ |- _ ] => move: H7 => [OX CX] end.
    match goal with 
    | [ H7 : ordered_nfset Value_lt (NFSet v0 VS0) /\ complete_nfset _ |- _ ] => move: H7 => [OX0 CX0] end.

    eapply ordered_extensional; eauto using StrictOrder_Value. 
    eapply cc_approx_equality; eauto.
    eapply mem_cc. split; eauto.
    eapply mem_cc. split; eauto.
Qed.    

(*                        
    
Definition maximal_approx_subset D1 D2 : 
  canonical_set D1 -> canonical_set D2 ->
  maximal D1 ->
  D1 ⊑ D2 -> D2 ⊑ D1 -> D1 ⊆ D2.
Proof.  
  intros C1 C2 M1 S1 S2. 
  intros x xIn.
  destruct (S1 x xIn) as [w [wIn hw]].
  destruct (S2 w wIn) as [z [zIn hz]].
  have AZ: approx x z. transitivity w; auto.
  have EQ: x = z. eapply M1; eauto. subst z.
  have EQ: w = x. eapply approx_antisymmetry; eauto.
  subst. done.
Qed.

Definition maximal_approx_equality D1 D2 : 
  canonical_set D1 -> canonical_set D2 ->
  maximal D1 -> maximal D2 ->
  D1 ⊑ D2 -> D2 ⊑ D1 -> D1 ≃ D2.
Proof.  
  intros C1 C2 M1 M2 S1 S2. 
  split; eauto using maximal_approx_subset.
Qed. *)


(* CC Examples *)

Example cc_f0 : cc ∘.
Proof. repeat econstructor; eauto. Qed.
#[local] Hint Resolve cc_f0 : examples.

Example cc_nfset_f0 : cc_nfset [∘].
Proof. repeat econstructor; eauto. invert. auto. Qed.
#[local] Hint Resolve cc_nfset_f0 : examples.

Example cc_f1 : cc f1.
Proof. repeat econstructor; eauto. invert. auto. Qed.
#[local] Hint Resolve cc_f1 : examples.

Example cc_nfset_f1 : cc_nfset [∘; f1].
Proof. econstructor; eauto.
       econstructor; eauto with examples.
       unfold complete_nfset.
       econstructor.
       - intros x Cx xA. invert. econstructor; eauto.
       - econstructor; eauto.
         intros x Cx Ax.
         unfold f1 in Ax.
         inversion Ax; subst; clear Ax.
         + econstructor; eauto.
         + inversion Cx; subst; clear Cx.
           inversion H3; subst. clear H3.
           remember (NFSet v VS) as X. 
           have EQ: X = [∘].
           { eapply ordered_extensional; eauto with examples. 
             eapply StrictOrder_Value.
             econstructor; eauto.
             eapply example_approx_nfset; eauto. }
           right. left. subst. rewrite EQ. unfold f1. done.
Qed.                        
#[local] Hint Resolve cc_nfset_f1 : examples.

Example cc_f2 : cc f2.
Proof.
  move: cc_nfset_f1 => [h1 h2].
  econstructor; eauto with examples.
  split; eauto.
  econstructor; simpl; eauto. 
Qed.

#[local] Hint Resolve cc_f2 : examples.


(*

(* Furthermore, values are finite, so we can *calculate* the (finite) set of values that 
   approximate a specific value. 

*)

Definition fset_of_list {A}`{EqDec_eq A} (l : list A) : fset A := 
  fold_right add_fset empty_fset l.

Definition unFSet {A} : fset A -> list A := 
  fun '(FSet xs) => xs.

Definition flat_map_fset {A B}`{EqDec_eq A}`{EqDec_eq B} (f : A -> fset B) : fset A -> fset B := 
  fun '(FSet xs)  => 
    fset_of_list (flat_map (fun x => unFSet (f x)) xs).


Fixpoint powerset {A}`{EqDec_eq A} (l : list A) : list (fset A) :=
    match l with 
    | nil => cons [] nil
    | cons x xs =>
        ps <- powerset xs ;;
        cons (add_fset x ps) (powerset xs)
    end.

Lemma powerset_spec {A}{D :EqDec_eq A} (x : list A) :
  forall (y : fset A), List.In y (powerset x) -> mem y ⊆ mem (FSet x).
Proof.
  induction x.
  - intros. simpl in *. destruct H; try done. subst.
    reflexivity.
  - intros y tIn. simpl in *.
    rewrite in_flat_map_Exists in tIn.
    inversion tIn; subst; clear tIn.
    + inversion H0; subst; clear H0.
      ++ rewrite <- H in IHx.
         specialize (IHx x0 ltac:(left; eauto)).
         move=>z zIn. 
         destruct x0 as [x0].
         unfold add_fset, add_list in zIn.
         destruct (In_dec_list a x0).
         right. eapply IHx. cbn. auto.
         destruct zIn. subst. left. auto.
         cbn. right. eapply IHx. cbn. auto.
      ++ rewrite <- H in IHx.
         specialize (IHx y ltac:(eauto)).
         move=>z zIn. cbn. right. eapply IHx. eauto.
    + rewrite <- H in IHx.
      rewrite Exists_nth in H0.
      destruct H0 as [i [d [ID InY]]].
      move: (nth_In l d ID) => h.
      destruct InY.
      ++ specialize (IHx (List.nth i l d) ltac:(right;eauto)).
         rewrite <- H0.
         intros z zIn.
         remember (List.nth i l d) as Z.
         destruct Z as [z0].
         unfold add_fset, add_list in zIn.
         destruct (In_dec_list a z0).
         right. eapply IHx. done.
         destruct zIn. subst. left. auto.
         right. eapply IHx. 
         move: H1. clear.  induction z0. intros. done.
         intros h. destruct h. subst. left. auto. 
         specialize (IHz0 H). right. eauto.
      ++ specialize (IHx y H0). 
         intros z zIn. right. eapply IHx. eauto.
Qed.         

Fixpoint approximates (v : Value) : list Value := 
  match v with 
  | v_nat k => cons (v_nat k) nil
  | v_fun => cons v_fun nil
  | v_map (FSet xs) w =>
      add_list v_fun
      (W1 <- (powerset (flat_map approximates xs)) ;;
       w1 <- (approximates w) ;;
       cons (W1 ↦ w1) nil)
  end.


Definition approximates_fset (W : fset Value) : list (fset Value) :=
  let '(FSet xs) := W in powerset (flat_map approximates xs).

Lemma aproximates_spec : forall v w, 
    approx w v <->
    List.In w (approximates v).
Admitted.
*)

Lemma sub_union {A} {X Y Z W: P A}: X ⊆ Z -> Y ⊆ W -> (X ∪ Y) ⊆ (Z ∪ W).
Proof. intros s1 s2.
       intros x xIn.
       destruct xIn.
       left; eauto.
       right; eauto.
Qed.

Lemma approx_union {D X Y} : D ⊑ (X ∪ Y) -> exists D1, exists D2, (D1 ⊑ X) /\ (D2 ⊑ Y) /\ (D ≃ (D1 ∪ D2)).
Proof. intros. 
       unfold approx_set in H.
       exists (fun x => (x ∈ D) /\ exists y, (y ∈ X) /\ (approx x y)).
       exists (fun x => (x ∈ D) /\ exists y, (y ∈ Y) /\ (approx x y)).
       repeat split.
       - intros x Pr.
         destruct Pr as [xIn [y [yIn yA]]]. exists y; split; eauto.
       - intros x Pr.
         destruct Pr as [xIn [y [yIn yA]]]. exists y; split; eauto.
       - intros x xIn.
         cbv.
         move: (H x xIn) => [y [yIn yA]].
         destruct yIn.
         left. split; eauto.
         right. split;  eauto.
       - intros x xIn.
         destruct xIn.
         move: H0 => [ xIn _]; auto.
         move: H0 => [ xIn _]; auto.
Qed.         

Lemma cc_union X Y :  cc_set X  -> cc_set Y -> cc_set (X ∪ Y).
  intros [X1 X2] [Y1 Y2].
  repeat rewrite Sets.Forall_forall in X1 Y1.
  split.
  - (* union is canonical *)
    rewrite Sets.Forall_forall.
    intros x [xX | xY]; eauto.
  - (* union is complete *)
    intros D' ccD' DAPP.
    rewrite Sets.Forall_forall in ccD'. 
    move: (approx_union DAPP) => [D1 [D2 [D1A [D2A EQ]]]].
    move: EQ => [h1 h2].
    have canD1 : Sets.Forall cc D1.
    { 
      rewrite Sets.Forall_forall.
      intros y yIn. apply ccD'. apply h2. left. auto.
    }
    have canD2 : Sets.Forall cc D2.
    { 
      rewrite Sets.Forall_forall.
      intros y yIn. apply ccD'. apply h2. right. auto.
    }
    transitivity (D1 ∪ D2); auto.
    eapply sub_union; eauto.
Qed.
    
                      
Instance Validity_Valid : Validity Value.
apply MkValid with (validT_set := fun X => (nonemptyT X * cc_set X)%type).
- intros X [NE CC].
  destruct NE. 
  have CCx: cc x. move: CC => [h1 h2]. rewrite Sets.Forall_forall in h1. auto.
  (* need to show that we can close a single element and produce a finite set. *)
  admit.  
- intros X [NE CC]. auto.
- intros X Y [NEX CCX] [NEY CCY].
  split. 
  + move: NEX => [x xIn]. exists x. left; auto.
  + eapply cc_union; eauto.
Admitted. 


(* --- semantic operators -------  *)

(*
Definition maximize (D : P Value) : P Value := 
  fun x => (x ∈ D) /\ forall y, y ∈ D -> approx x y -> x = y.

Lemma maximal_maximize D : maximal (maximize D).
Proof. intros x y xIn yIn A. move: xIn => [xIn mX].
       move: yIn => [yIn mY]. eauto. Qed.
*)

Inductive LAMBDA (f : P Value -> P Value) : P Value :=
  | s_map : forall V w, 
      cc (v_map V w) ->
      w ∈ f (mem V) ->
      LAMBDA f (v_map V w)
  | s_fun : 
      LAMBDA f v_fun.

(* Does application produce a maximal result??? *)

(* 
   Say D1 = { 1 ↦ ∘ } { 2 ↦ f0 }
       D2 = { 1 , 2 }
   then
       APPLY D1 D2 = { ∘ , f0 }    
   
   which is not maximal

*)
  

(* begin APPLY *)
Inductive APPLY : P Value -> P Value -> (Value -> Prop) :=
  | BETA : forall D1 D2 V w,
      (v_map V w ∈ D1) -> 
      (mem V ⊆ D2) -> 
      cc (v_map V w) ->
     APPLY D1 D2 w.
(* end APPLY *)

Inductive NAT (k : nat) : P Value :=
  | s_Nat : NAT k (v_nat k).

Inductive ADD : P Value :=
  | s_ADD : forall i j k,
      k = i + j ->
      ADD (v_map [ v_nat i ] (v_map [v_nat j] (v_nat k))).
(*  | s_ADD2 : forall i V1,
      ⌈ v_nat i ⌉ ≃ mem V1 ->
      ADD (v_map V1 v_fun)
  | s_ADD3 : ADD v_fun. *)

#[export] Hint Constructors Value LAMBDA APPLY NAT ADD : core.

Ltac invert_sem := 
  lazymatch goal with 
  | [ H : ?x ∈ LAMBDA ?f |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ APPLY ?v1 ?v2 |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ NAT ?k |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ ADD |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ close ?D |- _ ] => 
      let h1 := fresh "cc" in 
      let w  := fresh "w" in
      let wIn := fresh "IN" in
      let APP := fresh "APP" in
      move: H => [ h1 [w [wIn APP]]] 
  end.


(* --------------- canonical_set --------------------------------- *)

Lemma cc_set_Bottom : cc_set Bottom.
Proof. 
unfold cc_set. split; eauto. 
rewrite Sets.Forall_forall. intros x xIn. inversion xIn.
intros D ccD APP x xIn. destruct (APP x xIn) as [w [wIn h]].  done.
Qed.

#[export] Hint Resolve cc_set_Bottom : examples.

Lemma cc_set_NAT k : cc_set (NAT k).
unfold cc_set. split; eauto. 
rewrite Sets.Forall_forall. intros x xIn. inversion xIn.
unfold cc. econstructor; eauto.
intros D ccD APP x xIn. destruct (APP x xIn) as [w [wIn h]].  
invert_sem. invert. econstructor; eauto.
Qed.

#[export] Hint Resolve cc_set_NAT : examples.


(*
Lemma canonical_set_APPLY D1 D2 : 
  canonical_set D1 -> 
  canonical_set (APPLY D1 D2).
Proof. 
  intros C1.
  intros x xIn.
  invert_sem.
  inversion H1.
  auto.
Qed.

Lemma canonical_set_LAMBDA : forall F, canonical_set (LAMBDA F).
Proof.
  intros.
  intros x xIn.
  invert_sem; eauto.
Qed. *)



(* --------------- maximal  --------------------------------- *)

(*
Definition canonical_dom X :=
  ordered_nfset X /\
  maximal (mem X) /\
  Forall_nfset canonical X.


Lemma coapprox : forall y x1 x2, 
    canonical x1 -> canonical x2 -> canonical y ->
    approx x1 y -> approx x2 y -> approx x1 x2 \/ approx x2 x1.
Proof.
  intro y.
  eapply Value_ind' with (P := fun y => forall x1 x2, 
                                   canonical x1 -> canonical x2 -> canonical y ->
                                   approx x1 y -> approx x2 y -> approx x1 x2 \/ approx x2 x1).
  1: move=>n.
  2: move=>V w IHV IHw.
  all: intros x1 x2 C1 C2 C A1 A2.
  all: inversion C; subst; clear C.
  all: inversion A1; inversion A2; subst; clear A1 A2.
  all: try solve [left; eauto].
  all: try solve [right; eauto].
  inversion C1. inversion C2. subst. clear C1 C2.
  destruct (IHw w1 w0); eauto.
  - remember (NFSet v0 VS0) as X1.
    remember (NFSet v1 VS1) as X2.
    remember (NFSet v VS) as X.
    left.
Abort.

Lemma maximal_approx : forall D, 
    maximal D ->  
    forall X1 X2, 
      canonical_dom X1 -> canonical_dom X2 ->
      mem X1 ⊑ D -> mem X2 ⊑ D -> 
      exists X, (mem X ⊑ D) /\ (mem X1 ⊑ mem X) /\ (mem X2 ⊑ mem X).
Proof. 
  intros D mD X1 X2 C1 C2 A1 A2.
Admitted. *)

(*
Lemma maximal_Bottom : maximal Bottom.
Proof. 
intros x y xIn yIn. inversion xIn.
Qed.
*)

(*
Lemma maximal_APPLY D1 D2 : 
  maximal D1 ->
  maximal D2 -> 
  maximal (APPLY D1 D2).
Proof. 
  intros C1 C2.
  intros x y xIn yIn A.
  invert_sem.
  invert_sem.
  destruct H as [V1 [In1 [h1 CVw1]]].
  destruct H1 as [V2 [In2 [h2 CVw2]]].
(*   specialize (H0 V2 x In2 h2 CVw2). *)
  specialize (H2 V1 y In1 h1 CVw1).
  inversion CVw1. inversion CVw2. subst.
  eapply approx_antisymmetry; eauto.
Qed.

Lemma maximal_LAMBDA : forall F, (forall X, maximal X -> maximal (F X)) -> maximal (LAMBDA F).
Proof.
  intros.
  intros x y xIn yIn A.
  invert_sem. invert_sem.
  all: inversion A; subst; clear A.
  - inversion H0. inversion H2. subst. clear H0. clear H2.
    remember (NFSet v0 VS0) as X0.
    remember (NFSet v VS) as X.
    move: (H _ H10) => MF.
    move: (H _ H17) => MF0.
  -  specialize (H1 V w H). 
  - auto.
Qed.
*)


(*
Lemma maximal_NAT i : maximal (NAT i).
Proof.
  intros x y xIn yIn APPROX.
  repeat invert_sem. eauto.
Qed.

Lemma maximal_ADD : maximal ADD.
Proof.
  intros x y xIn yIn APP.
  repeat invert_sem.
  repeat invert.
  move: (H2 (v_nat i0) ltac:(left;eauto)) => [v [vIn h2]].
  move: (H3 (v_nat j0) ltac:(left;eauto)) => [w [wIn h3]].
  destruct vIn; try done; subst.
  destruct wIn; try done; subst.
  invert.
  auto.
Qed. *)

(* ------------------ complete ---------------------- *)

(* If we have a complete set, it works as well as any of its approximations in an application. *)

(*
Lemma complete_sub : forall D1, maximal D1 -> forall D1', D1' ⊑ D1 -> forall D2, 
        APPLY D1' D2 ⊆ APPLY D1 D2.
Proof.
  intros.
  intros x xIn.
  invert_sem.
  eapply BETA; eauto. 
  unfold maximal in H.
  eapply H in H0; eauto.
Qed.
*)

(*
Lemma complete_Bottom : complete Bottom.
Proof. intros x A y yIn. cbv in A.
destruct (A y yIn) as [v [h _]]. done.
Qed. *)

(*
Lemma complete_APPLY D1 D2 : 
  complete D1 -> 
  complete (APPLY D1 D2).
Proof. intros C1.
       intros x A y yIn.
       destruct (A y yIn) as [z [zIn h]].
       invert_sem.
       have CVz: canonical (V ↦ y).
       { inversion H1. subst. econstructor; eauto using approx_canonical_sub. }
       econstructor; eauto.
       eapply C1 with (D' := ⌈ V ↦ y ⌉); eauto.
       intros w wIn. inversion wIn; subst. exists (V ↦ z). split; eauto.
       econstructor; eauto.
       eapply Reflexive_approx_set.
       inversion H1. subst.
       eapply mem_canonical. eauto.
Qed.       

Lemma complete_LAMBDA : forall F, (forall D, complete D -> complete (F D)) -> complete (LAMBDA F).
Proof.
  intros.
  intros x A y yIn.
  destruct (A y yIn) as [z [zIn h]].
  invert_sem;  inversion h; subst; clear h.
  - econstructor; eauto.
  - move: (H _ H2) => CFD.
    econstructor; eauto.
    inversion H9.

inversion yIn; subst; econstructor; auto. clear yIn.
  inversion y. clear y. subst.  
  inversion H6. subst.
  move: (H (mem V) H2) => h.
  unfold complete in h.
  have C1: complete (mem V1).
  { unfold complete. intros x xIn.
    move: (H3 x xIn) => [v2 [h1 h2]].
    move=> y cy A.
    

  move: (H (mem V1) H2) => h.

Admitted. *)

Lemma singleton_nat i V1 V0 : 
  ⌈ v_nat i ⌉ ≃ mem V1 ->
  mem V0 ⊑ mem V1 -> 
  ⌈ v_nat i ⌉ ≃ mem V0.
Proof.
  intros.
  destruct V0.
  split.
  - intros x xIn. inversion xIn. subst .
    move: (H0 v ltac:(left; auto)) => [v1 [h1 h2]].
    rewrite <- H in h1. inversion h1. subst. clear h1.
    inversion h2. subst. clear h2.
    left; auto.
  - intros x xIn. 
    move: (H0 x xIn) => [v1 [h1 h2]].
    rewrite <- H in h1. inversion h1. subst. clear h1.
    inversion h2. subst. clear h2.
    eauto.
Qed.

(*
Lemma complete_NAT i : complete (NAT i).
  intros x xIn y cy yIn.
  invert_sem; inversion yIn; subst; clear yIn; eauto.
  econstructor; eauto.
Qed.  

Lemma complete_ADD : complete ADD.
  intros x xIn y cy yIn.
  invert_sem; inversion yIn; subst; clear yIn; eauto.
  - econstructor. 
  - inversion H5; subst; eauto; clear H5.
    econstructor; eauto.
    instantiate (1 := i).
    eapply singleton_nat; eauto.
    inversion H7; subst; clear H7.
    econstructor; eauto.
    eapply singleton_nat; eauto.
    eapply singleton_nat; eauto.
  - econstructor; eauto.
  - inversion H4. subst. clear H4.
    econstructor; eauto.
    eapply singleton_nat; eauto.
  - econstructor; eauto.
Qed.


#[export] Hint Resolve complete_Bottom : core.
*)

Import EnvNotations.

(* Denotation function *)

Definition Rho := list (P Value).


(* Denotation function *)
Fixpoint denot (a : tm) (ρ : Rho) : P Value :=
     match a with 
     | var_b n => ρ ⋅ n 

     | abs t => close (LAMBDA (fun D => denot t (D :: ρ)))

     | app t u   =>  close (APPLY (denot t ρ) (denot u ρ))

     | lit i => NAT i

     | prim p_add   => close ADD

     | _ => Bottom
     end.

(* --------------- monotonicity ------------------------------ *)

(*
(* MAXIMIZE is not monotonic. We may have to kick out some values.... *)
Lemma maximize_mon_sub {D1 D2} : 
  D1 ⊆ D2 -> maximize D1 ⊆ maximize D2.
Proof.
  intros SUB x xIn.
  destruct xIn as [xIn h].
  move: (SUB x xIn) => xIn2.
  split. auto.
  intros; eauto.
Abort. *)

Lemma approx_sub : forall D1 D2 D3, D1 ⊑ D2 -> D2 ⊆ D3 -> D1 ⊑ D3.
Proof.
  intros.
  intros x xIn.
  move: (H x xIn) => [y [yIn h]].
  exists y. split; eauto.
Qed.


Lemma close_cong { D1 D3 } :
    D1 ≃ D3 -> (close D1 ) ≃ (close D3 ).
Proof.
  intros [ d13 d31 ].
  split; eapply close_mono; eauto.
Qed.


#[export] Instance Proper_Included_close : Proper (Included ==> Included) close. 
unfold Proper. intros x1 y1 E1. eapply close_mono; eauto. Qed.

#[export] Instance Proper_Same_close : Proper (Same_set ==> Same_set) close. 
unfold Proper. intros x1 y1 E1. eapply close_cong; eauto. Qed.


(* Λ-ext-⊆  *)

(* NOTE: By restricting the hypothesis to only valid sets, we strengthen 
   the result. But this depends on the definition of Λ which quantifies
   over valid sets (i.e. CBV) *)
Lemma LAMBDA_ext_sub {F1 F2} :
  (forall {X : P Value}, nonempty X -> F1 X ⊆ F2 X) -> LAMBDA F1 ⊆ LAMBDA F2.
Proof.
  intros F1F2 v Iv.
  invert_sem; econstructor; try eapply F1F2; eauto.
  destruct V. exists v. cbn. left; auto.
Qed.

Lemma LAMBDA_ext {F1 F2} :
  (forall {X}, nonempty X -> F1 X ≃ F2 X) -> LAMBDA F1 ≃ LAMBDA F2.
Proof. 
  intros g. split;
  eapply LAMBDA_ext_sub; intros X NEX; destruct (g X); eauto.
Qed.

Lemma APPLY_mono_sub { D1 D2 D3 D4 } :
    D1 ⊆ D3 -> D2 ⊆ D4 -> ((APPLY D1 D2) ⊆ (APPLY D3 D4)).
Proof.  
  intros D13 D24 w wIn. 
  invert_sem.
  eapply BETA with (V := V); eauto.
  transitivity D2; auto.
Qed.

Lemma APPLY_cong { D1 D2 D3 D4 } :
    D1 ≃ D3 -> D2 ≃ D4 -> ((APPLY D1 D2) ≃ (APPLY D3 D4)).
Proof.
  intros [ d13 d31 ] [ d24 d42 ].
  split; eapply APPLY_mono_sub; eauto.
Qed.

#[export] Instance Proper_Included_APPLY : Proper (Included ==> Included ==> Included) APPLY. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply APPLY_mono_sub; eauto. Qed.

#[export] Instance Proper_Same_APPLY : Proper (Same_set ==> Same_set ==> Same_set) APPLY. 
unfold Proper. intros x1 y1 E1 x2 y2 E2. eapply APPLY_cong; eauto. Qed.

(* denot *)

#[export] Instance Proper_sub_denot : Proper (eq ==> List.Forall2 Included ==> Included) denot.
Proof.
  intros t1 t ->.
  induction t.
  1: move=>i.
  2: move=>y.
  3: move=>t1 t2 IH1 IH2.
  4: move=> t' IH.
  all: intros.
  all: try move=> ρ1 ρ2 SUB.
  all: try reflexivity.
  - eapply access_mono_sub; eauto.
  - simpl. simpl in H.
    eapply close_mono with (D1 := LAMBDA (fun D => denot t (D :: t1))).
    eapply LAMBDA_ext_sub; eauto.
    auto.
  - simpl.
    eapply close_mono.
    eapply APPLY_mono_sub; eauto.
Qed.

(* The denotation respects ≃ *)
#[export] Instance Proper_denot : Proper (eq ==> same_env ==> Same_set) denot.
Proof.
  intros t1 t -> x y E.
  unfold same_env in E.
  rewrite same_env_sub_env in E. destruct E. 
  split; eapply Proper_sub_denot; auto. 
Qed. 


(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: forall (sc : atoms), 
  monotone_env sc (denot t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot; auto.
Qed.

(* -- monotonicity WRT argument -- *)

(* denot-monotone-one *)
Lemma denot_monotone_one : forall ρ t, 
    monotone (fun D => denot t (D :: ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  eapply denot_monotone with (sc := S (dom ρ)); simpl; auto.
Qed.


(* ------------------ nonempty ---------------------- *)

Lemma nonempty_close : forall D, nonempty D -> Sets.Forall cc D -> nonempty (close D).
Proof. intros D vD ccD. destruct vD as [w wIn].
exists w. split. eapply ccD; eauto. exists w. split; eauto.
Qed.

Lemma cc_set_LAMBDA : forall F, Sets.Forall cc (LAMBDA F).
Proof. intros F. 
rewrite Sets.Forall_forall. intros x xIn.
inversion xIn; auto. eauto with examples.
Qed.

Lemma nonempty_LAMBDA : forall F, nonempty (close (LAMBDA F)).
Proof. intros F. exists v_fun. split. eauto with examples.
exists ∘. split. eapply s_fun. eauto. Qed.

Lemma nonempty_NAT : forall k, nonempty (NAT k).
Proof. intros k. cbv. exists (v_nat k). econstructor; eauto. Qed.

Lemma cc_v_nat k : cc (v_nat k).
Proof. econstructor; eauto. Qed.

Lemma cc_nfset_nat k : cc_nfset (singleton_nfset (v_nat k)).
Proof.
  unfold cc_nfset.
  split.
  econstructor; eauto. econstructor.
  unfold complete_nfset.
  econstructor; eauto.
  intros x xC xA.
  invert.
  eauto.
Qed.

#[export] Hint Resolve cc_v_nat cc_nfset_nat : examples.

Lemma nonempty_ADD : nonempty (close ADD).
Proof. 
  exists (v_map (singleton_nfset (v_nat 0)) 
            (v_map (singleton_nfset (v_nat 0)) (v_nat 0))).
  split.
  - have hO: ordered_nfset Value_lt (singleton_nfset (v_nat 0)).  simpl; auto.
    have hC: complete_nfset (singleton_nfset (v_nat 0)). 
    { econstructor; eauto. intros x cX aX. invert. eauto. }
    eapply restricted_v_map. reflexivity.
    split; auto. 
    econstructor; eauto.
    eapply restricted_v_map. reflexivity.
    split; auto.
    econstructor; eauto.
    eauto.
  - exists (v_map (singleton_nfset (v_nat 0)) 
            (v_map (singleton_nfset (v_nat 0)) (v_nat 0))).
    split. econstructor; eauto. 
    econstructor; eauto.
Qed.

Lemma Forall_access {A} : forall Pr ρ (d:A) k, List.Forall Pr ρ -> Pr d -> Pr (access d ρ k).
Proof. Admitted.

Lemma denot_complete : forall t ρ, List.Forall cc_set ρ -> cc_set (denot t ρ).
Proof.
  induction t.
  all: simpl; intros ρ CR.
  all: eauto with examples.
  - eapply Forall_access; eauto with examples.
  - eapply cc_close.
  - eapply cc_close.
  - destruct primitive5. eapply cc_close. 
    admit.
Admitted.

(* ------------------ continuity ---------------------- *)

(*
Definition continuous {A} (F : P Value -> P A) : Set :=
  forall X E, mem E ⊆ F X -> valid X -> cc_set X 
         -> exists D, (cc_nfset D) /\ (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)).

Definition continuous_In {A} (D:Rho Value -> P A) (ρ:Rho Value) (v:A) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env {A} (D:Rho Value -> P A) (ρ:Rho Value) : Prop :=
  forall (v : A), continuous_In D ρ v.

Definition continuous_Sub {A} (D:Rho Value -> P A) (ρ:Rho Value) (V:nfset A) : Prop :=
  mem V ⊆ D ρ -> 
  exists ρ', exists (pf : finite_env ρ'),
    ρ' ⊆e ρ  /\ (mem V ⊆ D ρ').
*)


(* ------------------ continuity ---------------------- *)

Definition close_nfset : nfset Value -> nfset Value. Admitted.
Lemma close_nfset_spec {V : nfset Value} : 
  mem (close_nfset V) ≃ close (mem V).
Admitted.



Lemma extract {V} :
  forall D, mem V ⊆ close D -> exists W, (mem W ⊆ D) /\ (close (mem V) ≃ close (mem W)).
Proof. 
  eapply nfset_induction with (Pr := fun V => forall D : P Value, mem V ⊆ close D -> exists W : nfset Value, (mem W ⊆ D) /\ (close (mem V) ≃ close (mem W))).
  - intros x D SUB.
    unfold singleton_nfset in SUB.
    unfold close in SUB.
    specialize (SUB x ltac:(left; auto)).
Abort.

Lemma close_continuous_env {D : Rho -> P Value}{ρ} :
    continuous_env D ρ 
  -> monotone_env (dom ρ) D 
  -> continuous_env (fun ρ => close (D ρ)) ρ.
Proof.  
Admitted.
(*
  intros IHD mD V VAL SUB VE.
  unfold continuous_env, continuous_Sub in IHD.
  have [W [h1 h2]]: (exists W, (mem W ⊆ D ρ) /\ validT_set (mem W)). admit.
  destruct (IHD W ltac:(auto)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]]; auto.
  exists ρ1. exists fρ1. split. auto.
  split. auto.
  exists y. split; auto.
Qed. 
*)

Lemma APPLY_continuous_env {D E : Rho -> P Value}{ρ} :
    continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env (dom ρ) D 
  -> monotone_env (dom ρ) E
  -> continuous_env (fun ρ => close (APPLY (D ρ)(E ρ))) ρ.
Proof.  
  intros IHD IHE mD mE.
Admitted.
(*
  intros W VW APP VE.
  unfold continuous_env, continuous_Sub in IHD.
  unfold close in APP.

  destruct (IHD (v_map V  w ) ltac:(auto)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
  have S1: same_scope ρ1 ρ2.
  { unfold same_scope. rewrite -> ρ1ρ. rewrite -> ρ2ρ. done. }
  have S2: same_scope ρ1 ρ.
  { unfold same_scope. rewrite -> ρ1ρ. done. }
  have S3: same_scope ρ2 ρ.
  { unfold same_scope. rewrite -> ρ2ρ. done. }
  exists (ρ1 ⊔e ρ2).
  repeat split.
    -- eapply join_finite_env; eauto.     
    -- eapply join_lub; eauto.
    -- have VwDp3 : ⌈ v_map V w ⌉ ⊆ D (ρ1 ⊔e ρ2).
    { transitivity (D ρ1); auto. eapply mD; auto.
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { transitivity (E ρ2); auto. eapply mE; auto.
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
Qed.
*)

(* Algebraicity.  
   Only need finite information from the environment.
*)

(*
Lemma LAMBDA_continuous_env {E ρ} {NE : nonempty_env ρ} :
    (forall V, valid (mem V) -> continuous_env E (mem V :: ρ))
  -> monotone_env (S (dom ρ)) E
  -> continuous_env (fun ρ => LAMBDA (fun D => E (D :: ρ))) ρ.
Proof.
  intros IH mE.
  intros v vIn.
  inversion vIn as [ V w CCfw wEVρ EQ | ]. subst; clear vIn.
  - (* v is V ↦ w *)
    have NEx: nonempty_env (mem V :: ρ). econstructor; eauto.
    specialize (IH V ltac:(eauto) w wEVρ).
    destruct IH as [ρ' [F' [S' h']]].
    inversion S'. subst. inversion F'. subst.
    exists l. eexists. eauto.
    repeat split; auto.
    eapply s_map; eauto.
    eapply mE with (ρ := x :: l); simpl_env; eauto. 
    simpl. f_equal. rewrite -> H3. auto.
    econstructor; eauto. 
  - exists (initial_finite_env ρ NE).
    repeat split; eauto. 
    econstructor.
Qed.

(* ⟦⟧-continuous *)
Lemma denot_continuous_env {t} : forall ρ,
    nonempty_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  induction t.
  all: intros ρ NE.
  all: intros c cIn.
  all: try solve [destruct c; try done].  
  all: simpl in cIn.
  all: simpl.
  - (* var case *)
    eapply access_continuous_env; eauto.
  - (* abs *)
    eapply close_continuous_env; eauto.
    eapply LAMBDA_continuous_env; eauto using denot_monotone.
    intros ρ1 ρ2 DE SUB; 
    eapply LAMBDA_ext_sub; intros X VX; eapply denot_monotone; eauto.
    Unshelve. eauto.
  - (* app *)
    eapply close_continuous_env; eauto.
    eapply APPLY_continuous_env; eauto using denot_monotone.
    intros ρ1 ρ2 DE SUB; eapply APPLY_mono_sub; eapply denot_monotone; eauto.
  - (* lit *)
    inversion cIn; subst;
    exists (initial_finite_env ρ NE); repeat split; eauto. 
  - (* add *)
    eapply close_continuous_env; eauto.
    inversion cIn; subst;
    exists (initial_finite_env ρ NE); repeat split; eauto. 
    intros ρ1 ρ2 DE SUB. reflexivity.
Qed.

(* --------------------------------------------------- *)

(* ⟦⟧-continuous-⊆ *) 
Lemma denot_continuous_sub {ρ t} : 
  nonempty_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros NE_ρ V VinEρ.
  eapply generic_continuous_sub;
    eauto using denot_continuous_env, denot_monotone.
Qed. 

(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ } :
  nonempty_env ρ 
  -> continuous (fun D => denot t (D :: ρ)).
Proof.
  intros NE_ρ .
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (X :: ρ)) as 
    [ρ' [pf [h1 h2]]].
  + eapply extend_nonempty_env; eauto.
  + eauto.
  + inversion h1. subst. inversion pf. subst.
    match goal with [H6 : finite x |- _ ] => move: H6 => [D [S NN]] end.
    exists D. split. transitivity x; auto.
    have SUB: List.Forall2 Included 
                (x :: l) (mem D :: ρ).
    econstructor; eauto. 
    transitivity (denot t (x :: l)); auto.
    eapply denot_monotone; eauto.
Qed.

(*  ----- Abstraction followed by Application is the identity -------- *)

Lemma same_dom V V0 w0 w2 : 
  cc (V ↦ w0) ->
  cc (V0 ↦ w2) ->
  mem V ⊑ mem V0 ->
  mem V ⊆ mem V0.
Proof.
  intros c1 c2 APP. inversion c1; inversion c2; clear c2 c2.
  subst X0. subst w1. subst X. subst w.
  split_hyp.
  
  move: (mem_complete H0) => h0.
  unfold complete_set in h0.
  have CV: Sets.Forall canonical (mem V). admit.
  specialize (h0 (mem V) CV APP).
  auto.
Admitted.

Definition cc_fun F := forall X, cc_set X -> cc_set (F X).



(* Λ-▪-id *)
Lemma LAMBDA_APPLY_id { F X } :
  continuous F -> monotone F -> cc_fun F -> valid X -> cc_set X 
  -> close (APPLY (close (LAMBDA F)) X) ≃ F X.
Proof. 
  intros Fcont Fmono Fcc NEX Xcc.
  split.
  + intros w wIn. invert_sem. invert_sem. invert_sem. invert_sem; invert.
    admit.
  + intros w wInFX.
    move: (Fcc X Xcc) => [ccFX compFX]. rewrite Sets.Forall_forall in ccFX.
    move: (ccFX _ wInFX) => ccw.
    split; auto.
    exists w. split. 
    have M : mem (singleton_nfset w) ⊆ F X. { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (singleton_nfset w) M NEX) => [ D [ DltX wInFD ]].
    have CCDw: cc (D ↦ w).
    { destruct D as [v V]. eapply restricted_v_map. eauto.
      split.
    eapply BETA with (V := D); eauto.
    split.

    ++ have EQ: V = V0. {
         inversion cc1. inversion H. subst.
         destruct H7. destruct H14.
      have II: mem (singleton_nfset w2) ⊆ F X. { intros w1 w1In. inversion w1In. subst.
      move: (Fcont X (singleton_nfset w2)) => h. [ D [ DltX [ wInFD NED ]]].
specialize (Fmono (mem V) X ltac:(auto)).
Admitted. (*
      eauto.
  + intros w wInFX.
    have M: mem (singleton_fset w) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (singleton_fset w) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    eapply BETA with (V:=D); eauto.
    eapply s_map; eauto.
Qed. *)


(* Λ⟦⟧-▪-id *)
Lemma LAMBDA_denot_APPLY_id :
  forall t ρ X,
    valid X
    -> nonempty_env ρ
    -> close (APPLY (close (LAMBDA (fun D => denot t  (D :: ρ)))) X) ≃
      denot t (X  ::  ρ).
Proof.
  intros.
  eapply @LAMBDA_APPLY_id with (F := (fun D => denot t (D :: ρ))); eauto.
  eapply denot_continuous_one; auto.
  eapply denot_monotone_one; auto.
Qed.

(* ------------------- addition works -------------------------- *)

Ltac invert_sub := 
  let h := fresh in
  match goal with 
  | [ H : mem ?V ⊆ ?X , I : ?v ∈ mem ?V |- _ ] => 
      move: (H _ I) => h ; invert_sem ; clear I
  end.
  


Lemma APPLY_ADD i j : close (APPLY (close (APPLY (close ADD) (NAT i))) (NAT j)) ≃ (NAT (i+j)).
Proof.
split.
- intros x xIn.
  unfold close in xIn.
  repeat invert_sem.
  repeat invert_sub.
  econstructor; eauto.
- intros x xIn.
  inversion xIn; subst; clear xIn.
  eapply BETA with (V := singleton_fset (v_nat j)); eauto.
  eapply BETA with (V := singleton_fset (v_nat i)); eauto.
  eapply s_ADD; eauto.
  eapply In_mem_Included. cbv; eauto.
  eapply In_mem_Included. cbv; eauto.
Qed.


(* ------------------- beta reduction is sound ----------------- *)

Definition open (t : tm) (u : tm) : tm. Admitted.

Lemma subst_denot1 :
  forall (t : tm) (u : tm) (ρ : list (P Value)),
(*    scoped t (denot u ρ :: ρ) 
    -> scoped u ρ  *)
      valid (denot u ρ)
    -> nonempty_env ρ
    -> denot t (denot u ρ :: ρ) ≃ denot (open t u) ρ.
Proof.
Admitted. 




Lemma beta_soundness : forall t u ρ, 
(*   scoped (abs t) ρ ->
  scoped u ρ ->  *)
  nonempty_env ρ ->
  valid (denot u ρ) -> 
  denot (app (abs t) u) ρ ≃ denot (open t u) ρ.
Proof.
  intros t u ρ NE V.
  simpl.
  rewrite (LAMBDA_denot_APPLY_id); auto.
  rewrite subst_denot1; eauto.
  reflexivity.
Qed.

(* ------------------------ examples --------------------------- *)

(*
Lemma In_valid_mem {A} {x : A}{f}: x ∈ mem f -> valid (mem f).
Proof. intro xIn.  destruct f.
       intro h. subst. done.
Qed.

#[export] Hint Resolve In_valid_mem : core.
*)

(* 3 + 4 is 7 *)

Definition tm_add_example := app (app add (lit 3)) (lit 4).

Lemma denot_add_example : denot tm_add_example nil ≃ (NAT 7).
Proof.
  unfold tm_add_example. simpl.
  rewrite APPLY_ADD.
  reflexivity.
Qed.

(* Identity function *)

Definition tm_Id : tm := abs (var_b 0).
 
(* begin idset *)
Definition idset : P Value := 
  fun t => match t with 
          | v_fun => True 
          | v_map INPUT OUT => OUT ∈ mem INPUT 
          | _ => False
        end.
(* end idset *)

Definition id0 := v_fun.
Example example0 : id0 ∈ idset. done. Qed.
Definition id1 := v_map (FSet (id0 :: nil) ) id0.
Example example1 : id1 ∈ idset. cbn. left. done. Qed.
Definition id2 := v_map (FSet (id0 :: id1 :: nil) ) id1.
Example example2 : id2 ∈ idset. cbn. right. left. done. Qed.
Definition id3 := v_map (FSet (id0 :: id1 :: id2 :: nil) ) id2.
Example example3 : id2 ∈ idset. cbn. right. left. done. Qed.


Lemma denot_Id1 : denot tm_Id nil ⊆ idset.
Proof.
  simpl.
  intros x xIn.
  invert_sem; cbn; auto.
Qed.

Lemma denot_Id2 : idset  ⊆  denot tm_Id nil.
Proof. 
  simpl.
  move=> x xIn.
  destruct x; try done.
  + cbn in xIn.
    eapply s_map; eauto.
Qed.


(* \f.\x. f x *)
Definition tm_eta_Id := abs (abs (app (var_b 1) (var_b 0))).

Lemma denot_eta_Id : denot tm_eta_Id nil ⊆ idset.
Proof.
  simpl.
  move=> x xIn.
  invert_sem; try done.
  invert_sem; try done.
  invert_sem; try done.
  cbn. admit. 
  cbn. admit.
Abort.

(* Example: constant function K -- \x. \y. x n *)

Definition tm_K : tm := abs (abs (var_b 1)).  

Definition K_set : P Value := 
  fun t => match t with 
          | v_map V1 w => valid_mem V1 /\
              match w with 
                | v_map V2 v => (valid_mem V2) /\ (v ∈ mem V1)
                | v_fun => True
                | _ => False
              end
          | v_fun => True
          | _ => False
        end.

Lemma denot_K2 : K_set ⊆ denot tm_K nil.
Proof.
  intros v vIn.
  unfold tm_K.
  simpl.
  destruct v; try done.
  destruct v; cbn in vIn; try done.
  all: try solve [cbn; intuition].
Qed.

Lemma denot_K1 : denot tm_K nil ⊆ K_set.
Proof.
  unfold tm_K.
  simpl.
  intros v vIn.
  inversion vIn as [V w wIn h1 h2|]. subst. clear vIn.
  inversion wIn as [V2 w2 w2In h3 h4|]. subst.
  all: try solve [cbn in *; intuition].
Qed.


(* --------------- CBV Y-combinator: Z ---------------------- *)
(* \lambda f.(\lambda x.f(\lambda v.xxv))\ (\lambda x.f(\lambda v.xxv)) *)

Definition xxv : tm := (abs (app (app (var_b 1) (var_b 0)) (var_b 0))).

Definition tm_Z : tm := 
   abs (app (abs  (app (var_b 1) xxv))
            (abs  (app (var_b 1) xxv))).


(* --------------------------------------------------------- *)

(* Delta := \x. x x *)

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).

Definition Delta_set : P Value :=
  fun t => match t with 
          | v_fun => True
          | v_map f y => 
              valid_mem f /\ 
                exists V, (v_map V y ∈ mem f) /\ 
                       (valid_mem V) /\ (mem V ⊆ mem f)
          | _ => False
        end.


Lemma denot_Delta2 : Delta_set ⊆ denot tm_Delta nil.
Proof.
  unfold tm_Delta.
  simpl.
  intros y yIn.
  destruct y; try done.
  cbn in yIn. 
  move: yIn => [VF [V [SF [VV SV]]]]. 
  cbn.
  eapply s_map; eauto.
  eapply BETA;  eauto.
Qed.

Lemma denot_Delta1 : denot tm_Delta nil ⊆ Delta_set.
Proof.
  unfold tm_Delta.
  simpl.
  intros y yIn.
  inversion yIn as [V w wIn h1 h2|]; subst; clear yIn; cbn; eauto. 
  invert_sem; cbn; eauto.
Qed.

Lemma denot_Delta : denot tm_Delta nil ≃ Delta_set.
Proof. split. eapply denot_Delta1. eapply denot_Delta2. Qed.

(* Omega := (\x. x x)(\x. x x) *)

(* For this part, we show that the denotation of an infinite looping 
   term is the empty set. 
   We do this through a proof of contradiction. An inhabitant of 
   this denotation would mean that the Delta_set contains an 
   infinite descending chain of values, each smaller than the 
   previous. However, values are inductively defined, so that 
   is impossible.
*)

Definition tm_Omega : tm := app tm_Delta tm_Delta.

(* the "size" of a value that gets smaller --- the maximum depth
   of the tree. This calculation is stable under fsets... no 
   matter what list represents an fset, the maximum depth 
   of any value in the fset will remain the same. *)

Definition max_list := List.fold_right max 0.

Fixpoint depth (v : Value) : nat :=
  match v with 
  | v_fun => 0
  | v_map (FSet VS) W => 1 + max (max_list (List.map depth VS)) (depth W)
  | _ => 0
  end.

Definition depth_fset (VS : fset Value) := 
  match VS with 
  | FSet l => max_list (List.map depth l)
  end.

Lemma depth_v_map VS w : depth (v_map VS w) =
       1 + max (depth_fset VS) (depth w).
Proof. cbn. destruct VS. done. Qed.

Lemma mem_In {A} {x:A}{XS : fset A}: x ∈ mem XS -> In_fset x XS.
Proof.
  destruct XS.
  induction l; cbn.
  - auto.
  - auto.
Qed.

Lemma In_smaller {x:Value}{XS} :
  In_fset x XS -> depth x <= depth_fset XS.
Proof.
  destruct XS.
  induction l.
  intros h. done.
  intros h. cbn. fold max_list.
  destruct h.
  subst. lia. 
  cbn in IHl.
  specialize (IHl H).
  lia. 
Qed.

Lemma depth_mem V1 V2 : 
  mem V1 ⊆ mem V2 -> 
  depth_fset V1 <= depth_fset V2.
Proof.
  intros.
  unfold depth_fset.
  destruct V1. destruct V2.
  induction l.
  - cbn. lia.
  - cbn.
    have n: mem (FSet l) ⊆ mem (FSet l0).
    { intros x xIn. eapply H; eauto. right. auto. }
    specialize (IHl n).
    specialize (H a ltac:(left; auto)).
    move: ( In_smaller (mem_In H)) => h.
    cbn in h.
    lia.
Qed.

(* description of an infinite descending chain, indexed by 
   the first number in the chain. *)
CoInductive descending_chain : nat -> Prop := 
  | dcons : 
      forall n m, m < n -> descending_chain m -> descending_chain n.

(* we can't have such a thing. *)
Lemma impossible : forall n, descending_chain n -> False.
Proof.
  induction n.
  intros h. inversion h. lia.
  intros h. inversion h. subst.
  apply IHn. destruct m. inversion H0. lia.
  inversion H0. subst.
  have LT : m0 < n. lia.
  eapply dcons with (m := m0); auto.
Qed.

CoFixpoint Delta_chain { V1 w V } : 
  v_map V1 w ∈ mem V -> 
  mem V1 ⊆ mem V ->
  mem V ⊆ Delta_set -> 
  descending_chain (depth_fset V).
Proof.  
  intros h1 h2 h3.
  move: (h3 (v_map V1 w) h1) => [_ [V2 [I2 [K2 M2]]]]. 
  apply dcons with (m := (depth_fset V1)).
  move: (In_smaller (mem_In h1)) => h4.
  rewrite depth_v_map in h4. lia.
  eapply (Delta_chain V2 w V1 I2 M2).
  transitivity (mem V); auto.
Qed.

Lemma denot_Omega : denot tm_Omega nil ⊆ (fun x => False).
Proof. intros x xIn.
       unfold tm_Omega in xIn.
       replace (denot (app tm_Delta tm_Delta) nil) with 
         (APPLY (denot tm_Delta nil) (denot tm_Delta nil)) in xIn. 2: auto.
       rewrite denot_Delta in xIn.
       inversion xIn. subst. clear xIn.
       cbv.
       destruct H as [_ [V1 [H [h1 M1]]]].       
       move: (Delta_chain H M1 H0) => chain.
       eapply impossible; eauto.
Qed.
*)

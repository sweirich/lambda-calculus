Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.List.

Require Import lc.SetsAsPredicates.
Import SetNotations.
Local Open Scope set_scope.


(* Values *)

Inductive Value : Type :=
  (* natural number *)
  | v_nat : nat -> Value

  (* one entry in a function's table *)
  | v_map : list Value -> Value -> Value

  (* trivial function value, evaluated to a value but never applied *)
  | v_fun : Value

  (* list/tuple of values *)
  | v_list : list Value -> Value

  (* dynamic type error *)
  | v_wrong : Value
.

(* 
   The default induction principle for values is not
   strong enough for lists in the v_map and v_list case. So we prove a stronger
   version below.

   Value_ind
     : forall P : Value -> Prop,
       (forall n : nat, P (v_nat n)) ->
       (forall (l : list Value) (v : Value), P v -> P (v_map l v)) ->
       P v_fun -> 
       (forall l : list Value, P (v_list l)) -> 
       P v_wrong -> 
       forall v : Value, P v 
*)

Fixpoint Value_ind' (P : Value -> Prop)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : list Value) (v : Value), Forall P l -> P v -> P (v_map l v)) 
       (f : P v_fun)
       (l : (forall l : list Value, Forall P l -> P (v_list l)))
       (w : P v_wrong) 
       (v : Value) : P v := 
  let rec := Value_ind' P n m f l w 
  in
  let fix rec_list (vs : list Value) : Forall P vs :=
    match vs with 
    | nil => Forall_nil _
    | cons w ws => @Forall_cons Value P w ws (rec w) (rec_list ws)
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

(* We do the same thing for Value_rect *)

Fixpoint Value_rec' (P : Value -> Type)
       (n : forall n : nat, P (v_nat n)) 
       (m : forall (l : list Value) (v : Value),
           ForallT P l -> P v -> P (v_map l v)) 
       (f : P v_fun)
       (l : (forall l : list Value, ForallT P l -> P (v_list l)))
       (w : P v_wrong) (v : Value) : P v := 
  let rec := Value_rec' P n m f l w 
  in
  let fix rec_list (vs : list Value) : ForallT P vs :=
    match vs with 
    | nil => ForallT_nil _
    | cons w ws => @ForallT_cons Value P w ws (rec w) (rec_list ws)
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


(* ----------------------------------------------- *)

(* Consistent values: we will model function values as a set of approximations

   But now that we have different sorts of values, those approximations should
   all agree with eachother.

   We can define this concept by first identifying the head of a value. 
   Two values will *definitely* be inconsistent if they have different heads.
   But they could have the same head if inside the value

*)

Inductive v_head := 
   h_nat  : nat -> v_head 
  | h_fun  : v_head
  | h_list : v_head
  | h_wrong : v_head 
.

Definition head (v : Value) : v_head := 
  match v with 
  | v_nat k => h_nat k
  | v_map _ _ => h_fun
  | v_fun => h_fun
  | v_list _ => h_list
  | v_wrong => h_wrong
  end.


Inductive Consistent : Value -> Value -> Prop :=
  | c_nat : forall i, Consistent (v_nat i) (v_nat i)
  | c_list : forall XS YS, Forall2 Consistent XS YS ->
      Consistent (v_list XS) (v_list YS)
  | c_wrong : Consistent v_wrong v_wrong

  | c_fun : Consistent v_fun v_fun
  | c_fun1 : forall X r, Consistent v_fun (v_map X r)
  | c_fun2 : forall X r, Consistent (v_map X r) v_fun

    (* maps that produce consistent results are consistent *)
  | c_map2 : forall X1 X2 r1 r2,
      Consistent r1 r2 -> 
      Consistent (v_map X1 r1) (v_map X2 r2)

    (* maps that don't overlap in their inputs are consistent *)
    (* note: should this be exists or forall? *)
  | c_map1 : forall X1 X2 r1 r2, 
      (exists x1 x2, List.In x1 X1 /\ List.In x2 X2 /\ Inconsistent x1 x2) ->
      Consistent (v_map X1 r1) (v_map X2 r2)

with Inconsistent : Value -> Value -> Prop :=
  | i_head : forall x y, 
      head x <> head y ->
      Inconsistent x y
  | i_list_l : forall XS YS, 
      length XS <> length YS ->
      Inconsistent (v_list XS) (v_list YS)      
  | i_list_e : forall XS YS,
      Exists2 Inconsistent XS YS ->
      Inconsistent (v_list XS) (v_list YS)
  | i_map : forall X1 X2 r1 r2,
      (forall x1 x2, List.In x1 X1 -> List.In x2 X2 -> Consistent x1 x2) ->
      Inconsistent r1 r2 ->
      Inconsistent (v_map X1 r1) (v_map X2 r2).

Hint Constructors Consistent Inconsistent : core.

(* There are two ways to compare *lists* of values for consistency:

     Pointwise - corresponding elements must be consistent
     Any - all pairs of elements from the two lists must be consistent

 *)

Definition ConsistentPointwiseList XS YS := 
  Forall2 Consistent XS YS.
Definition InconsistentPointwiseList XS YS := 
  length XS <> length YS \/ Exists2 Inconsistent XS YS.
Definition ConsistentAnyList XS YS := 
  forall x y, List.In x XS -> List.In y YS -> Consistent x y.
Definition InconsistentAnyList XS YS := 
  (exists x y, List.In x XS /\ List.In y YS /\ Inconsistent x y).



(* Two values cannot be both consistent and inconsistent. *)

Lemma Consistent_Inconsistent_disjoint : 
  forall x y, Consistent x y -> Inconsistent x y -> False.
Proof.
  intros x.
  eapply Value_ind' with (P := fun x => 
  forall y : Value, Consistent x y -> Inconsistent x y -> False).
  all: intros.
  all: try solve [inversion H; inversion H0; subst; done].
  + inversion H2; inversion H1; subst.
    all: try simpl in H3; try done.
    - inversion H9; subst. clear H9.
      eapply H0; eauto.
    - inversion H9; subst. clear H9.
    destruct H11 as [x1 [x2 [I1 [I2 ii]]]].
    specialize (H5 _ _ I1 I2).
    rewrite Forall_forall in H.
    eapply H; eauto.
  + inversion H0; inversion H1; subst. simpl in H5; try done.
    - inversion H7; subst. eauto using Forall2_length.
    - inversion H7; subst; clear H7.
      clear H1 H0. move: YS H3 H6.
      induction H; intros YS h1 h2;
        inversion h1; inversion h2; subst.  
      inversion H7; subst. eauto.
      inversion H7; subst. eauto.
Qed.

(* Determining whether two values are consistent or inconsistent 
   is decidable *)

Definition ConsistentDecidable := fun v1 => forall v2 : Value, 
                     {Consistent v1 v2} + {Inconsistent v1 v2}.



Lemma dec_any : forall XS, ForallT ConsistentDecidable XS -> forall YS, { ConsistentAnyList XS YS } + {InconsistentAnyList XS YS}.
induction XS.
- intros h. intros ys. left. intros x y h1 h2. inversion h1.
- intros h. inversion h. subst. clear h.
  intros YS. unfold ConsistentDecidable in H1.
  destruct (IHXS H2 YS).
  + induction YS. left. intros x y h1 h2. inversion h2.
    have CE: (ConsistentAnyList XS YS).
    intros x y h1 h2. 
    eapply c; eauto. simpl. eauto.
    specialize (IHYS CE). destruct IHYS.
    ++ destruct (H1 a0).       
       left. 
       { intros x y h1 h2.
         destruct h1 as [EQ|INXS]; destruct h2 as [EQ2|INYS]; subst.
         -- auto.
         -- apply c0; eauto. simpl; auto.
         -- apply c; eauto. simpl; auto.
         -- apply CE; eauto.
       } 
       right. exists a . exists a0. simpl. split; auto.
    ++ right. destruct i as [x [y [h1 [h2 h3]]]].
       exists x. exists y. simpl. eauto.

  + right. destruct i as [x1 [x2 [h1 [h2]]]].
    exists x1. exists x2. simpl. split; eauto. 
Qed.

Lemma dec_point : forall XS,  ForallT ConsistentDecidable XS -> forall YS, { ConsistentPointwiseList XS YS } + {InconsistentPointwiseList XS YS}.
Proof.  
induction XS; intros IH [|y YS].
+ left. unfold ConsistentPointwiseList. eauto.
+ right. unfold InconsistentPointwiseList. simpl; left; auto.
+ right. left; simpl; auto.
+ inversion IH; subst. 
  destruct (H1 y); destruct (IHXS H2 YS); unfold ConsistentPointwiseList in *; 
    unfold InconsistentPointwiseList in *.
  all: try solve [simpl; left; eauto].
  all: try solve [right; destruct i; simpl; right; eauto].
  right; destruct i; simpl. left; eauto. right; eauto.
Qed.  
  
Lemma dec_con : forall v1 v2, {Consistent v1 v2 } + {Inconsistent v1 v2 }.
intros v1. 
eapply Value_rec' with 
(P := fun v1 =>  forall v2 : Value, {Consistent v1 v2} + {Inconsistent v1 v2}).
all: intros.
all: destruct v2.
all: try solve [right; eapply i_head; simpl; done].
all: try solve [left; eauto].
+ destruct (Nat.eq_dec n n0). subst.
  left. eauto. right. eapply i_head; simpl. intro h.
  inversion h. subst.  done.
+ destruct (H0 v2).
  left. eapply c_map2; eauto.
  destruct (dec_any l H l0).
  right. eapply i_map; eauto.
  left. eauto.
+ destruct (dec_point l H l0).
  left; eauto.
  right. destruct i; eauto.
Qed.

Lemma DecSetList : forall XS, ForallT ConsistentDecidable XS.
intros XS. induction XS. econstructor; eauto.
econstructor; eauto. unfold ConsistentDecidable. eapply dec_con; eauto.
Qed.


(* Consistency is also reflexive *)

Definition ConsistentReflexive (x : Value) := Consistent x x.

Lemma ConsistentPointwiseList_refl : forall XS, ForallT ConsistentReflexive XS -> ConsistentPointwiseList XS XS. 
Proof.
  induction 1; unfold ConsistentPointwiseList; eauto.
Qed.

#[export] Instance Consistent_refl : Reflexive Consistent.
intro x.
eapply Value_ind' with (P := ConsistentReflexive).
all: unfold ConsistentReflexive; intros; eauto using ConsistentPointwiseList_refl.
econstructor. rewrite <- Forall_Forall2. auto.
Qed.


(* ------------------------------------------------- *)
(* Consistent sets *)

(* Two sets are consistent if all of their elements 
   are consistent. *)
Definition ConsistentSet V1 V2 := 
    forall x y, x ∈ V1 -> y ∈ V2 -> Consistent x y.


Lemma ConsistentSet_sub {X1 X2 Y1 Y2} : 
  ConsistentSet Y1 Y2 -> X1 ⊆ Y1 -> X2 ⊆ Y2 -> ConsistentSet X1 X2.
Proof.
  unfold ConsistentSet in *.
  unfold Included in *. eauto.
Qed.


(* A set of values is consistent if it is consistent 
   with itself. *)
Definition ConsistentW V := ConsistentSet V V.

Lemma ConsistentW_sub {X Y} : ConsistentW Y -> X ⊆ Y -> ConsistentW X.
Proof.
  unfold ConsistentW, ConsistentSet in *.
  unfold Included in *. eauto.
Qed.

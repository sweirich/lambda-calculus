Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.
Require Import denot.semantic_notions. 

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

(* ------------------------------------------------------- *)

Definition RET {A} (x : P A) : P (Comp (vfin A)) :=
  fun z => match z with 
          | c_multi (V :: nil) => (vmem V ⊆ x)   
          |  _ => False
        end.

(* Q: can we get rid of V <> nil ? What part of the proof breaks? *)

(* A: V must be nonempty because RET is strict. If x is ⊥ then the 
   returned Comp set should be ⊥ not c_multi [ ⊥ ] . 

   A: But, really RET should only be applied to nonempty x. Maybe 
   we shouldn't care about what happens when x is ⊥ ?

*)


Definition BIND {A B} (S : P (Comp (vfin A))) (K : P A -> P (Comp B)) : P (Comp B) :=
  fun t => 
   exists (s : Comp (vfin A)),    (* in S *)
   exists (k : vfin A -> Comp B),  (* in K, for every valid finite set in u *)
       t = bind s k          (* produces t *)
      /\ (s ∈ S)      
      /\ forall (V : vfin A),
          Comp_In V s -> (k V) ∈ K (vmem V).    

(* Above, we need V nonempty to show that m ⊆ BIND m RET  as RET is strict *)

(* ------------------------------------------------------- *)

Lemma RET_mono {A} : forall (U V : P A), 
 U ⊆ V -> RET U ⊆ RET V. 
Proof. 
    intros U V h x xIn.
    unfold Included in h.
    destruct x; simpl in *; eauto.
    destruct l as [| y t]; try done.
    destruct t; try done.
    unfold RET in *. cbn in *.
    unfold Included in xIn.
    intros x. 
    eauto.
Qed.

Lemma RET_cong {A} : forall (U V : P A), 
 U ≃ V -> RET U ≃ RET V. 
Proof. 
intros x1 y1 E1. split. eapply RET_mono. rewrite E1. reflexivity.
eapply  RET_mono. rewrite E1. reflexivity.
Qed.

#[export] Instance Proper_Included_RET {A} : Proper (Included ==> Included) 
                                               (@RET A).
unfold Proper. intros x1 y1 E1. eapply RET_mono; auto. Qed.

#[export] Instance Proper_Same_RET {A} : Proper (Same_set ==> Same_set) (@RET A).
unfold Proper. intros x1 y1 E1. eapply RET_cong; auto. Qed.

Lemma BIND_mono {A B} : forall (D1 D2 : P (Comp (vfin A))) (K1 K2 : P A -> P (Comp B)),
  D1 ⊆ D2 -> (forall x, K1 x ⊆ K2 x) ->
  BIND D1 K1 ⊆ BIND D2 K2.
Proof. 
  intros D1 D2 K1 K2 subD subK.
  unfold BIND.
  move=> x [s1 [k1 [-> [inS1 inK1]]]]. 
  exists s1. exists k1.
  repeat split; auto.
  specialize (subD _ inS1).
  intros a aIn.
  eapply subK.
  eapply inK1.
  auto.
Qed.

Lemma BIND_cong {A B} : forall (D1 D2 : P (Comp (vfin A))) (K1 K2 : P A -> P (Comp B)),
  D1 ≃ D2 -> (forall x, K1 x ≃ K2 x) ->
  BIND D1 K1 ≃ BIND D2 K2.
Proof.
intros D1 D2 K1 K2 [h1 h2] E2.
split; eapply BIND_mono; eauto; intro x; destruct (E2 x); eauto.
Qed.

#[export] Instance Proper_Included_BIND {A B} : 
  Proper (Included ==> (Logic.eq ==> Included) ==> Included) (@BIND A B).
intros x1 y1 E1 x2 y2 E2. 
eapply BIND_mono; eauto. 
Qed. 

#[export] Instance Proper_Same_BIND {A B} : Proper (Same_set ==> (Logic.eq ==> Same_set) ==> Same_set) (@BIND A B).
unfold Proper. intros x1 y1 E1 x2 y2 E2.
unfold respectful in E2.
eapply BIND_cong; eauto.
Qed.

(* ------ Computation law ---- BIND (RETURN x) k = k x ------------------- *)

Lemma bind_ret_Comp : forall {A B} (x : A) (k : A -> Comp B), 
    bind (ret x) k = k x.
Proof.
  intros.
  cbv.
  destruct (k x); auto.
  f_equal.
  eapply app_nil_r.
Qed. 

Lemma BIND_RET1 : forall {A B} (x : P A) (k : P A -> P (Comp (vfin B))), 
    monotone k ->  
    BIND (RET x) k ⊆ k x.
Proof.
  intros A B x k MK. 
  unfold BIND, RET.
  repeat split.
  intros y.
  move =>[U [k0 [h2 [h3 h4]]]]. 
  subst.
  destruct U; try done.
  destruct l; try done.
  destruct l; try done.
  cbn.
  specialize (h4 v ltac:(cbv;eauto)).
  rewrite append_Comp_nil.
  eapply MK; eauto.
Qed.

Lemma BIND_RET2 : forall {A}{B} (x : P A) (k : P A -> P (Comp (vfin B))), 
    monotone k -> 
    continuous k ->
    valid x ->
    k x ⊆ BIND (RET x) k.
Proof. 
  intros A B x k km kc vx.
  unfold continuous in kc. 
  unfold BIND, RET.
  intros y yIn.
  unfold Ensembles.In.
  have M: mem (y :: nil) ⊆ k x. intros z zIn.
  { destruct zIn; try done. subst. auto. }
  move: (kc _ vx (y :: nil) M) => [D [S1 S2]].
  exists (c_multi (D :: nil)).
  exists (fun _ => y).
  repeat split; auto.
  - cbn.
    destruct y; auto. 
    cbn. rewrite app_nil_r. auto.
  - intros v vIn.
    simpl in vIn. destruct vIn; try done.
    subst.
    eapply S2.
    eauto.
Qed.
  
Lemma BIND_RET : forall {A}{B} (x : P A) (k : P A -> P (Comp (vfin B))), 
    monotone k -> 
    continuous k ->
    valid x ->
    BIND (RET x) k ≃ k x.
Proof.
  intros.
  split.
  eapply BIND_RET1; eauto.
  eapply BIND_RET2; eauto.
Qed.

(* ------------------------------------------------------------- *)
(* monad law (right identity) *)

Lemma monad_law {A} {y : Comp A} : y = x <- y;; ret x.
Proof.
  destruct y.
  cbn. done.
  cbn. 
Admitted.

Lemma RET_BIND2 : forall {A B} (m : P (Comp (vfin A))) (k : P A -> P (Comp (vfin B))), 
    m ⊆ BIND m RET.
Proof.
  intros.
  unfold BIND, RET.
  intros y yIn.
  unfold Ensembles.In.
  exists y. exists ret.
  repeat split; auto.
  eapply monad_law.
  intros V inV.
  simpl. reflexivity.  
Qed.

(* NOTE: the opposite version is not true.

   BIND m RET may contain some a in c_multi l that is a less precise
   approximation of m. 
*)

Lemma RET_BIND1 : forall {A B} (m : P (Comp (vfin A))) (k : P A -> P (Comp (vfin B))), 
    BIND m RET ⊆ m.
Proof.
  intros.
  unfold BIND, RET.
  intros y yIn.
  unfold Ensembles.In in yIn.
  move: yIn => [u1 [k1 [h1 [h2 h3]]]].
  destruct u1; cbn in h2.
  + subst. eauto.
  + subst.
    move: h2 h3.
    induction l; intros h2 h3.
    ++ cbn. auto.
    ++ specialize (h3 a ltac:(simpl; auto)).
       destruct (k1 a) eqn:h. done.
       destruct l0; try done. destruct l0; try done.
Abort.


(* -------------------------------------------------------- *)
(* Associative law *)

   (* (m >>= g) >>= h = m >>= (\x -> g x >>= h) *)

Lemma monad_associative_law {A}{B}{C}
  {m : Comp A}{g : A -> Comp B}{h : B -> Comp C} : 
  bind (bind m g) h = bind m (fun x => bind (g x) h).
Admitted.


Lemma BIND_ASSOC1 {A}{B}{C}
  {m : P (Comp (vfin A))}
  {g : P A -> P (Comp (vfin B)) }
  {h : P B -> P (Comp (vfin C)) } : 
   monotone g -> 
   continuous g ->
  BIND (BIND m g) h ⊆ BIND m (fun x => BIND (g x) h).  
Proof.  
  intros monoG contG.
  unfold BIND.
  intros x [s1 [k1 [-> [h1 h2]]]].
  move: h1 => [s2 [k2 [-> [h3 h4]]]].
  rewrite monad_associative_law.
  exists s2. exists (fun x => y <- k2 x ;; k1 y). split. 
  auto.
  repeat split; auto.
  intros v vin.
  specialize (h4 v vin).
  exists (k2 v). exists k1. 
  repeat split; auto.
  intros v2 v2in.
  specialize (h2 v2).
  eapply h2. 
Abort. (* cannot make any more progress here. *)

Lemma BIND_ASSOC2 {A}{B}{C}
  {m : P (Comp (vfin A))}
  {g : P A -> P (Comp (vfin B)) }
  {h : P B -> P (Comp (vfin C)) } : 
  BIND m (fun x => BIND (g x) h) ⊆ BIND (BIND m g) h.
Proof.
  unfold BIND.
  intros x [s1 [k1 [-> [h1 h2]]]].
  eexists. eexists.
  repeat split.
Abort. (* This seems even less likely to be true. *)  


(* ---------------------------------------------------- *)

Section Env.

Context {Value : Type}.
Let Rho := Env (P Value).

Import EnvNotations.

Lemma RET_continuous_env {D: Rho -> (P Value)}{ρ} : 
  valid_env ρ ->
  continuous_env D ρ ->
  monotone_env D ->
  continuous_env (fun ρ => RET (D ρ)) ρ.
Proof.
  intros VE IHD mD.
  intros c cIn.
  destruct c; try done.
  destruct l; try done.
  destruct l; try done.
  destruct v.
  cbn in cIn. 
  have lemma: (exists ρ', exists _ : finite_env ρ', ρ' ⊆e ρ /\ ((mem x) ⊆ D ρ')).
  { 
    eapply continuous_In_sub; eauto.
  }
  destruct lemma as [ρ' [F' [S' h]]]. 
  exists ρ'. exists F'.
  split; auto.
Qed.  

Lemma BIND_continuous_env {A B} 
  {D : Rho -> P (Comp (vfin A))} 
  {K : Rho -> P A -> P (Comp B)} {ρ}: 
  valid_env ρ -> 
  continuous_env D ρ ->
  monotone_env D ->
  (forall v, continuous_env (fun ρ => K ρ v) ρ) ->
  (forall v, monotone_env (fun ρ => K ρ v)) ->
  continuous_env (fun ρ => (BIND (D ρ) (K ρ))) ρ. 
Proof.
  intros NE IHD mD IHK mK.
  intros c cIn.
  destruct cIn as [u [k [-> [uIn h2]]]].
  destruct (IHD u uIn) as [ ρ1 [F1 [S1 uIn1]]].
  destruct u.
  + exists ρ1. exists F1. split; auto.
    cbn. unfold BIND.
    exists c_wrong. exists k.
    repeat split. eapply uIn1.
    intros a aIn. inversion aIn.
  + have lemma :
      forall l, 
         (forall a : vfin A, Comp_In a (c_multi l) -> K ρ (vmem a) (k a)) -> 
         exists ρ', exists (_ : finite_env ρ'), 
           ρ' ⊆e ρ /\
           (forall a : vfin A, Comp_In a (c_multi l) -> K ρ' (vmem a) (k a)).
    { clear uIn ρ1 F1 S1 uIn1 l h2.
      induction l; intros h2.
      ++ exists (initial_finite_env ρ NE). eexists; repeat split; eauto.
         intros a inA. simpl in inA. done.
      ++ destruct IHl 
          as [ρ2 [F2 [S2 uIn2]]].
          { intros x xIn. apply h2. simpl. simpl in xIn. right.  auto. }
          move: (h2 a ltac:(econstructor; eauto)) => Ka.
          destruct (IHK (vmem a) _ Ka) as
            [ρ1 [F1 [S1 uIn1]]].
          have SS1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
          have SS2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
          have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
          exists (ρ1 ⊔e ρ2).
          repeat split.
          - eapply join_finite_env; eauto.    
          - eapply join_lub; eauto.
          - intros x xIn. simpl in xIn. destruct xIn. 
            subst. eapply (mK (vmem x)); try eassumption. eapply join_sub_left; auto.
            eapply (mK (vmem x)). 2: { eapply uIn2; eauto. }
            eapply join_sub_right; eauto.
    }
    destruct (lemma l h2) as 
      [ρ2 [F2 [S2 In2]]]. clear lemma.
    have SS1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have SS2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    - eapply join_finite_env; eauto.    
    - eapply join_lub; eauto.
    - exists (c_multi l). exists k.
    repeat split; eauto.
    eapply mD; try eassumption. eapply join_sub_left; auto.
    intros a aIn.
    eapply (mK (vmem a)). 2: { eapply In2; eauto. }
    eapply join_sub_right; eauto.
Qed.                 

End Env.

(* ----------------------------------------------------------------------- *)

Lemma BIND_monotone {Value A B} 
  {D : P Value -> P (Comp (vfin A))} 
  {K : P Value -> P A -> P (Comp B)}: 
  monotone D ->
  (forall v, monotone (fun x => K x v)) ->
  monotone (fun v => (BIND (D v) (K v))). 
Proof. 
  intros mD mK x y S.
  eapply BIND_mono; eauto. 
  intro z; eapply mK; auto.
Qed.
 
Lemma BIND_continuous {Value A B} 
  {D : P Value -> P (Comp (vfin A))} 
  {K : P Value -> P A -> P (Comp B)}: 
  continuous D ->
  monotone D ->
  (forall v, continuous (fun x => K x v)) ->
  (forall v, monotone (fun x => K x v)) ->
  continuous (fun v => (BIND (D v) (K v))). 
Proof.
  intros IHD mD IHK mK.
  intros w VW F SUB.
  induction F.
  - destruct VW as [v vIn].
    have VW : valid w. econstructor; eauto.
    destruct (IHD w VW nil ltac:(cbv; done)) as [D1 [IS1 OS1]]. 
    exists D1.
    repeat split; eauto.
    cbv. done.
  - destruct IHF as [D1 [IS1 OS1]]. 
    intros y yIn. eapply SUB. right. auto.
    have C: a ∈ BIND (D w)(K w). eapply SUB. left.  auto.
    destruct C as [u [k [uIn [h1 h2]]]].    
    unfold continuous in IHD.
    destruct (IHD w VW (u :: nil) ltac:(eauto)) as [D2 [IS2 OS2]]. 
    destruct u.
    + simpl in h1. subst.
      exists (vfin_Union D1 D2).
      repeat rewrite vmem_Union.
      repeat split; eauto.
      eapply union_left; auto.
      cbn.
      intros z zIn. 
      destruct zIn; subst.
      ++ exists c_wrong. exists k.
         repeat split.
         eapply mD. 2: eapply OS2; auto.
         auto.
         intros x h. inversion h.
      ++ specialize (OS1 z H).
         eapply BIND_mono.
         3: eapply OS1.
         eapply mD. auto.
         intros x y yIn.
         eapply mK. 2: eapply yIn. auto.
    + have lemma:          
      forall l, 
         (forall a : vfin A, Comp_In a (c_multi l) -> K w (vmem a) (k a)) -> 
         exists D0, (vmem D0 ⊆ w) /\
           (forall a : vfin A, Comp_In a (c_multi l) -> K (vmem D0) (vmem a) (k a)).
      { clear uIn D1 IS1 OS1 OS2 h1 h2.
        induction l0; intros h2.
        ++ exists D2. 
           repeat split; eauto.
           intros a0 a0In.
           simpl in a0In. done.
        ++ destruct IHl0 as [D3 [IS3 OS3]].
           { intros x xIn. apply h2. simpl. simpl in xIn. right. auto. }
           move: (h2 a0 ltac:(econstructor; eauto)) => Ka.
           specialize (IHK (vmem a0) w VW (k a0 :: nil)) as [D4 [IS4 OS4]].
           { rewrite <- In_Sub. auto. }
           exists (vfin_Union D3 D4).
           repeat rewrite vmem_Union.
           repeat split; eauto.
           eapply union_left; auto. 
           intros y yIn. destruct yIn.  
           subst. eapply mK. 2: eapply OS4. eapply sub_union_right. eauto.
           eapply mK. 2: eapply OS3. eapply sub_union_left. eauto.
      }
      destruct (lemma l h2) as [D3 [IS3 OS3]].
      exists (vfin_Union D1 (vfin_Union D2 D3)).
      repeat rewrite vmem_Union.
      repeat split; eauto.
      eapply union_left; auto.  eapply union_left; auto.
      intros y yIn. destruct yIn.
      ++ subst a. subst y.
         exists (c_multi l). exists k.
         repeat split; eauto.
         eapply mD. 2: eapply OS2; eauto. right. left. auto.
         intros x xIn.
         eapply mK. 2: eapply OS3; eauto.
         right. right. auto.
      ++ eapply BIND_mono. 3: eapply OS1; auto.
         eapply mD. left. auto.
         intros v z zIn. eapply mK. 2: eapply zIn. left. auto.
Qed.

Lemma RET_monotone  {Value A} {D : P Value -> P A } :
  monotone D -> monotone (fun v : P Value => RET (D v)).
Proof. intros mD x y S. eapply RET_mono; eauto. Qed.


Lemma RET_continuous {Value A} {D : P Value -> P A } :
  continuous D -> monotone D -> continuous (fun v : P Value => RET (D v)).
Proof.
  intros IHD mD.
  intros w VW F SUB.
  induction F.
  - destruct (IHD w VW nil ltac:(cbv; done)) as [D1 [IS1 OS1]].
    exists D1.
    repeat split; eauto.
    cbv. done.
  - destruct IHF as [D1 [IS1 OS1]].
    intros y yIn. eapply SUB. right. auto.
    have C: a ∈ RET (D w). eapply SUB. left.  auto.
    destruct a; try done.
    destruct l; try done.
    destruct l; try done.
    cbn in C.
    unfold continuous in IHD.
    destruct v as [l NE]. simpl in C.
    destruct (IHD w VW l ltac:(eauto)) as [D2 [IS2 OS2]].
    exists (vfin_Union D1 D2).
    rewrite vmem_Union.
    repeat split; eauto.
    eapply union_left; eauto.
    intros y yIn. 
    destruct yIn.
    ++ subst.
       cbn. intros z zIn. specialize (OS2 z zIn). 
       eapply mD. 2: eapply OS2. eauto.
    ++ specialize (OS1 y H).
       eapply RET_mono. 2: eapply OS1. auto.
Qed.



(* generated by Ott 0.33, locally-nameless lngen from: ./lc.ott *)
Require Import Metalib.Metatheory.
Require Export Metalib.LibLNgen. 

(** syntax *)
Definition tmvar : Set := var. (*r variables *)
Definition const : Set := nat.

Inductive tm : Set :=  (*r terms *)
 | ext (a:const)
 | let_ (t:tm) (u:tm) (*r let *)
 | var_b (_:nat) (*r variables *)
 | var_f (x:tmvar) (*r variables *)
 | abs (t:tm) (*r abstractions *)
 | app (t:tm) (u:tm) (*r function application *).

Definition relation : Type := tm -> tm -> Prop.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
Definition is_v_of_tm (t5:tm) : Prop :=
  match t5 with
  | (ext a) => False
  | (let_ t u) => False
  | (var_b nat) => False
  | (var_f x) => False
  | (abs t) => (True)
  | (app t u) => False
end.

(** arities *)
(** opening up abstractions *)
Fixpoint open_tm_wrt_tm_rec (k:nat) (t5:tm) (t_6:tm) {struct t_6}: tm :=
  match t_6 with
  | (ext a) => ext a
  | (let_ t u) => let_ (open_tm_wrt_tm_rec k t5 t) (open_tm_wrt_tm_rec (S k) t5 u)
  | (var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_b nat
        | inleft (right _) => t5
        | inright _ => var_b (nat - 1)
      end
  | (var_f x) => var_f x
  | (abs t) => abs (open_tm_wrt_tm_rec (S k) t5 t)
  | (app t u) => app (open_tm_wrt_tm_rec k t5 t) (open_tm_wrt_tm_rec k t5 u)
end.

Definition open_tm_wrt_tm t5 t_6 := open_tm_wrt_tm_rec 0 t_6 t5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_tm *)
Inductive lc_tm : tm -> Prop :=    (* defn lc_tm *)
 | lc_ext : forall (a:const),
     (lc_tm (ext a))
 | lc_let_ : forall (t u:tm),
     (lc_tm t) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm u (var_f x) )  )  ->
     (lc_tm (let_ t u))
 | lc_var_f : forall (x:tmvar),
     (lc_tm (var_f x))
 | lc_abs : forall (t:tm),
      ( forall x , lc_tm  ( open_tm_wrt_tm t (var_f x) )  )  ->
     (lc_tm (abs t))
 | lc_app : forall (t u:tm),
     (lc_tm t) ->
     (lc_tm u) ->
     (lc_tm (app t u)).
(** free variables *)
Fixpoint fv_tm (t5:tm) : vars :=
  match t5 with
  | (ext a) => {}
  | (let_ t u) => (fv_tm t) \u (fv_tm u)
  | (var_b nat) => {}
  | (var_f x) => {{x}}
  | (abs t) => (fv_tm t)
  | (app t u) => (fv_tm t) \u (fv_tm u)
end.

(** substitutions *)
Fixpoint subst_tm (t5:tm) (x5:tmvar) (t_6:tm) {struct t_6} : tm :=
  match t_6 with
  | (ext a) => ext a
  | (let_ t u) => let_ (subst_tm t5 x5 t) (subst_tm t5 x5 u)
  | (var_b nat) => var_b nat
  | (var_f x) => (if eq_var x x5 then t5 else (var_f x))
  | (abs t) => abs (subst_tm t5 x5 t)
  | (app t u) => app (subst_tm t5 x5 t) (subst_tm t5 x5 u)
end.


(** definitions *)

(* defns JBeta *)
Inductive beta : tm -> tm -> Prop :=    (* defn beta *)
 | beta_reduct : forall (t u:tm),
     lc_tm (abs t) ->
     lc_tm u ->
     beta (app  ( (abs t) )  u)  (open_tm_wrt_tm t u ) .

(* defns JEta *)
Inductive eta : tm -> tm -> Prop :=    (* defn eta *)
 | eta_reduct : forall (L:vars) (t' t:tm),
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm t' (var_f x) )  = (app t (var_f x))  )  ->
     eta (abs t') t.

(* defns JBetaEta *)
Inductive betaeta : tm -> tm -> Prop :=    (* defn betaeta *)
 | eta_beta : forall (t u:tm),
     beta t u ->
     betaeta t u
 | eta_eta : forall (t u:tm),
     eta t u ->
     betaeta t u.

(* defns JGen *)
Inductive compatible_closure : relation -> tm -> tm -> Prop :=    (* defn compatible_closure *)
 | cc_rel : forall (R:relation) (t u:tm),
      R t u  ->
     compatible_closure R t u
 | cc_abs : forall (L:vars) (R:relation) (t u:tm),
      ( forall x , x \notin  L  -> compatible_closure R  ( open_tm_wrt_tm t (var_f x) )   ( open_tm_wrt_tm u (var_f x) )  )  ->
     compatible_closure R (abs t) (abs u)
 | cc_app1 : forall (R:relation) (t u t':tm),
     lc_tm u ->
     compatible_closure R t t' ->
     compatible_closure R (app t u) (app t' u)
 | cc_app2 : forall (R:relation) (t u u':tm),
     lc_tm t ->
     compatible_closure R u u' ->
     compatible_closure R (app t u) (app t u').

(* defns JRC *)
Inductive refl_closure : relation -> tm -> tm -> Prop :=    (* defn refl_closure *)
 | r_rel : forall (R:relation) (t u:tm),
      R t u  ->
     refl_closure R t u
 | r_refl : forall (R:relation) (t:tm),
     lc_tm t ->
     refl_closure R t t.

(* defns JTC *)
Inductive trans_closure : relation -> tm -> tm -> Prop :=    (* defn trans_closure *)
 | t_rel : forall (R:relation) (t u:tm),
      R t u  ->
     trans_closure R t u
 | t_trans : forall (R:relation) (t1 t3 t2:tm),
     trans_closure R t1 t2 ->
     trans_closure R t2 t3 ->
     trans_closure R t1 t3.

(* defns JRTC *)
Inductive refl_trans_closure : relation -> tm -> tm -> Prop :=    (* defn refl_trans_closure *)
 | rt_rel : forall (R:relation) (t u:tm),
      R t u  ->
     refl_trans_closure R t u
 | rt_refl : forall (R:relation) (t:tm),
     lc_tm t ->
     refl_trans_closure R t t
 | rt_trans : forall (R:relation) (t1 t3 t2:tm),
     refl_trans_closure R t1 t2 ->
     refl_trans_closure R t2 t3 ->
     refl_trans_closure R t1 t3.

(* defns JSTC *)
Inductive sym_trans_closure : relation -> tm -> tm -> Prop :=    (* defn sym_trans_closure *)
 | st_rel : forall (R:relation) (t u:tm),
      R t u  ->
     sym_trans_closure R t u
 | st_sym : forall (R:relation) (t u:tm),
     sym_trans_closure R u t ->
     sym_trans_closure R t u
 | st_trans : forall (R:relation) (t1 t3 t2:tm),
     sym_trans_closure R t1 t2 ->
     sym_trans_closure R t2 t3 ->
     sym_trans_closure R t1 t3.

(* defns JPar *)
Inductive parallel : tm -> tm -> Prop :=    (* defn parallel *)
 | p_beta : forall (t u t' u':tm),
     parallel t (abs t') ->
     parallel u u' ->
     parallel (app t u)  (open_tm_wrt_tm t' u' ) 
 | p_var : forall (x:tmvar),
     parallel (var_f x) (var_f x)
 | p_abs : forall (L:vars) (t t':tm),
      ( forall x , x \notin  L  -> parallel  ( open_tm_wrt_tm t (var_f x) )   ( open_tm_wrt_tm t' (var_f x) )  )  ->
     parallel (abs t) (abs t')
 | p_app : forall (t u t' u':tm),
     parallel t t' ->
     parallel u u' ->
     parallel (app t u) (app t' u').

(* defns JOp *)
Inductive Step : tm -> tm -> Prop :=    (* defn Step *)
 | S_app : forall (t u t':tm),
     lc_tm u ->
     Step t t' ->
     Step (app t u) (app t' t)
 | S_beta : forall (t u:tm),
     lc_tm (abs t) ->
     lc_tm u ->
     Step (app  ( (abs t) )  u)  (open_tm_wrt_tm t u ) .

(* defns JOpV *)
Inductive StepV : tm -> tm -> Prop :=    (* defn StepV *)
 | SV_app1 : forall (t u t':tm),
     lc_tm u ->
     StepV t t' ->
     StepV (app t u) (app t' t)
 | SV_app2 : forall (u u' v5:tm),
     is_v_of_tm v5 ->
     is_v_of_tm v5 ->
     lc_tm v5 ->
     StepV u u' ->
     StepV (app v5 u) (app v5 u')
 | SV_betav : forall (t v5:tm),
     is_v_of_tm v5 ->
     is_v_of_tm v5 ->
     lc_tm (abs t) ->
     lc_tm v5 ->
     StepV (app  ( (abs t) )  v5)  (open_tm_wrt_tm t v5 ) .

(* defns JEval *)
Inductive Eval : tm -> tm -> Prop :=    (* defn Eval *)
 | E_beta : forall (t u v5 t':tm),
     is_v_of_tm v5 ->
     Eval t (abs t') ->
     Eval  (open_tm_wrt_tm t' u )  v5 ->
     Eval (app t u) v5.

(* defns JEq *)
Inductive conversion : tm -> tm -> Prop :=    (* defn conversion *)
 | eq_beta : forall (t u:tm),
     lc_tm (abs t) ->
     lc_tm u ->
     conversion (app  ( (abs t) )  u)  (open_tm_wrt_tm t u ) 
 | eq_refl : forall (t:tm),
     lc_tm t ->
     conversion t t
 | eq_sym : forall (t u:tm),
     conversion u t ->
     conversion t u
 | eq_trans : forall (t1 t3 t2:tm),
     conversion t1 t2 ->
     conversion t2 t3 ->
     conversion t1 t3
 | eq_app1 : forall (t u t':tm),
     lc_tm u ->
     conversion t t' ->
     conversion (app t u) (app t' u)
 | eq_app2 : forall (t u u':tm),
     lc_tm t ->
     conversion u u' ->
     conversion (app t u) (app t u')
 | eq_abs : forall (L:vars) (t t':tm),
      ( forall x , x \notin  L  -> conversion  ( open_tm_wrt_tm t (var_f x) )   ( open_tm_wrt_tm t' (var_f x) )  )  ->
     conversion (abs t) (abs t').

(* defns JRed *)
Inductive full_reduction : tm -> tm -> Prop :=    (* defn full_reduction *)
 | F_beta : forall (t u:tm),
     lc_tm (abs t) ->
     lc_tm u ->
     full_reduction (app  ( (abs t) )  u)  (open_tm_wrt_tm t u ) 
 | F_abs : forall (L:vars) (t t':tm),
      ( forall x , x \notin  L  -> full_reduction  ( open_tm_wrt_tm t (var_f x) )   ( open_tm_wrt_tm t' (var_f x) )  )  ->
     full_reduction (abs t) (abs t')
 | F_app1 : forall (t u t':tm),
     lc_tm u ->
     full_reduction t t' ->
     full_reduction (app t u) (app t' u)
 | F_app2 : forall (t u u':tm),
     lc_tm t ->
     lc_tm u' ->
     full_reduction u u ->
     full_reduction (app t u) (app t u').

(* defns Jredex *)
Inductive redex : relation -> tm -> Prop :=    (* defn redex *)
 | redex_def : forall (R:relation) (t u:tm),
      R t u  ->
     redex R t.

(* defns Jterminal *)
Inductive terminal : relation -> tm -> Prop :=    (* defn terminal *)
 | terminal_def : forall (R:relation) (t u:tm),
      (forall  u ,   not (  R t u  )  )  ->
     terminal R t.

(* defns JNF *)
Inductive nf : relation -> tm -> Prop :=    (* defn nf *)
 | nf_var : forall (R:relation) (x:tmvar),
      not ( redex R (var_f x) )  ->
     nf R (var_f x)
 | nf_abs : forall (L:vars) (R:relation) (t:tm),
      ( forall x , x \notin  L  -> nf R  ( open_tm_wrt_tm t (var_f x) )  )  ->
      not ( redex R  ( (abs t) )  )  ->
     nf R  ( (abs t) ) 
 | nf_app : forall (R:relation) (t u:tm),
     nf R t ->
     nf R u ->
      not ( redex R  ( (app t u) )  )  ->
     nf R  ( (app t u) ) .


(** infrastructure *)
Hint Constructors beta eta betaeta compatible_closure refl_closure trans_closure refl_trans_closure sym_trans_closure parallel Step StepV Eval conversion full_reduction redex terminal nf lc_tm : core.



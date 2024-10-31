Require Export fintype.




Section Op.
Inductive Op  : Type :=
  | opAdd : Op 
  | opGt : Op 
  | opInt : Op .

Lemma congr_opAdd  : opAdd  = opAdd  .
Proof. congruence. Qed.

Lemma congr_opGt  : opGt  = opGt  .
Proof. congruence. Qed.

Lemma congr_opInt  : opInt  = opInt  .
Proof. congruence. Qed.

End Op.

Section ValExp.
Inductive Val (nVal : nat) : Type :=
  | var_Val : (fin) (nVal) -> Val (nVal)
  | Int : nat   -> Val (nVal)
  | Prim : Op   -> Val (nVal)
  | Tuple : list (Val  (nVal)) -> Val (nVal)
  | Lam : Exp  ((S) nVal) -> Val (nVal)
 with Exp (nVal : nat) : Type :=
  | Ret : Val  (nVal) -> Exp (nVal)
  | App : Val  (nVal) -> Val  (nVal) -> Exp (nVal)
  | Seq : Exp  (nVal) -> Exp  (nVal) -> Exp (nVal)
  | Unify : Val  (nVal) -> Exp  (nVal) -> Exp (nVal)
  | Exists : Exp  ((S) nVal) -> Exp (nVal)
  | Or : Exp  (nVal) -> Exp  (nVal) -> Exp (nVal)
  | Fail : Exp (nVal)
  | One : Exp  (nVal) -> Exp (nVal)
  | All : Exp  (nVal) -> Exp (nVal).

Lemma congr_Int { mVal : nat } { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : Int (mVal) s0 = Int (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_Prim { mVal : nat } { s0 : Op   } { t0 : Op   } (H1 : s0 = t0) : Prim (mVal) s0 = Prim (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_Tuple { mVal : nat } { s0 : list (Val  (mVal)) } { t0 : list (Val  (mVal)) } (H1 : s0 = t0) : Tuple (mVal) s0 = Tuple (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_Lam { mVal : nat } { s0 : Exp  ((S) mVal) } { t0 : Exp  ((S) mVal) } (H1 : s0 = t0) : Lam (mVal) s0 = Lam (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_Ret { mVal : nat } { s0 : Val  (mVal) } { t0 : Val  (mVal) } (H1 : s0 = t0) : Ret (mVal) s0 = Ret (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_App { mVal : nat } { s0 : Val  (mVal) } { s1 : Val  (mVal) } { t0 : Val  (mVal) } { t1 : Val  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : App (mVal) s0 s1 = App (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Seq { mVal : nat } { s0 : Exp  (mVal) } { s1 : Exp  (mVal) } { t0 : Exp  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : Seq (mVal) s0 s1 = Seq (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Unify { mVal : nat } { s0 : Val  (mVal) } { s1 : Exp  (mVal) } { t0 : Val  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : Unify (mVal) s0 s1 = Unify (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Exists { mVal : nat } { s0 : Exp  ((S) mVal) } { t0 : Exp  ((S) mVal) } (H1 : s0 = t0) : Exists (mVal) s0 = Exists (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_Or { mVal : nat } { s0 : Exp  (mVal) } { s1 : Exp  (mVal) } { t0 : Exp  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : Or (mVal) s0 s1 = Or (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Fail { mVal : nat } : Fail (mVal) = Fail (mVal) .
Proof. congruence. Qed.

Lemma congr_One { mVal : nat } { s0 : Exp  (mVal) } { t0 : Exp  (mVal) } (H1 : s0 = t0) : One (mVal) s0 = One (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_All { mVal : nat } { s0 : Exp  (mVal) } { t0 : Exp  (mVal) } (H1 : s0 = t0) : All (mVal) s0 = All (mVal) t0 .
Proof. congruence. Qed.

Definition upRen_Val_Val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (s : Val (mVal)) : Val (nVal) :=
    match s return Val (nVal) with
    | var_Val (_) s => (var_Val (nVal)) (xiVal s)
    | Int (_) s0 => Int (nVal) ((fun x => x) s0)
    | Prim (_) s0 => Prim (nVal) ((fun x => x) s0)
    | Tuple (_) s0 => Tuple (nVal) ((list_map (ren_Val xiVal)) s0)
    | Lam (_) s0 => Lam (nVal) ((ren_Exp (upRen_Val_Val xiVal)) s0)
    end
 with ren_Exp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (s : Exp (mVal)) : Exp (nVal) :=
    match s return Exp (nVal) with
    | Ret (_) s0 => Ret (nVal) ((ren_Val xiVal) s0)
    | App (_) s0 s1 => App (nVal) ((ren_Val xiVal) s0) ((ren_Val xiVal) s1)
    | Seq (_) s0 s1 => Seq (nVal) ((ren_Exp xiVal) s0) ((ren_Exp xiVal) s1)
    | Unify (_) s0 s1 => Unify (nVal) ((ren_Val xiVal) s0) ((ren_Exp xiVal) s1)
    | Exists (_) s0 => Exists (nVal) ((ren_Exp (upRen_Val_Val xiVal)) s0)
    | Or (_) s0 s1 => Or (nVal) ((ren_Exp xiVal) s0) ((ren_Exp xiVal) s1)
    | Fail (_)  => Fail (nVal)
    | One (_) s0 => One (nVal) ((ren_Exp xiVal) s0)
    | All (_) s0 => All (nVal) ((ren_Exp xiVal) s0)
    end.

Definition up_Val_Val { m : nat } { nVal : nat } (sigma : (fin) (m) -> Val (nVal)) : (fin) ((S) (m)) -> Val ((S) nVal) :=
  (scons) ((var_Val ((S) nVal)) (var_zero)) ((funcomp) (ren_Val (shift)) sigma).

Fixpoint subst_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : Val (mVal)) : Val (nVal) :=
    match s return Val (nVal) with
    | var_Val (_) s => sigmaVal s
    | Int (_) s0 => Int (nVal) ((fun x => x) s0)
    | Prim (_) s0 => Prim (nVal) ((fun x => x) s0)
    | Tuple (_) s0 => Tuple (nVal) ((list_map (subst_Val sigmaVal)) s0)
    | Lam (_) s0 => Lam (nVal) ((subst_Exp (up_Val_Val sigmaVal)) s0)
    end
 with subst_Exp { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : Exp (mVal)) : Exp (nVal) :=
    match s return Exp (nVal) with
    | Ret (_) s0 => Ret (nVal) ((subst_Val sigmaVal) s0)
    | App (_) s0 s1 => App (nVal) ((subst_Val sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | Seq (_) s0 s1 => Seq (nVal) ((subst_Exp sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Unify (_) s0 s1 => Unify (nVal) ((subst_Val sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Exists (_) s0 => Exists (nVal) ((subst_Exp (up_Val_Val sigmaVal)) s0)
    | Or (_) s0 s1 => Or (nVal) ((subst_Exp sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Fail (_)  => Fail (nVal)
    | One (_) s0 => One (nVal) ((subst_Exp sigmaVal) s0)
    | All (_) s0 => All (nVal) ((subst_Exp sigmaVal) s0)
    end.

Definition upId_Val_Val { mVal : nat } (sigma : (fin) (mVal) -> Val (mVal)) (Eq : forall x, sigma x = (var_Val (mVal)) x) : forall x, (up_Val_Val sigma) x = (var_Val ((S) mVal)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_Val { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : Val (mVal)) : subst_Val sigmaVal s = s :=
    match s return subst_Val sigmaVal s = s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_id (idSubst_Val sigmaVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((idSubst_Exp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    end
 with idSubst_Exp { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : Exp (mVal)) : subst_Exp sigmaVal s = s :=
    match s return subst_Exp sigmaVal s = s with
    | Ret (_) s0 => congr_Ret ((idSubst_Val sigmaVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_Val sigmaVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((idSubst_Exp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((idSubst_Exp sigmaVal EqVal) s0)
    | All (_) s0 => congr_All ((idSubst_Exp sigmaVal EqVal) s0)
    end.

Definition upExtRen_Val_Val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_Val_Val xi) x = (upRen_Val_Val zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (zetaVal : (fin) (mVal) -> (fin) (nVal)) (EqVal : forall x, xiVal x = zetaVal x) (s : Val (mVal)) : ren_Val xiVal s = ren_Val zetaVal s :=
    match s return ren_Val xiVal s = ren_Val zetaVal s with
    | var_Val (_) s => (ap) (var_Val (nVal)) (EqVal s)
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_ext (extRen_Val xiVal zetaVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((extRen_Exp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s0)
    end
 with extRen_Exp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (zetaVal : (fin) (mVal) -> (fin) (nVal)) (EqVal : forall x, xiVal x = zetaVal x) (s : Exp (mVal)) : ren_Exp xiVal s = ren_Exp zetaVal s :=
    match s return ren_Exp xiVal s = ren_Exp zetaVal s with
    | Ret (_) s0 => congr_Ret ((extRen_Val xiVal zetaVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((extRen_Val xiVal zetaVal EqVal) s0) ((extRen_Val xiVal zetaVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((extRen_Exp xiVal zetaVal EqVal) s0) ((extRen_Exp xiVal zetaVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((extRen_Val xiVal zetaVal EqVal) s0) ((extRen_Exp xiVal zetaVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((extRen_Exp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((extRen_Exp xiVal zetaVal EqVal) s0) ((extRen_Exp xiVal zetaVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((extRen_Exp xiVal zetaVal EqVal) s0)
    | All (_) s0 => congr_All ((extRen_Exp xiVal zetaVal EqVal) s0)
    end.

Definition upExt_Val_Val { m : nat } { nVal : nat } (sigma : (fin) (m) -> Val (nVal)) (tau : (fin) (m) -> Val (nVal)) (Eq : forall x, sigma x = tau x) : forall x, (up_Val_Val sigma) x = (up_Val_Val tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : Val (mVal)) : subst_Val sigmaVal s = subst_Val tauVal s :=
    match s return subst_Val sigmaVal s = subst_Val tauVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_ext (ext_Val sigmaVal tauVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((ext_Exp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    end
 with ext_Exp { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : Exp (mVal)) : subst_Exp sigmaVal s = subst_Exp tauVal s :=
    match s return subst_Exp sigmaVal s = subst_Exp tauVal s with
    | Ret (_) s0 => congr_Ret ((ext_Val sigmaVal tauVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_Val sigmaVal tauVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((ext_Exp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((ext_Exp sigmaVal tauVal EqVal) s0)
    | All (_) s0 => congr_All ((ext_Exp sigmaVal tauVal EqVal) s0)
    end.

Definition up_ren_ren_Val_Val { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_Val_Val tau) (upRen_Val_Val xi)) x = (upRen_Val_Val theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (rhoVal : (fin) (mVal) -> (fin) (lVal)) (EqVal : forall x, ((funcomp) zetaVal xiVal) x = rhoVal x) (s : Val (mVal)) : ren_Val zetaVal (ren_Val xiVal s) = ren_Val rhoVal s :=
    match s return ren_Val zetaVal (ren_Val xiVal s) = ren_Val rhoVal s with
    | var_Val (_) s => (ap) (var_Val (lVal)) (EqVal s)
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_comp (compRenRen_Val xiVal zetaVal rhoVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((compRenRen_Exp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s0)
    end
 with compRenRen_Exp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (rhoVal : (fin) (mVal) -> (fin) (lVal)) (EqVal : forall x, ((funcomp) zetaVal xiVal) x = rhoVal x) (s : Exp (mVal)) : ren_Exp zetaVal (ren_Exp xiVal s) = ren_Exp rhoVal s :=
    match s return ren_Exp zetaVal (ren_Exp xiVal s) = ren_Exp rhoVal s with
    | Ret (_) s0 => congr_Ret ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((compRenRen_Exp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s0)
    | All (_) s0 => congr_All ((compRenRen_Exp xiVal zetaVal rhoVal EqVal) s0)
    end.

Definition up_ren_subst_Val_Val { k : nat } { l : nat } { mVal : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> Val (mVal)) (theta : (fin) (k) -> Val (mVal)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_Val_Val tau) (upRen_Val_Val xi)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) tauVal xiVal) x = thetaVal x) (s : Val (mVal)) : subst_Val tauVal (ren_Val xiVal s) = subst_Val thetaVal s :=
    match s return subst_Val tauVal (ren_Val xiVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_comp (compRenSubst_Val xiVal tauVal thetaVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((compRenSubst_Exp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compRenSubst_Exp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) tauVal xiVal) x = thetaVal x) (s : Exp (mVal)) : subst_Exp tauVal (ren_Exp xiVal s) = subst_Exp thetaVal s :=
    match s return subst_Exp tauVal (ren_Exp xiVal s) = subst_Exp thetaVal s with
    | Ret (_) s0 => congr_Ret ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((compRenSubst_Exp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s0)
    | All (_) s0 => congr_All ((compRenSubst_Exp xiVal tauVal thetaVal EqVal) s0)
    end.

Definition up_subst_ren_Val_Val { k : nat } { lVal : nat } { mVal : nat } (sigma : (fin) (k) -> Val (lVal)) (zetaVal : (fin) (lVal) -> (fin) (mVal)) (theta : (fin) (k) -> Val (mVal)) (Eq : forall x, ((funcomp) (ren_Val zetaVal) sigma) x = theta x) : forall x, ((funcomp) (ren_Val (upRen_Val_Val zetaVal)) (up_Val_Val sigma)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_Val (shift) (upRen_Val_Val zetaVal) ((funcomp) (shift) zetaVal) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_Val zetaVal (shift) ((funcomp) (shift) zetaVal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (ren_Val zetaVal) sigmaVal) x = thetaVal x) (s : Val (mVal)) : ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val thetaVal s :=
    match s return ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_comp (compSubstRen_Val sigmaVal zetaVal thetaVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((compSubstRen_Exp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compSubstRen_Exp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (ren_Val zetaVal) sigmaVal) x = thetaVal x) (s : Exp (mVal)) : ren_Exp zetaVal (subst_Exp sigmaVal s) = subst_Exp thetaVal s :=
    match s return ren_Exp zetaVal (subst_Exp sigmaVal s) = subst_Exp thetaVal s with
    | Ret (_) s0 => congr_Ret ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((compSubstRen_Exp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s0)
    | All (_) s0 => congr_All ((compSubstRen_Exp sigmaVal zetaVal thetaVal EqVal) s0)
    end.

Definition up_subst_subst_Val_Val { k : nat } { lVal : nat } { mVal : nat } (sigma : (fin) (k) -> Val (lVal)) (tauVal : (fin) (lVal) -> Val (mVal)) (theta : (fin) (k) -> Val (mVal)) (Eq : forall x, ((funcomp) (subst_Val tauVal) sigma) x = theta x) : forall x, ((funcomp) (subst_Val (up_Val_Val tauVal)) (up_Val_Val sigma)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_Val (shift) (up_Val_Val tauVal) ((funcomp) (up_Val_Val tauVal) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_Val tauVal (shift) ((funcomp) (ren_Val (shift)) tauVal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : Val (mVal)) : subst_Val tauVal (subst_Val sigmaVal s) = subst_Val thetaVal s :=
    match s return subst_Val tauVal (subst_Val sigmaVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_comp (compSubstSubst_Val sigmaVal tauVal thetaVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((compSubstSubst_Exp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compSubstSubst_Exp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : Exp (mVal)) : subst_Exp tauVal (subst_Exp sigmaVal s) = subst_Exp thetaVal s :=
    match s return subst_Exp tauVal (subst_Exp sigmaVal s) = subst_Exp thetaVal s with
    | Ret (_) s0 => congr_Ret ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((compSubstSubst_Exp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0)
    | All (_) s0 => congr_All ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0)
    end.

Definition rinstInst_up_Val_Val { m : nat } { nVal : nat } (xi : (fin) (m) -> (fin) (nVal)) (sigma : (fin) (m) -> Val (nVal)) (Eq : forall x, ((funcomp) (var_Val (nVal)) xi) x = sigma x) : forall x, ((funcomp) (var_Val ((S) nVal)) (upRen_Val_Val xi)) x = (up_Val_Val sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (sigmaVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, ((funcomp) (var_Val (nVal)) xiVal) x = sigmaVal x) (s : Val (mVal)) : ren_Val xiVal s = subst_Val sigmaVal s :=
    match s return ren_Val xiVal s = subst_Val sigmaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple ((list_ext (rinst_inst_Val xiVal sigmaVal EqVal)) s0)
    | Lam (_) s0 => congr_Lam ((rinst_inst_Exp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s0)
    end
 with rinst_inst_Exp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (sigmaVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, ((funcomp) (var_Val (nVal)) xiVal) x = sigmaVal x) (s : Exp (mVal)) : ren_Exp xiVal s = subst_Exp sigmaVal s :=
    match s return ren_Exp xiVal s = subst_Exp sigmaVal s with
    | Ret (_) s0 => congr_Ret ((rinst_inst_Val xiVal sigmaVal EqVal) s0)
    | App (_) s0 s1 => congr_App ((rinst_inst_Val xiVal sigmaVal EqVal) s0) ((rinst_inst_Val xiVal sigmaVal EqVal) s1)
    | Seq (_) s0 s1 => congr_Seq ((rinst_inst_Exp xiVal sigmaVal EqVal) s0) ((rinst_inst_Exp xiVal sigmaVal EqVal) s1)
    | Unify (_) s0 s1 => congr_Unify ((rinst_inst_Val xiVal sigmaVal EqVal) s0) ((rinst_inst_Exp xiVal sigmaVal EqVal) s1)
    | Exists (_) s0 => congr_Exists ((rinst_inst_Exp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s0)
    | Or (_) s0 s1 => congr_Or ((rinst_inst_Exp xiVal sigmaVal EqVal) s0) ((rinst_inst_Exp xiVal sigmaVal EqVal) s1)
    | Fail (_)  => congr_Fail 
    | One (_) s0 => congr_One ((rinst_inst_Exp xiVal sigmaVal EqVal) s0)
    | All (_) s0 => congr_All ((rinst_inst_Exp xiVal sigmaVal EqVal) s0)
    end.

Lemma rinstInst_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) : ren_Val xiVal = subst_Val ((funcomp) (var_Val (nVal)) xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Val xiVal (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_Exp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) : ren_Exp xiVal = subst_Exp ((funcomp) (var_Val (nVal)) xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Exp xiVal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_Val { mVal : nat } : subst_Val (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Val (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_Exp { mVal : nat } : subst_Exp (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Exp (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_Val { mVal : nat } : @ren_Val (mVal) (mVal) (id) = id .
Proof. exact ((eq_trans) (rinstInst_Val ((id) (_))) instId_Val). Qed.

Lemma rinstId_Exp { mVal : nat } : @ren_Exp (mVal) (mVal) (id) = id .
Proof. exact ((eq_trans) (rinstInst_Exp ((id) (_))) instId_Exp). Qed.

Lemma varL_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) : (funcomp) (subst_Val sigmaVal) (var_Val (mVal)) = sigmaVal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) : (funcomp) (ren_Val xiVal) (var_Val (mVal)) = (funcomp) (var_Val (nVal)) xiVal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Val (mVal)) : subst_Val tauVal (subst_Val sigmaVal s) = subst_Val ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_Val sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp_Exp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Exp (mVal)) : subst_Exp tauVal (subst_Exp sigmaVal s) = subst_Exp ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_Exp sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Val tauVal) (subst_Val sigmaVal) = subst_Val ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Val sigmaVal tauVal n)). Qed.

Lemma compComp'_Exp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Exp tauVal) (subst_Exp sigmaVal) = subst_Exp ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Exp sigmaVal tauVal n)). Qed.

Lemma compRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Val (mVal)) : ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val ((funcomp) (ren_Val zetaVal) sigmaVal) s .
Proof. exact (compSubstRen_Val sigmaVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma compRen_Exp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Exp (mVal)) : ren_Exp zetaVal (subst_Exp sigmaVal s) = subst_Exp ((funcomp) (ren_Val zetaVal) sigmaVal) s .
Proof. exact (compSubstRen_Exp sigmaVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Val zetaVal) (subst_Val sigmaVal) = subst_Val ((funcomp) (ren_Val zetaVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Val sigmaVal zetaVal n)). Qed.

Lemma compRen'_Exp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Exp zetaVal) (subst_Exp sigmaVal) = subst_Exp ((funcomp) (ren_Val zetaVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Exp sigmaVal zetaVal n)). Qed.

Lemma renComp_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Val (mVal)) : subst_Val tauVal (ren_Val xiVal s) = subst_Val ((funcomp) tauVal xiVal) s .
Proof. exact (compRenSubst_Val xiVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma renComp_Exp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Exp (mVal)) : subst_Exp tauVal (ren_Exp xiVal s) = subst_Exp ((funcomp) tauVal xiVal) s .
Proof. exact (compRenSubst_Exp xiVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Val tauVal) (ren_Val xiVal) = subst_Val ((funcomp) tauVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Val xiVal tauVal n)). Qed.

Lemma renComp'_Exp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Exp tauVal) (ren_Exp xiVal) = subst_Exp ((funcomp) tauVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Exp xiVal tauVal n)). Qed.

Lemma renRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Val (mVal)) : ren_Val zetaVal (ren_Val xiVal s) = ren_Val ((funcomp) zetaVal xiVal) s .
Proof. exact (compRenRen_Val xiVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma renRen_Exp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Exp (mVal)) : ren_Exp zetaVal (ren_Exp xiVal s) = ren_Exp ((funcomp) zetaVal xiVal) s .
Proof. exact (compRenRen_Exp xiVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Val zetaVal) (ren_Val xiVal) = ren_Val ((funcomp) zetaVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Val xiVal zetaVal n)). Qed.

Lemma renRen'_Exp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Exp zetaVal) (ren_Exp xiVal) = ren_Exp ((funcomp) zetaVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Exp xiVal zetaVal n)). Qed.

End ValExp.

Section SC.
Inductive SC (nVal : nat) : Type :=
  | SCchoicehole : SC (nVal)
  | SCchoiceleft : SC  (nVal) -> Exp  (nVal) -> SC (nVal)
  | SCchoiceright : Exp  (nVal) -> SC  (nVal) -> SC (nVal).

Lemma congr_SCchoicehole { mVal : nat } : SCchoicehole (mVal) = SCchoicehole (mVal) .
Proof. congruence. Qed.

Lemma congr_SCchoiceleft { mVal : nat } { s0 : SC  (mVal) } { s1 : Exp  (mVal) } { t0 : SC  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : SCchoiceleft (mVal) s0 s1 = SCchoiceleft (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_SCchoiceright { mVal : nat } { s0 : Exp  (mVal) } { s1 : SC  (mVal) } { t0 : Exp  (mVal) } { t1 : SC  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : SCchoiceright (mVal) s0 s1 = SCchoiceright (mVal) t0 t1 .
Proof. congruence. Qed.

Fixpoint subst_SC { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : SC (mVal)) : SC (nVal) :=
    match s return SC (nVal) with
    | SCchoicehole (_)  => SCchoicehole (nVal)
    | SCchoiceleft (_) s0 s1 => SCchoiceleft (nVal) ((subst_SC sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | SCchoiceright (_) s0 s1 => SCchoiceright (nVal) ((subst_Exp sigmaVal) s0) ((subst_SC sigmaVal) s1)
    end.

Fixpoint idSubst_SC { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : SC (mVal)) : subst_SC sigmaVal s = s :=
    match s return subst_SC sigmaVal s = s with
    | SCchoicehole (_)  => congr_SCchoicehole 
    | SCchoiceleft (_) s0 s1 => congr_SCchoiceleft ((idSubst_SC sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | SCchoiceright (_) s0 s1 => congr_SCchoiceright ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_SC sigmaVal EqVal) s1)
    end.

Fixpoint ext_SC { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : SC (mVal)) : subst_SC sigmaVal s = subst_SC tauVal s :=
    match s return subst_SC sigmaVal s = subst_SC tauVal s with
    | SCchoicehole (_)  => congr_SCchoicehole 
    | SCchoiceleft (_) s0 s1 => congr_SCchoiceleft ((ext_SC sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | SCchoiceright (_) s0 s1 => congr_SCchoiceright ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_SC sigmaVal tauVal EqVal) s1)
    end.

Fixpoint compSubstSubst_SC { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : SC (mVal)) : subst_SC tauVal (subst_SC sigmaVal s) = subst_SC thetaVal s :=
    match s return subst_SC tauVal (subst_SC sigmaVal s) = subst_SC thetaVal s with
    | SCchoicehole (_)  => congr_SCchoicehole 
    | SCchoiceleft (_) s0 s1 => congr_SCchoiceleft ((compSubstSubst_SC sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | SCchoiceright (_) s0 s1 => congr_SCchoiceright ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_SC sigmaVal tauVal thetaVal EqVal) s1)
    end.

Lemma instId_SC { mVal : nat } : subst_SC (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_SC (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_SC { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : SC (mVal)) : subst_SC tauVal (subst_SC sigmaVal s) = subst_SC ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_SC sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_SC { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_SC tauVal) (subst_SC sigmaVal) = subst_SC ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_SC sigmaVal tauVal n)). Qed.

End SC.

Section scopeContext.
Inductive scopeContext (nVal : nat) : Type :=
  | SXone : SC  (nVal) -> scopeContext (nVal)
  | SXall : SC  (nVal) -> scopeContext (nVal).

Lemma congr_SXone { mVal : nat } { s0 : SC  (mVal) } { t0 : SC  (mVal) } (H1 : s0 = t0) : SXone (mVal) s0 = SXone (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_SXall { mVal : nat } { s0 : SC  (mVal) } { t0 : SC  (mVal) } (H1 : s0 = t0) : SXall (mVal) s0 = SXall (mVal) t0 .
Proof. congruence. Qed.

Definition subst_scopeContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : scopeContext (mVal)) : scopeContext (nVal) :=
    match s return scopeContext (nVal) with
    | SXone (_) s0 => SXone (nVal) ((subst_SC sigmaVal) s0)
    | SXall (_) s0 => SXall (nVal) ((subst_SC sigmaVal) s0)
    end.

Definition idSubst_scopeContext { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : scopeContext (mVal)) : subst_scopeContext sigmaVal s = s :=
    match s return subst_scopeContext sigmaVal s = s with
    | SXone (_) s0 => congr_SXone ((idSubst_SC sigmaVal EqVal) s0)
    | SXall (_) s0 => congr_SXall ((idSubst_SC sigmaVal EqVal) s0)
    end.

Definition ext_scopeContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : scopeContext (mVal)) : subst_scopeContext sigmaVal s = subst_scopeContext tauVal s :=
    match s return subst_scopeContext sigmaVal s = subst_scopeContext tauVal s with
    | SXone (_) s0 => congr_SXone ((ext_SC sigmaVal tauVal EqVal) s0)
    | SXall (_) s0 => congr_SXall ((ext_SC sigmaVal tauVal EqVal) s0)
    end.

Definition compSubstSubst_scopeContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : scopeContext (mVal)) : subst_scopeContext tauVal (subst_scopeContext sigmaVal s) = subst_scopeContext thetaVal s :=
    match s return subst_scopeContext tauVal (subst_scopeContext sigmaVal s) = subst_scopeContext thetaVal s with
    | SXone (_) s0 => congr_SXone ((compSubstSubst_SC sigmaVal tauVal thetaVal EqVal) s0)
    | SXall (_) s0 => congr_SXall ((compSubstSubst_SC sigmaVal tauVal thetaVal EqVal) s0)
    end.

Lemma instId_scopeContext { mVal : nat } : subst_scopeContext (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_scopeContext (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_scopeContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : scopeContext (mVal)) : subst_scopeContext tauVal (subst_scopeContext sigmaVal s) = subst_scopeContext ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_scopeContext sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_scopeContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_scopeContext tauVal) (subst_scopeContext sigmaVal) = subst_scopeContext ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_scopeContext sigmaVal tauVal n)). Qed.

End scopeContext.

Section ExpCompatContextValCompatContextValListCompatContext.
Inductive ExpCompatContext (nVal : nat) : Type :=
  | EHole : ExpCompatContext  (nVal) -> ExpCompatContext (nVal)
  | ESeq1 : ExpCompatContext  (nVal) -> Exp  (nVal) -> ExpCompatContext (nVal)
  | ESeq2 : Exp  (nVal) -> ExpCompatContext  (nVal) -> ExpCompatContext (nVal)
  | EUnify1 : ValCompatContext  (nVal) -> Exp  (nVal) -> ExpCompatContext (nVal)
  | EUnify2 : Val  (nVal) -> ExpCompatContext  (nVal) -> ExpCompatContext (nVal)
  | EExists : ExpCompatContext  ((S) nVal) -> ExpCompatContext (nVal)
  | EOr1 : ExpCompatContext  (nVal) -> Exp  (nVal) -> ExpCompatContext (nVal)
  | EOr2 : Exp  (nVal) -> ExpCompatContext  (nVal) -> ExpCompatContext (nVal)
  | EOne : ExpCompatContext  (nVal) -> ExpCompatContext (nVal)
  | EAll : ExpCompatContext  (nVal) -> ExpCompatContext (nVal)
  | EApp1 : ValCompatContext  (nVal) -> Val  (nVal) -> ExpCompatContext (nVal)
  | EApp2 : Val  (nVal) -> ValCompatContext  (nVal) -> ExpCompatContext (nVal)
  | ERet : ValCompatContext  (nVal) -> ExpCompatContext (nVal)
 with ValCompatContext (nVal : nat) : Type :=
  | VTuple : ValListCompatContext  (nVal) -> ValCompatContext (nVal)
  | VLam : ExpCompatContext  ((S) nVal) -> ValCompatContext (nVal)
 with ValListCompatContext (nVal : nat) : Type :=
  | VEcons1 : ValCompatContext  (nVal) -> list (Val  (nVal)) -> ValListCompatContext (nVal)
  | VEcons2 : Val  (nVal) -> ValListCompatContext  (nVal) -> ValListCompatContext (nVal).

Lemma congr_EHole { mVal : nat } { s0 : ExpCompatContext  (mVal) } { t0 : ExpCompatContext  (mVal) } (H1 : s0 = t0) : EHole (mVal) s0 = EHole (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_ESeq1 { mVal : nat } { s0 : ExpCompatContext  (mVal) } { s1 : Exp  (mVal) } { t0 : ExpCompatContext  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : ESeq1 (mVal) s0 s1 = ESeq1 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_ESeq2 { mVal : nat } { s0 : Exp  (mVal) } { s1 : ExpCompatContext  (mVal) } { t0 : Exp  (mVal) } { t1 : ExpCompatContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : ESeq2 (mVal) s0 s1 = ESeq2 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_EUnify1 { mVal : nat } { s0 : ValCompatContext  (mVal) } { s1 : Exp  (mVal) } { t0 : ValCompatContext  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : EUnify1 (mVal) s0 s1 = EUnify1 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_EUnify2 { mVal : nat } { s0 : Val  (mVal) } { s1 : ExpCompatContext  (mVal) } { t0 : Val  (mVal) } { t1 : ExpCompatContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : EUnify2 (mVal) s0 s1 = EUnify2 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_EExists { mVal : nat } { s0 : ExpCompatContext  ((S) mVal) } { t0 : ExpCompatContext  ((S) mVal) } (H1 : s0 = t0) : EExists (mVal) s0 = EExists (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_EOr1 { mVal : nat } { s0 : ExpCompatContext  (mVal) } { s1 : Exp  (mVal) } { t0 : ExpCompatContext  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : EOr1 (mVal) s0 s1 = EOr1 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_EOr2 { mVal : nat } { s0 : Exp  (mVal) } { s1 : ExpCompatContext  (mVal) } { t0 : Exp  (mVal) } { t1 : ExpCompatContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : EOr2 (mVal) s0 s1 = EOr2 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_EOne { mVal : nat } { s0 : ExpCompatContext  (mVal) } { t0 : ExpCompatContext  (mVal) } (H1 : s0 = t0) : EOne (mVal) s0 = EOne (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_EAll { mVal : nat } { s0 : ExpCompatContext  (mVal) } { t0 : ExpCompatContext  (mVal) } (H1 : s0 = t0) : EAll (mVal) s0 = EAll (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_EApp1 { mVal : nat } { s0 : ValCompatContext  (mVal) } { s1 : Val  (mVal) } { t0 : ValCompatContext  (mVal) } { t1 : Val  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : EApp1 (mVal) s0 s1 = EApp1 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_EApp2 { mVal : nat } { s0 : Val  (mVal) } { s1 : ValCompatContext  (mVal) } { t0 : Val  (mVal) } { t1 : ValCompatContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : EApp2 (mVal) s0 s1 = EApp2 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_ERet { mVal : nat } { s0 : ValCompatContext  (mVal) } { t0 : ValCompatContext  (mVal) } (H1 : s0 = t0) : ERet (mVal) s0 = ERet (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_VTuple { mVal : nat } { s0 : ValListCompatContext  (mVal) } { t0 : ValListCompatContext  (mVal) } (H1 : s0 = t0) : VTuple (mVal) s0 = VTuple (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_VLam { mVal : nat } { s0 : ExpCompatContext  ((S) mVal) } { t0 : ExpCompatContext  ((S) mVal) } (H1 : s0 = t0) : VLam (mVal) s0 = VLam (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_VEcons1 { mVal : nat } { s0 : ValCompatContext  (mVal) } { s1 : list (Val  (mVal)) } { t0 : ValCompatContext  (mVal) } { t1 : list (Val  (mVal)) } (H1 : s0 = t0) (H2 : s1 = t1) : VEcons1 (mVal) s0 s1 = VEcons1 (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_VEcons2 { mVal : nat } { s0 : Val  (mVal) } { s1 : ValListCompatContext  (mVal) } { t0 : Val  (mVal) } { t1 : ValListCompatContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : VEcons2 (mVal) s0 s1 = VEcons2 (mVal) t0 t1 .
Proof. congruence. Qed.

Fixpoint subst_ExpCompatContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : ExpCompatContext (mVal)) : ExpCompatContext (nVal) :=
    match s return ExpCompatContext (nVal) with
    | EHole (_) s0 => EHole (nVal) ((subst_ExpCompatContext sigmaVal) s0)
    | ESeq1 (_) s0 s1 => ESeq1 (nVal) ((subst_ExpCompatContext sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | ESeq2 (_) s0 s1 => ESeq2 (nVal) ((subst_Exp sigmaVal) s0) ((subst_ExpCompatContext sigmaVal) s1)
    | EUnify1 (_) s0 s1 => EUnify1 (nVal) ((subst_ValCompatContext sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | EUnify2 (_) s0 s1 => EUnify2 (nVal) ((subst_Val sigmaVal) s0) ((subst_ExpCompatContext sigmaVal) s1)
    | EExists (_) s0 => EExists (nVal) ((subst_ExpCompatContext (up_Val_Val sigmaVal)) s0)
    | EOr1 (_) s0 s1 => EOr1 (nVal) ((subst_ExpCompatContext sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | EOr2 (_) s0 s1 => EOr2 (nVal) ((subst_Exp sigmaVal) s0) ((subst_ExpCompatContext sigmaVal) s1)
    | EOne (_) s0 => EOne (nVal) ((subst_ExpCompatContext sigmaVal) s0)
    | EAll (_) s0 => EAll (nVal) ((subst_ExpCompatContext sigmaVal) s0)
    | EApp1 (_) s0 s1 => EApp1 (nVal) ((subst_ValCompatContext sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | EApp2 (_) s0 s1 => EApp2 (nVal) ((subst_Val sigmaVal) s0) ((subst_ValCompatContext sigmaVal) s1)
    | ERet (_) s0 => ERet (nVal) ((subst_ValCompatContext sigmaVal) s0)
    end
 with subst_ValCompatContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : ValCompatContext (mVal)) : ValCompatContext (nVal) :=
    match s return ValCompatContext (nVal) with
    | VTuple (_) s0 => VTuple (nVal) ((subst_ValListCompatContext sigmaVal) s0)
    | VLam (_) s0 => VLam (nVal) ((subst_ExpCompatContext (up_Val_Val sigmaVal)) s0)
    end
 with subst_ValListCompatContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : ValListCompatContext (mVal)) : ValListCompatContext (nVal) :=
    match s return ValListCompatContext (nVal) with
    | VEcons1 (_) s0 s1 => VEcons1 (nVal) ((subst_ValCompatContext sigmaVal) s0) ((list_map (subst_Val sigmaVal)) s1)
    | VEcons2 (_) s0 s1 => VEcons2 (nVal) ((subst_Val sigmaVal) s0) ((subst_ValListCompatContext sigmaVal) s1)
    end.

Fixpoint idSubst_ExpCompatContext { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : ExpCompatContext (mVal)) : subst_ExpCompatContext sigmaVal s = s :=
    match s return subst_ExpCompatContext sigmaVal s = s with
    | EHole (_) s0 => congr_EHole ((idSubst_ExpCompatContext sigmaVal EqVal) s0)
    | ESeq1 (_) s0 s1 => congr_ESeq1 ((idSubst_ExpCompatContext sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | ESeq2 (_) s0 s1 => congr_ESeq2 ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_ExpCompatContext sigmaVal EqVal) s1)
    | EUnify1 (_) s0 s1 => congr_EUnify1 ((idSubst_ValCompatContext sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | EUnify2 (_) s0 s1 => congr_EUnify2 ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_ExpCompatContext sigmaVal EqVal) s1)
    | EExists (_) s0 => congr_EExists ((idSubst_ExpCompatContext (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    | EOr1 (_) s0 s1 => congr_EOr1 ((idSubst_ExpCompatContext sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | EOr2 (_) s0 s1 => congr_EOr2 ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_ExpCompatContext sigmaVal EqVal) s1)
    | EOne (_) s0 => congr_EOne ((idSubst_ExpCompatContext sigmaVal EqVal) s0)
    | EAll (_) s0 => congr_EAll ((idSubst_ExpCompatContext sigmaVal EqVal) s0)
    | EApp1 (_) s0 s1 => congr_EApp1 ((idSubst_ValCompatContext sigmaVal EqVal) s0) ((idSubst_Val sigmaVal EqVal) s1)
    | EApp2 (_) s0 s1 => congr_EApp2 ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_ValCompatContext sigmaVal EqVal) s1)
    | ERet (_) s0 => congr_ERet ((idSubst_ValCompatContext sigmaVal EqVal) s0)
    end
 with idSubst_ValCompatContext { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : ValCompatContext (mVal)) : subst_ValCompatContext sigmaVal s = s :=
    match s return subst_ValCompatContext sigmaVal s = s with
    | VTuple (_) s0 => congr_VTuple ((idSubst_ValListCompatContext sigmaVal EqVal) s0)
    | VLam (_) s0 => congr_VLam ((idSubst_ExpCompatContext (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    end
 with idSubst_ValListCompatContext { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : ValListCompatContext (mVal)) : subst_ValListCompatContext sigmaVal s = s :=
    match s return subst_ValListCompatContext sigmaVal s = s with
    | VEcons1 (_) s0 s1 => congr_VEcons1 ((idSubst_ValCompatContext sigmaVal EqVal) s0) ((list_id (idSubst_Val sigmaVal EqVal)) s1)
    | VEcons2 (_) s0 s1 => congr_VEcons2 ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_ValListCompatContext sigmaVal EqVal) s1)
    end.

Fixpoint ext_ExpCompatContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : ExpCompatContext (mVal)) : subst_ExpCompatContext sigmaVal s = subst_ExpCompatContext tauVal s :=
    match s return subst_ExpCompatContext sigmaVal s = subst_ExpCompatContext tauVal s with
    | EHole (_) s0 => congr_EHole ((ext_ExpCompatContext sigmaVal tauVal EqVal) s0)
    | ESeq1 (_) s0 s1 => congr_ESeq1 ((ext_ExpCompatContext sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | ESeq2 (_) s0 s1 => congr_ESeq2 ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_ExpCompatContext sigmaVal tauVal EqVal) s1)
    | EUnify1 (_) s0 s1 => congr_EUnify1 ((ext_ValCompatContext sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | EUnify2 (_) s0 s1 => congr_EUnify2 ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_ExpCompatContext sigmaVal tauVal EqVal) s1)
    | EExists (_) s0 => congr_EExists ((ext_ExpCompatContext (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    | EOr1 (_) s0 s1 => congr_EOr1 ((ext_ExpCompatContext sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | EOr2 (_) s0 s1 => congr_EOr2 ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_ExpCompatContext sigmaVal tauVal EqVal) s1)
    | EOne (_) s0 => congr_EOne ((ext_ExpCompatContext sigmaVal tauVal EqVal) s0)
    | EAll (_) s0 => congr_EAll ((ext_ExpCompatContext sigmaVal tauVal EqVal) s0)
    | EApp1 (_) s0 s1 => congr_EApp1 ((ext_ValCompatContext sigmaVal tauVal EqVal) s0) ((ext_Val sigmaVal tauVal EqVal) s1)
    | EApp2 (_) s0 s1 => congr_EApp2 ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_ValCompatContext sigmaVal tauVal EqVal) s1)
    | ERet (_) s0 => congr_ERet ((ext_ValCompatContext sigmaVal tauVal EqVal) s0)
    end
 with ext_ValCompatContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : ValCompatContext (mVal)) : subst_ValCompatContext sigmaVal s = subst_ValCompatContext tauVal s :=
    match s return subst_ValCompatContext sigmaVal s = subst_ValCompatContext tauVal s with
    | VTuple (_) s0 => congr_VTuple ((ext_ValListCompatContext sigmaVal tauVal EqVal) s0)
    | VLam (_) s0 => congr_VLam ((ext_ExpCompatContext (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    end
 with ext_ValListCompatContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : ValListCompatContext (mVal)) : subst_ValListCompatContext sigmaVal s = subst_ValListCompatContext tauVal s :=
    match s return subst_ValListCompatContext sigmaVal s = subst_ValListCompatContext tauVal s with
    | VEcons1 (_) s0 s1 => congr_VEcons1 ((ext_ValCompatContext sigmaVal tauVal EqVal) s0) ((list_ext (ext_Val sigmaVal tauVal EqVal)) s1)
    | VEcons2 (_) s0 s1 => congr_VEcons2 ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_ValListCompatContext sigmaVal tauVal EqVal) s1)
    end.

Fixpoint compSubstSubst_ExpCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : ExpCompatContext (mVal)) : subst_ExpCompatContext tauVal (subst_ExpCompatContext sigmaVal s) = subst_ExpCompatContext thetaVal s :=
    match s return subst_ExpCompatContext tauVal (subst_ExpCompatContext sigmaVal s) = subst_ExpCompatContext thetaVal s with
    | EHole (_) s0 => congr_EHole ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s0)
    | ESeq1 (_) s0 s1 => congr_ESeq1 ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | ESeq2 (_) s0 s1 => congr_ESeq2 ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s1)
    | EUnify1 (_) s0 s1 => congr_EUnify1 ((compSubstSubst_ValCompatContext sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | EUnify2 (_) s0 s1 => congr_EUnify2 ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s1)
    | EExists (_) s0 => congr_EExists ((compSubstSubst_ExpCompatContext (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    | EOr1 (_) s0 s1 => congr_EOr1 ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | EOr2 (_) s0 s1 => congr_EOr2 ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s1)
    | EOne (_) s0 => congr_EOne ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s0)
    | EAll (_) s0 => congr_EAll ((compSubstSubst_ExpCompatContext sigmaVal tauVal thetaVal EqVal) s0)
    | EApp1 (_) s0 s1 => congr_EApp1 ((compSubstSubst_ValCompatContext sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s1)
    | EApp2 (_) s0 s1 => congr_EApp2 ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_ValCompatContext sigmaVal tauVal thetaVal EqVal) s1)
    | ERet (_) s0 => congr_ERet ((compSubstSubst_ValCompatContext sigmaVal tauVal thetaVal EqVal) s0)
    end
 with compSubstSubst_ValCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : ValCompatContext (mVal)) : subst_ValCompatContext tauVal (subst_ValCompatContext sigmaVal s) = subst_ValCompatContext thetaVal s :=
    match s return subst_ValCompatContext tauVal (subst_ValCompatContext sigmaVal s) = subst_ValCompatContext thetaVal s with
    | VTuple (_) s0 => congr_VTuple ((compSubstSubst_ValListCompatContext sigmaVal tauVal thetaVal EqVal) s0)
    | VLam (_) s0 => congr_VLam ((compSubstSubst_ExpCompatContext (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compSubstSubst_ValListCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : ValListCompatContext (mVal)) : subst_ValListCompatContext tauVal (subst_ValListCompatContext sigmaVal s) = subst_ValListCompatContext thetaVal s :=
    match s return subst_ValListCompatContext tauVal (subst_ValListCompatContext sigmaVal s) = subst_ValListCompatContext thetaVal s with
    | VEcons1 (_) s0 s1 => congr_VEcons1 ((compSubstSubst_ValCompatContext sigmaVal tauVal thetaVal EqVal) s0) ((list_comp (compSubstSubst_Val sigmaVal tauVal thetaVal EqVal)) s1)
    | VEcons2 (_) s0 s1 => congr_VEcons2 ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_ValListCompatContext sigmaVal tauVal thetaVal EqVal) s1)
    end.

Lemma instId_ExpCompatContext { mVal : nat } : subst_ExpCompatContext (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ExpCompatContext (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_ValCompatContext { mVal : nat } : subst_ValCompatContext (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ValCompatContext (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_ValListCompatContext { mVal : nat } : subst_ValListCompatContext (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ValListCompatContext (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_ExpCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : ExpCompatContext (mVal)) : subst_ExpCompatContext tauVal (subst_ExpCompatContext sigmaVal s) = subst_ExpCompatContext ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_ExpCompatContext sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp_ValCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : ValCompatContext (mVal)) : subst_ValCompatContext tauVal (subst_ValCompatContext sigmaVal s) = subst_ValCompatContext ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_ValCompatContext sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp_ValListCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : ValListCompatContext (mVal)) : subst_ValListCompatContext tauVal (subst_ValListCompatContext sigmaVal s) = subst_ValListCompatContext ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_ValListCompatContext sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_ExpCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_ExpCompatContext tauVal) (subst_ExpCompatContext sigmaVal) = subst_ExpCompatContext ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ExpCompatContext sigmaVal tauVal n)). Qed.

Lemma compComp'_ValCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_ValCompatContext tauVal) (subst_ValCompatContext sigmaVal) = subst_ValCompatContext ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ValCompatContext sigmaVal tauVal n)). Qed.

Lemma compComp'_ValListCompatContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_ValListCompatContext tauVal) (subst_ValListCompatContext sigmaVal) = subst_ValListCompatContext ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ValListCompatContext sigmaVal tauVal n)). Qed.

End ExpCompatContextValCompatContextValListCompatContext.

Section choiceContext.
Inductive choiceContext (nVal : nat) : Type :=
  | CXhole : choiceContext (nVal)
  | CXchoiceright : Val  (nVal) -> choiceContext  (nVal) -> Exp  (nVal) -> choiceContext (nVal)
  | CXseqleft : choiceContext  (nVal) -> Exp  (nVal) -> choiceContext (nVal)
  | CXseqright : Exp  (nVal) -> choiceContext  (nVal) -> choiceContext (nVal)
  | CXexists : choiceContext  ((S) nVal) -> choiceContext (nVal).

Lemma congr_CXhole { mVal : nat } : CXhole (mVal) = CXhole (mVal) .
Proof. congruence. Qed.

Lemma congr_CXchoiceright { mVal : nat } { s0 : Val  (mVal) } { s1 : choiceContext  (mVal) } { s2 : Exp  (mVal) } { t0 : Val  (mVal) } { t1 : choiceContext  (mVal) } { t2 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : CXchoiceright (mVal) s0 s1 s2 = CXchoiceright (mVal) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_CXseqleft { mVal : nat } { s0 : choiceContext  (mVal) } { s1 : Exp  (mVal) } { t0 : choiceContext  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : CXseqleft (mVal) s0 s1 = CXseqleft (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_CXseqright { mVal : nat } { s0 : Exp  (mVal) } { s1 : choiceContext  (mVal) } { t0 : Exp  (mVal) } { t1 : choiceContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : CXseqright (mVal) s0 s1 = CXseqright (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_CXexists { mVal : nat } { s0 : choiceContext  ((S) mVal) } { t0 : choiceContext  ((S) mVal) } (H1 : s0 = t0) : CXexists (mVal) s0 = CXexists (mVal) t0 .
Proof. congruence. Qed.

Fixpoint subst_choiceContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : choiceContext (mVal)) : choiceContext (nVal) :=
    match s return choiceContext (nVal) with
    | CXhole (_)  => CXhole (nVal)
    | CXchoiceright (_) s0 s1 s2 => CXchoiceright (nVal) ((subst_Val sigmaVal) s0) ((subst_choiceContext sigmaVal) s1) ((subst_Exp sigmaVal) s2)
    | CXseqleft (_) s0 s1 => CXseqleft (nVal) ((subst_choiceContext sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | CXseqright (_) s0 s1 => CXseqright (nVal) ((subst_Exp sigmaVal) s0) ((subst_choiceContext sigmaVal) s1)
    | CXexists (_) s0 => CXexists (nVal) ((subst_choiceContext (up_Val_Val sigmaVal)) s0)
    end.

Fixpoint idSubst_choiceContext { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : choiceContext (mVal)) : subst_choiceContext sigmaVal s = s :=
    match s return subst_choiceContext sigmaVal s = s with
    | CXhole (_)  => congr_CXhole 
    | CXchoiceright (_) s0 s1 s2 => congr_CXchoiceright ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_choiceContext sigmaVal EqVal) s1) ((idSubst_Exp sigmaVal EqVal) s2)
    | CXseqleft (_) s0 s1 => congr_CXseqleft ((idSubst_choiceContext sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | CXseqright (_) s0 s1 => congr_CXseqright ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_choiceContext sigmaVal EqVal) s1)
    | CXexists (_) s0 => congr_CXexists ((idSubst_choiceContext (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    end.

Fixpoint ext_choiceContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : choiceContext (mVal)) : subst_choiceContext sigmaVal s = subst_choiceContext tauVal s :=
    match s return subst_choiceContext sigmaVal s = subst_choiceContext tauVal s with
    | CXhole (_)  => congr_CXhole 
    | CXchoiceright (_) s0 s1 s2 => congr_CXchoiceright ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_choiceContext sigmaVal tauVal EqVal) s1) ((ext_Exp sigmaVal tauVal EqVal) s2)
    | CXseqleft (_) s0 s1 => congr_CXseqleft ((ext_choiceContext sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | CXseqright (_) s0 s1 => congr_CXseqright ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_choiceContext sigmaVal tauVal EqVal) s1)
    | CXexists (_) s0 => congr_CXexists ((ext_choiceContext (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    end.

Fixpoint compSubstSubst_choiceContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : choiceContext (mVal)) : subst_choiceContext tauVal (subst_choiceContext sigmaVal s) = subst_choiceContext thetaVal s :=
    match s return subst_choiceContext tauVal (subst_choiceContext sigmaVal s) = subst_choiceContext thetaVal s with
    | CXhole (_)  => congr_CXhole 
    | CXchoiceright (_) s0 s1 s2 => congr_CXchoiceright ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_choiceContext sigmaVal tauVal thetaVal EqVal) s1) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s2)
    | CXseqleft (_) s0 s1 => congr_CXseqleft ((compSubstSubst_choiceContext sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | CXseqright (_) s0 s1 => congr_CXseqright ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_choiceContext sigmaVal tauVal thetaVal EqVal) s1)
    | CXexists (_) s0 => congr_CXexists ((compSubstSubst_choiceContext (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    end.

Lemma instId_choiceContext { mVal : nat } : subst_choiceContext (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_choiceContext (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_choiceContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : choiceContext (mVal)) : subst_choiceContext tauVal (subst_choiceContext sigmaVal s) = subst_choiceContext ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_choiceContext sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_choiceContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_choiceContext tauVal) (subst_choiceContext sigmaVal) = subst_choiceContext ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_choiceContext sigmaVal tauVal n)). Qed.

End choiceContext.

Section exContext.
Inductive exContext (nVal : nat) : Type :=
  | Xhole : exContext (nVal)
  | Xeqright : Val  (nVal) -> exContext  (nVal) -> Exp  (nVal) -> exContext (nVal)
  | Xseqleft : exContext  (nVal) -> Exp  (nVal) -> exContext (nVal)
  | Xseqright : Exp  (nVal) -> exContext  (nVal) -> exContext (nVal).

Lemma congr_Xhole { mVal : nat } : Xhole (mVal) = Xhole (mVal) .
Proof. congruence. Qed.

Lemma congr_Xeqright { mVal : nat } { s0 : Val  (mVal) } { s1 : exContext  (mVal) } { s2 : Exp  (mVal) } { t0 : Val  (mVal) } { t1 : exContext  (mVal) } { t2 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Xeqright (mVal) s0 s1 s2 = Xeqright (mVal) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Xseqleft { mVal : nat } { s0 : exContext  (mVal) } { s1 : Exp  (mVal) } { t0 : exContext  (mVal) } { t1 : Exp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : Xseqleft (mVal) s0 s1 = Xseqleft (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Xseqright { mVal : nat } { s0 : Exp  (mVal) } { s1 : exContext  (mVal) } { t0 : Exp  (mVal) } { t1 : exContext  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : Xseqright (mVal) s0 s1 = Xseqright (mVal) t0 t1 .
Proof. congruence. Qed.

Fixpoint subst_exContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : exContext (mVal)) : exContext (nVal) :=
    match s return exContext (nVal) with
    | Xhole (_)  => Xhole (nVal)
    | Xeqright (_) s0 s1 s2 => Xeqright (nVal) ((subst_Val sigmaVal) s0) ((subst_exContext sigmaVal) s1) ((subst_Exp sigmaVal) s2)
    | Xseqleft (_) s0 s1 => Xseqleft (nVal) ((subst_exContext sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Xseqright (_) s0 s1 => Xseqright (nVal) ((subst_Exp sigmaVal) s0) ((subst_exContext sigmaVal) s1)
    end.

Fixpoint idSubst_exContext { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : exContext (mVal)) : subst_exContext sigmaVal s = s :=
    match s return subst_exContext sigmaVal s = s with
    | Xhole (_)  => congr_Xhole 
    | Xeqright (_) s0 s1 s2 => congr_Xeqright ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_exContext sigmaVal EqVal) s1) ((idSubst_Exp sigmaVal EqVal) s2)
    | Xseqleft (_) s0 s1 => congr_Xseqleft ((idSubst_exContext sigmaVal EqVal) s0) ((idSubst_Exp sigmaVal EqVal) s1)
    | Xseqright (_) s0 s1 => congr_Xseqright ((idSubst_Exp sigmaVal EqVal) s0) ((idSubst_exContext sigmaVal EqVal) s1)
    end.

Fixpoint ext_exContext { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : exContext (mVal)) : subst_exContext sigmaVal s = subst_exContext tauVal s :=
    match s return subst_exContext sigmaVal s = subst_exContext tauVal s with
    | Xhole (_)  => congr_Xhole 
    | Xeqright (_) s0 s1 s2 => congr_Xeqright ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_exContext sigmaVal tauVal EqVal) s1) ((ext_Exp sigmaVal tauVal EqVal) s2)
    | Xseqleft (_) s0 s1 => congr_Xseqleft ((ext_exContext sigmaVal tauVal EqVal) s0) ((ext_Exp sigmaVal tauVal EqVal) s1)
    | Xseqright (_) s0 s1 => congr_Xseqright ((ext_Exp sigmaVal tauVal EqVal) s0) ((ext_exContext sigmaVal tauVal EqVal) s1)
    end.

Fixpoint compSubstSubst_exContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : exContext (mVal)) : subst_exContext tauVal (subst_exContext sigmaVal s) = subst_exContext thetaVal s :=
    match s return subst_exContext tauVal (subst_exContext sigmaVal s) = subst_exContext thetaVal s with
    | Xhole (_)  => congr_Xhole 
    | Xeqright (_) s0 s1 s2 => congr_Xeqright ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_exContext sigmaVal tauVal thetaVal EqVal) s1) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s2)
    | Xseqleft (_) s0 s1 => congr_Xseqleft ((compSubstSubst_exContext sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s1)
    | Xseqright (_) s0 s1 => congr_Xseqright ((compSubstSubst_Exp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_exContext sigmaVal tauVal thetaVal EqVal) s1)
    end.

Lemma instId_exContext { mVal : nat } : subst_exContext (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exContext (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_exContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : exContext (mVal)) : subst_exContext tauVal (subst_exContext sigmaVal s) = subst_exContext ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_exContext sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exContext { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_exContext tauVal) (subst_exContext sigmaVal) = subst_exContext ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exContext sigmaVal tauVal n)). Qed.

End exContext.

Arguments var_Val {nVal}.

Arguments Int {nVal}.

Arguments Prim {nVal}.

Arguments Tuple {nVal}.

Arguments Lam {nVal}.

Arguments Ret {nVal}.

Arguments App {nVal}.

Arguments Seq {nVal}.

Arguments Unify {nVal}.

Arguments Exists {nVal}.

Arguments Or {nVal}.

Arguments Fail {nVal}.

Arguments One {nVal}.

Arguments All {nVal}.

Arguments SCchoicehole {nVal}.

Arguments SCchoiceleft {nVal}.

Arguments SCchoiceright {nVal}.

Arguments SXone {nVal}.

Arguments SXall {nVal}.

Arguments EHole {nVal}.

Arguments ESeq1 {nVal}.

Arguments ESeq2 {nVal}.

Arguments EUnify1 {nVal}.

Arguments EUnify2 {nVal}.

Arguments EExists {nVal}.

Arguments EOr1 {nVal}.

Arguments EOr2 {nVal}.

Arguments EOne {nVal}.

Arguments EAll {nVal}.

Arguments EApp1 {nVal}.

Arguments EApp2 {nVal}.

Arguments ERet {nVal}.

Arguments VTuple {nVal}.

Arguments VLam {nVal}.

Arguments VEcons1 {nVal}.

Arguments VEcons2 {nVal}.

Arguments CXhole {nVal}.

Arguments CXchoiceright {nVal}.

Arguments CXseqleft {nVal}.

Arguments CXseqright {nVal}.

Arguments CXexists {nVal}.

Arguments Xhole {nVal}.

Arguments Xeqright {nVal}.

Arguments Xseqleft {nVal}.

Arguments Xseqright {nVal}.

Global Instance Subst_Val { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (Val (mVal)) (Val (nVal)) := @subst_Val (mVal) (nVal) .

Global Instance Subst_Exp { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (Exp (mVal)) (Exp (nVal)) := @subst_Exp (mVal) (nVal) .

Global Instance Subst_SC { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (SC (mVal)) (SC (nVal)) := @subst_SC (mVal) (nVal) .

Global Instance Subst_scopeContext { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (scopeContext (mVal)) (scopeContext (nVal)) := @subst_scopeContext (mVal) (nVal) .

Global Instance Subst_ExpCompatContext { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (ExpCompatContext (mVal)) (ExpCompatContext (nVal)) := @subst_ExpCompatContext (mVal) (nVal) .

Global Instance Subst_ValCompatContext { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (ValCompatContext (mVal)) (ValCompatContext (nVal)) := @subst_ValCompatContext (mVal) (nVal) .

Global Instance Subst_ValListCompatContext { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (ValListCompatContext (mVal)) (ValListCompatContext (nVal)) := @subst_ValListCompatContext (mVal) (nVal) .

Global Instance Subst_choiceContext { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (choiceContext (mVal)) (choiceContext (nVal)) := @subst_choiceContext (mVal) (nVal) .

Global Instance Subst_exContext { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (exContext (mVal)) (exContext (nVal)) := @subst_exContext (mVal) (nVal) .

Global Instance Ren_Val { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (Val (mVal)) (Val (nVal)) := @ren_Val (mVal) (nVal) .

Global Instance Ren_Exp { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (Exp (mVal)) (Exp (nVal)) := @ren_Exp (mVal) (nVal) .

(*
Global Instance Ren_SC { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (SC (mVal)) (SC (nVal)) := @ren_SC (mVal) (nVal) .

Global Instance Ren_scopeContext { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (scopeContext (mVal)) (scopeContext (nVal)) := @ren_scopeContext (mVal) (nVal) .

Global Instance Ren_ExpCompatContext { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (ExpCompatContext (mVal)) (ExpCompatContext (nVal)) := @ren_ExpCompatContext (mVal) (nVal) .

Global Instance Ren_ValCompatContext { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (ValCompatContext (mVal)) (ValCompatContext (nVal)) := @ren_ValCompatContext (mVal) (nVal) .

Global Instance Ren_ValListCompatContext { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (ValListCompatContext (mVal)) (ValListCompatContext (nVal)) := @ren_ValListCompatContext (mVal) (nVal) .

Global Instance Ren_choiceContext { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (choiceContext (mVal)) (choiceContext (nVal)) := @ren_choiceContext (mVal) (nVal) .

Global Instance Ren_exContext { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (exContext (mVal)) (exContext (nVal)) := @ren_exContext (mVal) (nVal) .
*)

Global Instance VarInstance_Val { mVal : nat } : Var ((fin) (mVal)) (Val (mVal)) := @var_Val (mVal) .

Notation "x '__Val'" := (var_Val x) (at level 5, format "x __Val") : subst_scope.

Notation "x '__Val'" := (@ids (_) (_) VarInstance_Val x) (at level 5, only printing, format "x __Val") : subst_scope.

Notation "'var'" := (var_Val) (only printing, at level 1) : subst_scope.

Class Up_Val X Y := up_Val : X -> Y.

Notation "↑__Val" := (up_Val) (only printing) : subst_scope.

Notation "↑__Val" := (up_Val_Val) (only printing) : subst_scope.

Global Instance Up_Val_Val { m : nat } { nVal : nat } : Up_Val (_) (_) := @up_Val_Val (m) (nVal) .

Notation "s [ sigmaVal ]" := (subst_Val sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Val sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Val xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Val xiVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_Exp sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Exp sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Exp xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Exp xiVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_SC sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_SC sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_scopeContext sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_scopeContext sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_ExpCompatContext sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_ExpCompatContext sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_ValCompatContext sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_ValCompatContext sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_ValListCompatContext sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_ValListCompatContext sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_choiceContext sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_choiceContext sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_exContext sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_exContext sigmaVal) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Val,  Subst_Exp,  Subst_SC,  Subst_scopeContext,  Subst_ExpCompatContext,  Subst_ValCompatContext,  Subst_ValListCompatContext,  Subst_choiceContext,  Subst_exContext,  Ren_Val,  Ren_Exp,  VarInstance_Val.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Val,  Subst_Exp,  Subst_SC,  Subst_scopeContext,  Subst_ExpCompatContext,  Subst_ValCompatContext,  Subst_ValListCompatContext,  Subst_choiceContext,  Subst_exContext,  Ren_Val,  Ren_Exp,  VarInstance_Val in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_Val| progress rewrite ?compComp_Val| progress rewrite ?compComp'_Val| progress rewrite ?instId_Exp| progress rewrite ?compComp_Exp| progress rewrite ?compComp'_Exp| progress rewrite ?instId_SC| progress rewrite ?compComp_SC| progress rewrite ?compComp'_SC| progress rewrite ?instId_scopeContext| progress rewrite ?compComp_scopeContext| progress rewrite ?compComp'_scopeContext| progress rewrite ?instId_ExpCompatContext| progress rewrite ?compComp_ExpCompatContext| progress rewrite ?compComp'_ExpCompatContext| progress rewrite ?instId_ValCompatContext| progress rewrite ?compComp_ValCompatContext| progress rewrite ?compComp'_ValCompatContext| progress rewrite ?instId_ValListCompatContext| progress rewrite ?compComp_ValListCompatContext| progress rewrite ?compComp'_ValListCompatContext| progress rewrite ?instId_choiceContext| progress rewrite ?compComp_choiceContext| progress rewrite ?compComp'_choiceContext| progress rewrite ?instId_exContext| progress rewrite ?compComp_exContext| progress rewrite ?compComp'_exContext| progress rewrite ?rinstId_Val| progress rewrite ?compRen_Val| progress rewrite ?compRen'_Val| progress rewrite ?renComp_Val| progress rewrite ?renComp'_Val| progress rewrite ?renRen_Val| progress rewrite ?renRen'_Val| progress rewrite ?rinstId_Exp| progress rewrite ?compRen_Exp| progress rewrite ?compRen'_Exp| progress rewrite ?renComp_Exp| progress rewrite ?renComp'_Exp| progress rewrite ?renRen_Exp| progress rewrite ?renRen'_Exp| progress rewrite ?varL_Val| progress rewrite ?varLRen_Val| progress (unfold up_ren, upRen_Val_Val, up_Val_Val)| progress (cbn [subst_Val subst_Exp subst_SC subst_scopeContext subst_ExpCompatContext subst_ValCompatContext subst_ValListCompatContext subst_choiceContext subst_exContext ren_Val ren_Exp])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_Val in *| progress rewrite ?compComp_Val in *| progress rewrite ?compComp'_Val in *| progress rewrite ?instId_Exp in *| progress rewrite ?compComp_Exp in *| progress rewrite ?compComp'_Exp in *| progress rewrite ?instId_SC in *| progress rewrite ?compComp_SC in *| progress rewrite ?compComp'_SC in *| progress rewrite ?instId_scopeContext in *| progress rewrite ?compComp_scopeContext in *| progress rewrite ?compComp'_scopeContext in *| progress rewrite ?instId_ExpCompatContext in *| progress rewrite ?compComp_ExpCompatContext in *| progress rewrite ?compComp'_ExpCompatContext in *| progress rewrite ?instId_ValCompatContext in *| progress rewrite ?compComp_ValCompatContext in *| progress rewrite ?compComp'_ValCompatContext in *| progress rewrite ?instId_ValListCompatContext in *| progress rewrite ?compComp_ValListCompatContext in *| progress rewrite ?compComp'_ValListCompatContext in *| progress rewrite ?instId_choiceContext in *| progress rewrite ?compComp_choiceContext in *| progress rewrite ?compComp'_choiceContext in *| progress rewrite ?instId_exContext in *| progress rewrite ?compComp_exContext in *| progress rewrite ?compComp'_exContext in *| progress rewrite ?rinstId_Val in *| progress rewrite ?compRen_Val in *| progress rewrite ?compRen'_Val in *| progress rewrite ?renComp_Val in *| progress rewrite ?renComp'_Val in *| progress rewrite ?renRen_Val in *| progress rewrite ?renRen'_Val in *| progress rewrite ?rinstId_Exp in *| progress rewrite ?compRen_Exp in *| progress rewrite ?compRen'_Exp in *| progress rewrite ?renComp_Exp in *| progress rewrite ?renComp'_Exp in *| progress rewrite ?renRen_Exp in *| progress rewrite ?renRen'_Exp in *| progress rewrite ?varL_Val in *| progress rewrite ?varLRen_Val in *| progress (unfold up_ren, upRen_Val_Val, up_Val_Val in *)| progress (cbn [subst_Val subst_Exp subst_SC subst_scopeContext subst_ExpCompatContext subst_ValCompatContext subst_ValListCompatContext subst_choiceContext subst_exContext ren_Val ren_Exp] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_Val); try repeat (erewrite rinstInst_Exp).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_Val); try repeat (erewrite <- rinstInst_Exp).


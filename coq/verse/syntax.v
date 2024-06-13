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
Inductive Val (n : nat) : Type :=
  | var_Val : fin n -> Val n
  | Int : nat -> Val n
  | Prim : Op -> Val n
  | Tuple : list (Val n) -> Val n
  | Lam : Exp (S n) -> Val n
 with Exp (n : nat) : Type :=
  | Ret : Val n -> Exp n
  | App : Val n -> Val n -> Exp n
  | Seq : Exp n -> Exp  n -> Exp n
  | Unify : Val n -> Exp  n -> Exp n
  | Exists : Exp (S n) -> Exp n
  | Or : Exp  n -> Exp  n -> Exp n
  | Fail : Exp n
  | One : Exp n -> Exp n
  | All : Exp n -> Exp n.

Lemma congr_Int { m : nat } { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : Int m s0 = Int m t0 .
Proof. congruence. Qed.

Lemma congr_Prim { m : nat } { s0 : Op   } { t0 : Op   } (H1 : s0 = t0) : Prim m s0 = Prim m t0 .
Proof. congruence. Qed.

Lemma congr_Tuple { m : nat } { s0 : list (Val  m) } { t0 : list (Val  m) } (H1 : s0 = t0) : Tuple m s0 = Tuple m t0 .
Proof. congruence. Qed.

Lemma congr_Lam { m : nat } { s0 : Exp  (S m) } { t0 : Exp  (S m) } (H1 : s0 = t0) : Lam m s0 = Lam m t0 .
Proof. congruence. Qed.

Lemma congr_Ret { m : nat } { s0 : Val  m } { t0 : Val  m } (H1 : s0 = t0) : Ret m s0 = Ret m t0 .
Proof. congruence. Qed.

Lemma congr_App { m : nat } { s0 : Val  m } { s1 : Val  m } { t0 : Val  m } { t1 : Val  m } (H1 : s0 = t0) (H2 : s1 = t1) : App m s0 s1 = App m t0 t1 .
Proof. congruence. Qed.

Lemma congr_Seq { m : nat } { s0 : Exp  m } { s1 : Exp  m } { t0 : Exp  m } { t1 : Exp  m } (H1 : s0 = t0) (H2 : s1 = t1) : Seq m s0 s1 = Seq m t0 t1 .
Proof. congruence. Qed.

Lemma congr_Unify { m : nat } { s0 : Val  m } { s1 : Exp  m } { t0 : Val  m } { t1 : Exp  m } (H1 : s0 = t0) (H2 : s1 = t1) : Unify m s0 s1 = Unify m t0 t1 .
Proof. congruence. Qed.

Lemma congr_Exists { m : nat } { s0 : Exp  (S m) } { t0 : Exp  (S m) } (H1 : s0 = t0) : Exists m s0 = Exists m t0 .
Proof. congruence. Qed.

Lemma congr_Or { m : nat } { s0 : Exp  m } { s1 : Exp  m } { t0 : Exp  m } { t1 : Exp  m } (H1 : s0 = t0) (H2 : s1 = t1) : Or m s0 s1 = Or m t0 t1 .
Proof. congruence. Qed.

Lemma congr_Fail { m : nat } : Fail m = Fail m .
Proof. congruence. Qed.

Lemma congr_One { m : nat } { s0 : Exp  m } { t0 : Exp  m } (H1 : s0 = t0) : One m s0 = One m t0 .
Proof. congruence. Qed.

Lemma congr_All { m : nat } { s0 : Exp  m } { t0 : Exp  m } (H1 : s0 = t0) : All m s0 = All m t0 .
Proof. congruence. Qed.

Lemma congr_nil {A} : (nil : list A) = nil. Proof. reflexivity. Qed.

Lemma congr_cons {A} {x y : A} {xs ys : list A} (H1 : x = y) (H2 : xs = ys) : cons x xs = cons y ys.
Proof. congruence. Qed.

Definition upRen_Val_Val { m : nat } { n : nat } (xi : fin m -> fin (n)) : fin (S m) -> fin (S (n)) :=
  (up_ren) xi.


Fixpoint ren_Val { m : nat } { n : nat } (xiVal : fin m -> fin n) (s : Val m) : Val n :=
  let ren_Vals (vs : list (Val m)) := List.map (ren_Val xiVal) vs in
    match s return Val n with
    | var_Val (_) s => (var_Val n) (xiVal s)
    | Int (_) s0 => Int n ((fun x => x) s0)
    | Prim (_) s0 => Prim n ((fun x => x) s0)
    | Tuple (_) s0 => Tuple n (ren_Vals s0)
    | Lam (_) s0 => Lam n ((ren_Exp (upRen_Val_Val xiVal)) s0)
    end
 with ren_Exp { m : nat } { n : nat } (xiVal : fin m -> fin n) (s : Exp m) : Exp n :=
    match s return Exp n with
    | Ret (_) s0 => Ret n ((ren_Val xiVal) s0)
    | App (_) s0 s1 => App n ((ren_Val xiVal) s0) ((ren_Val xiVal) s1)
    | Seq (_) s0 s1 => Seq n ((ren_Exp xiVal) s0) ((ren_Exp xiVal) s1)
    | Unify (_) s0 s1 => Unify n ((ren_Val xiVal) s0) ((ren_Exp xiVal) s1)
    | Exists (_) s0 => Exists n ((ren_Exp (upRen_Val_Val xiVal)) s0)
    | Or (_) s0 s1 => Or n ((ren_Exp xiVal) s0) ((ren_Exp xiVal) s1)
    | Fail (_)  => Fail n
    | One (_) s0 => One n ((ren_Exp xiVal) s0)
    | All (_) s0 => All n ((ren_Exp xiVal) s0)
    end.

Definition ren_Vals {m}{n} (xiVal : fin m -> fin n) (vs : list (Val m)) := 
  List.map (ren_Val xiVal) vs.

Definition up_Val_Val { m : nat } { n : nat } (sigma : fin m -> Val n) : fin (S m) -> Val (S n) :=
  (scons) ((var_Val (S n)) (var_zero)) ((funcomp) (ren_Val (shift)) sigma).

Fixpoint subst_Val { m : nat } { n : nat } (sigmaVal : fin m -> Val n) (s : Val m) : Val n :=
  let subst_Vals (vs : list (Val m)) := 
    List.map (subst_Val sigmaVal) vs in
    match s return Val n with
    | var_Val (_) s => sigmaVal s
    | Int (_) s0 => Int n ((fun x => x) s0)
    | Prim (_) s0 => Prim n ((fun x => x) s0)
    | Tuple (_) s0 => Tuple n (subst_Vals s0)
    | Lam (_) s0 => Lam n ((subst_Exp (up_Val_Val sigmaVal)) s0)
    end
 with subst_Exp { m : nat } { n : nat } (sigmaVal : fin m -> Val n) (s : Exp m) : Exp n :=
    match s return Exp n with
    | Ret (_) s0 => Ret n ((subst_Val sigmaVal) s0)
    | App (_) s0 s1 => App n ((subst_Val sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | Seq (_) s0 s1 => Seq n ((subst_Exp sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Unify (_) s0 s1 => Unify n ((subst_Val sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Exists (_) s0 => Exists n ((subst_Exp (up_Val_Val sigmaVal)) s0)
    | Or (_) s0 s1 => Or n ((subst_Exp sigmaVal) s0) ((subst_Exp sigmaVal) s1)
    | Fail (_)  => Fail n
    | One (_) s0 => One n ((subst_Exp sigmaVal) s0)
    | All (_) s0 => All n ((subst_Exp sigmaVal) s0)
    end.

Definition subst_Vals { m : nat } { n : nat } (sigmaVal : fin m -> Val n) 
  (vs : list (Val m)) : list (Val n) := List.map (subst_Val sigmaVal) vs.

Definition upId_Val_Val { m : nat } (sigma : fin m -> Val m) (Eq : forall x, sigma x = (var_Val m) x) : forall x, (up_Val_Val sigma) x = (var_Val (S m)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.


Definition idSubst_nil { m } : 
  forall (sigmaVal : fin m -> Val m), subst_Vals sigmaVal nil = nil := fun s => eq_refl.


Fixpoint idSubst_Val { m : nat } (sigmaVal : fin m -> Val m) (EqVal : forall x, sigmaVal x = (var_Val m) x) (s : Val m) : subst_Val sigmaVal s = s :=
  let fix idSubst_Vals (vs : list (Val m)) : subst_Vals sigmaVal vs = vs := 
         match vs with
         | nil => idSubst_nil sigmaVal
         | cons v vs' => congr_cons (idSubst_Val sigmaVal EqVal v) (idSubst_Vals vs')
         end in
    match s return subst_Val sigmaVal s = s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (idSubst_Vals s0)
    | Lam (_) s0 => congr_Lam ((idSubst_Exp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    end
 with idSubst_Exp { m : nat } (sigmaVal : fin m -> Val m) (EqVal : forall x, sigmaVal x = (var_Val m) x) (s : Exp m) : subst_Exp sigmaVal s = s :=
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

Definition upExtRen_Val_Val { m : nat } { n : nat } (xi : fin m -> fin (n)) (zeta : fin m -> fin (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_Val_Val xi) x = (upRen_Val_Val zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_Val { m : nat } { n : nat } (xiVal : fin m -> fin n) (zetaVal : fin m -> fin n) (EqVal : forall x, xiVal x = zetaVal x) (s : Val m) : ren_Val xiVal s = ren_Val zetaVal s :=
    let fix extRen_Vals (vs : list (Val m)) := 
      match vs return ren_Vals xiVal vs = ren_Vals zetaVal vs with 
      | nil => eq_refl
      | cons v vs' => congr_cons (extRen_Val xiVal zetaVal EqVal v) (extRen_Vals vs')
        end in
    match s return ren_Val xiVal s = ren_Val zetaVal s with
    | var_Val (_) s => (ap) (var_Val n) (EqVal s)
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (extRen_Vals s0)
    | Lam (_) s0 => congr_Lam ((extRen_Exp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s0)
    end
 with extRen_Exp { m : nat } { n : nat } (xiVal : fin m -> fin n) (zetaVal : fin m -> fin n) (EqVal : forall x, xiVal x = zetaVal x) (s : Exp m) : ren_Exp xiVal s = ren_Exp zetaVal s :=
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

Definition upExt_Val_Val { m : nat } { n : nat } (sigma : fin m -> Val n) (tau : fin m -> Val n) (Eq : forall x, sigma x = tau x) : forall x, (up_Val_Val sigma) x = (up_Val_Val tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_Val { m : nat } { n : nat } (sigmaVal : fin m -> Val n) (tauVal : fin m -> Val n) (EqVal : forall x, sigmaVal x = tauVal x) (s : Val m) : subst_Val sigmaVal s = subst_Val tauVal s :=
    let fix ext_Vals (vs : list (Val m)) :=       
      match vs return subst_Vals sigmaVal vs = subst_Vals tauVal vs with  
      | nil => eq_refl
      | cons v vs' => congr_cons (ext_Val sigmaVal tauVal EqVal v) (ext_Vals vs')
      end in
    match s return subst_Val sigmaVal s = subst_Val tauVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (ext_Vals s0)
    | Lam (_) s0 => congr_Lam ((ext_Exp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    end
 with ext_Exp { m : nat } { n : nat } (sigmaVal : fin m -> Val n) (tauVal : fin m -> Val n) (EqVal : forall x, sigmaVal x = tauVal x) (s : Exp m) : subst_Exp sigmaVal s = subst_Exp tauVal s :=
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

Definition up_ren_ren_Val_Val { k : nat } { l : nat } { m : nat } (xi : fin (k) -> fin (l)) (tau : fin (l) -> fin m) (theta : fin (k) -> fin m) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_Val_Val tau) (upRen_Val_Val xi)) x = (upRen_Val_Val theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_Val { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (rhoVal : fin m -> fin (lVal)) (EqVal : forall x, ((funcomp) zetaVal xiVal) x = rhoVal x) (s : Val m) : ren_Val zetaVal (ren_Val xiVal s) = ren_Val rhoVal s :=
  let fix compRenRen_Vals (vs : list (Val m)) := 
    match vs return ren_Vals zetaVal (ren_Vals xiVal vs) = ren_Vals rhoVal vs with 
    | nil => eq_refl
    | cons v vs' => congr_cons (compRenRen_Val xiVal zetaVal rhoVal EqVal v)
                              (compRenRen_Vals vs')
    end in
    match s return ren_Val zetaVal (ren_Val xiVal s) = ren_Val rhoVal s with
    | var_Val (_) s => (ap) (var_Val (lVal)) (EqVal s)
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (compRenRen_Vals s0)
    | Lam (_) s0 => congr_Lam ((compRenRen_Exp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s0)
    end
 with compRenRen_Exp { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (rhoVal : fin m -> fin (lVal)) (EqVal : forall x, ((funcomp) zetaVal xiVal) x = rhoVal x) (s : Exp m) : ren_Exp zetaVal (ren_Exp xiVal s) = ren_Exp rhoVal s :=
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

Definition up_ren_subst_Val_Val { k : nat } { l : nat } { m : nat } (xi : fin (k) -> fin (l)) (tau : fin (l) -> Val m) (theta : fin (k) -> Val m) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_Val_Val tau) (upRen_Val_Val xi)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_Val { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (thetaVal : fin m -> Val (lVal)) (EqVal : forall x, ((funcomp) tauVal xiVal) x = thetaVal x) (s : Val m) : subst_Val tauVal (ren_Val xiVal s) = subst_Val thetaVal s :=
  let fix compRenSubst_Vals (vs : list (Val m)) := 
    match vs return subst_Vals tauVal (ren_Vals xiVal vs) = subst_Vals thetaVal vs with
    | nil => eq_refl
    | cons v vs' => congr_cons (compRenSubst_Val xiVal tauVal thetaVal EqVal v)
                              (compRenSubst_Vals vs')
    end in
    match s return subst_Val tauVal (ren_Val xiVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (compRenSubst_Vals s0)
    | Lam (_) s0 => congr_Lam ((compRenSubst_Exp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compRenSubst_Exp { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (thetaVal : fin m -> Val (lVal)) (EqVal : forall x, ((funcomp) tauVal xiVal) x = thetaVal x) (s : Exp m) : subst_Exp tauVal (ren_Exp xiVal s) = subst_Exp thetaVal s :=
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

Definition up_subst_ren_Val_Val { k : nat } { lVal : nat } { m : nat } (sigma : fin (k) -> Val (lVal)) (zetaVal : fin (lVal) -> fin m) (theta : fin (k) -> Val m) (Eq : forall x, ((funcomp) (ren_Val zetaVal) sigma) x = theta x) : forall x, ((funcomp) (ren_Val (upRen_Val_Val zetaVal)) (up_Val_Val sigma)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_Val (shift) (upRen_Val_Val zetaVal) ((funcomp) (shift) zetaVal) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_Val zetaVal (shift) ((funcomp) (shift) zetaVal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_Val { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (thetaVal : fin m -> Val (lVal)) (EqVal : forall x, ((funcomp) (ren_Val zetaVal) sigmaVal) x = thetaVal x) (s : Val m) : ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val thetaVal s :=
  let fix compSubstRen_Vals (vs : list( Val m)) := 
    match vs return ren_Vals zetaVal (subst_Vals sigmaVal vs) = subst_Vals thetaVal vs with
    | nil => eq_refl
    | cons v vs' => congr_cons (compSubstRen_Val sigmaVal zetaVal thetaVal EqVal v)
                              (compSubstRen_Vals vs')
    end in
    match s return
          ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (compSubstRen_Vals s0)
    | Lam (_) s0 => congr_Lam ((compSubstRen_Exp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compSubstRen_Exp { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (thetaVal : fin m -> Val (lVal)) (EqVal : forall x, ((funcomp) (ren_Val zetaVal) sigmaVal) x = thetaVal x) (s : Exp m) : ren_Exp zetaVal (subst_Exp sigmaVal s) = subst_Exp thetaVal s :=
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

Definition up_subst_subst_Val_Val { k : nat } { lVal : nat } { m : nat } (sigma : fin (k) -> Val (lVal)) (tauVal : fin (lVal) -> Val m) (theta : fin (k) -> Val m) (Eq : forall x, ((funcomp) (subst_Val tauVal) sigma) x = theta x) : forall x, ((funcomp) (subst_Val (up_Val_Val tauVal)) (up_Val_Val sigma)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_Val (shift) (up_Val_Val tauVal) ((funcomp) (up_Val_Val tauVal) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_Val tauVal (shift) ((funcomp) (ren_Val (shift)) tauVal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_Val { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (thetaVal : fin m -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : Val m) : subst_Val tauVal (subst_Val sigmaVal s) = subst_Val thetaVal s :=
  let fix compSubstSubst_Vals (vs : list (Val m)) :=
    match vs  return subst_Vals tauVal (subst_Vals sigmaVal vs) = subst_Vals thetaVal vs with
    | nil => eq_refl
    | cons v vs' => congr_cons (compSubstSubst_Val sigmaVal tauVal thetaVal EqVal v)
                              (compSubstSubst_Vals vs')
    end in 
    match s return subst_Val tauVal (subst_Val sigmaVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (compSubstSubst_Vals s0)
    | Lam (_) s0 => congr_Lam ((compSubstSubst_Exp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    end
 with compSubstSubst_Exp { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (thetaVal : fin m -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : Exp m) : subst_Exp tauVal (subst_Exp sigmaVal s) = subst_Exp thetaVal s :=
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

Definition rinstInst_up_Val_Val { m : nat } { n : nat } (xi : fin m -> fin n) (sigma : fin m -> Val n) (Eq : forall x, ((funcomp) (var_Val n) xi) x = sigma x) : forall x, ((funcomp) (var_Val (S n)) (upRen_Val_Val xi)) x = (up_Val_Val sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_Val { m : nat } { n : nat } (xiVal : fin m -> fin n) (sigmaVal : fin m -> Val n) (EqVal : forall x, ((funcomp) (var_Val n) xiVal) x = sigmaVal x) (s : Val m) : ren_Val xiVal s = subst_Val sigmaVal s :=
  let fix rinst_inst_Vals (vs : list (Val m)) := 
    match vs return ren_Vals xiVal vs = subst_Vals sigmaVal vs with
    | nil => eq_refl
    | cons v vs' => congr_cons (rinst_inst_Val xiVal sigmaVal EqVal v) (rinst_inst_Vals vs') 
    end in
    match s return ren_Val xiVal s = subst_Val sigmaVal s with
    | var_Val (_) s => EqVal s
    | Int (_) s0 => congr_Int ((fun x => (eq_refl) x) s0)
    | Prim (_) s0 => congr_Prim ((fun x => (eq_refl) x) s0)
    | Tuple (_) s0 => congr_Tuple (rinst_inst_Vals s0)
    | Lam (_) s0 => congr_Lam ((rinst_inst_Exp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s0)
    end
 with rinst_inst_Exp { m : nat } { n : nat } (xiVal : fin m -> fin n) (sigmaVal : fin m -> Val n) (EqVal : forall x, ((funcomp) (var_Val n) xiVal) x = sigmaVal x) (s : Exp m) : ren_Exp xiVal s = subst_Exp sigmaVal s :=
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

Lemma rinstInst_Val { m : nat } { n : nat } (xiVal : fin m -> fin n) : ren_Val xiVal = subst_Val ((funcomp) (var_Val n) xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Val xiVal (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_Exp { m : nat } { n : nat } (xiVal : fin m -> fin n) : ren_Exp xiVal = subst_Exp ((funcomp) (var_Val n) xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Exp xiVal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_Val { m : nat } : subst_Val (var_Val m) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Val (var_Val m) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_Exp { m : nat } : subst_Exp (var_Val m) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Exp (var_Val m) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_Val { m : nat } : @ren_Val m m (id) = id .
Proof. exact ((eq_trans) (rinstInst_Val ((id) (_))) instId_Val). Qed.

Lemma rinstId_Exp { m : nat } : @ren_Exp m m (id) = id .
Proof. exact ((eq_trans) (rinstInst_Exp ((id) (_))) instId_Exp). Qed.

Lemma varL_Val { m : nat } { n : nat } (sigmaVal : fin m -> Val n) : (funcomp) (subst_Val sigmaVal) (var_Val m) = sigmaVal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_Val { m : nat } { n : nat } (xiVal : fin m -> fin n) : (funcomp) (ren_Val xiVal) (var_Val m) = (funcomp) (var_Val n) xiVal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_Val { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (s : Val m) : subst_Val tauVal (subst_Val sigmaVal s) = subst_Val ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_Val sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp_Exp { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (s : Exp m) : subst_Exp tauVal (subst_Exp sigmaVal s) = subst_Exp ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_Exp sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_Val { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (tauVal : fin (kVal) -> Val (lVal)) : (funcomp) (subst_Val tauVal) (subst_Val sigmaVal) = subst_Val ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Val sigmaVal tauVal n)). Qed.

Lemma compComp'_Exp { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (tauVal : fin (kVal) -> Val (lVal)) : (funcomp) (subst_Exp tauVal) (subst_Exp sigmaVal) = subst_Exp ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Exp sigmaVal tauVal n)). Qed.

Lemma compRen_Val { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (s : Val m) : ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val ((funcomp) (ren_Val zetaVal) sigmaVal) s .
Proof. exact (compSubstRen_Val sigmaVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma compRen_Exp { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (s : Exp m) : ren_Exp zetaVal (subst_Exp sigmaVal s) = subst_Exp ((funcomp) (ren_Val zetaVal) sigmaVal) s .
Proof. exact (compSubstRen_Exp sigmaVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_Val { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) : (funcomp) (ren_Val zetaVal) (subst_Val sigmaVal) = subst_Val ((funcomp) (ren_Val zetaVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Val sigmaVal zetaVal n)). Qed.

Lemma compRen'_Exp { kVal : nat } { lVal : nat } { m : nat } (sigmaVal : fin m -> Val (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) : (funcomp) (ren_Exp zetaVal) (subst_Exp sigmaVal) = subst_Exp ((funcomp) (ren_Val zetaVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Exp sigmaVal zetaVal n)). Qed.

Lemma renComp_Val { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (s : Val m) : subst_Val tauVal (ren_Val xiVal s) = subst_Val ((funcomp) tauVal xiVal) s .
Proof. exact (compRenSubst_Val xiVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma renComp_Exp { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (tauVal : fin (kVal) -> Val (lVal)) (s : Exp m) : subst_Exp tauVal (ren_Exp xiVal s) = subst_Exp ((funcomp) tauVal xiVal) s .
Proof. exact (compRenSubst_Exp xiVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_Val { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (tauVal : fin (kVal) -> Val (lVal)) : (funcomp) (subst_Val tauVal) (ren_Val xiVal) = subst_Val ((funcomp) tauVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Val xiVal tauVal n)). Qed.

Lemma renComp'_Exp { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (tauVal : fin (kVal) -> Val (lVal)) : (funcomp) (subst_Exp tauVal) (ren_Exp xiVal) = subst_Exp ((funcomp) tauVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Exp xiVal tauVal n)). Qed.

Lemma renRen_Val { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (s : Val m) : ren_Val zetaVal (ren_Val xiVal s) = ren_Val ((funcomp) zetaVal xiVal) s .
Proof. exact (compRenRen_Val xiVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma renRen_Exp { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) (s : Exp m) : ren_Exp zetaVal (ren_Exp xiVal s) = ren_Exp ((funcomp) zetaVal xiVal) s .
Proof. exact (compRenRen_Exp xiVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_Val { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) : (funcomp) (ren_Val zetaVal) (ren_Val xiVal) = ren_Val ((funcomp) zetaVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Val xiVal zetaVal n)). Qed.

Lemma renRen'_Exp { kVal : nat } { lVal : nat } { m : nat } (xiVal : fin m -> fin (kVal)) (zetaVal : fin (kVal) -> fin (lVal)) : (funcomp) (ren_Exp zetaVal) (ren_Exp xiVal) = ren_Exp ((funcomp) zetaVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Exp xiVal zetaVal n)). Qed.

End ValExp.

Arguments var_Val {n}.

Arguments Int {n}.

Arguments Prim {n}.

Arguments Tuple {n}.

Arguments Lam {n}.

Arguments Ret {n}.

Arguments App {n}.

Arguments Seq {n}.

Arguments Unify {n}.

Arguments Exists {n}.

Arguments Or {n}.

Arguments Fail {n}.

Arguments One {n}.

Arguments All {n}.

Global Instance Subst_Val { m : nat } { n : nat } : Subst1 (fin m -> Val n) (Val m) (Val n) := @subst_Val m n .

Global Instance Subst_Exp { m : nat } { n : nat } : Subst1 (fin m -> Val n) (Exp m) (Exp n) := @subst_Exp m n .

Global Instance Ren_Val { m : nat } { n : nat } : Ren1 (fin m -> fin n) (Val m) (Val n) := @ren_Val m n .

Global Instance Ren_Exp { m : nat } { n : nat } : Ren1 (fin m -> fin n) (Exp m) (Exp n) := @ren_Exp m n .

Global Instance VarInstance_Val { m : nat } : Var (fin m) (Val m) := @var_Val m .

Class Up_Val X Y := up_Val : X -> Y.

Global Instance Up_Val_Val { m : nat } { n : nat } : Up_Val (_) (_) := @up_Val_Val m n.

Module SubstNotations.

Notation "x '__Val'" := (var_Val x) (at level 5, format "x __Val") : subst_scope.

Notation "x '__Val'" := (@ids (_) (_) VarInstance_Val x) (at level 5, only printing, format "x __Val") : subst_scope.

Notation "'var'" := (var_Val) (only printing, at level 1) : subst_scope.

Notation "↑__Val" := (up_Val) (only printing) : subst_scope.

Notation "↑__Val" := (up_Val_Val) (only printing) : subst_scope.

Notation "s [ sigmaVal ]" := (subst_Val sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Val sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Val xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Val xiVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_Exp sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Exp sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Exp xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Exp xiVal) (at level 1, left associativity, only printing) : fscope.

End SubstNotations.


Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Val,  Subst_Exp,  Ren_Val,  Ren_Exp,  VarInstance_Val.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Val,  Subst_Exp,  Ren_Val,  Ren_Exp,  VarInstance_Val in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_Val| progress rewrite ?compComp_Val| progress rewrite ?compComp'_Val| progress rewrite ?instId_Exp| progress rewrite ?compComp_Exp| progress rewrite ?compComp'_Exp| progress rewrite ?rinstId_Val| progress rewrite ?compRen_Val| progress rewrite ?compRen'_Val| progress rewrite ?renComp_Val| progress rewrite ?renComp'_Val| progress rewrite ?renRen_Val| progress rewrite ?renRen'_Val| progress rewrite ?rinstId_Exp| progress rewrite ?compRen_Exp| progress rewrite ?compRen'_Exp| progress rewrite ?renComp_Exp| progress rewrite ?renComp'_Exp| progress rewrite ?renRen_Exp| progress rewrite ?renRen'_Exp| progress rewrite ?varL_Val| progress rewrite ?varLRen_Val| progress (unfold up_ren, upRen_Val_Val, up_Val_Val)| progress (cbn [subst_Val subst_Exp ren_Val ren_Exp])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_Val in *| progress rewrite ?compComp_Val in *| progress rewrite ?compComp'_Val in *| progress rewrite ?instId_Exp in *| progress rewrite ?compComp_Exp in *| progress rewrite ?compComp'_Exp in *| progress rewrite ?rinstId_Val in *| progress rewrite ?compRen_Val in *| progress rewrite ?compRen'_Val in *| progress rewrite ?renComp_Val in *| progress rewrite ?renComp'_Val in *| progress rewrite ?renRen_Val in *| progress rewrite ?renRen'_Val in *| progress rewrite ?rinstId_Exp in *| progress rewrite ?compRen_Exp in *| progress rewrite ?compRen'_Exp in *| progress rewrite ?renComp_Exp in *| progress rewrite ?renComp'_Exp in *| progress rewrite ?renRen_Exp in *| progress rewrite ?renRen'_Exp in *| progress rewrite ?varL_Val in *| progress rewrite ?varLRen_Val in *| progress (unfold up_ren, upRen_Val_Val, up_Val_Val in *)| progress (cbn [subst_Val subst_Exp ren_Val ren_Exp] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_Val); try repeat (erewrite rinstInst_Exp).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_Val); try repeat (erewrite <- rinstInst_Exp).


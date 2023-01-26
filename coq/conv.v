Require Export lc.tactics.
Require Export lc.relations.

Import LCNotations.
Local Open Scope lc_scope.

Local Notation "t ≡β t'"  := (conversion t t') 
    (at level 70, right associativity) : lc_scope.


Lemma conversion_lc : forall t u, t ≡β u -> lc_tm t /\ lc_tm u.
Proof. 
  intros t u H.
  induction H; split; split_hyp; auto with lngen.
  + pick fresh x.
    apply (lc_abs_exists x).
    spec x. split_hyp. auto.
  + pick fresh x.
    apply (lc_abs_exists x).
    spec x. split_hyp. auto.
Qed.

#[local]
Instance lc_conversion : lc conversion.
Proof. constructor. apply conversion_lc. apply conversion_lc. Qed.

(* Proposition 2.1.17 in Barendregt *)

#[local]
Instance subst1_conversion : substitutive conversion.
Proof.
  constructor.
  intros t t' x u LC Eq.
  induction Eq; simpl; eauto with lngen.
  + (* eq_beta *)
    autorewrite with lngen; auto.
    eapply eq_beta.
    match goal with 
    | [ H : lc_tm (abs ?t) |- _ ] => 
        inversion H;
        move: (subst_tm_lc_tm _ _ x H LC) => h
    end.
    auto.
    eauto with lngen.
  + (* eq_abs *)
    pick fresh y and apply eq_abs. 
    spec y.
    autorewrite with lngen in H0; auto.
Qed.

Lemma subst2_conversion : forall x t u u', 
    lc_tm t -> 
    u ≡β u' -> t [ x ~> u ] ≡β t [ x ~> u' ].
Proof.
  intros x t u u' LC EQ.
  induction LC; simpl; eauto.
  + (* var *)
    destruct (x0 == x); auto.
  + (* abs *)
    pick fresh y and apply eq_abs.
    spec y.
    autorewrite with lngen in H0; eauto with lngen; eauto using lc1,lc2.
  + (*  app *)
    eapply eq_trans with (t2 := app (t [x ~> u]) (u0 [x ~> u'])).
    eapply eq_app2; eauto using lc1,lc2.
    eapply eq_app1; eauto using lc1,lc2.
Qed.

Lemma conversion_subst3 : forall x t t' u u', 
    t ≡β t' -> u ≡β u' -> t [ x ~> u ] ≡β t' [ x ~> u' ].
Proof.
  intros.
  apply eq_trans with (t2 := t' [ x ~> u ]).
  eapply subst1_conversion; eauto using lc1.
  eapply subst2_conversion; eauto using lc2.
Qed.

Lemma conversion_compatible : compatible conversion.
Proof.
  constructor.
  intros.
  + intros. pick fresh y and apply eq_abs.
    rewrite (subst_tm_intro x); auto.
    rewrite (subst_tm_intro x u); auto.
    apply subst; eauto.
  + intros. eauto.
  + intros. eauto.
Qed.

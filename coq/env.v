Require Export lc.tactics.
Require Export lc.relations.
Require Import Coq.Logic.FunctionalExtensionality.

Import LCNotations.
Local Open Scope lc_scope.

Section Env.

Variable Value : Type.

Polymorphic Definition GEnv := atom -> Value.

Definition env_cons : atom -> Value -> GEnv -> GEnv := 
  fun x v γ => fun y => match (x == y) with 
                  | left _ => v
                  | right pf => γ y
                  end.

Lemma cons_cons : forall x y z v γ, 
    z <> y ->
    z <> x ->
    env_cons y ((env_cons z v γ) x) (env_cons z v γ) = env_cons z v (env_cons y (γ x) γ).
Proof.
  intros.
  unfold env_cons.
  extensionality w.
  destruct (y == w) eqn:YW;
  destruct (z == w) eqn:ZW; auto.
  + subst. done. 
  + subst. destruct (z == x). subst. done. done.
Qed.     

End Env.

Arguments env_cons {_}.
Arguments cons_cons {_}.

Module EnvNotations.
Notation "x ⤇ v ● ρ" := (env_cons x v ρ) (at level 60).
End EnvNotations.

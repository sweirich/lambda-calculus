(* Derived From coq-ext-lib/theories/structures/Functor / Applicative / Monad *)
(* Also includes Alternative *)

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Require Import Coq.Lists.List.

Declare Scope monad_scope.

Polymorphic Class Functor@{d c} (F : Type@{d} -> Type@{c}) : Type :=
{ fmap : forall {A B : Type@{d}}, (A -> B) -> F A -> F B }.

Polymorphic Definition ID@{d} {T : Type@{d}} (f : T -> T) : Prop :=
  forall x : T, f x = x.

Module FunctorNotation.
  Notation "f <$> x" := (@fmap _ _ _ _ f x) (at level 52, left associativity).
End FunctorNotation.


Class Applicative@{d c} (T : Type@{d} -> Type@{c}) :=
{ pure : forall {A : Type@{d}}, A -> T A
; ap : forall {A B : Type@{d}}, T (A -> B) -> T A -> T B
}.

Module ApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 52, left associativity).
End ApplicativeNotation.
Import ApplicativeNotation.

Section applicative.
  Definition liftA@{d c} {T : Type@{d} -> Type@{c}} {AT:Applicative@{d c} T} {A B : Type@{d}} (f:A -> B) (aT:T A) : T B := pure f <*> aT.
  Definition liftA2@{d c} {T : Type@{d} -> Type@{c}} {AT:Applicative@{d c} T} {A B C : Type@{d}} (f:A -> B -> C) (aT:T A) (bT:T B) : T C := liftA f aT <*> bT.
End applicative.

Section Instances.

Universe d c.
Context (T : Type@{d} -> Type@{c}) {AT : Applicative T}.

Global Instance Functor_Applicative@{} : Functor T :=
{ fmap := @liftA _ _ }.

End Instances.


Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Section monadic.

  Definition liftM@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U : Type@{d}} (f : T -> U) : m T -> m U :=
    fun x => bind x (fun x => ret (f x)).

  Definition liftM2@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U V : Type@{d}} (f : T -> U -> V) : m T -> m U -> m V :=
    Eval cbv beta iota zeta delta [ liftM ] in
      fun x y => bind x (fun x => liftM (f x) y).

  Definition liftM3@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U V W : Type@{d}} (f : T -> U -> V -> W) : m T -> m U -> m V -> m W :=
    Eval cbv beta iota zeta delta [ liftM2 ] in
      fun x y z => bind x (fun x => liftM2 (f x) y z).

  Definition apM@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {A B : Type@{d}} (fM:m (A -> B)) (aM:m A) : m B :=
    bind fM (fun f => liftM f aM).

  (* Left-to-right composition of Kleisli arrows. *)
  Definition mcompose@{c d}
             {m:Type@{d}->Type@{c}}
             {M: Monad m}
             {T U V:Type@{d}}
             (f: T -> m U) (g: U -> m V): (T -> m V) :=
    fun x => bind (f x) g.

  Definition join@{d c} {m : Type@{d} -> Type@{c}} {a} `{Monad m} : m (m a) -> m a :=
    fun x => bind x (fun y => y).

End monadic.

Module MonadBaseNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 61, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 61, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad
    (at level 61, right associativity) : monad_scope.

End MonadBaseNotation.

Module MonadNotation.

  Export MonadBaseNotation.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

End MonadNotation.

Module MonadLetNotation.

  Export MonadBaseNotation.

  Notation "'let*' p ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity) : monad_scope.

End MonadLetNotation.

Section Instances.

Universe d c.
Context (m : Type@{d} -> Type@{c}) {M : Monad m}.

Global Instance Functor_Monad@{} : Functor m :=
{ fmap := @liftM _ _ }.

Global Instance Applicative_Monad@{} : Applicative m :=
{ pure := @ret _ _
; ap := @apM _ _
}.

End Instances.

(* ---------------- Alternative ---------------- *)

Class Alternative@{d c} (m : Type@{d} -> Type@{c}) : Type :=
  { empty  : forall {t : Type@{d}}, m t 
  ; choose : forall {t : Type@{d}}, m t -> m t -> m t
  }.

Module AlternativeNotation.
  Notation "f1 <|> f2" := (@choose _ _ _ f1 f2) (at level 52, left associativity).
End AlternativeNotation.



(* ---------------- Laws ---------------------- *)

(* asum in Haskell, for any foldable, not just list *)
Definition Any {A}{F : Type -> Type}`{Alternative F} : list (F A) -> F A :=
  fold_right choose empty.


Import AlternativeNotation.

Class AlternativeLaws {F} (Alt_F : Alternative F) := { 
    alt_lunit : 
       forall {A} (p : F A), (empty <|> p) = p;
    alt_runit : 
       forall {A} (p : F A), (p <|> empty) = p;
    alt_assoc : 
       forall{A} (p1 p2 p3 : F A), ((p1 <|> p2) <|> p3) = (p1 <|> (p2 <|> p3))
}.

Class MonadLaws {M : Type -> Type} (Monad_F : Monad M) := 
  {  bind_of_return : forall {A B} (a : A) (f : A -> M B),
      bind (ret a) f = f a;
     return_of_bind : forall {A} (aM: M A), bind aM ret = aM;
    bind_associativity :
  forall {A B C} (aM:M A) (f:A -> M B) (g:B -> M C),
        bind (bind aM f) g = bind aM (fun a => bind (f a) g)
  }.

Class FunctorLaws {F} (Functor_F : Functor F) :=
  { fmap_id : forall {T} (x : F T), fmap id x = x
  ; fmap_compose : forall {T U V} (f : T -> U) (g : U -> V) (x : F T),
        fmap (fun x => g (f x)) x = fmap g (fmap f x)
  }.


(* ------------------------------------------- *)                             



(* list monad *)


#[export] Instance Functor_list : Functor list :=
{ fmap := map }.

#[export] Instance Monad_list : Monad list :=
{ ret  := fun _ x => x :: nil; 
  bind := fun _ _ x f =>  flat_map f x
}.

#[export] Instance Alternative_list : Alternative list :=
  { empty := @nil ;
    choose := @app
  }.

(* option monad *)

#[export] Instance Fuctor_option : Functor option :=
  { fmap := @option_map }.
#[export] Instance Monad_option : Monad option :=
  { ret  := @Some ;
    bind := fun (A B : Type) (o : option A) (f : A -> option B) => match o with
                                                       | Some x => f x
                                                       | None => None
                                                       end }.
#[export] Instance Alternative_option : Alternative option :=
  { empty := @None ;
    choose := fun (A : Type) (x : option A) (y : option A) => 
                match x with 
                | Some x => Some x
                | None =>  y
                end
  }.

(* Identity monad *)

Definition Id : Type -> Type := fun x => x.

#[export] Instance Monad_Id : Monad Id :=
{ 
  ret := fun _ x => x;
  bind := fun _ _ x f => f x
}.

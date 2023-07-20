Require Export structures.Option.
Require Export structures.Sets.
Require Export structures.List.
Require Export structures.Env.
Require Export structures.Monad.


(*
  In : forall {A}, A -> M A -> Prop;

  (* Property holds of all elements in the container *)
  Forall  : forall {A} (P : A -> Prop), M A -> Prop ;

  (* Property holds of some element in the container *)
  Exists :  forall {A} (P : A -> Prop), M A -> Prop ;

  (* Versions in Type *)
  ForallT : forall {A} (P : A -> Type), M A -> Type ;
  ExistsT :  forall {A} (P : A -> Type), M A -> Type ;

  Forall_forall : forall {A} (P : A -> Prop) (l : M A), 
      Forall P l <-> (forall x, In x l -> P x) ;
  Exists_exists : forall {A} (P : A -> Prop) (l : M A), 
      Exists P l <-> (exists x, In x l /\ P x) ;


  Forall2 : forall {A B} (P : A -> B -> Prop), M A -> M B -> Prop ;

  (* Property holds of some corresponding pair of elements *)
  Exists2 : forall {A B} (P : A -> B -> Prop), M A -> M B -> Prop;

  Forall_Forall2 : forall {A} (P : A -> A -> Prop) (l:M A), 
       Forall (fun x => P x x) l <-> Forall2 P l l ;
  Exists_Exists2 : forall {A} (P : A -> A -> Prop) (l:M A), 
       Exists (fun x => P x x) l <-> Exists2 P l l 

*)

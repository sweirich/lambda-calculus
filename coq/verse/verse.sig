Val  : Type
Exp  : Type
Op : Type
nat : Type

opAdd : Op
opGt  : Op
opInt : Op


Int   : nat -> Val
Prim  : Op -> Val
Tuple : Val -> Val
Lam   : (Val -> Exp) -> Val

Ret   : Val -> Exp
App   : Val -> Val -> Exp
Seq   : Exp -> Exp -> Exp
Unify : Exp -> Exp -> Exp
Exists : (Val -> Exp) -> Exp
Or    : Exp -> Exp -> Exp
Fail  : Exp 
One   : Exp -> Exp
All   : Exp -> Exp

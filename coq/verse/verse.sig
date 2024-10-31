Val  : Type
Exp  : Type
Op : Type
nat : Type

list : Functor

opAdd : Op
opGt  : Op
opInt : Op


Int   : nat -> Val
Prim  : Op -> Val
Tuple : "list"(Val) -> Val
Lam   : (Val -> Exp) -> Val

Ret   : Val -> Exp
App   : Val -> Val -> Exp
Seq   : Exp -> Exp -> Exp
Unify : Val -> Exp -> Exp
Exists : (Val -> Exp) -> Exp
Or    : Exp -> Exp -> Exp
Fail  : Exp 
One   : Exp -> Exp
All   : Exp -> Exp

exContext : Type
Xhole : exContext
Xeqright : Val -> exContext -> Exp -> exContext
Xseqleft : exContext -> Exp -> exContext
Xseqright : Exp -> exContext -> exContext


-- ValContext : Type
-- ValListContext : Type
-- Vhole : ValContext
-- Vcons : ValListContext -> ValContext 
-- VXconsleft : ValContext -> "list" (Val) -> ValListContext 
-- VXconsright : Val -> ValListContext -> ValListContext


SC : Type
SCchoicehole : SC
SCchoiceleft : SC -> Exp -> SC
SCchoiceright : Exp -> SC -> SC

scopeContext : Type 
SXone : SC -> scopeContext
SXall : SC -> scopeContext

choiceContext : Type
CXhole : choiceContext
CXchoiceright : Val -> choiceContext -> Exp -> choiceContext
CXseqleft: choiceContext -> Exp -> choiceContext
CXseqright : Exp -> choiceContext -> choiceContext
CXexists : (Val -> choiceContext) -> choiceContext

ExpCompatContext : Type 
ValCompatContext : Type
ValListCompatContext : Type
EHole : ExpCompatContext -> ExpCompatContext
ESeq1 : ExpCompatContext -> Exp -> ExpCompatContext
ESeq2 : Exp -> ExpCompatContext -> ExpCompatContext
EUnify1 : ValCompatContext -> Exp -> ExpCompatContext
EUnify2 : Val -> ExpCompatContext -> ExpCompatContext
EExists : (Val -> ExpCompatContext) -> ExpCompatContext
EOr1 : ExpCompatContext -> Exp -> ExpCompatContext
EOr2 : Exp -> ExpCompatContext -> ExpCompatContext
EOne : ExpCompatContext -> ExpCompatContext
EAll : ExpCompatContext -> ExpCompatContext
EApp1 : ValCompatContext -> Val -> ExpCompatContext
EApp2 : Val -> ValCompatContext -> ExpCompatContext
ERet  :ValCompatContext -> ExpCompatContext
VTuple : ValListCompatContext  -> ValCompatContext
VLam  : (Val -> ExpCompatContext) -> ValCompatContext
VEcons1 : ValCompatContext -> "list" (Val) -> ValListCompatContext
VEcons2 : Val -> ValListCompatContext -> ValListCompatContext

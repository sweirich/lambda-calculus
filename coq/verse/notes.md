NOTES:

* The denotation of the function "\x. if x = 3 then loop else x" is:

         { 1 |-> 1 , 2 |-> 2 , 4 |-> 4 , ... }

  If the function diverges on a particular input there just isn't a result 
  in the table for that argument.

  On application, this will produce an empty set, because
  there won't be a matching domain.
  
How to represent (finite) choice?
---------------------------------
  
* We have: `one ( v | loop ) = v`

  This example means that we must interpret choose lazily.
  In other words, if one part of the sequence fails to terminate, then the 
  rest of the sequence should not be jeopardized.
  
* This means that we cannot just add a new constructor

        v_choice : list Value -> Value 
  
  to the semantic type `Value` because we cannot represent an infinite loop in
  the middle of a choice.
  
  Instead we need to do something like this to allow divergence inside of 
  choice. 
  
        denot t : list (P Value)
        denot (v | loop) = [ denot_v v ; {} ]
        
  Then, `one` can ignore the diverging term and `all` can detect it and 
  diverge.

* NOTE: it may be useful to distinguish between the denotation of a value and
  the denotation of an expression.
  
        denot_v t : P Value
        denot_e t : list (P Value)

* However, functions should be able to go wrong or fail or return 
  multiple results. What to do?
  
Do we need to modify  v_map : Value -> Value -> Value ?
-------------------------------------------------------

Can we still use the "graph" approximation of functions, even in the presence
of choice?

* The fact that the denotation of expressions produces a list 
  means that we need to have this type for LAMBDA:

      LAMBDA : (P Value -> list (P Value)) -> list (P Value)

* We can use the old type for APPLY 
  
      APPLY : P Value -> P Value -> P Value
  
  For function application, we use bind for CBV

      v1 <- denot e1 ;;
      v2 <- denot e2 ;;
      ret (APPLY v1 v2)

  If the denotation of e1 is a list of functions, i.e. functions that 
  return results
  
  This means that we would have the following equation:
  
     \x . (e1 | e2) == (\x . e1) | (\x. e2)

  Is that OK? One looks like a single result, and the other looks like 
  multiple results. 
  
* This approach is a bit suspicious. How do we define LAMBDA above?
  And doesn the equation above require the function to produce the same 
  set of choices for all arguments?

* Can we denote a function "\x. x | x + 1"  

  A list of sets:
  
      [ { 1 |-> 1 , 2 |-> 2 } ; { 1 |-> 2 , 2 |-> 3 , ... }  ]

  A set of lists:

      { [1 |-> 1 ; 1 |-> 2] , [2 |-> 2 ; 2 |-> 3] , ... } ]
       
* Can we denote:  "\x.  x | loop | x + 1"

  A list of sets: Yes!
  
    [ { 1 |-> 1 , 2 |-> 2 } ; {} ; { 1 |-> 2 , 2 |-> 3 , ... }  ]
  
  A set of lists: NO!
  
    { [1 |-> 1 ; ??? ; 1 |-> 2] , [2 |-> 2 ; ??? ; 2 |-> 3] , ... }


* Can we denote:  `\x.  x | loop | x + 1 | fail`

  A list of sets: Yes! (But, it looks the same as above...)
  
        [ { 1 |-> 1 , 2 |-> 2 } ; {} ; { 1 |-> 2 , 2 |-> 3 , ... }  ]

* Can we denote: "\x.fail"  

        [] 

  NOTE: this is the same as "fail"
  
        [] 

  But is different from "\x.loop"
  
        [ {} ]
    
* Can we denot: "\x. x<3" i.e. identity for 0,1,2 but fail for 3 and above?
 
        e1 = [ { 0|->0, 1|->1, 2|->2 } ]

  Is this different from:
  
        e2 = [ { 0|->0, 1|->1, 2|->2 } ; {} ]

  If we do an application `e1 3`
  
        v1 <- e1
        v2 <- [ v_nat 0 ] 
        ret (APPLY v1 v2)
  
  The APPLY operation cannot find anything, so returns `[ {} ]`
  a single diverging value.
  
  For the second version `e2 3` we have `[ {} ; {} ]`. That is different
  but not what we want (i.e. no value `[]` )
  
Idea: choice values + choice expressions
----------------------------------------

What if we add 

      v_multi : list Value -> Value 
      
to the domain and use `v_multi []` as the result of failing lambda
expressions. However, it is the responsibilty of the `return` operation 
to map `v_multi` into lists.

      return : P Value -> list (P Value)








Examples from verse paper:

( 1 | ( 2 | 3 ) ) = ( 1 | 2 | 3 )


one ( 1 | loop ) = 1

all ( 1 | loop ) = loop 


all ( 1 | 2 | 3 ) = < 1, 2, 3 >

exists x. < 1 , 2, 3 > x = ( 1 | 2 | 3 )


(ground) values 
  v ::= k | op | < v1 ... vn > | \x . e

Rules from verse paper for choice:

one (fail)  = fail
one (v)     = v
one (v | e) = v
all (fail)  = <> 
all (v1 | .. | vn) = < v1 .. vn >
fail | e    = e 
e | fail    = e 

Example with functions/one/choice:

one { (\x. (x | loop) 3 }

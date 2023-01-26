This file provides an overview of the use of the locally nameless
representation in Coq to prove the Church-Rosser theorem for the untyped
lambda calculus.

Unless otherwise specified, all files are in the `coq/` subdirectory.

1. Read over the language specification in `lc.ott` (toplevel directory) in 
   parallel with the Ott-generated definitions in `lc_ott.v`.
   
   The Ott file starts with the listing of the metavariables (i.e. the notation 
   that the file uses for lambda-calculus term variables, like `x`).

   The first grammar section specifies the syntax of the untyped lambda 
   calculus along with its related substitution and free variable 
   functions. 
   
   The second grammar section adds syntax for arbitrary binary term relations, R, 
   plus a few example such relations, like beta and eta (defined later in the file).
   It also defines values, a subgrammar of terms.
   These two grammar sections are separated because we only want LNgen to process
   the definition of terms.

   The `lc_ott.v` file, contains definitions of the `tm` datatype, with
   separate constructors for free and bound variables, as well as the opening
   (`open_tm_wrt_tm`), free variable (`fv_tm`) and substitution (`subst_tm`)
   operations and the local closure property (`lc_tm`).
   
   The remainder of the file corresponds to inductively-defined relations shown 
   in the Ott file.

2. Skim the generated `lc_inf.v` file.  This file first defines several
   auxiliary functions that go along with the Ott produced file. The most
   important of these is the `close_tm_wrt_tm` function, which acts as a
   quasi-inverse to the opening operation. Opening with some free variable `x`
   can convert a bound variable to a free variable. Closing does the opposite,
   converting some free variable to a bound variable. We will need this
   operation in this tutorial.
   
   Much of the file is the statements of lemmas about substitution, free
   variables, opening and closing. The key lemmas that we need for this
   tutorial are listed below. Those marked with (*) were also described in
   `Lec1.v` in the `Stlc` tutorial.
   
        subst_tm_open_tm_wrt_tm    (*)
        subst_tm_fresh_eq          (*)
        subst_tm_intro             (*)
        fv_tm_subst_tm_upper       (*)
        subst_tm_lc_tm             (*)
        open_tm_wrt_tm_inj
        fv_tm_close_tm_wrt_tm
        open_tm_wrt_tm_close_tm_wrt_tm
   
   You'll notice that all of the lemmas are `Admitted.` You can generate the
   version with the proofs using the makefile target `make coq/lc_inf_proofs.v`.
   However, this version can take a long time to compile.
   
3. Next, take a look at `tactics.v`. This file contains various Ltac definitions 
   and hints intended to make working with a locally nameless representation more 
   automatic. This file has not been automatically generated, so it contains 
   comments describing the purpose of its definitions.

4. Finally, begin the development proper with `relations_full.v` : the version of 
   the tutorial with exercises. Exercise answers are available in `relations_sol.v`.
   This file contains the proof of the Church Rosser theorem.

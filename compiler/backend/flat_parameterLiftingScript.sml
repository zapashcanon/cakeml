open
  preamble
  flatLangTheory
  mlintTheory

(* Used to make a program scope-insensitive by passing extra arguments to each function definition and call *)
val _ = new_theory "flat_parameterLifting"

val compile_exp_def = tDefine "compile_exp"

  `(compile_exp sol (Raise t e) = Raise t (compile_exp sol e)) ∧
   (compile_exp sol (Handle t e pes) = Handle t (compile_exp sol e) (compile_pes sol pes)) ∧
   (compile_exp sol (Lit t l) = Lit t l) ∧
   (compile_exp sol (Con t id es) = Con t id (compile_exps sol es)) ∧
   (compile_exp sol (Var_local t x) = Var_local t x (* TODO *)) ∧
   (compile_exp sol (Fun t x e) = Fun t x (compile_exp sol e) (* if we wanted to lambda lift anonymous functions, then, a name has already been given previously, so we don't care about this case *)) ∧
   (compile_exp sol (App t op es) = App t op es (* TODO: if op = Opapp then ... else ...*)) ∧
   (compile_exp sol (If t e1 e2 e3) = If t (compile_exp sol e1) (compile_exp sol e2) (compile_exp sol e3)) ∧
   (compile_exp sol (Mat t e pes) = Mat t (compile_exp sol e) (compile_pes sol pes)) ∧
   (compile_exp sol (Let t x e1 e2) = Let t x (compile_exp sol e1) (compile_exp sol e2) (* we consider Let as not being a function, see how sol is computed *) (* TODO: we could also check if there's some bindings for x in sol, if yes it means we decided to treat let as functions, so we can handle it, if we decided not to do it there will be nothing in sol *)) ∧
   (compile_exp sol (Letrec t funs e) = Letrec t (compile_funs sol funs) (compile_exp sol e)) ∧
   (compile_exps sol es = MAP (λ exp. compile_exp sol exp) es) ∧
   (compile_fun sol (vName, e) fName =
    let e' = compile_exp sol e in
    case ALOOKUP sol fName of
    | NONE => (vName, e')
    | SOME [] => (vName, e')
    | SOME (h::t) => let tra = Cons orphan_trace 1 in
      h, FOLDL (λ acc el. Fun tra el acc) (Fun tra vName e') t (* vName, e ---> arg1, λ arg2. ... λ argN. λ vName. e' *)) ∧
   (compile_funs sol fs = MAP (λ (fName, vName, e). let (vName', e') = (compile_fun sol (vName, e) fName) in (fName, vName', e')) fs) ∧
   (compile_pe sol (p, e) = (p, (compile_exp sol e))) ∧
   (compile_pes sol pes = MAP (λ pe. compile_pe sol pe) pes)`

cheat
(*
  ( WF_REL_TAC `inv_image $< (λ x. (case x of
  | INL (_, e) => exp_size e
  | INR (INL (_, es)) => exp6_size es
  | INR (INR (INL (_, f, _))) => exp4_size f
  | INR (INR (INR (INL (_, funs)))) => exp1_size funs
  | INR (INR (INR (INR (INL (_, pe))))) => exp5_size pe
  | INR (INR (INR (INR (INR (_, pes))))) => exp3_size pes
  ))`)
*)

val compile_decs_def = Define

  `compile_decs sol decs =
   MAP (λ x. case x of
   | Dlet e => Dlet (compile_exp sol e)
   | _ => x
   ) decs`

val _ = export_theory ()

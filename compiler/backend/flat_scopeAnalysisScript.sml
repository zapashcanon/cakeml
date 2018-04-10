open
  preamble
  flatLangTheory
  mlintTheory

(* Used to give all identifiers a unique name *)
val _ = new_theory "flat_scopeAnalysis";

val mk_unique_name_def = Define`
  mk_unique_name n s =
    CONCAT [explode (mlint$toString n); "_"; s]
`

val compile_p_def = tDefine "compile_p" `
  ( compile_p counter repl Pany =
      (counter, repl, Pany)
  ) ∧ (
    compile_p counter repl (Pvar x) =
      let newName = mk_unique_name counter x in
      (counter + 1, (x, newName)::repl, Pvar newName)
  ) ∧ (
    compile_p counter repl (Plit lit) =
      (counter, repl, Plit lit)
  ) ∧ (
    compile_p counter repl (Pcon id l) =
      let (counter, repl, l) = compile_ps counter repl l in
      (counter, repl, Pcon id l)
  ) ∧ (
    compile_p counter repl (Pref p) =
      let (counter, repl, p) = compile_p counter repl p in
      (counter, repl, Pref p)
  ) ∧ (
    compile_ps counter repl [] =
      (counter, repl, [])
  ) ∧ (
    compile_ps counter repl (p::ps) =
      let (counter, repl, p) = compile_p counter repl p in
      let (counter, repl, ps) = compile_ps counter repl ps in
      (counter, repl, p::ps)
  )
`
( WF_REL_TAC `inv_image $< (λ x. (case x of
  | INL (_, _, p) => pat_size p
  | INR (_, _, ps) => pat1_size ps
  ))`
)

val compile_name_rec_fun_def = Define`
  compile_name_rec_fun counter repl (fName, vName, e) =
    let newFName = mk_unique_name counter fName in
    counter + 1,
    (fName, newFName)::repl,
    (newFName, vName, e)
`

val compile_name_rec_funs_def = Define`
  ( compile_name_rec_funs counter repl [] =
      (counter, repl, [])
  ) ∧ (
    compile_name_rec_funs counter repl (f::funs) =
      let (counter, repl, f) = compile_name_rec_fun counter repl f in
      let (counter, repl, funs) = compile_name_rec_funs counter repl funs in
      (counter, repl, f::funs)
  )
`

val compile_name_rec_funs_LENGTH = Q.store_thm(
  "compile_name_rec_funs_LENGTH",
  `∀ counter repl funs counter' repl' funs'.
     (counter',repl',funs') = compile_name_rec_funs counter repl funs
     ⇒ LENGTH funs' = LENGTH funs`,
  Induct_on`funs` >>
  rw[compile_name_rec_funs_def,compile_name_rec_fun_def,exp_size_def] >>
  Cases_on`h` >> Cases_on`r` >>
  fs[mk_unique_name_def,exp_size_def,compile_name_rec_fun_def] >>
  qmatch_asmsub_abbrev_tac`compile_name_rec_funs counter0 repl0 _` >>
  Cases_on`(compile_name_rec_funs counter0 repl0 funs)` >>
  Cases_on`r` >>
  first_x_assum (assume_tac o Q.SPECL[`counter0`,`repl0`]) >>
  rfs[]);

val compile_exp_def = tDefine "compile_exp" `
  ( compile_exp counter repl (Raise t e) =
      let (counter, e) = compile_exp counter repl e in
      (counter, Raise t e)
  ) ∧ (
    compile_exp counter repl (Handle t e pes) =
      let (counter, e) = compile_exp counter repl e in
      let (counter, pes) = compile_pes counter repl pes in
      (counter, Handle t e pes)
  ) ∧ (
    compile_exp counter repl (Lit t l) =
      (counter, Lit t l)
  ) ∧ (
    compile_exp counter repl (Con t id es) =
      let (counter, es) = compile_exps counter repl es in
      (counter, Con t id es)
  ) ∧ (
    compile_exp counter repl (Var_local t x) =
      (* TODO: in the case of NONE, we should rename x (and add (x, newX) to the
      * repl ? maybe not...), this will avoid crash when something is undefined, it will not
      * append after passng through the stdlib and typechecking, but when
      * debugging, if we use something like equality test or addition, then
        * it'll not work... *)
      (counter, Var_local t (case ALOOKUP repl x of | NONE => x | SOME x => x))
  ) ∧ (
    compile_exp counter repl (Fun t x e) =
      let newName = mk_unique_name counter x in
      let (counter, e) = compile_exp (counter + 1) ((x, newName)::repl) e in
      (counter, Fun t newName e)
  ) ∧ (
    compile_exp counter repl (App t op es) =
      let (counter, es) = compile_exps counter repl es in
      (counter, App t op es)
  ) ∧ (
    compile_exp counter repl (If t e1 e2 e3) =
      let (counter, e1) = compile_exp counter repl e1 in
      let (counter, e2) = compile_exp counter repl e2 in
      let (counter, e3) = compile_exp counter repl e3 in
      (counter, If t e1 e2 e3)
  ) ∧ (
    compile_exp counter repl (Mat t e pes) =
      let (counter, e) = compile_exp counter repl e in
      let (counter, pes) = compile_pes counter repl pes in
      (counter, Mat t e pes)
  ) ∧ (
    compile_exp counter repl (Let t (SOME x) e1 e2) =
      let newName = mk_unique_name counter x in
      let (counter, e1) = compile_exp (counter + 1) repl e1 in
      let (counter, e2) = compile_exp counter ((x, newName)::repl) e2 in
      (counter, Let t (SOME newName) e1 e2)
  ) ∧ (
    compile_exp counter repl (Let t NONE e1 e2) =
      let (counter, e1) = compile_exp counter repl e1 in
      let (counter, e2) = compile_exp counter repl e2 in
      (counter, Let t NONE e1 e2)
  ) ∧ (
    compile_exp counter repl (Letrec t funs e) =
      let (counter, repl, funs) = compile_name_rec_funs counter repl funs in
      let (counter, funs) = compile_funs counter repl funs in
      let (counter, e) = compile_exp counter repl e in
      (counter, Letrec t funs e)
  ) ∧ (
    compile_fun counter repl (vName, e) =
      let newVName = mk_unique_name counter vName in
      let (counter, e) = compile_exp (counter + 1) ((vName, newVName)::repl) e in
      (counter, (newVName, e))
  ) ∧ (
    compile_funs counter repl [] =
      (counter, [])
  ) ∧ (
    compile_funs counter repl ((fName, f)::funs) =
      let (counter, f) = compile_fun counter repl f in
      let (counter, funs) = compile_funs counter repl funs in
      (counter, (fName, f)::funs)
  ) ∧ (
    compile_exps counter repl [] =
      (counter, [])
  ) ∧ (
    compile_exps counter repl (e::es) =
      let (counter, e) = compile_exp counter repl e in
      let (counter, es) = compile_exps counter repl es in
      (counter, e::es)
  ) ∧ (
    compile_pe counter repl pe =
      let (p, e) = pe in
      let (counter, repl, p) = compile_p counter repl p in
      let (counter, e) = compile_exp counter repl e in
      (counter, (p, e))
  ) ∧ (
    compile_pes counter repl [] =
      (counter, [])
  ) ∧ (
    compile_pes counter repl (pe::pes) =
      let (counter, pe) = compile_pe counter repl pe in
      let (counter, pes) = compile_pes counter repl pes in
      (counter, pe::pes)
  )`
  cheat
(* This will not work, to do it correctly we've got to write a another exp_size function which doesn't use the var/fun name length ...
(
 WF_REL_TAC `inv_image $< ( λ x . ( case x of
    | INL (counter, repl, e) => exp_size e
    | INR (INL (counter, repl, f)) => exp4_size f
    | INR (INR (INL (counter, repl, funs))) => exp1_size funs
    | INR (INR (INR (INL (counter, repl, es)))) => exp6_size es
    | INR (INR (INR (INR (INL (counter, repl, pe))))) => exp5_size pe
    | INR (INR (INR (INR (INR (counter, repl, pes))))) => exp3_size pes
  ))` >>
  simp[exp_size_def] >>
  rw[]
      imp_res_tac compile_name_rec_funs_LENGTH >>
      last_x_assum (fn hyp => assume_tac (GSYM hyp)) >>
      fs[]
      ) >>


  CASE_TAC >> fs[]
  CASE_TAC >> fs[]

  >> Induct_on `funs`
  >> simp [compile_name_rec_funs_def]
  >> simp [compile_name_rec_fun_def]
  >> rw[]

  >> Induct_on `funs`
  >> Induct_on `funs'`
  >> simp[mk_unique_name_def]
  >> rfs[]
  >> Cases_on `h`
  >> Cases_on `r`
  >> res_tac
  >> Cases_on `e`
  >> metis_tac[]
  >> cheat
)
*)

val compile_dec_def = Define`
  compile_dec counter dec =
    case dec of
    | Dlet e =>
      let (counter, e) = compile_exp counter [] e in
      (counter, Dlet e)
    | _ => (counter, dec)
`

val compile_decs_aux_def = Define`
  compile_decs_aux counter decs =
    case decs of
    | [] => counter, []
    | dec::decs =>
      let (counter, dec) = compile_dec counter dec in
      let (counter, decs) = compile_decs_aux counter decs in
      counter, dec::decs
`

val compile_decs_def = Define`
  compile_decs decs =
    SND (compile_decs_aux 0 decs)
`


val _ = export_theory ()

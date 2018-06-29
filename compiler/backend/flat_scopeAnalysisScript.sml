open
  preamble
  flatLangTheory
  mlnumTheory

(* Used to give all identifiers a unique name *)
val _ = new_theory "flat_scopeAnalysis";

val mk_unique_name_def = Define

  `mk_unique_name n s = CONCAT [explode (mlnum$toString n); "_"; s]`

val compile_p_def = tDefine "compile_p"

  `(compile_p counter repl Pany = (counter, repl, Pany)) ∧ (
    compile_p counter repl (Pvar x) =
      let newName = mk_unique_name counter x in
      (counter + 1, (x, newName)::repl, Pvar newName)) ∧ (
    compile_p counter repl (Plit lit) = (counter, repl, Plit lit)) ∧ (
    compile_p counter repl (Pcon id l) =
      let (counter, repl, l) = compile_ps counter repl l in
      (counter, repl, Pcon id l)) ∧ (
    compile_p counter repl (Pref p) =
      let (counter, repl, p) = compile_p counter repl p in
      (counter, repl, Pref p)) ∧ (
    compile_ps counter repl [] = (counter, repl, [])) ∧ (
    compile_ps counter repl (p::ps) =
      let (counter, repl, p) = compile_p counter repl p in
      let (counter, repl, ps) = compile_ps counter repl ps in
      (counter, repl, p::ps))`

  (WF_REL_TAC `inv_image $< (λ x. (case x of
  | INL (_, _, p) => pat_size p
  | INR (_, _, ps) => pat1_size ps
  ))`)

val compile_name_rec_funs_def = Define

  `(compile_name_rec_funs counter repl [] = (counter, repl, [])) ∧ (
    compile_name_rec_funs counter repl ((fName, vName, e)::funs) =
      let newFName = mk_unique_name counter fName in
      let (counter, repl, funs) = compile_name_rec_funs (counter + 1) repl funs in
      (counter, (fName, newFName)::repl, (newFName, vName, e)::funs))`

val p_size_bis = Define

  `(p_size_bis Pany : num      = 1                                 ) ∧ (
    p_size_bis (Pvar _)   = 1                                 ) ∧ (
    p_size_bis (Plit _)   = 1                                 ) ∧ (
    p_size_bis (Pcon _ l) = 1 + ps_size_bis l                 ) ∧ (
    p_size_bis (Pref p)   = 1 + p_size_bis p                  ) ∧ (
    ps_size_bis []        = 1                                 ) ∧ (
    ps_size_bis (h::t)    = 1 + p_size_bis h + ps_size_bis t  )`

val exp_size_bis_def = tDefine "exp_size_bis"

  `(exp_size_bis (Raise _ e)        = 1 + exp_size_bis e                                      ) ∧ (
    exp_size_bis (Handle _ e pes)   = 1 + exp_size_bis e + pes_size_bis pes                   ) ∧ (
    exp_size_bis (Lit _ _)          = 1                                                       ) ∧ (
    exp_size_bis (Con _ _ es)       = 1 + exps_size_bis es                                    ) ∧ (
    exp_size_bis (Var_local _ _)    = 1                                                       ) ∧ (
    exp_size_bis (Fun _ _ e)        = 1 + exp_size_bis e                                      ) ∧ (
    exp_size_bis (App _ _ es)       = 1 + exps_size_bis es                                    ) ∧ (
    exp_size_bis (If _ e1 e2 e3)    = 1 + exp_size_bis e1 + exp_size_bis e2 + exp_size_bis e3 ) ∧ (
    exp_size_bis (Mat _ e pes)      = 1 + exp_size_bis e + pes_size_bis pes                   ) ∧ (
    exp_size_bis (Let _ _ e1 e2)    = 1 + exp_size_bis e1 + exp_size_bis e2                   ) ∧ (
    exp_size_bis (Letrec _ funs e)  = 1 + funs_size_bis funs + exp_size_bis e                 ) ∧ (
    fun_size_bis (_, e)             = 1 + exp_size_bis e                                      ) ∧ (
    funs_size_bis []                = 1                                                       ) ∧ (
    funs_size_bis ((_, f)::t)       = 1 + fun_size_bis f + funs_size_bis t                    ) ∧ (
    exps_size_bis []                = 1                                                       ) ∧ (
    exps_size_bis (e::es)           = 1 + exp_size_bis e + exps_size_bis es                   ) ∧ (
    pe_size_bis (p, e)              = 1 + p_size_bis p + exp_size_bis e                       ) ∧ (
    pes_size_bis []                 = 1                                                       ) ∧ (
    pes_size_bis (pe::t)            = 1 + pe_size_bis pe + pes_size_bis t                     )`

  ( WF_REL_TAC `inv_image $< ( λ x . ( case x of
  | INL e => exp_size e
  | INR (INL f) => exp4_size f
  | INR (INR (INL funs)) => exp1_size funs
  | INR (INR (INR (INL es))) => exp6_size es
  | INR (INR (INR (INR (INL pe)))) => exp5_size pe
  | INR (INR (INR (INR (INR pes)))) => exp3_size pes))`)

val compile_nrf_size = Q.store_thm("compile_nrf_size",

  `∀ l c r. funs_size_bis l = funs_size_bis (SND (SND (compile_name_rec_funs c r l)))`,

   Induct
>> rw[compile_name_rec_funs_def]
>> Cases_on `h`
>> Cases_on `r'`
>> fs[compile_name_rec_funs_def]
>> pairarg_tac
>> fs[]
>> metis_tac[exp_size_bis_def, SND])

val compile_exp_def = tDefine "compile_exp"
`(compile_exp counter repl (Raise t e) =
      let (counter, e) = compile_exp counter repl e in (counter, Raise t e)) ∧ (
    compile_exp counter repl (Handle t e pes) =
      let (counter, e) = compile_exp counter repl e in
      let (counter, pes) = compile_pes counter repl pes in
      (counter, Handle t e pes)) ∧ (
    compile_exp counter repl (Lit t l) = (counter, Lit t l)) ∧ (
    compile_exp counter repl (Con t id es) =
      let (counter, es) = compile_exps counter repl es in
      (counter, Con t id es)) ∧ (
    compile_exp counter repl (Var_local t x) =
      (* TODO: in the case of NONE, we should rename x (and add (x, newX) to the
      * repl ? maybe not...), this will avoid crash when something is undefined, it will not
      * append after passng through the stdlib and typechecking, but when
      * debugging, if we use something like equality test or addition, then
        * it'll not work... *)
      (counter, Var_local t (case ALOOKUP repl x of | NONE => x | SOME x => x))) ∧ (
    compile_exp counter repl (Fun t x e) =
      let newName = mk_unique_name counter x in
      let (counter, e) = compile_exp (counter + 1) ((x, newName)::repl) e in
      (counter, Fun t newName e)) ∧ (
    compile_exp counter repl (App t op es) =
      let (counter, es) = compile_exps counter repl es in
      (counter, App t op es)) ∧ (
    compile_exp counter repl (If t e1 e2 e3) =
      let (counter, e1) = compile_exp counter repl e1 in
      let (counter, e2) = compile_exp counter repl e2 in
      let (counter, e3) = compile_exp counter repl e3 in
      (counter, If t e1 e2 e3)) ∧ (
    compile_exp counter repl (Mat t e pes) =
      let (counter, e) = compile_exp counter repl e in
      let (counter, pes) = compile_pes counter repl pes in
      (counter, Mat t e pes)) ∧ (
    compile_exp counter repl (Let t (SOME x) e1 e2) =
      let newName = mk_unique_name counter x in
      let (counter, e1) = compile_exp (counter + 1) repl e1 in
      let (counter, e2) = compile_exp counter ((x, newName)::repl) e2 in
      (counter, Let t (SOME newName) e1 e2)) ∧ (
    compile_exp counter repl (Let t NONE e1 e2) =
      let (counter, e1) = compile_exp counter repl e1 in
      let (counter, e2) = compile_exp counter repl e2 in
      (counter, Let t NONE e1 e2)) ∧ (
    compile_exp counter repl (Letrec t funs e) =
      let (counter, repl, funs) = compile_name_rec_funs counter repl funs in
      let (counter, funs) = compile_funs counter repl funs in
      let (counter, e) = compile_exp counter repl e in
      (counter, Letrec t funs e)) ∧ (
    compile_fun counter repl (vName, e) =
      let newVName = mk_unique_name counter vName in
      let (counter, e) = compile_exp (counter + 1) ((vName, newVName)::repl) e in
      (counter, (newVName, e))) ∧ (
    compile_funs counter repl [] = (counter, [])) ∧ (
    compile_funs counter repl ((fName, f)::funs) =
      let (counter, f) = compile_fun counter repl f in
      let (counter, funs) = compile_funs counter repl funs in
      (counter, (fName, f)::funs)) ∧ (
    compile_exps counter repl [] = (counter, [])) ∧ (
    compile_exps counter repl (e::es) =
      let (counter, e) = compile_exp counter repl e in
      let (counter, es) = compile_exps counter repl es in
      (counter, e::es)) ∧ (
    compile_pe counter repl pe =
      let (p, e) = pe in
      let (counter, repl, p) = compile_p counter repl p in
      let (counter, e) = compile_exp counter repl e in
      (counter, (p, e))) ∧ (
    compile_pes counter repl [] = (counter, [])) ∧ (
    compile_pes counter repl (pe::pes) =
      let (counter, pe) = compile_pe counter repl pe in
      let (counter, pes) = compile_pes counter repl pes in
      (counter, pe::pes))`

   ( WF_REL_TAC `inv_image $< (λ x. (case x of
   | INL (counter, repl, e) => exp_size_bis e
   | INR (INL (counter, repl, f)) => fun_size_bis f
   | INR (INR (INL (counter, repl, funs))) => funs_size_bis funs
   | INR (INR (INR (INL (counter, repl, es)))) => exps_size_bis es
   | INR (INR (INR (INR (INL (counter, repl, pe))))) => pe_size_bis pe
   | INR (INR (INR (INR (INR (counter, repl, pes))))) => pes_size_bis pes))`

>> rw[exp_size_bis_def]
>> CASE_TAC
>> CASE_TAC
>> rw[]
>> `funs_size_bis funs' = funs_size_bis funs` by metis_tac[compile_nrf_size, SND]
>> rw[])

val compile_dec_def = Define

  `(compile_dec counter (Dlet e) = let (counter, e) = compile_exp counter [] e in (counter, Dlet e)) ∧ (
    compile_dec counter dec = (counter, dec))`

val compile_decs_aux_def = Define

  `(compile_decs_aux counter [] = (counter, [])) ∧ (
    compile_decs_aux counter (dec::decs) =
      let (counter, dec) = compile_dec counter dec in
      let (counter, decs) = compile_decs_aux counter decs in
      counter, dec::decs)`

val compile_decs_def = Define

  `compile_decs decs = SND (compile_decs_aux 0 decs)`

val _ = export_theory ()

open
  preamble
  flatLangTheory
  mlintTheory

val _ = new_theory "flat_deanonymization";

val compile_exp_def = tDefine "compile_exp" `
  (compile_exp counter e =
    case e of
    | Raise t e => let (counter, e) = compile_exp counter e in counter, Raise t e
    | Handle t e pes =>
        let (counter, e) = compile_exp counter e in
        let (counter, pes) = compile_pes counter pes in
        counter, Handle t e pes
    | Lit t l => counter, Lit t l
    | Con t id es => let (counter, es) = compile_exps counter es in counter, Con t id es
    | Var_local t x => counter, Var_local t x
    | Fun t x e =>
        (* This is the interesting case, we change
         * (λ x. e) to (let f = λ x. e in f)
         * where f is a new name *)
        (* NOT ENABLED CURRENTLY...
        * let newName = CONCAT [explode (mlint$toString counter); "_anonymous"] in
        let (counter, e) = compile_exp (counter + 1) e in
        counter, Let t (SOME newName) (Fun t x e) (Var_local t newName)*)
        let (counter, e) = compile_exp counter e in
        counter, Fun t x e
    | App t op es => let (counter, es) = compile_exps counter es in counter, App t op es
    | If t e1 e2 e3 =>
        let (counter, e1) = compile_exp counter e1 in
        let (counter, e2) = compile_exp counter e2 in
        let (counter, e3) = compile_exp counter e3 in
        counter, If t e1 e2 e3
    | Mat t e pes =>
        let (counter, e) = compile_exp counter e in
        let (counter, pes) = compile_pes counter pes in
        counter, Mat t e pes
    | Let t x e1 e2 =>
        let (counter, e1) = compile_exp counter e1 in
        let (counter, e2) = compile_exp counter e2 in
        counter, Let t x e1 e2
    | Letrec t funs e =>
        let (counter, funs) = compile_funs counter funs in
        let (counter, e) = compile_exp counter e in
        counter, Letrec t funs e
  ) ∧ (
  compile_fun counter f =
    let (vName, e) = f in
    let (counter, e) = compile_exp counter e in
    counter, (vName, e)
  ) ∧ (
  compile_funs counter funs =
    case funs of
    | [] => counter, []
    | (fName, vName, e)::funs =>
        let (counter, (vName, e)) = compile_fun counter (vName, e) in
        let (counter, funs) = compile_funs counter funs in
        counter, (fName, vName, e)::funs
  ) ∧ (
  compile_exps counter es =
    case es of
    | [] => counter, []
    | e::es =>
        let (counter, e) = compile_exp counter e in
        let (counter, es) = compile_exps counter es in
        counter, e::es
  ) ∧ (
  compile_pe counter pe =
    let (p, e) = pe in
    let (counter, e) = compile_exp counter e in
    counter, (p, e)
  ) ∧ (
  compile_pes counter pes =
    case pes of
    | [] => counter, []
    | pe::pes =>
        let (counter, pe) = compile_pe counter pe in
        let (counter, pes) = compile_pes counter pes in
        counter, pe::pes
  )`

(
  WF_REL_TAC `inv_image $< ( λ x . ( case x of
    | INL (counter, e) => exp_size e
    | INR (INL (counter, f)) => exp4_size f
    | INR (INR (INL (counter, funs))) => exp1_size funs
    | INR (INR (INR (INL (counter, es)))) => exp6_size es
    | INR (INR (INR (INR (INL (counter, pe))))) => exp5_size pe
    | INR (INR (INR (INR (INR (counter, pes))))) => exp3_size pes
  ))`
)

val compile_dec_def = Define`
  compile_dec counter dec =
    case dec of
    | Dlet e =>
        let (counter, e) = compile_exp counter e in
        counter, Dlet e
    | _ => (counter, dec)
`

val compile_decs_def = Define`
  compile_decs counter decs =
    case decs of
    | [] => counter, []
    | dec::decs =>
      let (counter, dec) = compile_dec counter dec in
      let (counter, decs) = compile_decs counter decs in
      counter, dec::decs
`

val _ = export_theory ()

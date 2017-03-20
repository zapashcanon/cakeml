open preamble modLangTheory;

open modSemTheory modPropsTheory
(* Liveness analysis for modLang globals, temporarily in proofs/ for convenience *)

val _ = new_theory "mod_live";

(* Expressions that do not have side effects
   Applications of functions are not considered pure *)
val pure_op_def = Define `
  pure_op op ⇔
  case op of
    Opref => F
  | Opapp => F
  | Opassign => F
  | Aw8update => F
  | Aw8alloc => F
  | Aw8sub => F
  | Vsub => F
  | Strsub => F
  | Chr => F
  | Aupdate => F
  | Aalloc => F
  | Asub => F
  | Opn Divide => F
  | Opn Modulo => F
  | FFI _ => F
  | _ => T`;

(* Handle the compilation of Dlet *)
val exh_pat_def = tDefine "exh_pat"`
  (exh_pat (ast$Pvar _) ⇔ T) ∧
  (exh_pat (Pcon NONE ls) ⇔ EVERY exh_pat ls) ∧
  (exh_pat _ ⇔ F)`
  (WF_REL_TAC `measure ast$pat_size` >>
  rw [] >>
  Induct_on`ls` >>
  rw[astTheory.pat_size_def]>>
  fs[]);

(* Checks purity *)
val pure_exp_def = tDefine "pure_exp"`
  (pure_exp (Raise _ ) ⇔ F) ∧
  (pure_exp (Handle e _ ) ⇔ pure_exp e) ∧ (* Don't need to check pes *)
  (pure_exp (Lit _) ⇔ T) ∧
  (pure_exp (Con _ ls) ⇔ EVERY pure_exp ls) ∧ (* Don't need to check pes *)
  (pure_exp (Var_local _) ⇔ T) ∧
  (pure_exp (Var_global _) ⇔ T) ∧
  (pure_exp (Fun _ _) ⇔ T) ∧
  (pure_exp (App op exps) ⇔ pure_op op ∧ EVERY pure_exp exps) ∧
  (pure_exp (If e1 e2 e3) ⇔ pure_exp e1 ∧ pure_exp e2 ∧ pure_exp e3) ∧
  (pure_exp (Mat e1 pes) ⇔ pure_exp e1 ∧ pure_match pes) ∧
  (pure_exp (Let _ e1 e2) ⇔ pure_exp e1 ∧ pure_exp e2) ∧
  (pure_exp (Letrec _ e) ⇔ pure_exp e) ∧
  (* Some exhaustive match cases *)
  (pure_match [(p,e)] ⇔ exh_pat p ∧ pure_exp e) ∧
  (pure_match _ ⇔ F)`
  (WF_REL_TAC `inv_image $<
    (\x. case x of INL e => exp_size e
                 | INR pes => exp3_size pes)`>>
  rw[]>>
  TRY(Induct_on`ls`)>>
  TRY(Induct_on`exps`)>>
  rw[modLangTheory.exp_size_def]>>
  fs[])

val list_union_def = Define`
  list_union xs = FOLDR (λg s. union g s) LN xs`

(* globals referenced by an expression *)
val glob_exp_def = tDefine "pure_exp"`
  (glob_exp (Var_global n) = insert n () LN) ∧
  (glob_exp (Raise e) = glob_exp e) ∧
  (glob_exp (Handle e pes) =
    let pglobs = list_union (MAP (λ(p,e). glob_exp e) pes) in
    union pglobs (glob_exp e)) ∧
  (glob_exp (Lit _)  = LN) ∧
  (glob_exp (Con _ es)  = list_union (MAP (λe. glob_exp e) es)) ∧
  (glob_exp (Var_local _) = LN) ∧
  (glob_exp (Fun n e) = glob_exp e) ∧
  (glob_exp (App _ es) = list_union (MAP (λe. glob_exp e) es)) ∧
  (glob_exp (If e1 e2 e3) =
    union (glob_exp e1) (union(glob_exp e2) (glob_exp e3))) ∧
  (glob_exp (Mat e pes) =
    let pglobs = list_union (MAP (λ(p,e). glob_exp e) pes) in
    union pglobs (glob_exp e)) ∧
  (glob_exp (Let _ e1 e2) =
    union (glob_exp e1) (glob_exp e2)) ∧
  (glob_exp (Letrec funs e) =
    let fglobs = list_union (MAP (λ(f,x,e). glob_exp e) funs) in
    union fglobs (glob_exp e))`
  (WF_REL_TAC `measure exp_size`>>
  fs[]>>
  rpt CONJ_TAC>>
  strip_tac>> Induct>>rw[exp_size_def]>>res_tac>>fs[exp_size_def])

(* This removes Dlet and Dletrec.
   pos tracks the next global position that this dec starts at
   g tracks the globals which must be live after

*)

val pos_notin_def = Define`
  (pos_notin pos 0 g = T) ∧
  (pos_notin pos (SUC n) g =
    (lookup pos g = NONE ∧
    pos_notin pos n g))`

(* Returns a modified dec + updates the globals it read *)
val live_dec_def = Define`
  (live_dec (Dlet n exp) pos g =
    if pos_notin pos n g ∧ pure_exp exp
    then
       (Dlet n (Con NONE (REPLICATE n (Con NONE []))),g)
    else
       let g' = glob_exp exp in
       (Dlet n exp,union g' g)) ∧
  (live_dec (Dletrec funs) pos g =
    let n = LENGTH funs in
    if pos_notin pos n g
    then
      (Dlet n (Con NONE (REPLICATE n (Con NONE []))),g)
    else
      let g' = list_union (MAP (λ(f,x,e). glob_exp e) funs) in
      (Dletrec funs,union g' g)) ∧
  (live_dec dec pos g = (dec,g))`

(* The number of positions that a dec defines*)
val pos_dec_def = Define`
  (pos_dec (modLang$Dlet n _) = n) ∧
  (pos_dec (Dletrec funs) = LENGTH funs) ∧
  (pos_dec _ = 0)`

val live_decs_def = Define`
  (live_decs [] pos g = ([],g)) ∧
  (live_decs (d::ds) pos g =
    let (ds',g') = live_decs ds (pos+pos_dec d) g in
    let (d',g'') = live_dec d pos g' in
    (d'::ds',g''))`

val pos_decs_def = Define`
  (pos_decs [] = 0) ∧
  (pos_decs (d::ds) = pos_dec d + pos_decs ds)`

val live_prompts_def = Define`
  (live_prompts [] pos g = ([],g)) ∧
  (live_prompts ((Prompt mn ds)::ps) pos g =
    let (ps',g') = live_prompts ps (pos + pos_decs ds) g in
    let (ds',g') = live_decs ds pos g in
    (Prompt mn ds'::ps',g'))`

val pure_exp_ind = fetch "-" "pure_exp_ind"

val hide_def = Define` hide x = x`

val pure_exp_evaluate = Q.prove(`
  (∀env (s:'a modSem$state) es s' res.
  evaluate env s es = (s',res) ∧
  EVERY pure_exp es ⇒
  hide(s = s' ∧
  case res of
    Rval v => T
  | Rerr (Rabort Rtype_error) => T
  | _ => F)) ∧
  (∀env (s:'a modSem$state) v pes err s' res.
  evaluate_match env s v pes err = (s',res) ∧
  pure_match pes ⇒
  hide(s = s' ∧
  case res of
    Rval v => T
  | Rerr (Rabort Rtype_error) => T
  | _ => F))`,
  ho_match_mp_tac modSemTheory.evaluate_ind >> rw[evaluate_def]>>
  fs[EVAL ``hide T``,pure_exp_def]
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    rpt TOP_CASE_TAC>>fs[hide_def]>>
    Cases_on`e`>>fs[]>>
    TRY(Cases_on`a'`>>fs[])>>
    TRY(Cases_on`a`>>fs[]))
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    rpt TOP_CASE_TAC>>fs[hide_def]>>
    TRY(Cases_on`a`>>fs[]))
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    rpt TOP_CASE_TAC>>fs[hide_def,EVERY_REVERSE,ETA_AX]>>
    rfs[]>>
    Cases_on`e`>>fs[]>>
    TRY(Cases_on`a'`>>fs[])>>
    TRY(Cases_on`a`>>fs[]))
  >-
    (EVERY_CASE_TAC>>fs[hide_def])
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>fs[])
    >-
      (IF_CASES_TAC
      >-
        (rw[]>>fs[pure_op_def])
      >>
      (* nasty op cases *)
      cheat)
    >>
    fs[EVERY_REVERSE,hide_def,ETA_AX]>>rw[]>>fs[])
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    ntac 3 TOP_CASE_TAC>> fs[hide_def]
    >- (rw[]>>simp[])
    >>
      rw[]>>fs[do_if_def]>>EVERY_CASE_TAC>>fs[])
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    ntac 3 TOP_CASE_TAC>> fs[hide_def]
    >-
      (rw[]>>res_tac>>fs[])
    >>
      Cases_on`e'`>>fs[]>>Cases_on`a`>>fs[]>>rw[]>>fs[])
  >-
    (qpat_x_assum` _ = (s',res)` mp_tac>>
    ntac 2 TOP_CASE_TAC>>fs[]>>rw[]>>fs[hide_def])
  >-
    (Cases_on`pes`>>fs[pure_exp_def]>>
    cheat));

val state_rel_def = Define`
  state_rel (g:num_set) s t ⇔
  s.clock = t.clock ∧
  s.refs = t.refs ∧
  s.ffi = t.ffi ∧
  s.defined_types = t.defined_types ∧
  s.defined_mods = t.defined_mods ∧
  LENGTH s.globals = LENGTH t.globals ∧
  ∀n.
    n ∈ domain g ∧
    n < LENGTH s.globals ⇒
    EL n s.globals = EL n t.globals`

val domain_list_union = prove(``
  ∀ls.
  ∀n. n ∈ domain (list_union ls) ⇔
  ∃g. n ∈ domain g ∧ MEM g ls``,
  Induct>>fs[list_union_def]>>fs[domain_union]>>
  metis_tac[]);

(* Value containment *)
val v_glob_exp_def = tDefine "v_glob_exp" `
  (v_glob_exp (Conv _ ls) = list_union (MAP v_glob_exp ls)) ∧
  (v_glob_exp (Closure env _ e) =
    union (glob_exp e) (list_union (MAP (λ(n,v). v_glob_exp v) (SND env)))) ∧
  (v_glob_exp (Recclosure env funs _) =
    union (list_union (MAP (λ(f,x,e). glob_exp e) funs))
      (list_union (MAP (λ(n,v). v_glob_exp v) (SND env)))) ∧
  (v_glob_exp (Vectorv vs) = list_union (MAP v_glob_exp vs)) ∧
  (v_glob_exp _ = LN)`
  (WF_REL_TAC `measure v_size`>>rpt CONJ_TAC>>
  TRY
    (ntac 3 strip_tac>>
    Induct>>rw[]>>res_tac>>fs[v_size_def])
  >-
    (Induct>>rw[]>>res_tac>>fs[v_size_def])
  >-
    (strip_tac>>
    Induct>>rw[]>>res_tac>>fs[v_size_def]))

(* global containment *)
val glob_contained_def = Define`
  glob_contained env (s:'a modSem$state) g ⇔
    EVERY (λ(n,v). subspt (v_glob_exp v) g) env.v ∧
    EVERY (λref. case ref of
      Refv v => subspt (v_glob_exp v) g
    | Varray vs => EVERY (λv. subspt (v_glob_exp v) g) vs
    | W8array _ => T) s.refs ∧
    EVERY (λv. case v of NONE => T | SOME v => subspt (v_glob_exp v) g) s.globals`

(* TODO: move to HOL? *)
val subspt_union = prove(``
  subspt (union (t1:num_set) (t2:num_set)) (t3:num_set) ⇔
  subspt t1 t3 ∧ subspt t2 t3``,
  fs[subspt_domain,domain_union])

val subspt_list_union = prove(``
  subspt (list_union gs) (g:num_set) ⇔
  EVERY (λg'. subspt g' g) gs``,
  rw[EVERY_MEM,subspt_domain,SUBSET_DEF]>>
  fs[domain_list_union,PULL_EXISTS]>>
  metis_tac[]);

val res_glob_contained_def = Define`
  res_glob_contained res g ⇔
    case res of
    Rval vs => EVERY (λv. subspt (v_glob_exp v) g) vs
  | Rerr (Rraise v) => subspt (v_glob_exp v) g
  | _ => T `

(* global containment *)
val glob_contained_evaluate = Q.prove(`
  (∀env (s:'a modSem$state) es s' res g.
  evaluate env s es = (s',res) ∧
  glob_contained env s g ∧
  EVERY (λe. subspt (glob_exp e) g) es ⇒
  hide(glob_contained env s' g ∧
  res_glob_contained res g)) ∧
  (∀env (s:'a modSem$state) v pes err s' res g.
  evaluate_match env s v pes err = (s',res) ∧
  glob_contained env s g ∧
  subspt (v_glob_exp v) g ∧
  subspt (v_glob_exp err) g ∧
  EVERY (λ(p,e). subspt (glob_exp e) g) pes ⇒
  hide(glob_contained env s' g ∧
  res_glob_contained res g))`,
  ho_match_mp_tac evaluate_ind>>
  fs[evaluate_def,glob_exp_def,v_glob_exp_def]>>
  rpt CONJ_TAC>>
  TRY(fs[hide_def,res_glob_contained_def,v_glob_exp_def]>>NO_TAC)
  >-
    (rw[]>>
    EVERY_CASE_TAC>>fs[hide_def]>>rveq>>
    fs[res_glob_contained_def]>>
    first_x_assum drule >> impl_tac>> fs[]>> strip_tac>>
    res_tac>>fs[]>>
    imp_res_tac evaluate_length>>
    Cases_on`a'`>>fs[])
  >-
    (rw[]>>EVERY_CASE_TAC>>fs[hide_def]>>rveq>>fs[res_glob_contained_def]>>
    res_tac>>fs[]>>
    imp_res_tac evaluate_length>>
    Cases_on`a`>>fs[])
  >-
    (rw[]>>EVERY_CASE_TAC>>fs[hide_def]>>rveq>>
    first_x_assum match_mp_tac>>fs[]>>
    TRY(metis_tac[subspt_list_union,subspt_union])>>
    first_x_assum drule>>fs[]>>impl_tac>>fs[]
    >-
      metis_tac[subspt_list_union,subspt_union]
    >>
      fs[subspt_union,subspt_list_union,EVERY_MAP,LAMBDA_PROD,res_glob_contained_def])
  >-
    (rw[]>>EVERY_CASE_TAC>>fs[hide_def,res_glob_contained_def]>>rveq>>fs[]>>
    first_x_assum drule>>fs[]>>impl_tac>>
    fs[EVERY_REVERSE,subspt_list_union,EVERY_MAP]>>
    fs[build_conv_def]>>EVERY_CASE_TAC>>rw[]>>
    fs[v_glob_exp_def,subspt_list_union,EVERY_REVERSE,EVERY_MAP])
  >-
    (rw[]>>EVERY_CASE_TAC>>
    fs[hide_def,res_glob_contained_def,glob_contained_def]>>
    imp_res_tac ALOOKUP_MEM>>
    fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[])
  >-
    (rw[]>>
    fs[hide_def,res_glob_contained_def,glob_contained_def,EVERY_EL,IS_SOME_EXISTS]>>
    first_x_assum(qspec_then`n` assume_tac)>>rfs[])
  >-
    (rw[]>>
    fs[subspt_union,subspt_list_union,EVERY_MAP,glob_contained_def,
       res_glob_contained_def,hide_def,LAMBDA_PROD,v_glob_exp_def])
  >-
    (* app case... *)
    cheat
  >-
    (rw[do_if_def]>>EVERY_CASE_TAC>>fs[hide_def]>>
    TRY(first_assum match_mp_tac>>fs[subspt_union])>>
    first_x_assum drule>>impl_tac>>rveq>>
    fs[res_glob_contained_def,subspt_union])
  >-
    (rw[]>>EVERY_CASE_TAC>>fs[hide_def]>>rveq>>
    first_assum match_mp_tac>>fs[subspt_union]>>
    imp_res_tac evaluate_length>>Cases_on`a`>>fs[]>>
    fs[subspt_union,subspt_list_union,EVERY_MAP,glob_contained_def,
       res_glob_contained_def,hide_def,LAMBDA_PROD,v_glob_exp_def])
  >-
    (rw[]>>EVERY_CASE_TAC>>fs[hide_def]
    >-
      (first_x_assum drule>>fs[subspt_union]>>strip_tac>>
      first_x_assum(qspec_then `g` mp_tac)>>impl_tac
      >-
        (fs[glob_contained_def,libTheory.opt_bind_def]>>
        Cases_on`n`>>fs[]>>
        imp_res_tac evaluate_length>>Cases_on`a`>>fs[res_glob_contained_def])
      >>
      fs[glob_contained_def,res_glob_contained_def,subspt_union])
    >>
    first_assum match_mp_tac>>fs[subspt_union])
  >-
    (* Letrec *)
    cheat
  >>
    rw[]>>EVERY_CASE_TAC>>fs[hide_def]>>rveq>>
    TRY(fs[res_glob_contained_def]>>NO_TAC)>>
    first_x_assum drule>>fs[]>>
    disch_then(qspec_then`g` mp_tac)>> impl_tac
    >-
      (fs[glob_contained_def]>>
      cheat)
    >>
    fs[hide_def,res_glob_contained_def,glob_contained_def]>>
    imp_res_tac ALOOKUP_MEM>>
    fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[]) |> SIMP_RULE std_ss [hide_def];

val glob_contained_evaluate_sing = Q.prove(`
  evaluate env s [e] = (s',res) ∧
  glob_contained env s g ∧
  subspt (glob_exp e) g  ⇒
  glob_contained env s' g ∧
  res_glob_contained res g`,
  rw[]>>
  drule (CONJUNCT1 glob_contained_evaluate)>>
  disch_then (qspec_then`g` assume_tac)>>
  rfs[])|>GEN_ALL;

fun lrule th =
  last_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

(* Evaluation of states that match on the globals *)
val state_rel_evaluate = Q.prove(`
  (∀env (s:'a modSem$state) es s' res g  t.
  evaluate env s es = (s',res) ∧
  state_rel g s t ∧
  glob_contained env s g ∧
  EVERY (λe. subspt (glob_exp e) g) es ∧
  (* g can be any over-approximation of the read-able globals *)
  res ≠ Rerr (Rabort Rtype_error) ⇒
  ∃t'.
  evaluate env t es = (t',res) ∧
  state_rel g s' t') ∧
  (∀env (s:'a modSem$state) v pes err s' res g t.
  evaluate_match env s v pes err = (s',res) ∧
  state_rel g s t ∧
  glob_contained env s g ∧
  subspt (v_glob_exp v) g ∧
  subspt (v_glob_exp err) g ∧
  EVERY (λ(p,e). subspt (glob_exp e) g) pes ∧
  res ≠ Rerr (Rabort Rtype_error) ⇒
  ∃t'.
  evaluate_match env t v pes err = (t',res) ∧
  state_rel g s' t')`,
  ho_match_mp_tac evaluate_ind>>rw[]
  >-
    (fs[evaluate_def]>>rw[])
  >-
    (fs[evaluate_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (TOP_CASE_TAC>>fs[]>>
      TOP_CASE_TAC>>fs[]>>
      rw[]>>fs[]>>
      first_x_assum drule >> impl_tac>> fs[]>>rw[]>>fs[]>>
      first_x_assum drule >> impl_tac>> fs[]>>rw[]>>fs[]>>
      metis_tac[glob_contained_evaluate_sing])
    >>
      rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[])
  >-
    (fs[evaluate_def]>>rw[])
  >-
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    rw[]>>fs[]>>
    first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[])
  >-
    (* handle *)
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (* no exceptions *)
      (rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[]>>
      fs[subspt_union])
    >>
    TOP_CASE_TAC>>fs[]
    >-
      (rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_union]>>
      first_x_assum drule>> impl_tac
      >-
        (fs[subspt_list_union,EVERY_MAP,LAMBDA_PROD]>>
        lrule glob_contained_evaluate_sing>>
        fs[res_glob_contained_def])
      >>
      rw[])
    >>
      rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_union])
  >-
    (* con *)
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (TOP_CASE_TAC>>fs[]>>rw[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>
      fs[EVERY_REVERSE,subspt_list_union,EVERY_MAP])
    >>
    rw[]>>fs[]>>
    first_x_assum drule>> impl_tac>> fs[]>>rw[]>>
    fs[EVERY_REVERSE,subspt_list_union,EVERY_MAP])
  >-
    (fs[evaluate_def,glob_exp_def]>>rw[])
  >-
    (*Var global*)
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum`A=res`mp_tac>> IF_CASES_TAC>>fs[state_rel_def,subspt_domain]>>
    res_tac>>fs[]>>rw[])
  >-
    (fs[evaluate_def,glob_exp_def]>>rw[])
  >-
    (*app*)
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (IF_CASES_TAC>>fs[]
      >-
        (ntac 3(TOP_CASE_TAC>>fs[])
        >-
          (rw[]>>fs[]>>
          first_x_assum drule>> impl_tac
          >-
            (fs[]>>rw[]>>
            fs[subspt_list_union,EVERY_MAP,EVERY_REVERSE])
          >>
          rw[]>>fs[state_rel_def])
        >>
          first_x_assum drule>> impl_tac
          >-
            (fs[]>>rw[]>>
            fs[subspt_list_union,EVERY_MAP,EVERY_REVERSE])>>
          rw[]>>fs[]>>
          `t'.clock ≠ 0` by fs[state_rel_def]>>fs[]>>
          first_x_assum(qspecl_then[`g`,`dec_clock t'`] mp_tac)>>
          impl_tac
          >-
            (fs[state_rel_def,dec_clock_def]>>
            lrule (CONJUNCT1 glob_contained_evaluate)>>
            disch_then(qspec_then`g` mp_tac)>>
            impl_tac>-
              fs[EVERY_REVERSE,subspt_list_union,EVERY_MAP]>>
            strip_tac>>
            fs[do_opapp_def]>>qpat_x_assum`_=SOME(q',r)` mp_tac>>
            EVERY_CASE_TAC>>fs[]>>strip_tac>>rveq>>
            Cases_on`a`>>fs[res_glob_contained_def,v_glob_exp_def,subspt_union]>>
            fs[glob_contained_def,subspt_list_union,EVERY_MAP,LAMBDA_PROD]>>
            rfs[]>>
            (* Needs a simple induction on build_rec_env *)
            cheat)>>
          rw[]>>fs[])
      >>
      ntac 3 (TOP_CASE_TAC>>fs[])>>
      rw[]>>fs[]>>
      first_x_assum drule>> impl_tac
      >-
        (fs[]>>rw[]>>
        fs[subspt_list_union,EVERY_MAP,EVERY_REVERSE])
      >>
      rw[]>>fs[state_rel_def])
    >>
    rw[]>>fs[]>>
    first_x_assum drule>> impl_tac>> fs[]>>rw[]>>
    fs[subspt_list_union,EVERY_MAP,EVERY_REVERSE])
  >-
    (* If *)
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (fs[do_if_def]>>rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_union]>>
      metis_tac[glob_contained_evaluate_sing])
    >>
    rw[]>>fs[]>>
    first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_union])
  >-
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_union]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_list_union]
      >-
        (lrule glob_contained_evaluate_sing>>
        fs[res_glob_contained_def])
      >-
        (lrule glob_contained_evaluate_sing>>
        disch_then(qspec_then`g` assume_tac)>>rfs[]>>
        fs[res_glob_contained_def]>>
        imp_res_tac evaluate_length>>Cases_on`a`>>fs[])
      >-
        fs[v_glob_exp_def,list_union_def]
      >>
        fs[EVERY_MAP,LAMBDA_PROD])
    >>
      (rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[]>>
      fs[subspt_union]))
  >-
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    rw[]>>fs[]>>
    first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[subspt_union]>>
    first_assum match_mp_tac>>fs[]>>
    lrule glob_contained_evaluate_sing>> disch_then(qspec_then`g` assume_tac)>>rfs[]>>
    fs[glob_contained_def,libTheory.opt_bind_def]>>
    Cases_on`n`>>fs[]>>
    imp_res_tac evaluate_length>>Cases_on`a`>>fs[res_glob_contained_def])
  >-
    (fs[evaluate_def,glob_exp_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    rw[]>>fs[]>>
    first_x_assum drule>> impl_tac>> fs[]>>rw[]>>fs[]>>
    fs[subspt_union]>>
    (* build_rec_env *)
    cheat)
  >-
    (fs[evaluate_def]>>rw[])
  >>
    fs[evaluate_def]>>
    qpat_x_assum` _ = (s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (rw[]>>fs[]>>
      first_x_assum drule>> impl_tac
      >-
       (fs[]>>rw[]>>
       first_assum match_mp_tac>>fs[EXISTS_PROD,MEM_MAP])
      >>
      rfs[state_rel_def])
    >>
      rw[]>>fs[]>>
      first_x_assum drule>> impl_tac>>rfs[state_rel_def]>>
      (* glob_containment over pmatch *)
      cheat);

(* todo: move replicate_snoc to rich_list from multiword*)
val evaluate_replicate = Q.prove(`
  modSem$evaluate env t [Con NONE (REPLICATE n (Con NONE []))] =
    (t, Rval [Conv NONE (REPLICATE n (Conv NONE []))])`,
  Induct_on`n`>>
  fs[REVERSE_REPLICATE,REPLICATE,evaluate_def,evaluate_cons]>>
  fs[evaluate_def,semanticPrimitivesTheory.do_con_check_def,build_conv_def]>>
  pop_assum mp_tac>>ntac 2 (TOP_CASE_TAC>>fs[])>>
  rw[]>>
  FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,GSYM multiwordTheory.REPLICATE_SNOC]>>
  fs[GSYM REPLICATE]);

val state_rel_evaluate_dec = Q.prove(`
  ∀d pos g d' g' env s s' res t.
  live_dec d pos g = (d',g') ∧
  LENGTH s.globals = pos ∧
  evaluate_dec env s d = (s',res:(env_ctor # modSem$v list, modSem$v) semanticPrimitives$result) ∧
  state_rel g' s t ∧
  glob_contained env s g' ∧
  res ≠ Rerr (Rabort Rtype_error)
  ⇒
  ∃t' res'.
  evaluate_dec env t d' = (t',res') ∧
  (case res of
    Rval (env,vs) =>
      ∃env' vs'. res' = Rval(env',vs') ∧
      env = env' ∧ LENGTH vs = LENGTH vs' ∧
      (pos_notin (LENGTH s.globals) (pos_dec d) g ∨
      (vs = vs' ∧ res_glob_contained (Rval vs) g'))
  | Rerr e => res_glob_contained (Rerr e) g' ∧ res = res') ∧
  state_rel g s' t'`,
  Cases_on`d`>>fs[live_dec_def]
  >-
    (*Dlet *)
    (rw[evaluate_dec_def]
    >-
      (qpat_x_assum`_=(s',res)` mp_tac>>
      TOP_CASE_TAC>>fs[]>>
      TOP_CASE_TAC>>fs[]
      >-
        (ntac 5 (TOP_CASE_TAC>>fs[])>>
        strip_tac>>
        fs[evaluate_dec_def,evaluate_replicate,LENGTH_REPLICATE,pos_dec_def]>>
        drule (CONJUNCT1 pure_exp_evaluate)>>fs[hide_def]>>
        rw[]>>fs[])
      >>
      imp_res_tac pure_exp_evaluate>>rfs[hide_def]>>
      EVERY_CASE_TAC>>fs[])
    >>
    last_x_assum kall_tac>>
    fs[evaluate_dec_def]>>
    qpat_x_assum`_=(s',res)` mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >-
      (ntac 5 (TOP_CASE_TAC>>fs[])>>
      strip_tac>>
      drule (CONJUNCT1 state_rel_evaluate)>>
      disch_then drule>>fs[]>>impl_tac>-
        fs[subspt_domain,domain_union,glob_contained_def]>>
      rw[]>>simp[]>>
      fs[state_rel_def,domain_union]>>
      lrule glob_contained_evaluate_sing>>
      disch_then(qspecl_then[`union (glob_exp e) g`] mp_tac)>>impl_tac>-
        (fs[subspt_domain,domain_union]>>
        fs[glob_contained_def])>>
      strip_tac>>
      DISJ2_TAC>>
      fs[res_glob_contained_def,v_glob_exp_def,subspt_list_union,EVERY_MAP])
    >>
      strip_tac>>
      drule (CONJUNCT1 state_rel_evaluate)>>
      disch_then drule>>fs[]>>impl_tac>-
        (fs[subspt_domain,domain_union,glob_contained_def]>>
        Cases_on`e'`>>rw[])>>
      rw[]>>simp[]>>
      fs[state_rel_def,domain_union,res_glob_contained_def]>>
      Cases_on`e'`>>fs[]>>
      lrule glob_contained_evaluate_sing>>
      disch_then(qspecl_then[`union (glob_exp e) g`] mp_tac)>>impl_tac>-
        (fs[subspt_domain,domain_union]>>
        fs[glob_contained_def])>>
      strip_tac>>
      fs[res_glob_contained_def,v_glob_exp_def,subspt_list_union,EVERY_MAP])
  >-
    (rw[evaluate_dec_def]>>
    fs[evaluate_dec_def,evaluate_replicate,LENGTH_REPLICATE,pos_dec_def]>>
    fs[state_rel_def,domain_union]>>
    fs[res_glob_contained_def,EVERY_MAP,EVERY_MEM]>>
    rw[]>>
    PairCases_on`x`>>fs[v_glob_exp_def]>>
    fs[subspt_union,subspt_list_union,subspt_domain,domain_union,SUBSET_DEF,domain_list_union,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
    metis_tac[])
  >>
    (rw[evaluate_dec_def,pos_dec_def]>>
    fs[state_rel_def]>>rfs[res_glob_contained_def]));

(* Needs a better characterization of the globals that can appear in the first,
   third, and last envs
val state_rel_evaluate_decs = Q.prove(`
  ∀ds pos g ds' g' env s s' env' res err t.
  evaluate_decs env s ds = (s',env',res,err) ∧
  live_decs ds pos g = (ds',g') ∧
  LENGTH s.globals = pos ∧
  state_rel g' s t ∧
  glob_contained env s g' ∧
  err ≠ SOME (Rabort Rtype_error)
  ⇒
  ∃t' res'.
  evaluate_decs env t ds' = (t',env',res',err) ∧
  (∀n.
    pos + n ∈ domain g ⇒ EL n res = EL n res') ∧
  state_rel g s' t' ∧
  glob_contained env' s' g'`,
  Induct>>fs[evaluate_decs_def,live_decs_def]>>rw[]>>
  ntac 2 (pairarg_tac>>fs[])>>
  rw[]>>
  qpat_x_assum`A=(s',env',res,err)` mp_tac>>
  ntac 2 (TOP_CASE_TAC>>fs[])
  >-
    drule state_rel_evaluate_dec>>
    disch_then(qspecl_then [`env`,`s`,`q`,`Rval a`,`t`] mp_tac)>>fs[]>>strip_tac>>
    lrule evaluate_dec_globals>> strip_tac>>
    fs[evaluate_decs_def]>>
    Cases_on`a`>>fs[]
    >-
      cheat
    >>
    ntac 3 (TOP_CASE_TAC>>fs[])>>
    rw[]>>
    first_x_assum drule>>
    fs[]>>
    qpat_abbrev_tac`t'' = t' with globals updated_by A`>>
    disch_then(qspecl_then [`g`,`ds''`,`g''`,`t''`] mp_tac)>>
    impl_tac>-
      `LENGTH r = pos_dec h` by cheat>>
      fs[]>>
      state_rel_evaluate_dec
      simp[glob_contained_def]
      fs[state_rel_def]
        fs[state_rel_def]>>
        rfs[]
      fs[Abbr`t''`]
    rw[]>>simp[]>>
    simp[EL_APPEND_EQN]>>rw[]>>
    first_x_assum(qspec_then`n-LENGTH r` assume_tac)>>
    rfs[]>>fs[]>>

    first_x_assum (qspecl_then [`
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>

  >>
  strip_tac>>rw[]>>
  drule state_rel_evaluate_dec>>
  disch_then(qspecl_then [`env`,`s`,`q`,`Rerr e`,`t`] mp_tac)>>fs[]>>strip_tac>>
  fs[evaluate_decs_def]>>
  (* g is a submap of g'' *)
  cheat);

  rfs[]
  fs[]>>rw[]>>rfs[]
  fs[]>>rw[]>>rfs[]
*)

val _ = export_theory ();

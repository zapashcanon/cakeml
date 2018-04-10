open
  preamble
  semanticPrimitivesTheory
  semanticPrimitivesPropsTheory
  flatLangTheory
  flatSemTheory
  flat_scopeAnalysisTheory
  semanticsTheory
  basicSizeTheory

val _ = new_theory "flat_scopeAnalysisProof"

val alpha_eq_p_def = tDefine "alpha_eq_p"

  `(alpha_eq_p Pany Pany = T) ∧
   (alpha_eq_p (Pvar _) (Pvar _) = T) ∧
   (alpha_eq_p (Plit lit) (Plit lit') = (lit = lit')) ∧
   (alpha_eq_p (Pcon id l) (Pcon id' l') = (id = id' ∧ alpha_eq_ps l l')) ∧
   (alpha_eq_p (Pref p) (Pref p') = alpha_eq_p p p') ∧
   (alpha_eq_p _ _ = F) ∧
   (alpha_eq_ps [] [] = T) ∧
   (alpha_eq_ps (h::t) (h'::t') = (alpha_eq_p h h' ∧ alpha_eq_ps t t')) ∧
   (alpha_eq_ps _ _ = F)`

  (WF_REL_TAC `inv_image $< (λ x. case x of
    | INL (p, p') => pat_size p
    | INR (ps, ps') => pat1_size ps
  )`)

val alpha_eq_p_ind = theorem "alpha_eq_p_ind"

val alpha_eq_p_refl = Q.store_thm("alpha_eq_p_refl",

  `(∀ p p'. p = p' ⇒ alpha_eq_p p p') ∧
   (∀ ps ps'. ps = ps' ⇒ alpha_eq_ps ps ps')`,

   ho_match_mp_tac alpha_eq_p_ind
>> simp[alpha_eq_p_def])

val alpha_eq_p_sym = Q.store_thm("alpha_eq_p_sym",

  `(∀ p p'. alpha_eq_p p p' ⇒ alpha_eq_p p' p) ∧
   (∀ ps ps'. alpha_eq_ps ps ps' ⇒ alpha_eq_ps ps' ps)`,

   ho_match_mp_tac alpha_eq_p_ind
>> simp[alpha_eq_p_def])

val alpha_eq_p_trans = Q.store_thm("alpha_eq_p_trans",

  `(∀ p p' p''. (alpha_eq_p p p' ∧ alpha_eq_p p' p'') ⇒ alpha_eq_p p p'') ∧
   (∀ ps ps' ps''. (alpha_eq_ps ps ps' ∧ alpha_eq_ps ps' ps'') ⇒ alpha_eq_ps ps ps'')`,

   ho_match_mp_tac alpha_eq_p_ind
>> simp[alpha_eq_p_def, alpha_eq_p_refl, alpha_eq_p_sym]
>> rw[]
>- (Cases_on `p''` >> fs[alpha_eq_p_def])
>- (Cases_on `p''` >> fs[alpha_eq_p_def])
>- (Cases_on `p''` >> fs[alpha_eq_p_def])
>- (Cases_on `ps''` >> fs[alpha_eq_p_def]))

(* TODO: dddddddddd *)
fun progress tac = (fn g => let val (g',v) = tac g in if [g] = g' then failwith "foo" else (g', v) end)

val extract_repl_p_def = tDefine "extract_repl_p" `

  (extract_repl_p (Pvar x) (Pvar x') = [(x, x')]) ∧
  (extract_repl_p (Pcon _ l) (Pcon _ l') = extract_repl_ps l l') ∧
  (extract_repl_p (Pref p) (Pref p') = extract_repl_p p p') ∧
  (extract_repl_p _ _ = []) ∧
  (extract_repl_ps [] _ = []) ∧
  (extract_repl_ps _ [] = []) ∧
  (extract_repl_ps (h::t) (h'::t') = (extract_repl_p h h') ++ (extract_repl_ps t t'))`

  (WF_REL_TAC `inv_image $< (λ x. case x of
    | INL (p, _) => pat_size p
    | INR (ps, _) => pat1_size ps
  )`)

val alpha_eq_exp_def = tDefine "alpha_eq_exp" `
  (alpha_eq_pe repl (p, e) (p', e') = (alpha_eq_p p p' ∧ alpha_eq_exp ((extract_repl_p p p') ++ repl) e e')) ∧
  (alpha_eq_pes _ [] [] =T) ∧
  (alpha_eq_pes repl (h::t) (h'::t') = (alpha_eq_pe repl h h' ∧ alpha_eq_pes repl t t')) ∧
  (alpha_eq_pes _ _ _  = F) ∧
  (alpha_eq_es _ [] [] = T) ∧
  (alpha_eq_es repl (e::t) (e'::t') = (alpha_eq_exp repl e e' ∧ alpha_eq_es repl t t')) ∧
  (alpha_eq_es _ _ _ = F) ∧
  (alpha_eq_exp repl (Raise t e) (Raise t' e') = (t = t' ∧ alpha_eq_exp repl e e')) ∧
  (alpha_eq_exp repl (Handle t e pes) (Handle t' e' pes') = (t = t' ∧ alpha_eq_exp repl e e' ∧ alpha_eq_pes repl pes pes')) ∧
  (alpha_eq_exp repl (Lit t l) (Lit t' l') = (t = t' ∧ l = l')) ∧
  (alpha_eq_exp repl (Con t id es) (Con t' id' es') = (t = t' ∧ id = id' ∧ alpha_eq_es repl es es')) ∧
  (alpha_eq_exp repl (Var_local t x) (Var_local t' x') =
    let repl' = MAP SWAP repl in (* checking repl' is needed because otherwise, when there's free variables, this will be incorrect... *)
    let res = ALOOKUP repl x in let res' = ALOOKUP repl' x' in
    t = t' ∧
    (case res, res' of
    | SOME res, SOME res' => (res = x' ∧ res' = x)
    | NONE, NONE => x = x'
    | _, _ => F)) ∧
  (alpha_eq_exp repl (Fun t x e) (Fun t' x' e') = (t = t' ∧ alpha_eq_exp ((x, x')::repl) e e')) ∧
  (alpha_eq_exp repl (App t op es) (App t' op' es') = (t = t' ∧ op = op' ∧ alpha_eq_es repl es es')) ∧
  (alpha_eq_exp repl (If t e1 e2 e3) (If t' e1' e2' e3') = (t = t' ∧ alpha_eq_exp repl e1 e1' ∧ alpha_eq_exp repl e2 e2' ∧ alpha_eq_exp repl e3 e3')) ∧
  (alpha_eq_exp repl (Mat t e pes) (Mat t' e' pes') = (t = t' ∧ alpha_eq_exp repl e e' ∧ alpha_eq_pes repl pes pes')) ∧
  (alpha_eq_exp repl (Let t x e1 e2) (Let t' x' e1' e2') =
    (t = t' ∧ alpha_eq_exp repl e1 e1' ∧ (case x, x' of
      | NONE, NONE => alpha_eq_exp repl e2 e2'
      | SOME x, SOME x' => alpha_eq_exp ((x, x')::repl) e2 e2'
      | _, _ => F))) ∧
  (alpha_eq_exp repl (Letrec t funs e) (Letrec t' funs' e') =
    let repl' = MAP2 (λ (fName, _, _) (fName', _, _). fName, fName') funs funs' in
    t =  t' ∧ alpha_eq_exp (repl' ++ repl) e e' ∧ alpha_eq_funs (repl' ++ repl) funs funs') ∧
  (alpha_eq_exp _ _ _ = F) ∧
  (alpha_eq_fun repl (x, f) (x', f') = alpha_eq_exp ((x, x')::repl) f f') ∧
  (alpha_eq_funs repl [] [] = T) ∧
  (alpha_eq_funs repl ((_, x, e)::t) ((_, x', e')::t') = (alpha_eq_fun repl (x, e) (x', e') ∧ alpha_eq_funs repl t t')) ∧
  (alpha_eq_funs _ _ _ = F)`

  (WF_REL_TAC `inv_image $< (λ x. case x of
    | INL (_, pe, _) => exp5_size pe
    | INR (INL (_, pes, _)) => exp3_size pes
    | INR (INR (INL (_, es, _))) => exp6_size es
    | INR (INR (INR (INL (_, e, _)))) => exp_size e
    | INR (INR (INR (INR (INL (_, f, _))))) => exp4_size f
    | INR (INR (INR (INR (INR (_, funs, _))))) => exp1_size funs
  )`)

val repl_valid_refl_def = Define

  `repl_valid_refl (l : (tvarN, tvarN) alist) =
   ∀ el. MEM el l ⇒ FST el = SND el`

val repl_valid_refl_induct = Q.store_thm("repl_valid_refl_induct",

  `(repl_valid_refl [] = T) ∧
   (repl_valid_refl (h::t) ⇔ FST h = SND h ∧ repl_valid_refl t)`,

   rw[repl_valid_refl_def]
>> EQ_TAC >> rw[] >> fs[])

val repl_valid_refl_alookup = Q.store_thm("repl_valid_refl_alookup",

  `∀ l. repl_valid_refl l ⇒ (∀ x.  ALOOKUP l x = ALOOKUP (MAP SWAP l) x)`,

   Induct_on `l`
>> rw[SWAP_def]
>> imp_res_tac repl_valid_refl_induct
>> res_tac
>> fs[repl_valid_refl_def, SWAP_def]
>> last_assum (assume_tac o Q.SPEC `h`)
>> Cases_on `h`
>> fs[])

val extract_valid_refl = Q.store_thm("extract_valid_refl",

  `(∀ p p'. p = p' ⇒ repl_valid_refl (extract_repl_p p p')) ∧
   (∀ ps ps'. ps = ps' ⇒ repl_valid_refl (extract_repl_ps ps ps'))`,

   ho_match_mp_tac alpha_eq_p_ind
>> rw[extract_repl_p_def, repl_valid_refl_def]
>> Induct_on `ps`
>> NTAC 3 (simp[]))

val repl_concat_valid_refl = Q.store_thm("repl_concat_valid",

  `∀ p p'. repl_valid_refl p ∧ repl_valid_refl p' ⇒ repl_valid_refl (p ++ p')`,

   rw[repl_valid_refl_def]
>> NTAC 2 (simp[]))

val alpha_eq_exp_ind = theorem "alpha_eq_exp_ind"

val alpha_eq_exp_refl = Q.store_thm("alpha_eq_exp_refl",

 `(∀ l pe pe'. (pe = pe' ∧ repl_valid_refl l) ⇒ alpha_eq_pe l pe pe') ∧
  (∀ l pes pes'. (pes = pes'∧ repl_valid_refl l) ⇒  alpha_eq_pes l pes pes') ∧
  (∀ l es es'. (es = es' ∧ repl_valid_refl l) ⇒ alpha_eq_es l es es') ∧
  (∀ l exp exp'. (exp = exp' ∧ repl_valid_refl l) ⇒ alpha_eq_exp l exp exp') ∧
  (∀ l f f'. (f = f' ∧ repl_valid_refl l) ⇒ alpha_eq_fun l f f') ∧
  (∀ l funs funs'. (funs = funs' ∧ repl_valid_refl l) ⇒ alpha_eq_funs l funs funs')`,

   ho_match_mp_tac alpha_eq_exp_ind
>> simp[alpha_eq_exp_def, alpha_eq_p_def, alpha_eq_p_refl]
>> rw[]
>- fs[extract_valid_refl,repl_concat_valid_refl]
>- ( EVERY_CASE_TAC
  >> imp_res_tac repl_valid_refl_alookup
  >> fs[NOT_SOME_NONE, repl_valid_refl_def]
  >> imp_res_tac ALOOKUP_MEM
  >> fs[MEM_MAP,SWAP_def]
  >> rw[])
>- fs[repl_valid_refl_induct]
>- ( CASE_TAC
  >> fs[repl_valid_refl_induct])
>- ( first_x_assum match_mp_tac
  >> fs[repl_valid_refl_def]
  >> rw[]
  >> fs[MAP2_MAP, MEM_MAP]
  >> Cases_on `x`
  >> Cases_on `r`
  >> simp[])
>- ( first_x_assum match_mp_tac
  >> fs[repl_valid_refl_def]
  >> rw[]
  >> fs[MAP2_MAP, MEM_MAP]
  >> Cases_on `x`
  >> Cases_on`r`
  >> simp[])
>- fs[repl_valid_refl_induct])

val repl_valid_sym_def = Define

  `repl_valid_sym (l : (tvarN, tvarN) alist) =
   ∀ x y. case ALOOKUP l x of
   | NONE => (case ALOOKUP (MAP SWAP l) y of
     | NONE => T
     | SOME x' => x ≠ x')
   | SOME y' => (case ALOOKUP (MAP SWAP l) y' of
     | NONE => F
     | SOME x' => x' = x)`

val repl_valid_sym_def = Define

  `repl_valid_sym (l : (tvarN, tvarN) alist) =
   ∀ x y. (ALOOKUP           l  x = SOME y ⇒ ALOOKUP (MAP SWAP l) y = SOME x) ∧
          (ALOOKUP (MAP SWAP l) y = SOME x ⇒ ALOOKUP           l  x = SOME y)`

val ALOOKUP_MAP_SWAP = Q.store_thm("ALOOKUP_MAP_SWAP",

  `∀ l x y. ALOOKUP l x = SOME y ⇒ ALOOKUP (MAP SWAP l) y ≠ NONE`,

   Induct
>> fs[]
>> rw[]
>> Cases_on `h`
>> fs[SWAP_def]
>> FULL_CASE_TAC
>> rw[]
>> FULL_CASE_TAC
>> rw[]
>> res_tac)

val ALOOKUP_MAP_SWAP2 = Q.store_thm("ALOOKUP_MAP_SWAP2",

  `∀ l x y. ALOOKUP (MAP SWAP l) x = SOME y ⇒ ALOOKUP l y ≠ NONE`,

   Induct
>> fs[]
>> rw[]
>> Cases_on `h`
>> fs[SWAP_def]
>> FULL_CASE_TAC
>> rw[]
>> FULL_CASE_TAC
>> rw[]
>> res_tac)

val extract_valid_sym = Q.store_thm("extract_valid_sym",

  `(∀ p p'. extract_repl_p p p' = MAP SWAP (extract_repl_p p' p)) ∧
   (∀ ps ps'. extract_repl_ps ps ps' = MAP SWAP (extract_repl_ps ps' ps))`,

   ho_match_mp_tac alpha_eq_p_ind
>> rw[extract_repl_p_def, SWAP_def])

val map_swap_swap_id = Q.store_thm("map_swap_swap_id",

  `∀ l. MAP SWAP (MAP SWAP l) = l`,

   Induct_on `l`
>> simp[]
>> rw[SWAP_def])

val repl_valid_sym_sym = Q.store_thm("repl_valid_sym_sym",

  `∀ l. repl_valid_sym l ⇒ repl_valid_sym (MAP SWAP l)`,

   fs[repl_valid_sym_def, map_swap_swap_id, SWAP_def])

(* TODO *)
val extract_valid_sym = Q.store_thm("extract_valid_sym",

  `(∀ p p'. repl_valid_sym (extract_repl_p p p') ⇒ repl_valid_sym (extract_repl_p p' p)) ∧
   (∀ ps ps'. repl_valid_sym (extract_repl_ps ps ps') ⇒ repl_valid_sym (extract_repl_ps ps' ps))`,

   ho_match_mp_tac alpha_eq_p_ind
>> rw[extract_repl_p_def, SWAP_def]
>- rw[repl_valid_sym_def,SWAP_def]
>> fs[ALOOKUP_MAP_SWAP, ALOOKUP_MAP_SWAP2]

>> rw[Once extract_valid_sym]
>> rw[map_swap_swap_id]

>> rw[repl_valid_sym_sym]

>- qmatch_rename_tac `repl_valid_sym (l1 ++ l2)`)

val alpha_eq_exp_sym = Q.store_thm("alpha_eq_exp_sym",

  `(∀ l pe pe'. (repl_valid_sym l ∧ alpha_eq_pe l pe pe') ⇒ alpha_eq_pe l pe' pe) ∧
   (∀ l pes pes'. (repl_valid_sym l ∧ (alpha_eq_pes l pes pes' ⇒ alpha_eq_pes l pes' pes)) ∧
   (∀ l es es'. (repl_valid_sym l ∧ alpha_eq_es l es es') ⇒ alpha_eq_es l es' es) ∧
   (∀ l exp exp'. (repl_valid_sym l ∧ alpha_eq_exp l exp exp') ⇒ alpha_eq_exp l exp' exp) ∧
   (∀ l f f'. (repl_valid_sym l ∧ alpha_eq_fun l f f') ⇒ alpha_eq_fun l f' f) ∧
   (∀ l funs funs'. (repl_valid_sym ∧ alpha_eq_funs l funs funs') ⇒ alpha_eq_funs l funs' funs)`,

   cheat)

val alpha_eq_dec_def = Define

  `(alpha_eq_dec (Dlet e) (Dlet e') = alpha_eq_exp [] e e') ∧
   (alpha_eq_dec (Dtype id ctors) (Dtype id' ctors') = (id = id' ∧ ctors = ctors')) ∧
   (alpha_eq_dec (Dexn id arity) (Dexn id' arity') = (id = id' ∧ arity = arity')) ∧
   (alpha_eq_dec _ _ = F)`

val alpha_eq_dec_ind = theorem "alpha_eq_dec_ind"

val rename_dec_alpha_eq = Define

  `∀ dec n. (n', dec') = flat_scopeAnalysis$compile_dec n dec ⇒ alpha_eq_dec dec dec'`

   rw[]
>> Induct_on `dec`
>> Induct_on `e`
>> Induct_on `dec'`
>> simp[compile_dec_def]
>> rw[]
>> rw[compile_exp_def]
>> cheat

val alpha_eq_decs_def = Define

  `(alpha_eq_decs [] [] = T) ∧
   (alpha_eq_decs (h::t) (h'::t') = (alpha_eq_dec h h' ∧ alpha_eq_decs t t')) ∧
   (alpha_eq_decs _ _ = F)`

val rename_decs_alpha_eq = Q.store_thm("rename_decs_alpha_eq",

  `∀ decs. decs' = flat_scopeAnalysis$compile_decs decs ⇒ alpha_eq_decs decs decs'`

   rw[]
>> cheat)

(* TODO *)
val compile_exp_alpha_eq = Q.store_thm("compile_exp_alpha_eq",

  `∀ exp exp'. (_, exp') = flat_scopeAnalysis$compile_exp 0 [] exp ⇒ alpha_eq_exp [] exp exp'`,

)

val alpha_eq_dec_ind = theorem "alpha_eq_dec_ind"

(* TODO *)
val compile_dec_alpha_eq = Q.store_thm("compile_dec_alpha_eq",

  `∀ dec dec'. (_, dec') = flat_scopeAnalysis$compile_dec 0 dec ⇒ alpha_eq_dec dec dec'`,

   ho_match_mp_tac alpha_eq_dec_ind
>> rw[]
>> fs[compile_decs_def]
>> ho_match_mp_tac alpha_eq_exp_ind)

val compile_decs_alpha_eq = Q.store_thm("compile_decs_alpha_eq",

  `∀ decs. decs' = flat_scopeAnalysis$compile_decs decs ⇒ alpha_eq_decs decs decs'`,

   cheat)

(* TODO *)

(*
val (t_rel_rules, t_rel_ind, t_rel_cases) = Hol_reln

   (* TODO: on each case, do we need to check anything on t ? *)
  `(∀ env env' t t' e e'. t_rel env env' e e' ⇒ t_rel env env' (Raise t e) (Raise t e')) ∧
   (∀ env env' t t' e e' pes pes'. (* TODO: do we need to check something about pes and pes' ? *) t_rel env env' e e' ⇒ t_rel env env' (Handle t e pes) (Handle t' e' pes')) ∧
   (∀ env env' t t' l l'. l = l' ⇒ t_rel env env' (Lit t l) (Lit t' l')) ∧
   (∀ env env' t t' id id' es es'. (* TODO: do we care about id ? *) LIST_REL t_rel es es' ⇒ t_rel env env' (Con t id es) (Con t' id' es')) ∧
   (∀ env env' t t' x x'. OPTREL (t_rel env env') (ALOOKUP x env) (ALOOKUP x' env') ⇒ t_rel env env' (Var_local t x) (Var_local t' x')) ∧
   (∀ env env' t t' x x' e e'. t_rel ({env with v = (x,""::env.v) (x',"plop"::env') e e' ⇒ t_rel env env' (Fun t x e) (Fun t' x' e'))
*)

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln

  `(∀ lit lit'. lit = lit' ⇒ v_rel (flatSem$Litv lit) (flatSem$Litv lit')) ∧
   (∀ cn cn' vs vs'. cn = cn' ∧ LIST_REL v_rel vs vs' ⇒ v_rel (flatSem$Conv cn v) (flatSem$Conv cn' vs')) ∧
   ((* TODO: ... *)
    ∀ env env' x x' e e'. LIST_REL (λ (_, v) (_, v'). v_rel v v') env env'
    (* ∧ v_rel e e' *)
    ⇒ v_rel (flatSem$Closure env x e) (flatSem$Closure env' x' e')
    (* TODO: rec closure *)) ∧
   (∀ loc loc'. loc = loc' ⇒ v_rel (Loc loc) (Loc loc')) ∧
   (∀ vs vs'. LIST_REL v_rel vs vs' ⇒ v_rel (Vectorv vs) (Vectorv vs'))`

val (sv_rel_rules, sv_rel_ind, sv_rel_cases) = Hol_reln

  `(∀ v v'. v_rel v v' ⇒ sv_rel (Refv v) (Refv v')) ∧
   (∀ w. sv_rel (W8array w) (W8array w)) ∧
   (∀ vs vs'. LIST_REL v_rel vs vs' ⇒ sv_rel (Varray vs) (Varray vs'))`

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln

  `∀ (s : 'a flatSem$state) (s' : 'a flatSem$state). s.clock = s'.clock ∧ s.ffi = s'.ffi ∧ LIST_REL sv_rel s.refs s'.refs (* ∧ LIST_REL (OPTION_REL v_rel) s.globals s'.globals *) (* TODO *) ⇒ s_rel s s'`

(* TODO *)
val env_rel_def = Define

  `env_rel env env' = T`

(* TODO *)
val result_rel_def = Define

  `result_rel r r' = T`

val compile_decs_correct = Q.store_thm("compile_decs_correct",

  `∀ env env' (s : 'a flatSem$state) s' decs decs' resState resState' res res'.
      (resState, _, res) = flatSem$evaluate_decs env s decs
    ∧ res ≠ SOME (Rabort Rtype_error)
    ∧ env_rel env env'
    ∧ s_rel s s'
    ∧ decs' = flat_scopeAnalysis$compile_decs decs
    ∧ (resState', _, res') = flatSem$evaluate_decs env' s' decs'
    ⇒ s_rel resState resState' (* ∧ result_rel res res' *) (* TODO *)`,

   Induct_on `decs`
>- ( rw [compile_decs_def]
  >> fs [evaluate_decs_def])
>- ( rw [evaluate_decs_def]
  >> cheat))

open
  preamble
  semanticPrimitivesTheory
  semanticPrimitivesPropsTheory
  flatLangTheory
  flatSemTheory
  flat_scopeAnalysisTheory
  flat_parameterLiftingSolveTheory
  semanticsTheory
  basicSizeTheory
  set_utilsTheory
  mlnumTheory
  mlstringTheory
  ASCIInumbersTheory

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
(* fun progress tac = (fn g => let val (g',v) = tac g in if [g] = g' then failwith "foo" else (g', v) end)*)

val extract_repl_p_def = tDefine "extract_repl_p" `

  (extract_repl_p (Pvar x) (Pvar x') = [(x, x')]) ∧
  (extract_repl_p (Pcon _ l) (Pcon _ l') = extract_repl_ps l l') ∧
  (extract_repl_p (Pref p) (Pref p') = extract_repl_p p p') ∧
  (extract_repl_p _ _ = []) ∧
  (extract_repl_ps (h::t) (h'::t') = (extract_repl_p h h') ++ (extract_repl_ps t t')) ∧
  (extract_repl_ps _ _ = [])`

  (WF_REL_TAC `inv_image $< (λ x. case x of
    | INL (p, _) => pat_size p
    | INR (ps, _) => pat1_size ps
  )`)

(* TODO: useless :) *)
val extract_repl_exp_def = tDefine "extract_repl_exp"
  `(extract_repl_exp (Raise _ e) (Raise _ e') = extract_repl_exp e e') ∧
   (extract_repl_exp (Handle _ e pes) (Handle _ e' pes') = (extract_repl_exp e e') ++ (extract_repl_pes pes pes')) ∧
   (extract_repl_exp (Lit _ _) (Lit _ _) = []) ∧
   (extract_repl_exp (Con _ _ es) (Con _ _ es') = extract_repl_es es es') ∧
   (extract_repl_exp (Var_local _ _) (Var_local _ _) = []) ∧
   (extract_repl_exp (Fun _ x e) (Fun _ x' e') = (x, x')::(extract_repl_exp e e')) ∧
   (extract_repl_exp (App _ _ es) (App _ _ es') = extract_repl_es es es') ∧
   (extract_repl_exp (If _ e1 e2 e3) (If _ e1' e2' e3') =
      (extract_repl_exp e1 e1') ++ (extract_repl_exp e2 e2') ++ (extract_repl_exp e3 e3')) ∧
   (extract_repl_exp (Mat _ e pes) (Mat _ e' pes') = (extract_repl_exp e e') ++ (extract_repl_pes pes pes')) ∧
   (extract_repl_exp (Let _ x e1 e2) (Let _ x' e1' e2') =
      (case x, x' of | SOME x, SOME x' => [(x, x')] | _, _ => []) ++
      (extract_repl_exp e1 e1') ++ (extract_repl_exp e2 e2')) ∧
   (extract_repl_exp (Letrec _ funs e) (Letrec _ funs' e') =
      (extract_repl_funs funs funs') ++ (extract_repl_exp e e')) ∧
   (extract_repl_funs ((fName, vName, e)::t) ((fName', vName', e')::t') =
      (fName, fName')::(vName, vName')::(extract_repl_exp e e') ++ (extract_repl_funs t t')) ∧
   (extract_repl_funs _ _ = []) ∧
   (extract_repl_es (h::t) (h'::t') = (extract_repl_exp h h') ++ (extract_repl_es t t')) ∧
   (extract_repl_es _ _ = []) ∧
   (extract_repl_pe (p, e) (p', e') = (extract_repl_p p p') ++ (extract_repl_exp e e')) ∧
   (extract_repl_pes (h::t) (h'::t') = (extract_repl_pe h h') ++ (extract_repl_pes t t')) ∧
   (extract_repl_pes _ _ = [])`

val alpha_eq_exp_def = tDefine "alpha_eq_exp" `
  (alpha_eq_pe repl p e p' e' = (alpha_eq_p p p' ∧ alpha_eq_exp ((extract_repl_p p p') ++ repl) e e')) ∧
  (alpha_eq_pes _ [] [] = T) ∧
  (alpha_eq_pes repl ((p, e)::t) ((p',e')::t') = (alpha_eq_pe repl p e p' e' ∧ alpha_eq_pes repl t t')) ∧
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
    | INL (_, p, e, _, _) => exp5_size (p, e)
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

 `(∀ l p e p' e'. (p = p' ∧ e = e' ∧ repl_valid_refl l) ⇒ alpha_eq_pe l p e p' e') ∧
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

val MAP_SWAP_extract_repl_p = Q.store_thm("MAP_SWAP_extract_repl_p",
  `(∀ p p'. MAP SWAP (extract_repl_p p' p) = extract_repl_p p p' ) ∧
   (∀ ps ps'. MAP SWAP (extract_repl_ps ps' ps) = extract_repl_ps ps ps')`,
   ho_match_mp_tac alpha_eq_p_ind
>> rw[extract_repl_p_def, SWAP_def])

val map_swap_swap_id = Q.store_thm("map_swap_swap_id",
  `∀ l. MAP SWAP (MAP SWAP l) = l`,
   Induct_on `l` >> simp[] >> rw[SWAP_def])

val repl_valid_sym_sym = Q.store_thm("repl_valid_sym_sym",

  `∀ l. repl_valid_sym l ⇒ repl_valid_sym (MAP SWAP l)`,

   fs[repl_valid_sym_def, map_swap_swap_id, SWAP_def])

(* TODO
val extract_repl_p_repl_valid_sym = Q.store_thm("extract_repl_p_repl_valid_sym",

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

val alpha_eq_repl_valid_sym = Q.store_thm("alpha_eq_repl_valid_sym"
 `(∀ p p'. alpha_eq_p p p' ⇒ repl_valid_sym (extract_repl_p p p')) ∧
  (∀ ps ps'. alpha_eq_ps ps ps' ⇒ repl_valid_sym (extract_repl_ps ps ps'))`,

  ho_match_mp_tac alpha_eq_p_ind >>
  rw[repl_valid_sym_def, extract_repl_p_def, alpha_eq_p_def, SWAP_def] >>
  fs[ALOOKUP_APPEND] >>

  CASE_TAC >> fs[] >>
    >-(FULL_CASE_TAC
       >- fs[ALOOKUP_MAP_SWAP]
       >- (fs[] >> imp_res_tac ALOOKUP_MAP_SWAP))
    >-(FULL_CASE_TAC
       >- fs[ALOOKUP_MAP_SWAP]
       >- (fs[] >> imp_res_tac ALOOKUP_MAP_SWAP)
       )




  EVERY_CASE_TAC >> res_tac >> rw[] >> fs[] >>


     fs[ALOOKUP_MAP_SWAP2]
     rw[]
  )
  >-
  fs[ALOOKUP_]

  res_tac
  res_tac >>
  [MAP_APPEND,]
  Cases_on`p'` >>
  fs[extract_repl_p_def,SWAP_def]
  ALOOKUP_MAP_SWAP
  find"alpha_eq_p"
  >-
  >-
  >-
  >-
  MAP_SWAP_extract_repl_p,] >>

val alpha_eq_exp_sym = Q.store_thm("alpha_eq_exp_sym",

  `(∀ l p e p' e'. (repl_valid_sym l ∧ alpha_eq_pe l p e p' e') ⇒ alpha_eq_pe (MAP SWAP l) p' e' p e) ∧
   (∀ l pes pes'. (repl_valid_sym l ∧ alpha_eq_pes l pes pes') ⇒ alpha_eq_pes (MAP SWAP l) pes' pes) ∧
   (∀ l es es'. (repl_valid_sym l ∧ alpha_eq_es l es es') ⇒ alpha_eq_es (MAP SWAP l) es' es) ∧
   (∀ l exp exp'. (repl_valid_sym l ∧ alpha_eq_exp l exp exp') ⇒ alpha_eq_exp (MAP SWAP l) exp' exp) ∧
   (∀ l f f'. (repl_valid_sym l ∧ alpha_eq_fun l f f') ⇒ alpha_eq_fun (MAP SWAP l) f' f) ∧
   (∀ l funs funs'. (repl_valid_sym l ∧ alpha_eq_funs l funs funs') ⇒ alpha_eq_funs (MAP SWAP l) funs' funs)`,

   ho_match_mp_tac alpha_eq_exp_ind >>
   rw[alpha_eq_exp_def] >>
   fs[alpha_eq_exp_def,alpha_eq_p_sym, extract_repl_p_valid_sym] >>
   >-
   >-
   >-
   >-
   >-
   >-
   >-
   )

*)

val is_closed_term_exp_def = Define

  `is_closed_term_exp e = (compute_freeID_exp [] e = empty_set)`

val _ = temp_overload_on("alist_dom", ``λ l. MAP FST l``)

val _ = temp_overload_on("is_valid_term_exp",  ``λ l e. compute_freeID_exp  (alist_dom l) e = empty_set``)
val _ = temp_overload_on("is_valid_term_pe",   ``λ l e. compute_freeID_pe   (alist_dom l) e = empty_set``)
val _ = temp_overload_on("is_valid_term_pes",  ``λ l e. compute_freeID_pes  (alist_dom l) e = empty_set``)
val _ = temp_overload_on("is_valid_term_fun",  ``λ l e. compute_freeID_fun  (alist_dom l) e = empty_set``)
val _ = temp_overload_on("is_valid_term_funs", ``λ l e. compute_freeID_funs (alist_dom l) e = empty_set``)
val _ = temp_overload_on("is_valid_term_es",   ``λ l e. compute_freeID_exps (alist_dom l) e = empty_set``)

val alist_injective_def = Define

  `alist_injective l =
     ∀ x y z. ( ALOOKUP l x = SOME z ∧ ALOOKUP l y = SOME z ) ⇒ (x = y)`

val alist_rename_format_ok_def = Define

  `alist_rename_format_ok l n = ∀ x y. MEM (x, y) l ⇒ ∃ k. k < n ∧ y = mk_unique_name k x`

val alist_rename_ok_def = Define

  `alist_rename_ok l n = (alist_injective l ∧ alist_rename_format_ok l n)`

val num_toString_bij = Q.store_thm("num_toString_bij",

  `∀ n n'. num_toString n = num_toString n' ⇔ n = n'`,

  metis_tac[num_to_dec_string_def, num_toString_thm, toString_11])

val toString_bij = Q.store_thm("toString_bij",

  `∀ n n'. n = n' ⇔ toString n = toString n'`,

   rw[toString_def, implode_def]
>> metis_tac[num_toString_bij])

val mk_unique_bij1 = Q.store_thm("mk_unique_bij1",

  `∀ k k' s s'. (k = k' ∧ s = s') ⇒ mk_unique_name k s = mk_unique_name k' s'`,

  rw[mk_unique_name_def, STRCAT])

val mk_unique_bij2 = Q.store_thm("mk_unique_bij2",

  `∀ k k' s s'. mk_unique_name k s = mk_unique_name k' s' ⇒ (k = k' ∧ s = s')`,

  cheat (* this is true because "_" can't be in a number, proof will not be trivial...*))

val mk_unique_bij = Q.store_thm("mk_unique_big",

  `∀ k k' s s'. mk_unique_name k s = mk_unique_name k' s' ⇔ (k = k' ∧ s = s')`,

  metis_tac[mk_unique_bij1, mk_unique_bij2])

val compile_funs_le = Q.store_thm("compile_funs_le",

 `∀ funs n l. n ≤ FST (compile_name_rec_funs n l funs)`,

  cheat
  (* TODO: this doesn't work anymore
   Induct >> rw[] >> fs[compile_name_rec_funs_def]
>> rpt (pairarg_tac >> fs[])
>> Cases_on`h` >> Cases_on`r`
>> fs[compile_name_rec_fun_def]
>> rw[]
>> qmatch_asmsub_abbrev_tac `compile_name_rec_funs n0 l0`
>> first_x_assum (assume_tac o Q.SPECL [`n0`,`l0`])
>> unabbrev_all_tac
>> rfs[]*))

val compile_p_le = Q.store_thm("compile_p_le",

  `(∀ p n l. n ≤ FST (compile_p n l p)) ∧
   (∀ ps n l. n ≤ FST (compile_ps n l ps))`,

   Induct
>> fs[compile_p_def]
>> rpt (pairarg_tac >> fs[])
>> Induct
>> rw[]
>> rpt (pairarg_tac >> fs[])
>> metis_tac[FST, LESS_EQ_TRANS])

val compile_count_le = Q.store_thm("compile_count_le",

  `(∀ n l el n' el'. compile_exp n l el  = (n', el') ⇒ n ≤ n') ∧
   (∀ n l el n' el'. compile_fun n l el  = (n', el') ⇒ n ≤ n') ∧
   (∀ n l el n' el'. compile_funs n l el = (n', el') ⇒ n ≤ n') ∧
   (∀ n l el n' el'. compile_exps n l el = (n', el') ⇒ n ≤ n') ∧
   (∀ n l el n' el'. compile_pe n l el   = (n', el') ⇒ n ≤ n') ∧
   (∀ n l el n' el'. compile_pes n l el  = (n', el') ⇒ n ≤ n')`,

   ho_match_mp_tac compile_exp_ind
>> rw[compile_exp_def, compile_name_rec_funs_def, compile_funs_le]
>> rpt(pairarg_tac >> fs[])
>> rw[]
>> metis_tac[compile_funs_le, compile_p_le, FST, LESS_EQ_TRANS])

val ALIST_MAP_FST_SWAP_MAP_SND = Q.store_thm("ALIST_MAP_FST_SWAP_MAP_SND",

  `∀ l. MAP FST (MAP SWAP l) = MAP SND l`,

   Induct
>> rw[SWAP_def, FST])

val ALOOKUP_MEM_ADD = Q.store_thm("ALOOKUP_MEM_ADD",

  `∀ l h x y. ALOOKUP (h::l) x = SOME y ⇒ (y = SND h ∨ MEM y (MAP SND l))`,

   Induct
>> Cases_on `h`
>> rw[]
>- metis_tac[])

val ALOOKUP_SOME_MAP_SND = Q.store_thm("ALOOKUP_SOME_MAP_SND",

  `∀ l x y. (ALOOKUP l x = SOME y) ⇒ MEM y (MAP SND l)`,

   Induct
>> rw[]
>> rw[ALOOKUP_def, ALOOKUP_MEM, SND]
>> metis_tac[ALOOKUP_MEM_ADD])

val MEM_SWAP = Q.store_thm("MEM_SWAP",

  `∀ l x y. MEM (x, y) l ⇔ MEM (y, x) (MAP SWAP l)`,

  Induct
>- rw[]
>- ( rw[]
  >> `(x, y) = h ⇒ (y, x) = SWAP h` by metis_tac[SWAP_def, FST, SND]
  >> `(y, x) = SWAP h ⇒ (x, y) = h` by (EVAL_TAC >> fs[])
  >> metis_tac[]))

(*
val ALOOKUP_SWAP_NONE_SOME = Q.store_thm("ALOOKUP_SWAP_NONE_SOME",

  `∀ l x x'. ALOOKUP l x = SOME x' ⇔ ALOOKUP (MAP SWAP l) x' ≠ NONE`,

   Induct
>- rw[]
>> rw[]
>> Cases_on `h`
>> rw[SWAP_def, ALOOKUP_MEM, ALOOKUP_def, ALOOKUP_MAP_SWAP, ALOOKUP_MAP_SWAP2])
*)

val compute_freeID_still_empty_included = Q.store_thm("compute_freeID_still_empty_included",

  `∀ e e1 e2. (set_included e1 e2 ∧ compute_freeID_exp e1 e = empty_set) ⇒ compute_freeID_exp e2 e = empty_set`,

  cheat)

val compile_name_rec_funs_ok = Q.store_thm("compile_name_rec_funs_ok",

  `∀ n l funs n' l' funs' n'' funs''.
      compile_name_rec_funs n l funs = (n', l', funs') ∧
      compile_funs n' l' funs' = (n'', funs'')
      ⇒ l' = MAP2 (λ x y. FST x, FST y) funs funs'' ++ l`,

  cheat
(*
   Induct_on `funs`
>> fs[compile_name_rec_funs_def, compile_exp_def]
>> rw[]
>> Cases_on `funs'`
>> rw[]
>> fs[compile_name_rec_funs_def, compile_exp_def]
>> rw[]
>> rpt (pairarg_tac >> fs[])
>> rw[]
>> Cases_on `f`
>> fs[compile_exp_def]
>> rpt(pairarg_tac >> fs[])
>> rw[]
>> Cases_on `h`
>> fs[]
>> Cases_on`r'`
>> fs[compile_name_rec_funs_def, compile_name_rec_fun_def]
(* TODO: move compile_name_rec_fun directly into compile_name_rec_funs *)
>> rw[]

>> Cases_on`l'`
>- (
     fs[compile_exp_def]
     pairarg_tac >> fs[]
     rw[]
     cheat)
>> rw[compile_exp_def]
>> rw[compile_name_rec_fun_def]

res_tac

>> cheat
*))

val compute_freeID_still_empty_less_funs = Q.store_thm("compute_freeID_still_empty_less_funs",

  `∀ l f funs. compute_freeID_funs l (f::funs) = empty_set ⇒ compute_freeID_funs l funs = empty_set`,

  cheat)


val is_valid_less_funs = Q.store_thm("is_valid_less_funs",

  `∀ l f funs. is_valid_term_funs l (f::funs) ⇒ is_valid_term_funs l funs`,

   metis_tac[compute_freeID_still_empty_less_funs])

val is_valid_term_funs_fun = Q.store_thm("is_valid_term_funs_fun",

  `∀ l fName q r funs. is_valid_term_funs l ((fName, q, r):: funs) ⇒ is_valid_term_fun l (q, r)`,

   cheat)

val rename_p_alpha_eq = Q.store_thm("rename_p_alpha_eq",

  `(∀ n l p p' l' n'.
    compile_p n l p = (n', l', p') ⇒ alpha_eq_p p p') ∧
   (∀ n l p p' l' n'.
    compile_ps n l p = (n', l', p') ⇒ alpha_eq_ps ps ps')`,

   cheat)

val rename_alpha_eq = Q.store_thm("rename_alpha_eq",

  `(∀ n l e e' n'.
      ((is_valid_term_exp l e) ∧
       ((n', e') = compile_exp n l e) ∧
       (alist_rename_ok l n))
      ⇒ alpha_eq_exp l e e') ∧
   (∀ n l f f' n'.
      ((is_valid_term_fun l f) ∧
       ((n', f') = compile_fun n l f) ∧
       (alist_rename_ok l n))
      ⇒ alpha_eq_fun l f f') ∧
   (∀ n l funs funs' n'.
      ((is_valid_term_funs l funs) ∧
       ((n', funs') = compile_funs n l funs) ∧
       (alist_rename_ok l n))
      ⇒ alpha_eq_funs l funs funs') ∧
   (∀ n l es es' n'.
      ((is_valid_term_es l es) ∧
       ((n', es') = compile_exps n l es) ∧
       (alist_rename_ok l n))
      ⇒ alpha_eq_es l es es') ∧
  (∀ n l pe pe' n'.
       ((is_valid_term_pe l pe) ∧
        ((n', pe') = compile_pe n l pe) ∧
        (alist_rename_ok l n))
       ⇒ alpha_eq_pe l (FST pe) (SND pe) (FST pe') (SND pe')) ∧
   (∀ n l pes pes' n'.
      ((is_valid_term_pes l pes) ∧
       ((n', pes') = compile_pes n l pes) ∧
       (alist_rename_ok l n))
      ⇒ alpha_eq_pes l pes pes')`,

   ho_match_mp_tac compile_exp_ind
>> rw[alpha_eq_exp_def, compile_exp_def, alist_rename_ok_def, alist_rename_format_ok_def, alist_injective_def]
>> rpt(pairarg_tac >> fs[])
>> rw[alpha_eq_exp_def]
>> fs[compute_freeID_exp_def]
>> res_tac
>- ( first_x_assum match_mp_tac
  >> imp_res_tac set_union_empty)
>- ( first_x_assum match_mp_tac
   >> rw[compile_exp_def]
   >> `n ≤ counter'` by metis_tac [FST, LESS_EQ_TRANS, compile_p_le, compile_count_le]
  >> rw[]
  >- imp_res_tac set_union_empty
  >> res_tac
  >> qexists_tac `k`
  >> rw[])
>- ( CASE_TAC >- ( imp_res_tac ALOOKUP_NONE >> fs[set_add_non_empty])
  >> CASE_TAC >- imp_res_tac ALOOKUP_MAP_SWAP >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac MEM_SWAP >>
    res_tac >> metis_tac[mk_unique_bij])
>- ( first_x_assum match_mp_tac
  >> rw[]
  >- ( `set_included (set_add (alist_dom l) x) (x::(alist_dom l))` by (rw[set_included_def] >> metis_tac[set_add_thm])
    >> metis_tac[compute_freeID_still_empty_included])
  >- ( rw[]
    >> imp_res_tac ALOOKUP_MEM
    >> res_tac
    >> metis_tac[mk_unique_bij])
  >- ( rw[]
    >> imp_res_tac ALOOKUP_MEM
    >> res_tac
    >> metis_tac[mk_unique_bij])
  >- ( qexists_tac `n` >> rw[])
  >- ( res_tac >> qexists_tac `k` >> rw[]))
>- ( first_x_assum match_mp_tac >> imp_res_tac set_union_empty)
>- ( first_x_assum match_mp_tac
  >> NTAC 2 (imp_res_tac set_union_empty)
  >> fs[]
  >> rw[]
  >> res_tac
  >> qexists_tac `k`
  >> rw[]
  >> `n ≤ counter'` by metis_tac[compile_count_le]
  >> fs[LESS_EQ_LESS_TRANS, LESS_EQ_TRANS])
>- ( first_x_assum match_mp_tac
  >> NTAC 2 (imp_res_tac set_union_empty)
  >> fs[]
  >> rw[]
  >> res_tac
  >> qexists_tac `k`
  >> rw[]
  >> `n ≤ counter''` by metis_tac[compile_count_le, LESS_EQ_TRANS]
  >> fs[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS])
>- ( first_x_assum match_mp_tac >> imp_res_tac set_union_empty)
>- ( first_x_assum match_mp_tac
  >> imp_res_tac set_union_empty
  >> fs[]
  >> rw[]
  >> res_tac
  >> qexists_tac `k`
  >> fs[]
  >> `n ≤ counter'` by metis_tac[compile_count_le, LESS_EQ_TRANS]
  >> res_tac
  >> fs[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS])
>- ( first_x_assum match_mp_tac
  >> imp_res_tac set_union_empty
  >> fs[]
  >> rw[]
  >> fs[]
  >> res_tac
  >> qexists_tac `k`
  >> fs[])
>- ( first_x_assum match_mp_tac
  >> rw[]
  >- ( imp_res_tac set_union_empty
    >> `set_included (set_union (alist_dom l) [x]) (x::alist_dom l)` by metis_tac[set_eq_union_sing_app, set_eq_imp_incl]
    >> metis_tac[compute_freeID_still_empty_included])
  >- metis_tac[mk_unique_bij,ALOOKUP_MEM]
  >- metis_tac[mk_unique_bij,ALOOKUP_MEM]
  >- ( qexists_tac `n`
    >> rw[]
    >> `n + 1 ≤ counter'` by metis_tac[compile_count_le, LESS_EQ_TRANS]
    >> fs[])
  >- ( res_tac
    >> qexists_tac `k`
    >> `n + 1 ≤ counter'` by metis_tac[compile_count_le, LESS_EQ_TRANS]
    >> fs[]))
>- ( first_x_assum match_mp_tac >> imp_res_tac set_union_empty)
>- ( first_x_assum match_mp_tac
  >> imp_res_tac compile_count_le
  >> rw[]
  >- ( imp_res_tac set_union_empty
    >> `set_included (set_union (alist_dom l) empty_set) (alist_dom l)` by metis_tac[set_union_empty_id, set_eq_imp_incl]
    >> metis_tac[compute_freeID_still_empty_included])
  >- ( res_tac
    >> qexists_tac `k `
    >> rw[]))
>- ( imp_res_tac set_union_empty
  >> imp_res_tac compile_name_rec_funs_ok
  >> sg `is_valid_term_exp repl' e`
    >- ( imp_res_tac compile_name_rec_funs_ok
      >> fs[]
      >> rw[]
      (*>> sg `(alist_dom (MAP2 (λ x y. (FST x, FST y)) funs funs'')) = (MAP (λ (name, _, _). name) funs)`
        >- cheat*)
      >> cheat)
  >> fs[]
  >> rfs[]
  >> rw[]
  >> cheat)
>- ( imp_res_tac set_union_empty
  >> imp_res_tac compile_name_rec_funs_ok
  >> cheat)
>- ( first_x_assum match_mp_tac
  >> rw[]
  >> `set_eq (vName::alist_dom l) (set_add (alist_dom l) vName)` by (
          rw[set_eq_def]
        >> EQ_TAC
        >> rw[MEM, set_add_def]
        >> metis_tac[set_add_thm])
  >- metis_tac[compute_freeID_still_empty_included, set_eq_imp_incl]
  >- ( `MEM (y, mk_unique_name n vName) l` by metis_tac[ALOOKUP_MEM]
    >> res_tac
    >> metis_tac[mk_unique_bij])
  >- ( `MEM (x, mk_unique_name n vName) l` by metis_tac[ALOOKUP_MEM]
    >> res_tac
    >> metis_tac[mk_unique_bij])
  >- ( qexists_tac `n`
    >> rw[])
  >- ( res_tac
    >> qexists_tac `k`
    >> rw[]))
>- ( Cases_on `f`
  >> Cases_on` f'`
  >> fs[alpha_eq_exp_def]
  >> rw[]
  >> imp_res_tac is_valid_less_funs
  >> `n ≤ counter'` by metis_tac[compile_count_le]
  >- metis_tac[is_valid_term_funs_fun]
  >> first_x_assum match_mp_tac
  >> rw[]
  >> res_tac
  >> qexists_tac`k`
  >> fs[]
  >> imp_res_tac compile_count_le
  >> fs[])
>- ( first_x_assum match_mp_tac >> imp_res_tac set_union_empty)
>- ( first_x_assum match_mp_tac
  >> imp_res_tac set_union_empty
  >> rw[]
  >> res_tac
  >> qexists_tac `k`
  >> `n ≤ counter'` by metis_tac[compile_count_le, LESS_EQ_TRANS]
  >> fs[])
>- metis_tac[rename_p_alpha_eq]
>- ( `n ≤ counter'` by metis_tac[compile_p_le, LESS_EQ_LESS_TRANS, LESS_EQ_LESS_TRANS, FST]
  >> `set_eq (extract_repl_p p p' ++ l) repl'` by cheat
  (* TODO: rewrite compile_p_def so we only return new repl, not the old one updated ; should make this easier... *)
  >> cheat)
>- ( imp_res_tac set_union_empty
  >> rw[])
>- ( imp_res_tac set_union_empty
  >> rw[])
>- ( first_x_assum match_mp_tac
  >> imp_res_tac set_union_empty
  >> rw[]
  >> res_tac
  >> qexists_tac `k`
  >> `n ≤ counter''` by metis_tac[compile_p_le, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, FST]
  >> `counter'' ≤ counter'` by metis_tac[compile_count_le, LESS_EQ_TRANS]
  >> fs[]))

val alpha_eq_dec_def = Define

  `(alpha_eq_dec (Dlet e) (Dlet e') = alpha_eq_exp [] e e') ∧
   (alpha_eq_dec (Dtype id ctors) (Dtype id' ctors') = (id = id' ∧ ctors = ctors')) ∧
   (alpha_eq_dec (Dexn id arity) (Dexn id' arity') = (id = id' ∧ arity = arity')) ∧
   (alpha_eq_dec _ _ = F)`

val alpha_eq_dec_ind = theorem "alpha_eq_dec_ind"

val is_valid_dec_def = Define `
  (is_valid_dec (Dlet e) = (compute_freeID_exp [] e = empty_set)) ∧
  (is_valid_dec (Dtype _ _) = T) ∧
  (is_valid_dec (Dexn _ _) = T)
`

val rename_dec_alpha_eq = Q.store_thm("rename_dec_alpha_eq",

  `∀ dec n. (is_valid_dec dec ∧ (n', dec') = compile_dec n dec) ⇒ alpha_eq_dec dec dec'`,

   rw[]
>> Cases_on `dec`
>> Cases_on `dec'`
>> rw[alpha_eq_dec_def, compile_dec_def]
>> fs[alpha_eq_dec_def, compile_dec_def]
>- ( fs[is_valid_dec_def]
  >> `compile_exp n [] e = (n', e')` by (pairarg_tac >> fs[])
  >> `is_valid_term_exp [] e` by (`alist_dom [] = []` by EVAL_TAC >> rw[])
  >> `alist_rename_ok [] n` by rw[alist_rename_ok_def, alist_injective_def, alist_rename_format_ok_def]
  >> imp_res_tac rename_alpha_eq
  >> rw[])
>> pairarg_tac
>> fs[])

val alpha_eq_decs_def = Define

  `(alpha_eq_decs [] [] = T) ∧
   (alpha_eq_decs (h::t) (h'::t') = (alpha_eq_dec h h' ∧ alpha_eq_decs t t')) ∧
   (alpha_eq_decs _ _ = F)`

val is_valid_decs_def = Define

  `is_valid_decs decs = (∀ dec. MEM dec decs ⇒ is_valid_dec dec)`

val rename_decs_alpha_eq = Q.store_thm("rename_decs_alpha_eq",

  `∀ decs. (is_valid_decs decs ∧ decs' = compile_decs decs) ⇒ alpha_eq_decs decs decs'`,

  Induct
>- rw[alpha_eq_decs_def, rename_dec_alpha_eq, compile_decs_def, SND, compile_decs_aux_def]
>> rw[]
>> cheat)

val alpha_eq_dec_ind = theorem "alpha_eq_dec_ind"

(* TODO *)

(*
val (t_rel_rules, t_rel_ind, t_rel_cases) = Hol_reln

   (* TODO: on each case, do we need to check anything on t ? *)
  `(∀ env env' t t' e e'. t_rel env env' e e' ⇒ t_rel env env' (Raise t e) (Raise t' e')) ∧
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

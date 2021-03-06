open preamble

(* TODO: this file needs to be tided up and moved
         e.g., under a subdirectory (reachability) (analogous to reg_alloc/parmove)
         the definitions and proofs should also be split
*)

val _ = new_theory "reachability";

(******************************************************** GENERAL SPTREE LEMMAS *********************************************************)

(**************************** RESULTS FROM SPTREETHEORY *****************************)

val mk_BN_thm = prove(
  ``!t1 t2. mk_BN t1 t2 =
            if isEmpty t1 /\ isEmpty t2 then LN else BN t1 t2``,
  REPEAT Cases >> EVAL_TAC);

val mk_BS_thm = prove(
  ``!t1 t2. mk_BS t1 x t2 =
            if isEmpty t1 /\ isEmpty t2 then LS x else BS t1 x t2``,
  REPEAT Cases >> EVAL_TAC);

val oddevenlemma = prove(
  ``2n * y + 1 <> 2 * x + 2``,
  disch_then (mp_tac o AP_TERM ``EVEN``) >>
  simp[EVEN_ADD, EVEN_MULT]);

(**************************************** DOMAIN LEMMAS ****************************************)

val size_domain = Q.store_thm("size_domain",
    `∀ t . size t = CARD (domain t)`,
    Induct_on `t`
    >- rw[size_def, domain_def]
    >- rw[size_def, domain_def]
    >> rw[pred_setTheory.CARD_UNION_EQN, pred_setTheory.CARD_INJ_IMAGE]
    >| [
    `IMAGE (λn. 2 * n + 2) (domain t) ∩ IMAGE (λn. 2 * n + 1) (domain t') = {}`
        by (rw[GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >> Cases_on `ODD x`
        >> fs[ODD_EXISTS, ADD1, oddevenlemma]
           )
        >> simp[] ,
    `(({0} ∩ IMAGE (λn. 2 * n + 2) (domain t)) = {}) /\
     (({0} UNION (IMAGE (\n. 2 * n + 2) (domain t)))
          INTER (IMAGE (\n. 2 * n + 1) (domain t')) = {})`
    by (rw[GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >> Cases_on `ODD x`
        >> fs[ODD_EXISTS, ADD1, oddevenlemma]
           )
        >> simp[]
    ]
);

val num_set_domain_eq = Q.store_thm("num_set_domain_eq",
    `∀ t1 t2:num_set . wf t1 ∧ wf t2 ⇒
        (domain t1 = domain t2 ⇔ t1 = t2)`,
    rw[] >> EQ_TAC >> rw[spt_eq_thm] >> fs[EXTENSION, domain_lookup] >>
    pop_assum (qspec_then `n` mp_tac) >> strip_tac >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[]
);

(**************************************** UNION LEMMAS ****************************************)

val union_num_set_sym = Q.store_thm ("union_num_set_sym",
    `∀ t1:num_set t2 . union t1 t2 = union t2 t1`,
    Induct >> fs[union_def] >> rw[] >> CASE_TAC >> fs[union_def]
);

val mk_wf_union = Q.store_thm("mk_wf_union",
    `∀ t1 t2 . mk_wf (union t1 t2) = union (mk_wf t1) (mk_wf t2)`,
    rw[] >> `wf(union (mk_wf t1) (mk_wf t2)) ∧ wf(mk_wf (union t1 t2))` by
        metis_tac[wf_mk_wf, wf_union] >>
    rw[spt_eq_thm] >> fs[lookup_union, lookup_mk_wf]
);

(**************************************** DIFFERENCE LEMMAS ****************************************)

val domain_difference = Q.store_thm("domain_difference",
    `∀ t1 t2 . domain (difference t1 t2) = (domain t1) DIFF (domain t2)`,
    simp[pred_setTheory.EXTENSION, domain_lookup, lookup_difference] >>
    rw [] >> Cases_on `lookup x t1`
    >- fs[]
    >> fs[] >> Cases_on `lookup x t2`
        >- rw[] >- rw[]
);

val difference_sub = Q.store_thm("difference_sub",
    `(difference a b = LN) ⇒ (domain a ⊆ domain b)`,
    rw[] >>
    `(domain (difference a b) = {})` by rw[domain_def] >>
    fs[EXTENSION, domain_difference, SUBSET_DEF] >>
    metis_tac[]
);

val wf_difference = Q.store_thm("wf_difference",
    `∀ t1 t2 . (wf t1 ∧ wf t2) ⇒ wf (difference t1 t2)`,
    Induct >> rw[difference_def, wf_def] >> CASE_TAC >> fs[wf_def]
    >> rw[wf_def, wf_mk_BN, wf_mk_BS]
);

(**************************************** DELETION LEMMAS ****************************************)

val delete_fail = Q.store_thm ("delete_fail",
    `∀ n t . (wf t) ⇒ (n ∉  domain t ⇔ (delete n t = t))`,
    simp[domain_lookup] >>
    recInduct lookup_ind >>
    rw[lookup_def, wf_def, delete_def, mk_BN_thm, mk_BS_thm]
);

val size_delete = Q.store_thm ( "size_delete",
    `∀ n t . (size (delete n t) = if (lookup n t = NONE) then (size t) else (size t - 1))`,
    rw[size_def] >>
    fs[lookup_NONE_domain] >>
    TRY (qpat_assum `n NOTIN d` (qspecl_then [] mp_tac)) >>
    rfs[delete_fail, size_def] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain]
);

(**************************************** LOOKUP LEMMAS ****************************************)

val lookup_zero = Q.store_thm ( "lookup_zero",
  `∀ n t x. (lookup n t = SOME x) ==> (size t <> 0)`,
   recInduct lookup_ind
   \\ rw[lookup_def]
);

(**************************************** SUBTREE LEMMAS ****************************************)

val empty_sub = Q.store_thm("empty_sub",
    `isEmpty(difference a b) ∧ (subspt b a) ==> (domain a = domain b)`,
    fs[subspt_def] >>
    rw[] >>
    imp_res_tac difference_sub >>
    metis_tac[GSYM SUBSET_DEF, SUBSET_ANTISYM]
);

val subspt_delete = Q.store_thm("subspt_delete",
    `∀ a b x . subspt a b ⇒ subspt (delete x a) b`,
    rw[subspt_def, lookup_delete]
);

(**************************************** INTERSECTION LEMMAS ****************************************)

val inter_union_empty = Q.store_thm("inter_union_empty",
    `∀ a b c . isEmpty (inter (union a b) c) ⇔ isEmpty (inter a c) ∧ isEmpty (inter b c)`,
    rw[] >> EQ_TAC >> rw[] >> `wf (inter (union a b) c) ∧ wf (inter a c)` by metis_tac[wf_inter] >>
    fs[domain_empty] >> fs[EXTENSION] >> rw[] >> pop_assum (qspec_then `x` mp_tac) >> fs[domain_lookup] >>
    rw[] >> fs[lookup_inter, lookup_union] >> TRY(first_x_assum (qspec_then `x` mp_tac)) >> rw[] >>
    fs[lookup_inter, lookup_union] >> EVERY_CASE_TAC >> fs[]
);

val inter_insert_empty = Q.store_thm("inter_insert_empty",
    `∀ n t1 t2 . isEmpty (inter (insert n () t1) t2) ⇒ n ∉ domain t2 ∧ isEmpty(inter t1 t2)`,
    rw[] >> `∀ k . lookup k (inter (insert n () t1) t2) = NONE` by fs[lookup_def]
    >- (fs[domain_lookup] >> rw[] >> fs[lookup_inter] >> pop_assum (qspec_then `n` mp_tac) >>
        rw[] >> fs[] >> EVERY_CASE_TAC >> fs[])
    >- (`wf (inter t1 t2)` by metis_tac[wf_inter] >> fs[domain_empty] >> fs[EXTENSION] >> rw[] >>
        pop_assum (qspec_then `x` mp_tac) >> rw[] >> first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
        fs[domain_lookup, lookup_inter, lookup_insert] >> Cases_on `x = n` >> fs[] >>
        Cases_on `lookup n t2` >> fs[] >> CASE_TAC)
);

(**************************************** MISC LEMMAS ****************************************)

val fromList2_value = Q.store_thm("fromList2_value",
    `∀ e l t n . MEM e l ⇔  ∃ n . lookup n (fromList2 l) = SOME e`,
    rw[lookup_fromList2] >> rw[lookup_fromList] >> fs[MEM_EL] >>
    EQ_TAC >> rw[]
    >- (qexists_tac `n * 2` >> fs[] >> once_rewrite_tac [MULT_COMM] >> rw[EVEN_DOUBLE, MULT_DIV])
    >- (qexists_tac `n DIV 2` >> fs[])
);





(******************************************************** DEFINITIONS + RELATED LEMMAS *********************************************************)

(**************************************** NUM_SET_TREE_UNION ****************************************)

val num_set_tree_union_def = Define `
    (num_set_tree_union (LN:num_set num_map) t2 = t2) ∧
    (num_set_tree_union (LS a) t =
     case t of
       | LN => LS a
       | LS b => LS (union a b)
       | BN t1 t2 => BS t1 a t2
       | BS t1 b t2 => BS t1 (union a b) t2) ∧
  (num_set_tree_union (BN t1 t2) t =
     case t of
       | LN => BN t1 t2
       | LS a => BS t1 a t2
       | BN t1' t2' => BN (num_set_tree_union t1 t1') (num_set_tree_union t2 t2')
       | BS t1' a t2' => BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')) ∧
  (num_set_tree_union (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS b => BS t1 (union a b) t2
       | BN t1' t2' => BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')
       | BS t1' b t2' => BS (num_set_tree_union t1 t1') (union a b) (num_set_tree_union t2 t2'))
`;

(******** THEOREMS ********)

val num_set_tree_union_empty = Q.store_thm("num_set_tree_union_empty",
    `∀ t1 t2 . isEmpty(num_set_tree_union t1 t2) ⇔ isEmpty t1 ∧ isEmpty t2`,
    Induct >> rw[num_set_tree_union_def] >> CASE_TAC >> rw[num_set_tree_union_def]
);

val wf_num_set_tree_union = Q.store_thm("wf_num_set_tree_union",
    `∀ t1 t2 result . wf t1 ∧ wf t2 ∧ num_set_tree_union t1 t2 = result ⇒ wf result`,
    Induct >> rw[num_set_tree_union_def, wf_def] >> rw[wf_def] >> TRY(CASE_TAC) >>
    rw[wf_def] >> TRY(metis_tac[wf_def, num_set_tree_union_empty])
);

val domain_num_set_tree_union = Q.store_thm ("domain_num_set_tree_union",
    `∀ t1 t2 . domain (num_set_tree_union t1 t2) = domain t1 ∪ domain t2`,
    Induct >> rw[num_set_tree_union_def, domain_def] >> CASE_TAC >>
    rw[domain_def, domain_union] >> rw[UNION_ASSOC] >> rw[UNION_COMM] >> rw[UNION_ASSOC] >>
    rw[UNION_COMM] >> metis_tac[UNION_ASSOC, UNION_COMM, UNION_IDEMPOT]
);

val num_set_tree_union_sym = Q.store_thm("num_set_tree_union_sym",
    `∀ (t1 : num_set num_map) t2 . num_set_tree_union t1 t2 = num_set_tree_union t2 t1`,
    Induct >> rw[num_set_tree_union_def] >> Cases_on `t2` >> fs[num_set_tree_union_def] >>
    fs[union_num_set_sym]
);

val lookup_domain_num_set_tree_union = Q.store_thm("lookup_domain_num_set_tree_union",
    `∀ n (t1:num_set num_map) t2 x . lookup n t1 = SOME x
    ⇒ ∃ y . lookup n (num_set_tree_union t1 t2) = SOME y ∧ domain x ⊆ domain y`,
    Induct_on `t1` >> rw[]
    >- fs[lookup_def]
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >> fs[lookup_def, domain_union])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >> fs[lookup_def, domain_union] >>
        Cases_on `EVEN n` >> fs[])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >> fs[lookup_def, domain_union] >>
        Cases_on `n = 0` >> fs[domain_union] >> Cases_on `EVEN n` >> fs[])
);

val lookup_NONE_num_set_tree_union = Q.store_thm ("lookup_NONE_num_set_tree_union",
    `∀ n (t1:num_set num_map) t2 . lookup n t1 = NONE
    ⇒ lookup n (num_set_tree_union t1 t2) = lookup n t2`,
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >> Cases_on `n = 0` >> fs[] >>
    Cases_on `EVEN n` >> fs[]
);

val lookup_SOME_SOME_num_set_tree_union = Q.store_thm ("lookup_SOME_SOME_num_set_tree_union",
    `∀ n (t1:num_set num_map) x1 t2 x2 . lookup n t1 = SOME x1 ∧ lookup n t2 = SOME x2
    ⇒ lookup n (num_set_tree_union t1 t2) = SOME (union x1 x2)`,
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >>
    Cases_on `EVEN n` >> fs[] >>
    Cases_on `n = 0` >> fs[]
);

val lookup_num_set_tree_union = Q.store_thm("lookup_num_set_tree_union",
    `∀ (t1 : num_set num_map) t2 n .
        lookup n (num_set_tree_union t1 t2) = case (lookup n t1) of
            | NONE => lookup n t2
            | SOME s1 => case (lookup n t2) of
                | NONE => SOME s1
                | SOME s2 => SOME (union s1 s2)`,
    rw[] >> Cases_on `lookup n t1` >> fs[]
    >-  fs[lookup_NONE_num_set_tree_union]
    >- (Cases_on `lookup n t2` >> fs[]
        >- (fs[lookup_NONE_num_set_tree_union, num_set_tree_union_sym] >>
            imp_res_tac lookup_NONE_num_set_tree_union >>
            pop_assum (qspec_then `t1` mp_tac) >> rw[] >>
            fs[num_set_tree_union_sym])
        >-  fs[lookup_SOME_SOME_num_set_tree_union])
);

(**************************************** CODEANALYSIS_UNION ****************************************)

val codeAnalysis_union_def = Define `
    codeAnalysis_union (r1, t1) (r2, t2) = ((union r1 r2), (num_set_tree_union t1 t2))
`

(******** THEOREMS ********)

val wf_codeAnalysis_union = Q.store_thm("wf_codeAnalysis_union",
    `∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3`,
    rw[codeAnalysis_union_def] >> rw[wf_union]
);

val wf_codeAnalysis_union_strong = Q.store_thm("wf_codeAnalysis_union_strong",
    `∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3. wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2
        ∧ codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3`,
    rw[codeAnalysis_union_def] >> rw[wf_union] >> imp_res_tac wf_num_set_tree_union >> fs[]
);

val domain_codeAnalysis_union = Q.store_thm("domain_codeAnalysis_union",
    `∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 . domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3`,
    rw[codeAnalysis_union_def] >> rw[domain_union] >> rw[domain_num_set_tree_union] >>
    fs[SUBSET_DEF]
);

(**************************************** SUPERDOMAIN ****************************************)

val superdomain_def = Define `
    superdomain LN = LN ∧
    superdomain (LS (t:num_set)) = t ∧
    superdomain (BN t1 t2) = union (superdomain t1) (superdomain t2) ∧
    superdomain (BS t1 a t2) = union (superdomain t1) (union a (superdomain t2))
`

(* TODO - USE THIS FOLD DEFINITION OF SUPERDOMAIN

val sd_def = Define `
    sd (t:num_set num_map) = (foldi (λ k v a . union v a) 0 LN) t
`

val subspt_sd = Q.store_thm("subspt_sd",
    `∀ t1 a t2 . subspt (sd t1) (sd (BS t1 a t2)) ∧
                 subspt (sd t2) (sd (BS t1 a t2)) ∧
                 subspt a (sd (BS t1 a t2)) ∧
                 subspt (sd t1) (sd (BN t1 t2)) ∧
                 subspt (sd t2) (sd (BN t1 t2))`,
    cheat
);

*)

(******** THEOREMS ********)

val subspt_superdomain = Q.store_thm("subspt_superdomain",
    `∀ t1 a t2 . subspt (superdomain t1) (superdomain (BS t1 a t2)) ∧
                 subspt (superdomain t2) (superdomain (BS t1 a t2)) ∧
                 subspt a (superdomain (BS t1 a t2)) ∧
                 subspt (superdomain t1) (superdomain (BN t1 t2)) ∧
                 subspt (superdomain t2) (superdomain (BN t1 t2))`,
    rw[subspt_domain, superdomain_def, domain_union, SUBSET_DEF]
);

val superdomain_thm = Q.store_thm("superdomain_thm",
    `∀ x y (tree:num_set num_map) . lookup x tree = SOME y ⇒ domain y ⊆ domain (superdomain tree)`,
    Induct_on `tree` >- rw[lookup_def]
    >- rw[lookup_def, superdomain_def, foldi_def, domain_map]
    >> rw[] >> fs[lookup_def] >> Cases_on `EVEN x` >> res_tac >>
       qspecl_then [`tree`, `a`, `tree'`] mp_tac subspt_superdomain >>
       Cases_on `x = 0` >> fs[subspt_domain] >> metis_tac[SUBSET_TRANS]
);

val superdomain_inverse_thm = Q.store_thm("superdomain_inverse_thm",
    `∀ n tree . n ∈ domain (superdomain tree)
    ⇒ ∃ k aSet . lookup k tree = SOME aSet ∧ n ∈ domain aSet`,
    Induct_on `tree` >> rw[superdomain_def] >> fs[lookup_def, domain_union] >> res_tac
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `0` >> fs[])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
);

val superdomain_not_in_thm = Q.store_thm("superdomain_not_in_thm",
    `∀ n tree . n ∉ domain (superdomain tree) ⇒ ∀ k aSet . lookup k tree = SOME aSet ⇒ n ∉ domain aSet`,
    Induct_on `tree` >> rw[superdomain_def] >> fs[lookup_def, domain_union] >> res_tac >>
    Cases_on `k = 0` >> Cases_on `EVEN k` >> fs[] >> metis_tac[]
);

(*********************************** WF_SET_TREE/MAKE WF_SET_TREE ***********************************)

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧
        wf tree
`

val mk_wf_set_tree_def = Define `
    mk_wf_set_tree t =
        let t' = union t (map (K LN) (superdomain t)) in mk_wf (map (mk_wf) t')
`

(******** THEOREMS ********)

val mk_wf_set_tree_domain = Q.store_thm("mk_wf_set_tree_domain",
    `∀ tree . domain tree ⊆ domain (mk_wf_set_tree tree)`,
    Induct >> rw[mk_wf_set_tree_def, domain_map, domain_mk_wf, domain_union, SUBSET_DEF]
);

val mk_wf_set_tree_thm = Q.store_thm("mk_wf_set_tree_thm",
    `∀ x tree . x = mk_wf_set_tree tree ⇒ wf_set_tree x`,
    rw[mk_wf_set_tree_def, wf_set_tree_def] >> fs[lookup_map] >> rw[domain_map, domain_union] >>
    fs[lookup_union] >> Cases_on `lookup x' tree` >> fs[] >- fs[lookup_map] >> rw[] >>
    qspecl_then [`x'`, `x`, `tree`] mp_tac superdomain_thm >> rw[SUBSET_DEF]
);

val lookup_mk_wf_set_tree = Q.store_thm("lookup_mk_wf_set_tree",
    `∀ n tree x . lookup n tree = SOME x ⇒ ∃ y . lookup n (mk_wf_set_tree tree) = SOME y ∧ domain x = domain y`,
    rw[mk_wf_set_tree_def] >> rw[lookup_map] >> rw[lookup_union]
);

val lookup_domain_mk_wf_set_tree = Q.store_thm("lookup_domain_mk_wf_set_tree",
    `∀ n t x y . lookup n (mk_wf_set_tree t) = SOME x ⇒
        lookup n t = SOME y ⇒ domain y = domain x`,
    rw[mk_wf_set_tree_def] >> fs[lookup_map, lookup_union] >>
    metis_tac[domain_mk_wf]
);


(**************************************** GETONE ****************************************)

val getOne_def = Define `
    (* NB: no LN case, must ensure that "getOne LN" never occurs *)
    (getOne (BN LN t2) = 2n * (getOne t2) + 1n) ∧
    (getOne (BN t1 _ ) = 2n * (getOne t1) + 2n) ∧
    (* BN LN LN case should not occur under WF *)
    (getOne _ = 0n)
`;

val getOne_ind = theorem "getOne_ind";

val getOne_domain = Q.store_thm("getOne_domain",
    `∀ t . (wf t) ∧ (t ≠ LN) ⇒ (getOne t ∈ domain t)`,
    recInduct getOne_ind >> rw[getOne_def] >> fs[wf_def]
);

(**************************************** CLOSE_SPT/CLOSURE_SPT ****************************************)

(******** CLOSE_SPT ********)

val close_spt_def = tDefine "close_spt" `
    (close_spt (reachable :num_set) (seen :num_set) tree =
    let toLook = difference seen reachable in
    if toLook = LN then reachable else
    let index = (getOne toLook) in
    case (lookup index tree) of
        | NONE => reachable
        | SOME new =>
        close_spt (insert index () reachable) (union new seen) (delete index tree)
    )`
    (WF_REL_TAC `measure (λ (reachable, seen, tree) . size tree)`
    \\ rw[size_delete, lookup_zero]
    \\ imp_res_tac lookup_zero
    \\ fs[]);

val close_spt_ind = theorem "close_spt_ind";

val wf_close_spt = Q.store_thm("wf_close_spt",
    `∀ reachable seen tree. (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧ (∀ n x . (lookup n tree = SOME x) ⇒ wf x)
    ⇒ wf (close_spt reachable seen tree)`,
    recInduct close_spt_ind >> rw[] >> once_rewrite_tac [close_spt_def] >> rw[] >>
    CASE_TAC >- rw[]
    >> `∀n x. lookup n (delete (getOne (difference seen reachable)) tree) = SOME x ⇒ wf x` by (
            rw[lookup_delete] >> metis_tac[] ) >>
        metis_tac [wf_insert, wf_union, wf_delete, lookup_delete]
);

(******** CLOSURE_SPT ********)

val closure_spt_def = Define `closure_spt start tree = close_spt LN start tree`;

(**************************************** ADJACENCY/REACHABILITY ****************************************)

(******** ADJACENCY ********)

val isAdjacent_def = Define `
    isAdjacent tree x y =
    ∃ aSetx aSety. ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () )
        ∧ ( lookup y tree = SOME aSety )
`;

val adjacent_domain = Q.store_thm("adjacent_domain",
    `∀ tree x y . isAdjacent tree x y ⇒ x ∈ domain tree ∧ y ∈ domain tree`,
    rw[isAdjacent_def] >> rw[domain_lookup]
);

(******** REACHABILITY ********)

val isReachable_def = Define `
    isReachable tree = RTC (isAdjacent tree)
`;

val reachable_domain = Q.store_thm("reachable_domain",
    `∀ tree x y . isReachable tree x y ⇒ (x = y ∨ (x ∈ domain tree ∧ y ∈ domain tree))`,
    simp[isReachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> metis_tac[adjacent_domain]
);

val rtc_isAdjacent = Q.store_thm("rtc_isAdjacent",
    `s ⊆ t ∧ (∀ k . k ∈ t ⇒ ∀ n . (isAdjacent fullTree k n ⇒ n ∈ t)) ⇒
    ∀ x y . RTC(isAdjacent fullTree) x y ⇒ x ∈ s ⇒ y ∈ t`,
    strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    fs[SUBSET_DEF] >>
    metis_tac []
);

(******************************************************** OTHER LEMMAS *********************************************************)

(******** SUPERDOMAIN/NUM_SET_TREE_UNION ********)

val domain_superdomain_num_set_tree_union = Q.store_thm("domain_superdomain_num_set_tree_union",
    `∀ t1 t2 . domain (superdomain t1) ⊆ domain (superdomain (num_set_tree_union t1 t2))`,
    fs[SUBSET_DEF] >> rw[] >> imp_res_tac superdomain_inverse_thm >>
    imp_res_tac lookup_domain_num_set_tree_union >> pop_assum (qspec_then `t2` mp_tac) >>
    rw[] >> imp_res_tac superdomain_thm >> metis_tac[SUBSET_DEF]
);

val domain_superdomain_num_set_tree_union_STRONG = Q.store_thm("domain_superdomain_num_set_tree_union_STRONG",
    `∀ t1 t2 . domain (superdomain t1) ∪ domain (superdomain t2) = domain (superdomain (num_set_tree_union t1 t2))`,
    fs[EXTENSION] >> rw[] >> EQ_TAC >> rw[]
    >- metis_tac[domain_superdomain_num_set_tree_union, SUBSET_DEF, num_set_tree_union_sym]
    >- metis_tac[domain_superdomain_num_set_tree_union, SUBSET_DEF, num_set_tree_union_sym]
    >- (imp_res_tac superdomain_inverse_thm >> fs[lookup_num_set_tree_union] >> EVERY_CASE_TAC >> fs[]
        >- (disj1_tac >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF])
        >- (disj2_tac >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF])
        >- (rveq >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF, domain_union]))
);

(******** MK_WF_SET_TREE/NUM_SET_TREE_UNION ********)

val mk_wf_set_tree_num_set_tree_union = Q.store_thm("mk_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 . mk_wf_set_tree (num_set_tree_union t1 t2) =
        num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2)`,
    rw[] >>
    `wf (mk_wf_set_tree (num_set_tree_union t1 t2))` by metis_tac[mk_wf_set_tree_thm, wf_set_tree_def] >>
    `wf (num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2))` by
        metis_tac[mk_wf_set_tree_thm, wf_set_tree_def, wf_num_set_tree_union] >>
    rw[spt_eq_thm] >> simp[mk_wf_set_tree_def] >> fs[lookup_map] >> fs[lookup_union] >> fs[lookup_map] >>
    fs[lookup_num_set_tree_union] >> fs[lookup_map] >> fs[lookup_union] >> fs[lookup_map] >>
    fs[OPTION_MAP_COMPOSE, mk_wf_def] >> Cases_on `lookup n t1` >> Cases_on `lookup n t2` >> fs[] >>
    EVERY_CASE_TAC >> fs[mk_wf_def, union_def] >> fs[lookup_NONE_domain, GSYM domain_lookup] >>
    qspecl_then [`t1`, `t2`] mp_tac domain_superdomain_num_set_tree_union_STRONG >> strip_tac >>
    fs[EXTENSION]
    >-  metis_tac[]
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))` >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))` >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))` >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >-  metis_tac[mk_wf_union]
);

(******** ADJACENCY/REACHABILITY ********)

val isAdjacent_num_set_tree_union = Q.store_thm("isAdjacent_num_set_tree_union",
    `∀ t1 t2 n m .
        isAdjacent t1 n m ⇒ isAdjacent (num_set_tree_union t1 t2) n m`,
    rw[isAdjacent_def] >> imp_res_tac lookup_domain_num_set_tree_union >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    fs[SUBSET_DEF, domain_lookup]
);

val isAdjacent_wf_set_tree_num_set_tree_union = Q.store_thm ("isAdjacent_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 n m .
        isAdjacent (mk_wf_set_tree t1) n m
        ⇒ isAdjacent (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`,
    rw[isAdjacent_def] >> fs[mk_wf_set_tree_def] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >> fs[PULL_EXISTS] >> fs[lookup_num_set_tree_union] >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[] >>
    rveq >> fs[lookup_def, mk_wf_def, lookup_union] >> EVERY_CASE_TAC >> fs[] >>
    qspecl_then [`t1`, `t2`] mp_tac domain_superdomain_num_set_tree_union >>
    rw[SUBSET_DEF, domain_lookup]
);

val isReachable_wf_set_tree_num_set_tree_union = Q.store_thm ("isReachable_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 n m .
        isReachable (mk_wf_set_tree t1) n m ⇒ isReachable (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`,
    simp[isReachable_def] >> strip_tac >> strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
    simp[Once RTC_CASES2] >> disj2_tac >> qexists_tac `m` >> fs[] >>
    imp_res_tac isAdjacent_wf_set_tree_num_set_tree_union >> fs[]
);





(******************************************************** MAIN PROOFS **********************************************************)

(**************************************** CLOSE_SPT ****************************************)

val close_spt_thm = Q.store_thm("close_spt_thm",
    `∀ reachable seen tree fullTree x (roots:num set) .
        (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧ (wf fullTree) ∧
        (∀ n x . (lookup n fullTree = SOME x) ⇒ wf x) ∧
        (close_spt reachable seen tree = x) ∧
        (subspt reachable seen) ∧
        (subspt tree fullTree) ∧
        (∀ n . n ∉ domain (reachable) ⇒ (lookup n tree = lookup n fullTree)) ∧
        (∀ k . k ∈ domain (seen) ⇒ (∃ n . (n ∈ roots) ∧ (isReachable fullTree n k))) ∧
        (∀ k . k ∈ domain (reachable) ⇒ (∀ a . (isAdjacent fullTree k a) ⇒ a ∈ domain (seen))) ∧
        (roots ⊆ domain (seen)) ∧
        (roots ⊆ domain (fullTree)) ∧
        (wf_set_tree fullTree)
      ⇒ (domain x = {a | ∃ n . (isReachable fullTree n a) ∧ (n ∈ roots)})`,
    recInduct close_spt_ind
    >> rw[] >> once_rewrite_tac [close_spt_def] >> simp[]
    >> IF_CASES_TAC
    >- (
        drule empty_sub >> fs[] >> rw[] >> fs[] >> fs[EXTENSION] >> rw[] >> EQ_TAC >> rw[]
        >- metis_tac[]
        >> fs[SUBSET_DEF] >> fs[isReachable_def] >> `roots ⊆ domain (reachable)` by fs[SUBSET_DEF] >>
            drule rtc_isAdjacent >> rw[] >> metis_tac[]
       )
    >> CASE_TAC >> fs[] >> fs[subspt_domain] >> rw[] >> fs[SUBSET_DEF] >> rw[EXTENSION]
    >- (
        fs[lookup_NONE_domain] >>
        `getOne (difference seen reachable) ∈ domain (difference seen reachable)`
            by rw[wf_difference, getOne_domain] >>
        fs[domain_difference] >> res_tac >> imp_res_tac reachable_domain >>
        `n ∈ domain fullTree` by metis_tac[] >> fs[domain_lookup] >> rfs[]
       )
    >> rfs[EXTENSION] >> pop_assum match_mp_tac >>
    `∀ n x. lookup n tree = SOME x ⇒ wf x` by (fs[subspt_def, domain_lookup] >> metis_tac[]) >>
    `getOne (difference seen reachable) ∈ domain (union x seen)` by (
        rw[domain_union, getOne_domain] >>
        `domain (difference seen reachable) ⊆ domain seen` by rw[domain_difference] >>
        `getOne(difference seen reachable)∈ domain(difference seen reachable)`
            by rw[getOne_domain, wf_difference] >>
         fs[SUBSET_DEF] >> metis_tac [] ) >>
    `∀k. k = getOne (difference seen reachable) ∨ k ∈ domain reachable ⇒
        ∀a. isAdjacent fullTree k a ⇒ a ∈ domain (union x seen)` by (
        pop_assum kall_tac >> strip_tac >> Cases_on `k ∈ domain reachable`
        >> simp[domain_union] >> metis_tac [domain_union, isAdjacent_def, domain_lookup, SOME_11]) >>
    `∀k. k ∈ domain (union x seen) ⇒ ∃n. n ∈ roots ∧ isReachable fullTree n k` by (
        reverse(rw[domain_union] >> Cases_on `k ∈ domain seen` >> rw[])
        >- metis_tac []
        >> `getOne (difference seen reachable) ∈ domain seen ∧
            getOne (difference seen reachable) ∉ domain reachable`
            by ( `getOne(difference seen reachable) ∈ domain (difference seen reachable)`
                    by rw[wf_difference, getOne_domain] >>
                 fs[domain_difference]) >>
            res_tac >> qexists_tac `n` >> rw[isReachable_def, Once RTC_CASES2] >> disj2_tac >>
            qexists_tac `getOne (difference seen reachable)` >> rw[isAdjacent_def]
            >- metis_tac[isReachable_def] >> qexists_tac `x` >>
            res_tac >> rw[] >> fs[domain_lookup] >>
            qpat_x_assum `wf_set_tree _` assume_tac >> fs[wf_set_tree_def] >>
            qpat_x_assum `_ = SOME x` assume_tac >> qpat_x_assum `∀ x . _` kall_tac >>
            first_x_assum drule >> rw[SUBSET_DEF, domain_lookup]
      )
      >> asm_rewrite_tac[] >>
      simp[wf_insert, wf_difference, wf_union, wf_delete, lookup_delete, wf_close_spt,
        domain_union, subspt_delete, lookup_delete] >>
        fs[domain_union] >> metis_tac[wf_union]
);

(**************************************** CLOSURE_SPT ****************************************)

val closure_spt_lemma =
    close_spt_thm |> Q.SPECL [`LN`, `start:num_set`, `tree`, `tree`]
        |> SIMP_RULE std_ss [
            GSYM closure_spt_def, wf_def, wf_insert, subspt_def, domain_def, NOT_IN_EMPTY,
            domain_insert, SUBSET_DEF
           ]
        |> Q.SPECL[`domain (start:num_set)`]
        |> SIMP_RULE std_ss [
                ConseqConvTheory.AND_CLAUSES_XX, ConseqConvTheory.IMP_CLAUSES_XX,
                IN_SING, Once isReachable_def, RTC_REFL, AND_CLAUSES
           ] |> GEN_ALL
;

val closure_spt_thm = Q.store_thm("closure_spt_thm",
    `∀ tree start . wf start ∧ (wf_set_tree tree) ∧ (domain start ⊆ domain tree)
    ⇒ domain (closure_spt start tree) =
        {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`,
    rw[] >> assume_tac closure_spt_lemma >> rw[] >> fs[wf_set_tree_def] >>
    first_x_assum match_mp_tac >> reverse(rw[]) >> res_tac >> fs[SUBSET_DEF] >>
    qexists_tac `k` >> fs[]
);




val _ = export_theory();

open ml_monadBaseLib ml_monadBaseTheory
open ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib

val _ = new_theory "arrayStateProg"
val _ = ParseExtras.temp_loose_equality();
(* val _ = ParseExtras.temp_tight_equality(); *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

(* Register the types used for the translation *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``
val _ = register_type ``:'a option``
val _ = register_type ``:('a, 'b) exc``

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <| the_num : num ;
	          the_num_array : num list ;
                  the_int_array : int list |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | ReadError of unit | WriteError of unit`;

val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

val _ = register_type ``:state_refs``;
val STATE_REFS_TYPE_def = theorem"STATE_REFS_TYPE_def";

(* Monadic functions to handle the exceptions *)
val failwith_def = Define `
  ((failwith msg) : (state_refs, 'a, state_exn) M) = \state. (Failure (Fail msg), state)`;

val raise_read_error_def = Define `
((raise_read_error ()) :(state_refs, unit, state_exn) M) = \state. (Failure (ReadError ()), state)`;

val raise_write_error_def = Define `
((raise_write_error ()) :(state_refs, unit, state_exn) M) = \state. (Failure (WriteError ()), state)`;

val handle_fail_def = Define `
  handle_fail x f = \state.
    dtcase ((x : (state_refs, 'a, state_exn) M) state) of
    | (Failure (Fail t), state) => f t state
    | other => other`;

val handle_read_error_def = Define `
  handle_read_error x f = \state.
    dtcase ((x : (state_refs, 'a, state_exn) M) state) of
    | (Failure (ReadError t), state) => f t state
    | other => other`;

val handle_write_error_def = Define `
  handle_write_error x f = \state.
    dtcase ((x : (state_refs, 'a, state_exn) M) state) of
    | (Failure (WriteError t), state) => f t state
    | other => other`;

(* Define the functions used to access the elements of the state_refs data_type *)
val access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_name, get_the_num_def, set_the_num_def),
     (the_num_array_name, get_the_num_array_def, set_the_num_array_def),
     (the_int_array_name, get_the_int_array_def, set_the_int_array_def)] = access_funs;

val sub_exn = ``ReadError ()``;
val update_exn = ``WriteError ()``;
val array_access_funs = (List.tl access_funs);
val array_manip_funs = define_Marray_manip_funs array_access_funs sub_exn update_exn;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def)];

val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val arrays_init_values = [init_num_array_def, init_int_array_def];
val arrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip array_manip_funs arrays_init_values);

val infer_init_state = ``<|the_num := 0; the_num_array := []; the_int_array := []|>``;

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val EXN_RI = ``STATE_EXN_TYPE``;
val exc_ri_def = STATE_EXN_TYPE_def;

val refs_manip_list = List.map (fn (x, _, y, z) => (x, y, z)) refs_init_list;
val arrays_manip_list = List.map (fn (x1, _, x2, x3, x4, x5, x6, x7) => (x1, x2, x3, x4, x5, x6, x7)) arrays_init_list;

val translation_parameters = translate_dynamic_init_fixed_store refs_manip_list arrays_manip_list store_hprop_name state_type exc_ri_def;

(* Initialize the store *)
(* val (translation_parameters, store_trans_result) = translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type STATE_EXN_TYPE_def; *)

(* Initialize the translation *)
(* val store_pred_exists = #store_pred_exists_thm store_trans_result; *)
val store_pred_exists = NONE : thm option;
val _ = init_translation translation_parameters store_pred_exists exc_ri_def [];

(* Prove the theorems necessary to handle the exceptions *)
val raise_functions = [failwith_def, raise_read_error_def, raise_write_error_def];
val handle_functions = [handle_fail_def, handle_read_error_def, handle_write_error_def];
val exn_thms = add_raise_handle_functions raise_functions handle_functions STATE_EXN_TYPE_def

(* Monadic translations *)
val test2_def = Define `test2 n = the_num_array_sub n`;
val def = test2_def |> m_translate;

val test3_def = Define `test3 n x = update_the_num_array n x`;
val def = test2_def |> m_translate;

val test4_def = Define `test4 n x = alloc_the_num_array n x`;
val def = test3_def |> m_translate;

val test5_def = Define `
test5 n z =
    do
	alloc_the_num_array n z;
        return ()
    od`;
val def = test5_def |> m_translate;
val test5_trans_th = m_translate test5_def;

val test6_def = Define `
test6 n z = test5 n z`;
val def = test6_def;
val test6_trans_th = m_translate test6_def;

val test7_def = Define `
(test7 [] = return 0) /\ ((test7 (x::l)) = (do x <- test7 l; return (x+1) od))`;
val def = test7_def;
val test7_v_th = m_translate test7_def;

val test8_def = Define `
test8 l = test7 l`;
val test8_v_th = m_translate test8_def;

val test9_def = Define `
test9 n m z =
   do
       test5 n z;
       x <- test2 m;
       return x
   od`;
val test9_v_th = m_translate test9_def;

(* New definitions for ml_monadBaseTheory *)
val _ = ParseExtras.temp_tight_equality();

val handle_one_def = Define `
handle_one vname cname exp1 exp2 =
(Handle exp1 [(Pcon (SOME (Short cname)) [Pvar vname], Let (SOME vname) (Con (SOME (Short cname)) [Var(Short vname)]) exp2)])`;

val handle_mult_def = Define `
handle_mult varname (cname::cons_names) exp1 exp2 =
handle_one varname cname (handle_mult varname cons_names exp1 exp2) exp2 /\
handle_mult varname [] exp1 exp2 = exp1`;

val Mhandle_all_def = Define `
Mhandle_all (x : ('a, 'b, 'c) M) f = \state.
case x state of
    (Success y, s) => (Success y, s)
  | (Failure e, s) => (Success (f e), s)`;

val insert_monad_def = Define `
insert_monad (x : ('a, 'b, 'c) M) state = FST(x state)`;

val Eval_Monad_def = Define `
Eval_Monad env exp P refs H =
!(s : unit semanticPrimitives$state) p. REFS_PRED H refs p s ==>
!junk. ?s2 res refs2.
evaluate F env (s with refs := s.refs ++ junk) exp (s2, Rval res) /\
P res /\ REFS_PRED_FRAME H p (refs, s) (refs2, s2)`;

val handle_mult_append = Q.prove(
`!cons_names1 cons_names2 vname exp1 exp2.
handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2 =
handle_mult vname cons_names1 (handle_mult vname cons_names2 exp1 exp2) exp2`,
Induct >-(rw[handle_mult_def])
\\ rw[handle_mult_def]);

val evaluate_handle_mult_Rval = Q.prove(`!cons_names vname exp1 exp2 res s s2 env.
 evaluate F env s exp1 (s2, Rval res) ==>
 evaluate F env s (handle_mult vname cons_names exp1 exp2) (s2, Rval res)`,
Induct
>-(rw[handle_mult_def, handle_one_def])
\\ rw[handle_mult_def, handle_one_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_mult_Rabort = Q.prove(`!cons_names vname exp1 exp2 res s s2 env.
 evaluate F env s exp1 (s2, Rerr (Rabort res)) ==>
 evaluate F env s (handle_mult vname cons_names exp1 exp2) (s2, Rerr (Rabort res))`,
Induct
>-(rw[handle_mult_def, handle_one_def])
\\ rw[handle_mult_def, handle_one_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_EXN_THROUGH = Q.prove(`
!cons_names exp1 exp2 vname s s2 ev env.
evaluate F env s exp1 (s2, Rerr (Rraise ev)) ==>
EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names ==>
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F env s exp1`,
Induct >-(rw[handle_mult_def])
\\ rw[]
\\ rw[handle_mult_def]
\\ irule EQ_EXT
\\ rw[]
\\ last_assum (fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
\\ Cases_on `x`
\\ fs[]
\\ rw[handle_one_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[ALL_DISTINCT, pat_bindings_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_compos_suffices = Q.prove(`evaluate F env s exp3 = evaluate F env s exp4 ==>
(evaluate F env s
  (Handle exp3
     [(Pcon (SOME (Short h)) [Pvar vname],
       Let (SOME vname) (Con (SOME (Short h)) [Var (Short vname)])
         exp2)]) =
evaluate F env s
  (Handle exp4
     [(Pcon (SOME (Short h)) [Pvar vname],
       Let (SOME vname) (Con (SOME (Short h)) [Var (Short vname)])
         exp2)]))`,
rw[]
\\ irule EQ_EXT
\\ rw[Once evaluate_cases]
\\ rw[Once EQ_SYM_EQ]
\\ rw[Once evaluate_cases]);

val evaluate_handle_EXN_PARTIAL_THROUGH = Q.prove(`!cons_names1 cons_names2 exp1 exp2 vname s s2 ev env.
evaluate F env s exp1 (s2, Rerr (Rraise ev)) ==>
EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names2 ==>
evaluate F env s (handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2) =
evaluate F env s (handle_mult vname cons_names1 exp1 exp2)`,
Induct
>-(
    rw[handle_mult_def]
    \\ IMP_RES_TAC evaluate_handle_EXN_THROUGH
    \\ fs[])
\\ rw[handle_mult_def, handle_one_def]
\\ irule evaluate_handle_compos_suffices
\\ last_assum IMP_RES_TAC
\\ fs[]);

val EVERY_CONJ_1 = GSYM EVERY_CONJ |> SPEC_ALL |> EQ_IMP_RULE |> fst |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO];

val prove_evaluate_handle_mult_CASE =
rw[]
\\ last_x_assum IMP_RES_TAC
\\ qexists_tac `cname`
\\ qexists_tac `ev'`
\\ simp[]
\\ sg `?cons_names1 cons_names2. cons_names = cons_names1 ++ [cname] ++ cons_names2`
>-(
    fs[MEM_EL]
    \\ sg `?cons_names1 cons_names'. cons_names = cons_names1 ++ cons_names' /\ LENGTH cons_names1 = n`
    >-(
	qexists_tac `TAKE n cons_names`
        \\ qexists_tac `DROP n cons_names`
        \\ simp[TAKE_DROP, LENGTH_TAKE])
    \\ qexists_tac `cons_names1`
    \\ fs[]
    \\ qexists_tac `TL cons_names'`
    \\ Cases_on `cons_names'` >> fs[]
    \\ rw[]
    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    \\ `~NULL ([h] ++ t)` by fs[]
    \\ IMP_RES_TAC EL_LENGTH_APPEND
    \\ fs[])
\\ sg `EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names2`
>-(
    fs[ALL_DISTINCT_APPEND]
    \\ fs[EVERY_MEM]
    \\ rw[]
    \\ fs[EL_APPEND1, EL_APPEND2]
    \\ rw[Once pmatch_def]
    \\ fs[lookup_cons_def]
    \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
    \\ `cname' <> cname` by (first_assum(qspec_then `cname` ASSUME_TAC) \\ fs[] \\ metis_tac[])    \\ fs[])
\\ fs[EL_APPEND1, EL_APPEND2]
\\ rw[]
\\ IMP_RES_TAC evaluate_handle_EXN_PARTIAL_THROUGH
\\ fs[]
\\ rw[handle_mult_append, handle_mult_def]
\\ fs[Eval_def]
\\ qpat_x_assum `!e' ev1 cname'. P` IMP_RES_TAC
\\ first_x_assum(qspec_then `s2.refs ++ []` STRIP_ASSUME_TAC)
\\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
\\ fs[with_same_refs]
\\ sg `evaluate F env s (handle_mult vname cons_names1 (handle_one vname cname exp1 exp2) exp2) =
    evaluate F env s (handle_one vname cname exp1 exp2)`
>-(
    sg `?s' res. evaluate F env s (handle_one vname cname exp1 exp2) (s', Rval res)`
    >-(
	rw[handle_one_def]
	\\ rw[Once evaluate_cases]
	\\ last_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
	\\ rw[Once evaluate_cases]
	\\ fs[pat_bindings_def]
	\\ fs[pmatch_def]
	\\ fs[EVERY_MEM, lookup_cons_def]
	\\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
	\\ fs[write_def]
	\\ fs[with_same_refs]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
	\\ fs[namespaceTheory.id_to_n_def]
	\\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x]))
    \\ first_assum(fn x => MATCH_MP evaluate_handle_mult_Rval x |> ASSUME_TAC)
    \\ first_x_assum(qspecl_then [`cons_names1`, `vname`, `exp2`] ASSUME_TAC)
    \\ irule EQ_EXT
    \\ rw[]
    \\ Cases_on `x`
    \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
    \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
    \\ fs[])
\\ rw[]
\\ rw[handle_one_def]
\\ irule EQ_EXT
\\ rw[]
\\ Cases_on `x`
\\ rw[Once evaluate_cases]
\\ qpat_assum `evaluate F env s exp1 R` (fn x => simp[MATCH_MP evaluate_unique_result x])
\\ rw[Once evaluate_cases]
\\ fs[pat_bindings_def]
\\ fs[pmatch_def]
\\ fs[EVERY_MEM, lookup_cons_def]
\\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ fs[write_def]
\\ fs[with_same_refs]
\\ pop_assum(fn x => ALL_TAC)
\\ first_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def];

val evaluate_handle_mult_CASE_MODULE = Q.prove(`
!EXN_TYPE cons_names module_name vname exp1 exp2 s s2 e ev env.
(!e ev. EXN_TYPE e ev ==> ?ev' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev']) ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Long module_name (Short cname)))) cons_names ==>
(ALL_DISTINCT cons_names) ==>
(∀e ev ev1 cname.
EXN_TYPE e ev ==>
ev = Conv (SOME (cname,TypeExn (Long module_name (Short cname)))) [ev1] ==>
Eval (write vname ev (write vname ev1 env)) exp2 (\v. T)) ==>
evaluate F env s exp1 (s2, Rerr (Rraise ev))
/\ EXN_TYPE e ev ==>
?cname ev'. ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev'] /\
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F (write vname ev (write vname ev' env)) s2 exp2`,
prove_evaluate_handle_mult_CASE);

val evaluate_handle_mult_CASE_SIMPLE = Q.prove(`
!EXN_TYPE cons_names vname exp1 exp2 s s2 e ev env.
(!e ev. EXN_TYPE e ev ==> ?ev' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Short cname))) [ev']) ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Short cname))) cons_names ==>
(ALL_DISTINCT cons_names) ==>
(∀e ev ev1 cname.
EXN_TYPE e ev ==>
ev = Conv (SOME (cname,TypeExn (Short cname))) [ev1] ==>
Eval (write vname ev (write vname ev1 env)) exp2 (\v. T)) ==>
evaluate F env s exp1 (s2, Rerr (Rraise ev))
/\ EXN_TYPE e ev ==>
?cname ev'. ev = Conv (SOME (cname, TypeExn (Short cname))) [ev'] /\
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F (write vname ev (write vname ev' env)) s2 exp2`,
prove_evaluate_handle_mult_CASE);

val evaluate_Success_CONS = Q.prove(
`lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
evaluate F env s e (s', Rval v) ==>
evaluate F env s (Con (SOME (Short "Success")) [e]) (s', Rval (Conv (SOME ("Success",TypeId (Short "exc"))) [v]))`,
rw[]
\\ rw[Once evaluate_cases]
\\ fs[lookup_cons_def]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ rw[Once evaluate_cases]
\\ qexists_tac `s'`
\\ rw[Once evaluate_cases]);

val evaluate_Success_CONS_err = Q.prove(
`lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
evaluate F env s e (s', Rerr v) ==>
evaluate F env s (Con (SOME (Short "Success")) [e]) (s', Rerr v)`,
rw[]
\\ rw[Once evaluate_cases]
\\ fs[lookup_cons_def]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ rw[Once evaluate_cases]
\\ qexists_tac `s'`
\\ rw[Once evaluate_cases]);

fun evaluate_unique_result_tac (g as (asl, w)) = let
    val asl = List.map ASSUME asl
    val uniques = mapfilter (MATCH_MP evaluate_unique_result) asl
in simp uniques g end;

(* For the dynamic store initialisation *)
(* It is not possible to use register_type here... *)
val EXC_TYPE_aux_def = Define `
      (EXC_TYPE_aux a b (Failure x_2) v =
      ?v2_1.
        v = Conv (SOME ("Failure",TypeId (Short "exc"))) [v2_1] ∧
        b x_2 v2_1) /\
     (EXC_TYPE_aux a b (Success x_1) v <=>
     ?v1_1.
       v = Conv (SOME ("Success",TypeId (Short "exc"))) [v1_1] ∧
		a x_1 v1_1)`;

fun prove_EvalM_insert_monad handle_mult_CASE =
rw[EvalM_def, Eval_Monad_def]
\\ qpat_x_assum `!s p refs. P` IMP_RES_TAC
\\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
\\ Cases_on `res`
(* res is an Rval *)
>-(
    IMP_RES_TAC evaluate_Success_CONS
    \\ first_x_assum (fn x => MATCH_MP evaluate_handle_mult_Rval x |> ASSUME_TAC)
    \\ first_x_assum (qspecl_then [`cons_names`, `vname`, `(Con (SOME (Short "Failure")) [Var (Short vname)])`] ASSUME_TAC)
    \\ evaluate_unique_result_tac
    \\ fs[MONAD_def, insert_monad_def, EXC_TYPE_aux_def]
    \\ Cases_on `x init_state'`
    \\ Cases_on `q` \\ fs[]
    \\ fs[EXC_TYPE_aux_def]
    \\ metis_tac[])
\\ reverse(Cases_on `e`)
(* res is an Rerr (Rabort ...) *)
>-(
    irule FALSITY
    \\ fs[MONAD_def]
    \\ Cases_on `x init_state'`
    >> Cases_on `q`
    >> fs[])
(* res is an Rerr (Rraise ...) *)
\\ qpat_x_assum `MONAD A B X S1 S2` (fn x => RW[MONAD_def] x |> ASSUME_TAC)
\\ fs[]
\\ Cases_on `x init_state'` \\ fs[]
\\ Cases_on `q` \\ fs[]
\\ LAST_ASSUM IMP_RES_TAC
\\ IMP_RES_TAC (Thm.INST_TYPE [``:'b`` |-> ``:unit``] handle_mult_CASE)
\\ POP_ASSUM(fn x => ALL_TAC)
\\ first_x_assum(qspecl_then [`vname`, `Con (SOME (Short "Failure")) [Var (Short vname)]`] ASSUME_TAC)
\\ IMP_RES_TAC evaluate_Success_CONS_err
\\ first_assum(fn x => sg `^(fst(dest_imp (concl x)))`)
>-(
    rw[]
    \\ fs[EVERY_MEM]
    \\ first_x_assum(qspec_then `cname` IMP_RES_TAC)
    \\ fs[lookup_cons_def]
    \\ rw[Eval_def]
    \\ rw[Once evaluate_cases]
    \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
    \\ fs[namespaceTheory.id_to_n_def]
    \\ fs[write_def]
    \\ rw[Once evaluate_cases]
    \\ rw[Once evaluate_cases]
    \\ rw[Once evaluate_cases]
    \\ rw[state_component_equality])
\\ qpat_x_assum `P ==> Q` IMP_RES_TAC
\\ ntac 2 (POP_ASSUM (fn x => ALL_TAC))
\\ fs[]
\\ rw[Once evaluate_cases]
\\ fs[lookup_cons_def]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def, write_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[insert_monad_def, EXC_TYPE_aux_def]
\\ metis_tac[];

val EvalM_insert_monad_MODULE = Q.store_thm("EvalM_insert_monad_MODULE",
`!cons_names module_name vname TYPE EXN_TYPE x exp H init_state env.
(!e ev. EXN_TYPE e ev ==> ?ev' e' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev']) ==>
(ALL_DISTINCT cons_names) ==>
vname <> "Success" ==>
vname <> "Failure" ==>
EvalM env exp (MONAD TYPE EXN_TYPE x) H ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Long module_name (Short cname)))) cons_names ==>
lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
lookup_cons "Failure" env = SOME (1,TypeId (Short "exc")) ==>
Eval_Monad env (handle_mult vname cons_names (Con (SOME (Short "Success")) [exp]) (Con (SOME (Short "Failure")) [Var (Short vname)]))
(EXC_TYPE_aux TYPE EXN_TYPE (insert_monad x init_state)) init_state H`,
prove_EvalM_insert_monad evaluate_handle_mult_CASE_MODULE);

val EvalM_insert_monad_SIMPLE = Q.store_thm("EvalM_insert_monad_SIMPLE",
`!cons_names vname TYPE EXN_TYPE x exp H init_state env.
(!e ev. EXN_TYPE e ev ==> ?ev' e' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Short cname))) [ev']) ==>
(ALL_DISTINCT cons_names) ==>
vname <> "Success" ==>
vname <> "Failure" ==>
EvalM env exp (MONAD TYPE EXN_TYPE x) H ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Short cname))) cons_names ==>
lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
lookup_cons "Failure" env = SOME (1,TypeId (Short "exc")) ==>
Eval_Monad env (handle_mult vname cons_names (Con (SOME (Short "Success")) [exp]) (Con (SOME (Short "Failure")) [Var (Short vname)]))
(EXC_TYPE_aux TYPE EXN_TYPE (insert_monad x init_state)) init_state H`,
prove_EvalM_insert_monad evaluate_handle_mult_CASE_SIMPLE);


(* Test *)
set_trace "assumptions" 1

val current_state = get_state(get_ml_prog_state());
val current_env = get_env(get_ml_prog_state());

val spec = test9_v_th
val original_spec = spec;

val spec_info_pat = ``nsLookup (merge_env (LOCAL_ENV : v sem_env) env).v (Short NAME) = SOME EXPR``;


val initial_state = mk_var("s", ``:unit semanticPrimitives$state``);

val (name, def) = List.hd ref_name_def_pairs;

val evaluate_let_opref = Q.store_thm("evaluate_let_opref",
`Eval env exp1 P ==>
?junk v. evaluate F env s (Let (SOME vname) (App Opref [exp1]) exp2) = evaluate F (write vname (Loc (LENGTH (s.refs ++ junk))) env) (s with refs := s.refs ++ junk ++ [Refv v]) exp2 /\ P v`,
rw[Eval_def]
\\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
\\ IMP_RES_TAC evaluate_empty_state_IMP
\\ qexists_tac `refs'`
\\ qexists_tac `res`
\\ simp[]
\\ irule EQ_EXT
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[do_app_def, store_alloc_def]
\\ fs[write_def, namespaceTheory.nsOptBind_def]
\\ rw[Once DISJ_COMM]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[do_app_def, store_alloc_def]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[with_same_ffi]);

val Eval_Monad_Let_Fun = Q.store_thm("Eval_Monad_Let_Fun",
`Eval_Monad (merge_env (write vname (Closure (merge_env env1 env0) xv fexp) env1) env0) exp P refs H ==>
Eval_Monad (merge_env env1 env0) (Let (SOME vname) (Fun xv fexp) exp) P refs H`,
rw[Eval_Monad_def]
\\ last_x_assum IMP_RES_TAC
\\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[namespaceTheory.nsOptBind_def]
\\ fs[write_def, merge_env_def]
\\ metis_tac[]);

val merge_env_bind_empty = Q.store_thm("merge_env_bind_empty",
`merge_env <| v := Bind [] []; c := Bind [] [] |> env  = env`,
rw[merge_env_def]
\\ Cases_on `env`
\\ Cases_on `n`
\\ Cases_on `n0`
\\ rw[namespaceTheory.nsAppend_def, sem_env_component_equality]);

val Eval_Monad_Opref = Q.store_thm("Eval_Monad_Opref",
`Eval (merge_env <|v := Bind binds []; c := Bind [] []|> env0) state_exp (STATE_TYPE state) ==>
Eval (merge_env <| v := Bind binds []; c := Bind [] [] |> env0) get_ref_expr ((STATE_TYPE --> TYPE) (\state. get_val state)) ==>
(!loc. Eval_Monad (merge_env <| v := Bind ((loc_name, loc)::binds) []; c := Bind [] [] |> env0) exp P state (\state. REF_REL TYPE loc (get_val state) * H state)) ==>
Eval_Monad (merge_env <| v := Bind binds []; c := Bind [] [] |> env0)
(Let (SOME loc_name) (App Opref [App Opapp [get_ref_expr; state_exp]]) exp) P state (\state. H state)`,
rw[Eval_Monad_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[Eval_def]
\\ last_x_assum(qspec_then `s.refs ++ junk` STRIP_ASSUME_TAC)
\\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> ASSUME_TAC)
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ last_x_assum(qspec_then `s.refs ++ junk ++ refs'` STRIP_ASSUME_TAC)
\\ FULL_SIMP_TAC pure_ss [GSYM APPEND_ASSOC]
\\ `s.refs ++ (junk ++ (refs' ++ refs'')) = s.refs ++ (junk ++ refs') ++ refs''` by simp[]
\\ pop_assum(fn x => FULL_SIMP_TAC pure_ss [x])
\\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> ASSUME_TAC)
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ fs[Arrow_def]
\\ first_x_assum(qspec_then `state` ASSUME_TAC)
\\ fs[AppReturns_def]
\\ first_x_assum(qspec_then `res` IMP_RES_TAC)
\\ first_x_assum(qspec_then `s.refs ++ junk ++ refs' ++ refs''` STRIP_ASSUME_TAC)
\\ rw[]
\\ FULL_SIMP_TAC pure_ss [GSYM APPEND_ASSOC]
\\ `s.refs ++ (junk ++ (refs' ++ (refs'' ++ refs'''))) = s.refs ++ (junk ++ (refs' ++ refs'')) ++ refs'''` by simp[]
\\ pop_assum(fn x => FULL_SIMP_TAC pure_ss [x])
\\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> ASSUME_TAC)
\\ fs[]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[do_app_def, store_alloc_def]
\\ rw[namespaceTheory.nsOptBind_def]
\\ rw[with_same_ffi]
\\ qpat_abbrev_tac `loc = LENGTH junk + L`
\\ last_x_assum(qspecl_then [`Loc loc`, `s with refs := s.refs ++ junk ++ refs' ++ refs'' ++ refs''' ++ [Refv u]`, `p`] ASSUME_TAC)
\\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
>-(
    rw[REFS_PRED_def]
    \\ rw[GSYM STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ junk ++ refs' ++ refs'' ++ refs''')) [Refv u]`
    \\ qexists_tac `st2heap p (s with refs := s.refs ++ junk ++ refs' ++ refs'' ++ refs''')`
    \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
    \\ rw[STATE_SPLIT_REFS]
    >-(
	rw[REF_REL_def]
	\\ rw[SEP_CLAUSES, SEP_EXISTS_THM]
	\\ qexists_tac `u`
        \\ EXTRACT_PURE_FACTS_TAC
	\\ rw[REF_HPROP_SAT_EQ, cfStoreTheory.store2heap_aux_def])
    \\ rw[Once (GSYM GC_STAR_GC), STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `st2heap p (s with refs := s.refs)`
    \\ qexists_tac `store2heap_aux (LENGTH s.refs) (junk ++ refs' ++ refs'' ++ refs''')`
    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    \\ rw[STATE_SPLIT_REFS, SAT_GC]
    \\ fs[REFS_PRED_def, with_same_refs])
\\ qpat_x_assum `A ==> R` IMP_RES_TAC
\\ first_x_assum(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[merge_env_def]
\\ Cases_on `env0`
\\ Cases_on `n`
\\ Cases_on `n0`
\\ fs[namespaceTheory.nsBind_def, namespaceTheory.nsAppend_def]
\\ evaluate_unique_result_tac
\\ qexists_tac `refs2`
\\ fs[REFS_PRED_FRAME_def]
\\ rw[]
\\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
\\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
>-(
    rw[GSYM STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ junk ++ refs' ++ refs'' ++ refs''')) [Refv u]`
    \\ qexists_tac `st2heap p (s with refs := s.refs ++ junk ++ refs' ++ refs'' ++ refs''')`
    \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
    \\ rw[STATE_SPLIT_REFS]
    >-(
	rw[REF_REL_def]
	\\ rw[SEP_CLAUSES, SEP_EXISTS_THM]
	\\ qexists_tac `u`
        \\ EXTRACT_PURE_FACTS_TAC
	\\ rw[REF_HPROP_SAT_EQ, cfStoreTheory.store2heap_aux_def])
    \\ rw[STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `st2heap p (s with refs := s.refs)`
    \\ qexists_tac `store2heap_aux (LENGTH s.refs) (junk ++ refs' ++ refs'' ++ refs''')`
    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    \\ rw[STATE_SPLIT_REFS, SAT_GC]
    \\ fs[REFS_PRED_def, with_same_refs])
\\ qpat_x_assum `A ==> R` IMP_RES_TAC
\\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
\\ first_x_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
\\ fs[STAR_ASSOC]
\\ first_x_assum(fn x => MATCH_MP GC_ABSORB_R x |> ASSUME_TAC)
\\ fs[]);

val Eval_lookup_var = Q.store_thm("Eval_lookup_var",
`!env vname xv x TYPE. nsLookup env.v (Short vname) = SOME xv ==>
(Eval env (Var (Short vname)) (TYPE x) <=> TYPE x xv)`,
rw[Eval_def]
\\ EQ_TAC
>-(simp[Once evaluate_cases] \\ rw[] \\ metis_tac[])
\\ rw[Once evaluate_cases]
\\ rw[state_component_equality]);

val STATE_REFS_TYPE_def = theorem"STATE_REFS_TYPE_def";

val test_10_def = Define `test10 n m z refs = insert_monad (test9 n m z) refs`;

val Long_tm = ``namespace$Long : tvarN -> (tvarN, tvarN) id -> (tvarN, tvarN) id ``;
fun get_exn_constructs () = let
    val exn_type_def = !EXN_TYPE_def_ref
    val exn_type_conjs = CONJUNCTS exn_type_def
    val deep_cons_list = List.map (fn x => concl x |> strip_forall |> snd |> rhs |> strip_exists
				|> snd |> dest_conj |> fst |> rhs |> rator) exn_type_conjs
    val deep_names = List.map (fn x => rand x |> rand |> dest_pair |> fst) deep_cons_list

    (* Get the module name *)
    val deep_type = List.hd deep_cons_list |> rand |> rand |> dest_pair |> snd |> rand
    val uses_module_name = strip_comb deep_type |> fst |> same_const Long_tm
    val module_name = if uses_module_name then SOME(strip_comb deep_type |> snd |> List.hd)
		      else NONE
in (deep_names, module_name) end;

fun create_local_defs th = let
    (* Retrieve the lookup assumptions for the functions definitions *)
    val LOCAL_ENV = mk_var("LOCAL_ENV", ``:v sem_env``)
    val NAME = mk_var("NAME", ``:tvarN``)
    val EXPR = mk_var("EXPR", ``:v``)
    val pat = ``nsLookup ^LOCAL_ENV.v (Short ^NAME) = SOME ^EXPR``
    val substs =  mapfilter (match_term pat) (hyp th)
    val lookup_info = List.map (fn (tms, _) => (Term.subst tms NAME, Term.subst tms EXPR)) substs
    val lookup_info = List.filter(fn (x, y) => not(is_var y)) lookup_info

    fun get_env_var expr = rator expr |> rator |> rand |> rator |> rand
    fun compute_env_index env = let
	val env_name = dest_var env |> fst
	val env_index_str = String.extract(env_name, String.size local_environment_var_name, NONE)
	val index = string_to_int env_index_str
    in index end

    (* Sort the lookup assumptions *)
    val lookup_info = List.map (fn (name, expr) => let val env = get_env_var expr in
				(compute_env_index env, env, name, expr) end) lookup_info
    fun assum_order (i1 : int, _, _, _) (i2 : int, _, _, _) = i1 > i2
    val lookup_info = Lib.sort assum_order lookup_info
    val lookup_info = List.map (fn (_, x, y, z) => (x, y, z)) lookup_info

    (* Create the function definitions (Let expressions) *)
    val current_env = concl th |> rator |> rator |> rator |> rator |> rand |> rator |> rand
    val all_envs = List.map (fn (x, _, _) => x) lookup_info
    val last_env = List.last all_envs
    val all_envs = current_env::(List.take(all_envs, List.length all_envs - 1))
    val lookup_info = zip all_envs lookup_info

    fun create_fun_let ((env_var2, (env_var1, name, fexp)), th) = let
	(* Build the new environment *)
	val env0 = rator fexp |> rator |> rand |> rand
	val env1 = env_var1
	val vname = name
	val xv = rator fexp |> rand
	val fexp = rand fexp

	val nenv = ``(write ^vname (Closure (merge_env ^env1 ^env0) ^xv ^fexp) ^env1)``

	(* Replace the environment and create the Let expression *)
	val th' = Thm.INST [env_var2 |-> nenv] th
	val th' = MATCH_MP Eval_Monad_Let_Fun th'

	(* Remove the appropriate nsLookup assumption *)
	val assum = ``nsLookup (merge_env ^nenv ^env0).v (Short ^vname) =
		     SOME (Closure (merge_env (^env_var1) ^env0) ^xv ^fexp)``
	val assum_rw = EVAL assum
	val th' = DISCH assum th' |> SIMP_RULE bool_ss [assum_rw]
    in th' end

    val th = List.foldl create_fun_let th lookup_info
in th end;

fun translate_insert_monad def = let
    (* Decompose the definition *)
    val (def_lhs, def_rhs) = concl test_10_def |> strip_forall |> snd |> dest_eq
    val Mvar = mk_var("M", ``:('a, 'b, 'c) M``)
    val Svar = mk_var("S", ``:'a``)
    val (tms, tys) = match_term ``insert_monad ^Mvar ^Svar`` def_rhs
    val monad_tm = Term.subst tms (Term.inst tys Mvar)
    val state_tm = Term.subst tms (Term.inst tys Svar)
    val (monad_f, monad_params) = strip_comb monad_tm

    (* Construct the Eval predicates for the parameters *)
    fun var_create_Eval tm = let
	val (name,ty) = dest_var tm
	val inv = get_type_inv ty
	val str = stringSyntax.fromMLstring name
	val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
	val result = MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) result
    in check_inv "var" tm result end
    val params_evals = List.map var_create_Eval monad_params

    (* Get the monadic specification *)
    val monad_th = lookup_dynamic_v_thm monad_f
    val monad_th = (MATCH_MP Eval_IMP_PURE monad_th)
		 |> ISPEC (!H)
		 |> PURE_REWRITE_RULE[GSYM ArrowM_def]
    
    (* Insert the parameters *)
    val monad_th = List.foldl (fn (x, th) => MATCH_MP(MATCH_MP EvalM_ArrowM th) x)
			      monad_th params_evals

    (* Translate the insert_monad construct *)
    val env = concl monad_th |> rator |> rator |> rator |> rand
    val x = concl monad_th |> rator |> rand |> rand
    val exp = concl monad_th |> rator |> rator |> rand
    val MONAD_TYPE = concl monad_th |> rator |> rand |> rator
    val EXN_TYPE = rand MONAD_TYPE
    val TYPE = rator MONAD_TYPE |> rand
    val vname = stringSyntax.fromMLstring "vname"
    val (exn_cons_names, exn_module_name) = get_exn_constructs ()
    val cons_names = mk_list(exn_cons_names, ``:tvarN``)
    val th = case exn_module_name of
		 SOME module_name =>
		 ISPECL [cons_names, module_name, vname, TYPE, EXN_TYPE, x, exp,
			 !H, state_tm, env] EvalM_insert_monad_MODULE
	       | NONE =>
		 ISPECL [cons_names, vname, TYPE, EXN_TYPE, x, exp,
			 !H, state_tm, env] EvalM_insert_monad_SIMPLE
    (* Prove the assumptions *)
    val [EXN_assum, distinct_assum, vname_assum1, vname_assum2] = List.take(
	    concl th |> strip_imp |> fst, 4)
    val EXN_th = prove(EXN_assum, rw[] \\ Cases_on `e` \\ fs[!EXN_TYPE_def_ref])
    val th = MP th EXN_th
		
    val distinct_rw = SIMP_CONV list_ss [] distinct_assum
    val vname_rw1 = SIMP_CONV list_ss [] vname_assum1
    val vname_rw2 = SIMP_CONV list_ss [] vname_assum2
    val th = SIMP_RULE bool_ss [EXN_rw, distinct_rw, vname_rw1, vname_rw2] th
    val th = MP th monad_th

    (* Undischarge the lookup assumptions *)
    val every_lookup_assum = concl th |> dest_imp |> fst
    val every_lookup_rw = SIMP_CONV list_ss [] every_lookup_assum
    val th = SIMP_RULE bool_ss [every_lookup_rw, GSYM AND_IMP_INTRO] th |> UNDISCH_ALL

    (* Replace the environment *)
    val nenv = get_current_env()
    val th = Thm.INST [env |-> nenv] th

    (* Create the local function definitions *)
    val th = create_local_defs th

    (* Remove the last environment *)
    val empty_env = ``<| v := Bind [] []; c := Bind [] [] |> : v sem_env``
    val th = Thm.INST [last_env |-> empty_env] th |> PURE_REWRITE_RULE [merge_env_bind_empty]

    (*
     * Instantiate the environment 0
     *)
    val global_env = get_env(get_curr_prog_state())
    val params_bindings = List.map(fn x => (concl x |> rator |> rator |> rand |> rand |> rand,
					    concl x |> rator |> rand |> rand)) params_evals
    val state_var = concl th |> rator |> rand
    val state_var_eval = hol2deep state_var
    val state_var_binding = ((concl state_var_eval |> rator |> rand |> rand |> rand), state_var)
    
    (* Create variables for the deep embeddings of the parameters *)
    val fvl = HOLset.listItems(FVL ((concl th)::(hyp th)) empty_varset)
    val deep_params = List.map (fn (n, var) => variant fvl (mk_var((dest_var var |> fst) ^ "_v", ``:v``))) params_bindings
    val hol_deep_pairs = List.map (fn ((n, x), xv) => (x, xv)) (zip params_bindings deep_params)
    val deep_params_map = List.foldr (fn ((x, xv), m) => Redblackmap.insert(m, x, xv)) (Redblackmap.mkDict Term.compare) hol_deep_pairs

    val params_bindings_v = List.map (fn ((n, x), xv) => (n, xv)) (zip params_bindings deep_params)
    val params_bindings_v = List.map mk_pair params_bindings_v
    val params_bindings_v = mk_list(params_bindings_v, ``:tvarN # v``)

    (* val params_invs_hyps = List.map (fn ((n, x), xv) => list_mk_comb(get_type_inv (type_of x), [x, xv])) (zip params_bindings deep_params) *)

    (* Create the environment 0 and substitute it *)
    val env0 = ``merge_env <| v := Bind ^params_bindings_v []; c := Bind [] [] |> ^global_env``
    val th = Thm.INST [local_environment_var_0 |-> env0] th
    
    (* Simplify the assumptions *)
    val assums = hyp th
    val lookup_cons_assums = List.filter (can (match_term ``lookup_cons vname env = SOME t``)) assums
    val lookup_cons_rws = mapfilter(fn x => EVAL x |> EQT_ELIM) lookup_cons_assums
    val th = List.foldr (fn (a, th) => MP (DISCH (concl a) th) a) th lookup_cons_rws
    val assums = hyp th
    val nsLookup_assums = List.filter (can (match_term ``nsLookup env id = SOME var``)) assums
    val nsLookup_assums_rws = mapfilter(fn x => EVAL x |> EQT_ELIM) nsLookup_assums
    val th = List.foldr (fn (a, th) => MP (DISCH (concl a) th) a) th nsLookup_assums_rws
    val assums = hyp th
    val Eval_var_assums = List.filter (can (match_term ``Eval env exp (P x)``)) assums

    fun rewrite_Eval_var (assum, th) = let
	val env = rator assum |> rator |> rand
	val vname = rator assum |> rand |> rand |> rand
	val x = rand assum |> rand
	val xv = Redblackmap.find (deep_params_map, x)
	val TYPE = rand assum |> rator

	val rw_th = ISPECL[env, vname, xv, x, TYPE] Eval_lookup_var
	val rw_th_assum = concl rw_th |> dest_imp |> fst
	val rw_th = MP rw_th (EVAL rw_th_assum |> EQT_ELIM)

	val inv_to_eval = EQ_IMP_RULE rw_th |> snd |> UNDISCH
	val th = MP (DISCH (concl inv_to_eval) th) inv_to_eval
    in th end

    val th = List.foldl rewrite_Eval_var th Eval_var_assums

			(* Create the store *)



Eval_def

DB.apropos ``(x <=> T) <=> x``

EVAL ``lookup_cons "Success" (merge_env auto_env_9 init_env)``
``lookup_cons``

val assum1 = List.nth(assums, 1)
EVAL assum1

    val assums = DISCH_ALL th' 
    val clean_assumptions (DISCH_ALL th')

lookup_cons_def

EVAL ``NUM x y``
    val all_param_bindings = List.map mk_pair all_param_bindings
    val all_params_bindings = mk_list(all_param_bindings, ``:tvarN # v``)
    val env0 = ``merge_env

    val th' = Thm.INST[local_environment_var_0  |-> global_env] th |> DISCH_ALL


    (* Create the store *)
    fun create_local_store th = let
	val th = PURE_REWRITE_RULE [!H_def, GSYM STAR_ASSOC] th
	val state_var = concl th |> rator |> rand

th
Eval_Monad_Opref

assums
List.hd assums

fun create_local_store refs_init_list arrays_init_list store_hprop_name =
  let
      val _ = if List.null refs_init_list andalso List.null arrays_init_list
	      then raise (ERR "create_store" "need a non empty list of reference init values")
	      else ()

      val initial_state = mk_var("s", ``:unit semanticPrimitives$state``)
      val initial_store = ``^initial_state.refs``
      val initial_env = get_env(get_ml_prog_state())

      (* Allocate the references *)
      fun create_ref ((name, def), (s, env)) =
	let
	    val trans_th = abs_translate def
	    val expr = rator (concl trans_th) |> rand
	    val e = ``(App Opref [^expr])``
	    (derive_eval_thm name e)


	    val value_expr = 
	    val init_name = concl def |> dest_eq |> fst |> dest_const |> fst
	    val init_name = stringLib.fromMLstring init_name
	    val e = ``(App Opref [Var (Short ^init_name)])``
	    val _ = ml_prog_update (add_Dlet (derive_eval_thm name e) name [])
	    val ref_def = DB.fetch (current_theory()) (name ^ "_def")
	in
	    (value_def, ref_def)
	end
      val ref_name_def_pairs = List.map (fn (n, d, _, _) => (n, d)) refs_init_list
      val refs_trans_results = List.map create_ref ref_name_def_pairs

      (* Allocate the arrays *)
      fun create_array (name, def) =
	let
	    val init_name = concl def |> lhs |> dest_const |> fst

	    val (array_v_def, array_loc_def, ref_def, eval_th) =
		derive_eval_thm_ALLOCATE_EMPTY_ARRAY init_name def
	    val _ = ml_prog_update(add_Dlet eval_th name [])
         in
	     (array_v_def, array_loc_def, ref_def)
	end
      val array_name_def_pairs = List.map (fn (n, d, _, _, _, _, _, _) => (n, d)) arrays_init_list
      val arrays_trans_results = List.map create_array array_name_def_pairs
  in
    (initial_store, refs_trans_results, arrays_trans_results)
  end;

hol2deep ``state_refs x_3 x_2 x_1:state_refs``


Net.listItems (!dynamic_specs)

val _ = export_theory ();

open HolKernel boolLib boolSimps bossLib lcsymtacs preamble miscLib miscTheory arithmeticTheory rich_listTheory optionTheory 
open typeSystemTheory typeSoundTheory typeSoundInvariantsTheory typeSysPropsTheory untypedSafetyTheory
open standaloneTheory printTheory evalPropsTheory free_varsTheory
open inferTheory inferSoundTheory
open lexer_implTheory cmlParseTheory pegSoundTheory pegCompleteTheory
open bytecodeTheory bytecodeExtraTheory bytecodeClockTheory bytecodeEvalTheory compilerProofTheory
open initCompEnvTheory standalone_funTheory

val _ = new_theory "standalone_funProof";

val _ = ParseExtras.temp_tight_equality ();

val OPTION_JOIN_EQ_NONE = Q.prove (
`OPTION_JOIN x = NONE ⇔ (x = NONE ∨ x = SOME NONE)`,
 Cases_on `x` >>
 rw []);

(* install_bc_lists_def copied from repl_funScript.sml *)
val install_bc_lists_def = Define `
  install_bc_lists code bs =
    install_code (REVERSE (MAP num_bc code)) bs`;

val parse_correct = Q.prove (
`!toks. parse toks = parse_prog toks`,
 cheat);

val standalone_fun_correct = Q.store_thm ("standalone_fun_correct",
`!sem_is is init_bc_state input. 
  infer_sound_invariant is.inf_tenvT is.inf_tenvM is.inf_tenvC is.inf_tenvE ∧
  type_sound_invariants NONE (sem_is.tdecs,
                              sem_is.tenvT,
                              sem_is.tenvM,
                              sem_is.tenvC,
                              sem_is.tenv,
                              FST (SND sem_is.sem_env.sem_store),
                              sem_is.sem_env.sem_envM,
                              sem_is.sem_env.sem_envC,
                              sem_is.sem_env.sem_envE,
                              (SND (FST sem_is.sem_env.sem_store))) ∧
  convert_decls (is.inf_mdecls,is.inf_tdecls,is.inf_edecls) = sem_is.tdecs ∧
  is.inf_tenvT = sem_is.tenvT ∧
  convert_menv is.inf_tenvM = sem_is.tenvM ∧
  is.inf_tenvC = sem_is.tenvC ∧
  bind_var_list2 (convert_env2 is.inf_tenvE) <{}> = sem_is.tenv
  ⇒
  standalone sem_is TYPE_ERROR_MASK input 
  = 
  case standalone_to_bc SOMETHING_ABOUT_INIT_BC_LABELS is input of
     | Failure s => 
         SOME s
     | Success code => 
         case bc_eval (install_bc_lists code init_bc_state) of
            | SOME bs => 
                SOME bs.output
            | NONE => NONE`,
 rw [standalone_def, standalone_to_bc_def, ast_standalone_cases] >>
 Cases_on `parse (lexer_fun input)` >>
 fs [parse_correct] >>
 qabbrev_tac `infer = infer_prog (is.inf_mdecls,is.inf_tdecls,is.inf_edecls) is.inf_tenvT is.inf_tenvM is.inf_tenvC is.inf_tenvE x init_infer_state` >>
 `(?s is. infer = (Failure s,is)) ∨ (?types is. infer = (Success types,is))` 
               by metis_tac [pair_CASES, exc_nchotomy]
 >- cheat >>
 `?decls' tenvT' menv' cenv' env'.
    type_prog (convert_decls (is.inf_mdecls,is.inf_tdecls,is.inf_edecls)) is.inf_tenvT (convert_menv is.inf_tenvM) is.inf_tenvC
       (bind_var_list2 (convert_env2 is.inf_tenvE) <{}>) x
       (convert_decls decls') tenvT' (convert_menv menv') cenv'
       (convert_env2 env')`
            by metis_tac [infer_prog_sound, pair_CASES] >>
 rw [] >>
 REV_FULL_SIMP_TAC (srw_ss()) [] >>
 Cases_on `prog_diverges (sem_is.sem_env.sem_envM,sem_is.sem_env.sem_envC, sem_is.sem_env.sem_envE)
                         (SND (FST sem_is.sem_env.sem_store), FST (SND sem_is.sem_env.sem_store),FST sem_is.tdecs) 
                         x` >>
 rw []
 >- cheat >> (* type error case. Need to get the right type error mask *)
 imp_res_tac whole_prog_type_soundness >>
 fs [] >>
 pop_assum (qspecl_then [`SOME_COUNT`] strip_assume_tac) >>
 cheat);


val _ = export_theory ();


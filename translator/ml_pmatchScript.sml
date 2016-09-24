open preamble
     determTheory ml_translatorTheory
     patternMatchesTheory patternMatchesLib;
open astTheory libTheory semanticPrimitivesTheory bigStepTheory;
open determTheory evalPropsTheory bigClockTheory mlstringTheory;
open integerTheory terminationTheory;

val _ = new_theory "ml_pmatch";

val write_def = ml_progTheory.write_def;

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

val EvalPatRel_def = Define`
  EvalPatRel (:'ffi) env a p pat ⇔
    ∀x av. a x av ⇒ ∀(s:'ffi state).
      evaluate_match F env s av
        [(p,Con NONE [])] ARB
        (s,
         if ∃vars. pat vars = x
         then Rval(Conv NONE []) else Rerr(Rraise ARB))`

val EvalPatBind_def = Define`
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av refs env'.
      a x av ∧
      (pmatch_list env.c refs [p] [av] env.v = Match env') ∧
      (env2 = env with v := env') ∧
      (pat vars = x)`

val pmatch_PMATCH_ROW_COND_No_match = store_thm("pmatch_PMATCH_ROW_COND_No_match",
  ``EvalPatRel (:'ffi) env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    pmatch_list env.c refs [p] [res] env.v = No_match``,
  fs [PMATCH_ROW_COND_def] >>
  rw[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  rfs[] >>
  ntac 4 (fs[Once evaluate_cases]) >>
  first_x_assum(qspec_then`ARB with refs := refs`mp_tac) >>
  rw[pmatch_def]);

val pmatch_PMATCH_ROW_COND_Match = store_thm("pmatch_PMATCH_ROW_COND_Match",
  ``EvalPatRel (:'ffi) env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. pmatch_list env.c refs [p] [res] env.v = Match env2``,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  fs[Once evaluate_cases] >> rfs[] >>
  ntac 4 (fs[Once evaluate_cases]) >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  first_x_assum(qspec_then`ARB with refs := refs`mp_tac) >>
  rw[pmatch_def] >> rw[] >> PROVE_TAC[]);

val Eval_PMATCH_NIL = store_thm("Eval_PMATCH_NIL",
  ``!b x xv a.
      Eval (:'ffi) env x (a xv) ==>
      CONTAINER F ==>
      Eval (:'ffi) env (Mat x []) (b (PMATCH xv []))``,
  rw[CONTAINER_def]);

val Eval_PMATCH = store_thm("Eval_PMATCH",
  ``!b a x xv.
      ALL_DISTINCT (pat_bindings p []) ⇒
      (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
      Eval (:'ffi) env x (a xv) ⇒
      (p1 xv ⇒ Eval (:'ffi) env (Mat x ys) (b (PMATCH xv yrs))) ⇒
      EvalPatRel (:'ffi) env a p pat ⇒
      (∀env2 vars.
        EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
        Eval (:'ffi) env2 e (b (res vars))) ⇒
      (∀vars. PMATCH_ROW_COND pat (K T) xv vars ⇒ p2 vars) ∧
      ((∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ⇒ p1 xv) ⇒
      Eval (:'ffi) env (Mat x ((p,e)::ys)) (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs)))``,
  rw[Eval_def] >>
  rw[Once evaluate_cases,PULL_EXISTS] >> fs[] >>
  first_x_assum(qspec_then`s`strip_assume_tac) >>
  asm_exists_tac >> simp[] \\
  rw[Once evaluate_cases,PULL_EXISTS] >>
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    pop_assum kall_tac >>
    first_assum(qspec_then`s'.refs`strip_assume_tac) >>
    first_assum mp_tac >>
    simp_tac(srw_ss())[pmatch_def] >>
    TOP_CASE_TAC >> rw[] \\
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >>
    qpat_x_assum`p1 xv ⇒ ∀s. _`kall_tac >>
    simp[PMATCH_def,PMATCH_ROW_def] >>
    fs[PMATCH_ROW_COND_def] >>
    `(some v. pat v = xv) = SOME vars` by (
      simp[some_def] \\ metis_tac[]) \\
    rw[] \\
    first_x_assum match_mp_tac \\
    rw[EvalPatBind_def] \\
    asm_exists_tac \\ rw[] \\
    asm_exists_tac \\ rw[]) >>
  first_x_assum(qspec_then`s`strip_assume_tac) \\
  qpat_x_assum`evaluate F X Y (Mat A B) R`mp_tac >>
  simp[Once evaluate_cases] >> strip_tac >>
  imp_res_tac (CONJUNCT1 big_exp_determ) >> fs[] >> rw[] >>
  srw_tac[DNF_ss][] >> disj2_tac >>
  simp[PMATCH_def,PMATCH_ROW_def] >>
  drule (GEN_ALL pmatch_PMATCH_ROW_COND_No_match) >>
  disch_then drule \\ disch_then drule \\
  disch_then(qspec_then`s'.refs`mp_tac) \\
  fs[pmatch_def] >>
  BasicProvers.CASE_TAC \\
  asm_exists_tac \\ rw[]);

val PMATCH_option_case_rwt = store_thm("PMATCH_option_case_rwt",
  ``((case x of NONE => NONE
      | SOME (y1,y2) => P y1 y2) = SOME env2) <=>
    ?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2)``,
  Cases_on `x` \\ fs [] \\ Cases_on `x'` \\ fs []);

val _ = export_theory()

open HolKernel Parse boolLib bossLib lcsymtacs
open lexer_implTheory cmlParseTheory astTheory inferTheory compilerTheory
     compilerTerminationTheory bytecodeEvalTheory replTheory
     initialProgramTheory;
open listTheory arithmeticTheory relationTheory;
open bytecodeLabelsTheory bytecodeTheory;

val _ = new_theory "standalone_fun";

(* unlabel_and_encode_def copied from repl_funScript.sml *)
val unlabel_and_encode_def = Define`
  unlabel_and_encode (len,labs) code =
    let code = REVERSE code in
    let labs = FUNION labs (collect_labels code len real_inst_length) in
    let len = len + code_length real_inst_length code in
    let code = inst_labels labs code in
    ((len,labs),MAP bc_num code)`

val standalone_to_bc_def = Define `
standalone_to_bc ls is input =
  case parse_prog (lexer_fun input) of
    | NONE => Failure "<parse error>\n"
    | SOME prog =>
        case infer_prog (is.inf_mdecls,is.inf_tdecls,is.inf_edecls)
                        is.inf_tenvT is.inf_tenvM is.inf_tenvC is.inf_tenvE 
                        prog init_infer_state  of
           | (Failure _, _) => Failure "<type error>\n"
           | (Success _, _) =>
               let code = compile_prog is.comp_rs prog in
                 Success (SND (unlabel_and_encode ls code))`;

val basis_standalone_to_bc_def = Define `
basis_standalone_to_bc input = standalone_to_bc ARB (FST (THE basis_env)) input`;

val _ = export_theory ();


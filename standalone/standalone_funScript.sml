open HolKernel Parse boolLib bossLib lcsymtacs
open lexer_implTheory cmlParseTheory astTheory inferTheory compilerTheory
     compilerTerminationTheory bytecodeEvalTheory replTheory
     initialProgramTheory;
open listTheory arithmeticTheory relationTheory;
open bytecodeLabelsTheory bytecodeTheory;

val _ = new_theory "standalone_fun";

val standalone_to_bc_def = Define `
standalone_to_bc basis_code is input =
  case parse_prog (lexer_fun input) of
    | NONE => Failure "<parse error>\n"
    | SOME prog =>
        case infer_prog (is.inf_mdecls,is.inf_tdecls,is.inf_edecls)
                        is.inf_tenvT is.inf_tenvM is.inf_tenvC is.inf_tenvE
                        prog init_infer_state  of
           | (Failure _, _) => Failure "<type error>\n"
           | (Success _, _) =>
               let code = compile_prog is.comp_rs prog in
               let code = code_labels real_inst_length
                           (initial_bc_state.code ++ (REVERSE (code ++ basis_code))) in
                 Success code`;

val basis_standalone_to_bc_def = Define `
basis_standalone_to_bc input = standalone_to_bc (SND (THE basis_env) ++ SND (THE prim_env)) (FST (THE basis_env)) input`;

val _ = export_theory ();


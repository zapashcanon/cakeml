open HolKernel Parse boolLib bossLib lcsymtacs
open lexer_implTheory mmlParseTheory AstTheory inferTheory CompilerTheory
     PrinterTheory compilerTerminationTheory bytecodeEvalTheory replTheory
     ElabTheory

val _ = new_theory "repl_fun";

val _ = type_abbrev ("elaborator_state", ``:typeN list # ctor_env``);

val elaborate_top_def = Define `
elaborate_top ((types, constructors) : elaborator_state) ast_top =
  let (new_types, new_constructors, top) = elab_top types constructors ast_top in
    ((new_types++types, new_constructors ++ constructors), top)`;

val initial_elaborator_state_def = Define `
initial_elaborator_state : elaborator_state = ([], [])`;

val _ = type_abbrev ("inferencer_state", ``:(modN, (varN, num # infer_t) env) env # tenvC # (varN, num # infer_t) env``);

val infertype_top_def = Define `
infertype_top ((module_type_env, constructor_type_env, type_env) :inferencer_state) ast_top =
  case FST (infer_top module_type_env constructor_type_env type_env ast_top infer$init_infer_state) of
     | Failure _ => Failure "type error"
     | Success (new_module_type_env, new_constructor_type_env, new_type_env) =>
        Success (new_module_type_env ++ module_type_env,
                  new_constructor_type_env ++ constructor_type_env,
                  new_type_env ++ type_env)`;

val initial_inferencer_state_def = Define `
initial_inferencer_state : inferencer_state = ([], [], infer$init_type_env)`;

val _ = Hol_datatype`repl_fun_state = <|
  relaborator_state : elaborator_state;
  rinferencer_state : inferencer_state;
  rcompiler_state  : compiler_state;
  top : top |>`

val compile_decs = Define`
  compile_decs cs [] acc = (cs,acc) ∧
  compile_decs cs (d::ds) acc =
  let (cs,code) = compile_dec cs d in
  compile_decs cs ds (code::acc)`

val compile_primitives_def = Define`
  compile_primitives =
    compile_decs init_compiler_state
    [Dlet(Pvar"+")  (Fun"x"(Fun"y"(App(Opn Plus  )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"-")  (Fun"x"(Fun"y"(App(Opn Minus )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"*")  (Fun"x"(Fun"y"(App(Opn Times )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"div")(Fun"x"(Fun"y"(App(Opn Divide)(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"mod")(Fun"x"(Fun"y"(App(Opn Modulo)(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"<")  (Fun"x"(Fun"y"(App(Opb Lt    )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar">")  (Fun"x"(Fun"y"(App(Opb Gt    )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"<=") (Fun"x"(Fun"y"(App(Opb Leq   )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar">=") (Fun"x"(Fun"y"(App(Opb Geq   )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"=")  (Fun"x"(Fun"y"(App(Equality  )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar":=") (Fun"x"(Fun"y"(App(Opassign  )(Var(Short"x"))(Var(Short"y")))))
    ;Dlet(Pvar"!")  (Fun"x"(Uapp(Opderef)(Var(Short"x"))))
    ;Dlet(Pvar"ref")(Fun"x"(Uapp(Opref  )(Var(Short"x"))))] []`

val initial_repl_fun_state = Define`
  initial_repl_fun_state = <|
    relaborator_state := initial_elaborator_state;
    rinferencer_state := initial_inferencer_state;
    rcompiler_state   := FST compile_primitives;
    top := (Tmod "" NONE []) |>`

val print_result_def = Define `
  print_result s bs =
    if HD bs.stack = (Number 0) then
      (bs with <| stack := TL bs.stack |>
      ,case s.top of
       | Tmod _ _ _ => "module"
       | Tdec dec =>
           simple_printer
            (preprint_dec s.rcompiler_state dec)
            (cpam s.rcompiler_state) (TL bs.stack)
      )
    else
      (bs with <| stack := TL (TL bs.stack) |> (* TODO: depends on how exception handlers are represented *)
      ,"Exception" (* TODO: simple_print the actual exception at HD (TL bs.stack) *)
      )`

val update_state_def = Define`
  update_state s es is cs t =
  s with <| relaborator_state := es
          ; rinferencer_state := is
          ; rcompiler_state   := cs
          ; top               := t
          |>`

val compile_top_def = Define `
  (compile_top cs (Tmod _ _ _) = (cs,[])) /\ (* fix! *)
  (compile_top cs (Tdec dec) = compile_dec cs dec)`;

val parse_elaborate_infertype_compile_def = Define `
  parse_elaborate_infertype_compile tokens s =
    case parse_top tokens of
      (* case: parse error *)
      NONE => Failure "parse error"
    | (* case: ast_top produced *)
      SOME ast_top =>
        let (es,top) = elaborate_top s.relaborator_state ast_top in
          case infertype_top s.rinferencer_state top of
            (* type inference failed to find type *)
          | Failure _ => Failure "type error"
            (* type found, type safe! *)
          | Success is =>
             let (cs,code) = compile_top s.rcompiler_state top in
               Success (code,update_state s es is cs top)`

val install_code_def = Define `
  install_code code bs =
    let code = compile_labels bs.inst_length (bs.code ++ code) in
    bs with <| code := code ; pc := next_addr bs.inst_length bs.code |>`;

val initial_bc_state_def =  Define`
  initial_bc_state =
  install_code (FLAT(REVERSE(SND compile_primitives)))
    <|stack := [];
      code := [];
      pc := 0;
      refs := FEMPTY;
      handler := 0;
      inst_length := K 0 |>`

val tac = (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lex_until_toplevel_semicolon_LESS);

val main_loop_def = tDefine "main_loop" `
  main_loop (bs,s) input =
    case lex_until_toplevel_semicolon input of
      (* case: no semicolon found, i.e. trailing characters then end of input *)
      NONE => Terminate
    | (* case: tokens for next top have been read, now eval-print-and-loop *)
      SOME (tokens, rest_of_input) =>
        case parse_elaborate_infertype_compile tokens s of
          (* case: cannot turn into code, print error message, continue *)
          Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)
        | (* case: new code generated, install, run, print and continue *)
          Success (code,new_s) =>
            case bc_eval (install_code code bs) of
              (* case: evaluation of code does not terminate *)
              NONE => Diverge
            | (* case: evaluation terminated, print result and continue *)
              SOME new_bs =>
                let (new_bs,output) = print_result new_s new_bs in
                Result output (main_loop (new_bs,new_s) rest_of_input) ` tac ;

val repl_fun_def = Define`
  repl_fun input = main_loop (initial_bc_state,initial_repl_fun_state) input`;

(*

TODO:

 - Distinguish between error messages (e.g. from failed type check)
   and real output in repl_result, i.e. above

     Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)

   should really be something like:

     Failure error_msg => Error error_msg (main_loop (bs,s) rest_of_input)

*)

val _ = export_theory()

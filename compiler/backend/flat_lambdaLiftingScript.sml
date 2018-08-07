open
  preamble
  flatLangTheory
  mlintTheory
  flat_scopeAnalysisTheory
  flat_parameterLiftingTheory
  flat_parameterLiftingSolveTheory

(* Lambda lift a program *)
val _ = new_theory "flat_lambdaLifting";

val compile_decs_def = Define

  `compile_decs decs =
   let decs = flat_scopeAnalysis$compile_decs decs in
   (* TODO: let decs = flat_deanonymizationScript$compile_decs decs in *)
   let sol = flat_parameterLiftingSolve$compute_decs_sol decs in
   let decs = flat_parameterLifting$compile_decs sol decs in
   (* TODO: let decs = flat_blockFloating$compiles_decs decs in *)
   decs`

val _ = export_theory ()

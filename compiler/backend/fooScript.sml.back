open
  cfTacticsBaseLib
  source_to_flatTheory
  ml_progTheory
  astTheory
  namespaceTheory
  flat_scopeAnalysisTheory
  flat_parameterLiftingTheory
  flat_parameterLiftingSolveTheory

val prog = parse_topdecs`
  fun foldL f init l =
    case l of
      [] => init
    | h::t => foldL f (f h) t
`

val prog = parse_topdecs`
  fun f x =
    let
      fun g (y) =
        if y = 0 then 1 else x + g (y - 1)
    in
    g x + f (x - 1)
    end
    f 2
`

val prog = parse_topdecs`
  fun f x = 1 + x
`

val prog = parse_topdecs`
  fun f x =
    let fun g (y) =
      y x (g y)
    in
    g x (f x)
    end
    f 2
`

val flat_prog =
  EVAL ``SND (source_to_flat$compile empty_config ^prog)``
  |> SIMP_RULE (srw_ss()) [pat_bindings_def,pat_tups_def,nsLookup_def]
  |> concl |> rand |> EVAL |> concl |> rand

val unique_prog =
  EVAL ``SND (flat_to_unique$compile_decs 0 ^flat_prog)`` |> concl |> rand

val sol =
  EVAL ``named_to_nofree$compute_decs_sol ^unique_prog`` |> concl |> rand

val fr =
  EVAL ``MAP (λ x. case x of Dlet e => compute_freeID_exp [] e | _ => []) ^unique_prog`` |> concl |> rand

val sol =
  EVAL ``MAP (named_to_nofree$compute_equations_exp [] [] []) ^unique_exps``

val graph_test =
  EVAL ``[("f", [])] `` |> concl |> rand

val graph_test =
  EVAL ``[("f", ["f"; "g"; "h"]); ("g", ["f"]); ("h", ["h"])]`` |> concl |> rand

val scc_test =
  EVAL ``graph_utils$kosaraju [("f", [])]`` |> concl |> rand

val coalesced_test =
  EVAL ``graph_utils$coalesce [("f", [])] (graph_utils$kosaraju [("f", [])])`` |> concl |> rand

val lll =
  EVAL ``named_to_nofree$compute_equations_exp [] [] [] x``
  |> SIMP_RULE (srw_ss()) [pat_bindings_def,pat_tups_def,nsLookup_def]

g`MAP (named_to_nofree$compute_equations_exp [] [] []) ^unique_exps = xxx`
Induct >>
val _ = export_rewrites ["named_to_nofree.set_union_def",
"named_to_nofree.set_rm_def",
"named_to_nofree.set_add_def",
"named_to_nofree.set_intersection_def",
"named_to_nofree.set_big_union_def",
"named_to_nofree.set_add_def",
"named_to_nofree.compute_scc_def",
"named_to_nofree.compute_freeID_exp_def_def",
"named_to_nofree.compute_global_scc_sol_def_def"
]

val _ =
  translate named_to_nofree$compute_equations_exp_def

(*
  flat_to_source
  astPP.astPP
*)

open
  preamble
  flatLangTheory
  mlintTheory
  set_utilsTheory
  graph_utilsTheory

val _ = new_theory "flat_parameterLiftingSolve"

val compute_local_scc_sol_def = Define

  `compute_local_scc_sol scc nodeLocalSol =
    FOLDL (λ acc node. case ALOOKUP nodeLocalSol node of
    | SOME x => set_union acc x
    | NONE => acc
    ) empty_set scc`

val compute_global_scc_sol_def = tDefine "compute_global_scc_sol"

  `compute_global_scc_sol scc callGraphCoalesced sccLocalSol =

    let deps = case ALOOKUP callGraphCoalesced scc of
    | NONE => empty_set
    | SOME x => x in

    FOLDL (λ acc dep.
      let depLocalSol = case ALOOKUP sccLocalSol dep of
      | NONE => empty_set
      | SOME x => x in

      let depGlobalSol = compute_global_scc_sol dep callGraphCoalesced sccLocalSol in
      set_union acc (set_union depLocalSol depGlobalSol)
    ) [] deps`

  cheat

val compute_pattern_linkedID_def = Define

  `(compute_pattern_linkedID (Pvar x) = set_add empty_set x) ∧
   (compute_pattern_linkedID (Pref p) = compute_pattern_linkedID p) ∧
   (compute_pattern_linkedID (Pcon tr (h::t)) = set_union (compute_pattern_linkedID h) (compute_pattern_linkedID (Pcon tr t))) ∧
   (compute_pattern_linkedID Pany = empty_set) ∧
   (compute_pattern_linkedID (Pcon _ []) = empty_set) ∧
   (compute_pattern_linkedID (Plit _) = empty_set)`

val compute_freeID_exp_def = tDefine "compute_freeID_exp"

  `(compute_freeID_exp linkedID (Raise _ e) = compute_freeID_exp linkedID e) ∧
   (compute_freeID_exp linkedID (Handle _ e pes) = set_union (compute_freeID_exp linkedID e) (compute_freeID_pes linkedID pes)) ∧
   (compute_freeID_exp _ (Lit _ _) = empty_set) ∧
   (compute_freeID_exp linkedID (Con _ _ es) = compute_freeID_exps linkedID es) ∧
   (compute_freeID_exp linkedID (Var_local _ x) = if MEM x linkedID then empty_set else set_add empty_set x) ∧
   (compute_freeID_exp linkedID (Fun _ x e) = compute_freeID_exp (set_add linkedID x) e) ∧
   (compute_freeID_exp linkedID (App _ _ es) = compute_freeID_exps linkedID es) ∧
   (compute_freeID_exp linkedID (If _ e1 e2 e3) =
      set_union (compute_freeID_exp linkedID e1) (set_union (compute_freeID_exp linkedID e2) (compute_freeID_exp linkedID e3))) ∧
   (compute_freeID_exp linkedID (Mat _ e pes) = set_union (compute_freeID_exp linkedID e) (compute_freeID_pes linkedID pes)) ∧
   (compute_freeID_exp linkedID (Let _ x e1 e2) =
      let linkedID' = case x of | NONE => empty_set | SOME x => [x] in
      set_union (compute_freeID_exp linkedID e1) (compute_freeID_exp (set_union linkedID linkedID') e2)) ∧
   (compute_freeID_exp linkedID (Letrec _ funs e) =
      let linkedID' = set_union linkedID (MAP (λ (name, _, _). name) funs) in
      set_union (compute_freeID_exp linkedID' e) (compute_freeID_funs linkedID funs)) ∧
   (compute_freeID_exps _ [] = empty_set) ∧
   (compute_freeID_exps linkedID (h::t) = set_union (compute_freeID_exp linkedID h) (compute_freeID_exps linkedID t)) ∧
   (compute_freeID_fun linkedID (vName, e) = compute_freeID_exp (set_add linkedID vName) e) ∧
   (compute_freeID_funs _ [] = empty_set) ∧
   (compute_freeID_funs linkedID ((fName, vName, e)::t) =
      set_union (compute_freeID_fun (set_add linkedID fName) (vName, e)) (compute_freeID_funs linkedID t)) ∧
   (compute_freeID_pe linkedID (p, e) = let linkedID' = compute_pattern_linkedID p in
      compute_freeID_exp (set_union linkedID linkedID') e) ∧
   (compute_freeID_pes _ [] = empty_set) ∧
   (compute_freeID_pes linkedID (h::t) = set_union (compute_freeID_pe linkedID h) (compute_freeID_pes linkedID t))`

  (WF_REL_TAC `inv_image $< (λ x. (case x of
  | INL (_, e) => exp_size e
  | INR (INL (_, es)) => exp6_size es
  | INR (INR (INL (_, f))) => exp4_size f
  | INR (INR (INR (INL (_, funs)))) => exp1_size funs
  | INR (INR (INR (INR (INL (_, pe))))) => exp5_size pe
  | INR (INR (INR (INR (INR (_, pes))))) => exp3_size pes
  ))`)

val compute_equations_funs_def = Define`

  compute_equations_funs oldVars oldFuns oldSol funs =

    let linkedID = set_union oldVars oldFuns in
    let freeID = MAP (λ (name, vName, e). name, compute_freeID_exp ( [name; vName]) e) funs in

    let introducedRecFuns = MAP (λ (name, _, _). name) funs in
    let accessibleFuns = set_union oldFuns introducedRecFuns in

    let introducedRecVars = empty_set in (* we don't have mutually rec. vars. :-) *)
    let accessibleVars = set_union oldVars introducedRecVars in

    (* for each fun in the letrec, this is the part of the solution that doesn't depends on others funs in the letrec *)
    let localSol = MAP (λ (name, freeID). name,
      set_union
        (set_intersection accessibleVars freeID) (* vars *)
        (set_big_union (MAP (λ dep. case ALOOKUP oldSol dep of | NONE => empty_set | SOME x => x) (set_intersection oldFuns freeID))) (* funs *)
    ) freeID in

    (* for each fun in the letrec, this is the set of other funs in the letrec we depends on, i.e. the call graph *)
    let callGraph = MAP (λ (name, freeID). name,
      set_rm (set_intersection introducedRecFuns freeID) name
    ) freeID in

    (* the set of strongly connected components:
       f <--> g --> h is now [["f"; "g"]; ["h"]] *)
    let scc = kosaraju callGraph in

    (* we've got to rebuild the dep. graph between the scc: *)
    let callGraphCoalesced = coalesce callGraph scc in

    (* local sol for each scc *)
    let sccLocalSol = MAP (λ nodes.
      nodes, compute_local_scc_sol nodes localSol
    ) scc in

    (* global sol for each scc *)
    let sccGlobalSol = MAP (λ (scc, sol).
      let globalSol = compute_global_scc_sol scc callGraphCoalesced sccLocalSol in
      scc, set_union sol globalSol
    ) sccLocalSol in

    (* global sol for each function, we use the fact that each function from a
    * given scc have the same sol. that the whole SCC *)
    let funSol = FOLDL (λ acc (nodes, sol).
      set_union acc (MAP (λ node. node, sol) nodes)
    ) [] sccGlobalSol in

    accessibleVars,
    accessibleFuns,
    set_union oldSol funSol
`

val compute_equations_exp_def = tDefine "compute_equations_exp"

  `(compute_equations_exp vars funs sol (Raise _ e) = compute_equations_exp vars funs sol e) ∧
   (compute_equations_exp vars funs sol (Handle _ e pes) =
      set_union (compute_equations_exp vars funs sol e) (compute_equations_pes vars funs sol pes)) ∧
   (compute_equations_exp _ _ sol (Lit _ _) = sol) ∧
   (compute_equations_exp vars funs sol (Con _ _ es) = compute_equations_exps vars funs sol es) ∧
   (compute_equations_exp _ _ sol (Var_local _ _) = sol) ∧
   (compute_equations_exp vars funs sol (Fun _ x e) = compute_equations_exp (set_add vars x) funs sol e (* we currently don't care about this as we either gave a name to anonymous functions previously, or handle them separately if they occurs just after a function definition *)) ∧
   (compute_equations_exp vars funs sol (App _ _ es) = compute_equations_exps vars funs sol es) ∧
   (compute_equations_exp vars funs sol (If _ e1 e2 e3) = set_union (compute_equations_exp vars funs sol e1)
      (set_union (compute_equations_exp vars funs sol e2) (compute_equations_exp vars funs sol e3))) ∧
   (compute_equations_exp vars funs sol (Mat _ e pes) =
      set_union (compute_equations_exp vars funs sol e) (compute_equations_pes vars funs sol pes)) ∧
   (compute_equations_exp vars funs sol (Let _ x e1 e2) =
      (* currently, we assume Let are not functions, if they're it's not important, but they won't be lambda lifted, we should add a flag allowing to change this, and eventually do some benchmarks to test if it's better or not. *)
      set_union (compute_equations_exp vars funs sol e1)
      (compute_equations_exp (case x of | SOME x => set_add vars x | _ => vars) funs sol e2)) ∧
   (compute_equations_exp vars funs sol (Letrec _ fs e) =
      let (vars, funs, sol) = compute_equations_funs vars funs sol fs in
      (* TODO, for each Letrec, we have to go recursively into its expression *)
      let subSol =
        FOLDL (λ acc (fName, vName, e). compute_equations_exp (set_add vars
        vName) funs sol e) empty_set fs in
      set_union subSol (compute_equations_exp vars funs sol e)) ∧
   (compute_equations_exps _ _ sol [] = sol) ∧
   (compute_equations_exps vars funs sol (h::t) =
      set_union (compute_equations_exp vars funs sol h) (compute_equations_exps vars funs sol t)) ∧
   (compute_equations_pe vars funs sol (p, e) = compute_equations_exp (set_union vars (compute_pattern_linkedID p)) funs sol e) ∧
   (compute_equations_pes _ _ sol [] = sol) ∧
   (compute_equations_pes vars funs sol (h::t) = set_union (compute_equations_pe vars funs sol h) (compute_equations_pes vars funs sol t))`

  cheat
(*
  (WF_REL_TAC `inv_image $< (λ x. (case x of
  | INL (_, _, _, e) => exp_size e
  | INR (INL (_, _, _, es)) => exp6_size es
  | INR (INR (INL (_, _, _, pe))) => exp5_size pe
  | INR (INR (INR (_, _, _, pes))) => exp3_size pes
  ))`)
*)

val compute_dec_sol_def = Define

  `(compute_dec_sol (Dlet e) = compute_equations_exp [] [] [] e) ∧
   (compute_dec_sol _ = empty_set)`

val compute_decs_sol_def = Define

  `(compute_decs_sol [] = empty_set) ∧
   (compute_decs_sol (h::t) = set_union (compute_dec_sol h) (compute_decs_sol t))`

val _ = export_theory ()

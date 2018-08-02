open
  preamble
  set_utilsTheory

val _ = new_theory "graph_utils"

val _ = type_abbrev ("graph", ``:('a, ('a list)) alist``)

val empty_graph_def = Define

  `empty_graph = []`

val graph_add_def = Define

  `(graph_add [] el =[el]) ∧
   (graph_add (h::t) el = if FST h = FST el then el::t else h::(set_add t el))`

val get_out_neighbours_def = Define

  `get_out_neighbours graph name = THE (ALOOKUP graph name)`

val get_in_neighbours_aux_def = Define

  `(get_in_neighbours_aux [] _ acc = acc) ∧
   (get_in_neighbours_aux ((name, neighbours)::t) el acc = get_in_neighbours_aux t el (if MEM el neighbours then name::acc else acc))`

val get_in_neighbours_def = Define

  `get_in_neighbours graph name = get_in_neighbours_aux graph name empty_set`

val get_scc_def = Define

  `(get_scc ([] : 'a list list) (node : 'a) : ('a list) = []) ∧
   (get_scc (h::t) node = if MEM node h then h else get_scc t node)`

val coalesce_aux_def = Define

  `coalesce_aux (nodes : 'a list) (scc : 'a list list) (g : 'a graph) : ('a list list) =
    FOLDL (λ acc node.
      let deps = FOLDL (λ acc n.
        if MEM n nodes then acc
        else set_add acc (get_scc scc n)
     ) [] (get_out_neighbours g node) in
     set_union acc deps
    ) [] nodes`

val coalesce_def = Define

  `coalesce (g : 'a graph) (scc : 'a list list) : ('a list graph) = MAP (λ nodes. nodes, coalesce_aux nodes scc g) scc`

val kosaraju_fst_def = Define

  `kosaraju_fst (graph : 'a graph) = let (l : 'a set) = empty_set in l, MAP (λ (node, _). node, F) graph`

val is_visited_def = Define

  `is_visited name visited = THE (ALOOKUP visited name)`

val set_visited_def = Define

  `set_visited name visited = MAP (λ (name', seen). name', (name = name') ∨ seen) visited`

val visit_def = tDefine "visit"

  `visit (g : 'a graph) ((name, neighbours) : ('a # ('a list))) (l : 'a list) (visited : ('a, bool) alist) : (('a list) # (('a, bool) alist)) =

   if is_visited name visited then l, visited
   else let visited = set_visited name visited in
    let (l, visited) = FOLDL (λ (l, visited) el. visit g (el, get_out_neighbours g el) l visited) (l, visited) neighbours in
    (name::l), visited`

cheat

val kosaraju_snd_def = Define

  `(kosaraju_snd g [] l _ = l) ∧
   (kosaraju_snd g (h::t) l visited = let (l, visited) = visit g h l visited in kosaraju_snd g t l visited)`

val is_assigned_def = Define

  `is_assigned name assigned = THE (ALOOKUP assigned name)`

val set_assigned_def = Define

  `set_assigned name assigned = MAP (λ (name', assigned'). name', (name = name') ∨ assigned') assigned`

val add_to_component_def = Define

  `add_to_component name root components =
    let already_root = FOLDL (λ acc el. (FST el = root) ∨ acc) F components in
    if already_root then MAP (λ (root', others). root', if root = root' then name::others else others) components
    else (root, [name])::components
`

val assign_def = tDefine "assign"

  `assign graph name root assigned components =
    if ¬is_assigned name assigned then
      let assigned = set_assigned name assigned in
      let components = add_to_component name root components in
      FOLDL (λ (assigned, components) neighbour.
        assign graph neighbour root assigned components
      ) (assigned, components) (get_in_neighbours graph name)
    else (assigned, components)`

  cheat

val kosaraju_trd_def = Define

  `(kosaraju_trd graph [] assigned components = components) ∧
   (kosaraju_trd graph (h::t) assigned components =
      let (assigned, components) = assign graph h h assigned components in
      kosaraju_trd graph t assigned components)`

val kosaraju_def = Define

  `kosaraju (graph : 'a graph) : ('a list list) =
    let (l, visited) = kosaraju_fst graph in
    let l = kosaraju_snd graph graph l visited in
    let assigned = MAP (λ name. name, F) l in
    let scc = kosaraju_trd graph l assigned [] in
    MAP (λ (_, components). components) scc`

val _ = export_theory ()

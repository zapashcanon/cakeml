open
  preamble

val _ = new_theory "mlapplist"

val _ = Datatype`
  app_list =
    Nil
  | List ('a list)
  | Append app_list app_list
`

val append_aux_def = Define`
  append_aux l aux =
    case l of
      Nil => aux
    | List xs => xs ++ aux
    | Append l1 l2 => append_aux l1 (append_aux l2)
`

val append_def = Define`
  append l = append_aux l []
`

val append_aux_thm = Q.store_thm("append_aux_thm",

  `∀ l xs. append_aux l xs = append_aux l [] ++ xs`,

     Induct
  \\ metis_tac [APPEND, APPEND_ASSOC, append_aux_def]
)

val append_thm = Q.store_thm("append_thm[simp]",

  `append (Append l1 l2) = append l1 ++ append l2
  ∧ append (List xs) = xs
  ∧ append Nil = []`

     fs [append_def, append_aux_def]
  \\ once_rewrite_tac [append_aux_thm]
  \\ fs []
)

val SmartAppend_def = Define`
  SmartAppend l1 l2 =
    case l1 l2 of
      Nil l | l Nil => l
    | l1 l2 => Append l1 l2
`

val _ = export_rewrites["SmartAppend_def"]

val SmartAppend_thm = Q.store_thm("SmartAppend_thm",

  `∀ l1 l2. SmartAppend l1 l2 =
  if l1 = Nil then l2
  else if l2 = Nil then l1
  else Append l1 l2`,

     Cases
  \\ Cases
  \\ rw []
)

val append_Smart_Append = Q.store_thm("append_SmartAppend[simp]",

  `append SmartAppend l1 l2 = append l1 ++ append l2`,

     rw [append_def, SmartAppend_thm, append_aux_def]
  \\ rw [Once append_aux_thm]
)

val _ = export_theory ()

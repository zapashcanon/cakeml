open preamble mlintTheory

val _ = new_theory "set_utils"

val _ = type_abbrev ("set", ``: 'a list``)

val empty_set_def = Define

  `empty_set = []`

val set_eq_def = Define

  `set_eq e1 e2 = ∀ x. MEM x e1 ⇔ MEM x e2`

val set_add_def = Define

  `(set_add [] el = [el]) ∧
   (set_add (h::t) el = h::(if h = el then t else set_add t el))`

val set_add_thm = Q.store_thm("set_add_thm",

  `∀ e el. MEM el (set_add e el)`,

   Induct
>> rw[set_add_def])

val set_add_included = Q.store_thm("set_add_thm",

  `∀ e1 el x. MEM x e1 ∨ x = el ⇔ MEM x (set_add e1 el)`,

   Induct >> rw[set_add_def]
>> EQ_TAC >> rw[]
>> res_tac >> fs[]
>> metis_tac[set_add_thm])

val set_rm_def = Define

  `(set_rm [] el = []) ∧
   (set_rm (h::t) el = if h = el then t else h::(set_rm t el))`

val set_union_def = Define

  `(set_union [] s = s) ∧
   (set_union (h::t) s = set_union t (set_add s h))`

val set_union_thm = Q.store_thm("set_union_thm",

  `∀ e1 e2 x. (MEM x e1 ∨ MEM x e2) ⇔ MEM x (set_union e1 e2)`,

  Induct
  >- ( Induct
    >> rw[set_union_def, set_add_def])
  >> rw[set_union_def, set_add_def]
  >> metis_tac[set_add_thm, set_add_included])

val set_big_union_def = Define

  `(set_big_union [] = []) ∧
   (set_big_union (h::t) = set_union h (set_big_union t))`

val set_membership_def = Define

  `(set_membership [] _ = F) ∧
   (set_membership (h::t) el = (h = el ∨ set_membership t el))`

val set_intersection_def = Define

  `(set_intersection _ [] = []) ∧
   (set_intersection [] _ = []) ∧
   (set_intersection (h::t) s = let res = set_intersection t s in if set_membership s h then h::res else res)`

val set_img_def = Define

  `(set_img [] f = []) ∧
   (set_img (h::t) f = set_add (set_img t f) (f h))`

val set_included_def = Define

  `set_included e1 e2 = ∀ x. MEM x e1 ⇒ MEM x e2`

val set_included_thm = Q.store_thm("set_included_thm",

  `∀ el e1 e2. set_included e1 (el::e1) ∧ set_included e1 (set_add e1 el) ∧ set_included e1 (set_union e1 e2)`,

  rw[set_included_def]
  >- ( Induct_on `e1` >> NTAC 2 (rw[set_add_def]))
  >- metis_tac[set_union_thm])

val set_eq_imp_incl = Q.store_thm("set_eq_imp_incl",

  `∀ e1 e2. set_eq e1 e2 ⇔ set_included e1 e2 ∧ set_included e2 e1`,

   rw[set_eq_def, set_included_def]
>> EQ_TAC
>> metis_tac[set_eq_def])

val set_eq_union_sing_app = Q.store_thm("set_eq_union_sing_app",

  `∀ e1 el. set_eq (set_union e1 [el]) (el::e1)`,

  Induct
>- rw[set_eq_def, set_union_def]
>- (
  rw[set_eq_def, set_union_def]
  >> EQ_TAC
  >> `MEM el [el]` by fs[]
  >> rw[]
  >> (
    fs[set_union_def, set_add_def]
    >> EVERY_CASE_TAC
    >> rw[]
    >> metis_tac[set_union_thm, set_add_thm, MEM])))



val set_add_non_empty = Q.store_thm("set_add_non_empty",

  `∀ el e. set_add e el ≠ empty_set`,

   Induct_on `e`
>> rw[set_add_def, empty_set_def])

val set_union_empty = Q.store_thm("set_union_empty",

  `∀ e1 e2. (set_union e1 e2 = empty_set) ⇒ (e1 = empty_set ∧ e2 = empty_set)`,

  `∀ e1 e2. (set_union e1 e2 = empty_set) ⇔ (e1 = empty_set ∧ e2 = empty_set)`
  suffices_by fs[] >>
   Induct_on `e1`
>> fs[set_union_def, set_add_non_empty]
>> rw[set_add_non_empty,empty_set_def])

val set_union_empty_id = Q.store_thm("set_union_empty_id",

  `∀ e1. set_eq (set_union e1 empty_set) e1`,

  Induct
  >> rw[set_eq_def, set_union_def, empty_set_def]
  >> fs[set_add_def]
  >> EQ_TAC >> rw[]
  >- (imp_res_tac set_union_thm >> fs[])
  >> `MEM h [h]` by fs[]
  >> imp_res_tac set_union_thm >> fs[])

val set_union_commut = Q.store_thm("set_union_commut",

  `∀ e1 e2. set_eq (set_union e1 e2) (set_union e2 e1)`,

  Induct
  >-( Induct
    >- rw[set_union_def, set_eq_def]
    >- ( rw[]
      >> fs[set_union_def,set_union_empty_id,empty_set_def, set_add_thm, set_add_def]
      >> rw[set_eq_def]
      >> `MEM h [h]` by fs[]
      >> imp_res_tac set_union_thm
      >> EQ_TAC
      >> rw[]
      >> fs[]
      >- metis_tac[set_union_thm]
      >> imp_res_tac set_union_thm
      >> fs[]))
  >-( Induct_on `e2`
    >> rw[]
    >- ( fs[set_union_def, set_eq_def,set_add_def]
      >> rw[]
      >> EQ_TAC
      >> rw[]
      >> fs[]
      >> `MEM h [h]` by fs[]
      >> imp_res_tac set_union_thm
      >> fs[])
    >- (
      cheat
      (* TODO *)
    )))

val _ = export_theory ()

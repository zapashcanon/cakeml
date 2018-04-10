open  preamble mlintTheory

val _ = new_theory "set_utils"

val _ = type_abbrev ("set", ``: 'a list``)

val empty_set_def = Define

  `empty_set = []`

val set_add_def = Define

  `(set_add [] el =[el]) ∧
   (set_add (h::t) el = h::(if h = el then t else set_add t el))`

val set_rm_def = Define

  `(set_rm [] el = []) ∧
   (set_rm (h::t) el = if h = el then t else h::(set_rm t el))`

val set_union_def = Define

  `(set_union [] s = s) ∧
   (set_union s [] = s) ∧
   (set_union (h::t) s = set_union t (set_add s h))`

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

val _ = export_theory ()

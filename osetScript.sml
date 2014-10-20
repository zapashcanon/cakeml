open HolKernel boolLib bossLib BasicProvers Parse;
open optionTheory pairTheory stringTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open balanced_mapTheory;
open lcsymtacs;

val _ = new_theory "oset";

val _ = temp_tight_equality ();

(* oset for ordered set *)
val _ = type_abbrev ("oset", ``:('a,unit) balanced_map``);
val _ = overload_on ("good_oset", ``(\cmp s. good_cmp cmp ∧ invariant cmp s):('a -> 'a -> comparison) -> 'a oset -> bool``);
val _ = overload_on ("oin", ``(\cmp v s. lookup cmp v s ≠ NONE):('a -> 'a -> comparison) -> 'a -> 'a oset -> bool``);
val _ = overload_on ("oinsert", ``(\cmp v s. insert cmp v () s):('a -> 'a -> comparison) -> 'a -> 'a oset -> 'a oset``);
val _ = overload_on ("odelete", ``(\cmp s v. delete cmp v s):('a -> 'a -> comparison) -> 'a oset -> 'a -> 'a oset``);
val _ = overload_on ("ounion", ``(\cmp s1 s2. union cmp s1 s2):('a -> 'a -> comparison) -> 'a oset -> 'a oset -> 'a oset``);
val _ = overload_on ("oimage", ``(\cmp f s. map_keys cmp f s):('b -> 'b -> comparison) -> ('a -> 'b) -> 'a oset -> 'b oset``);

val good_oset_oinsert = Q.store_thm ("good_oset_oinsert",
`!cmp s x. good_oset cmp s ⇒ good_oset cmp (oinsert cmp x s)`,
 rw [] >>
 metis_tac [insert_thm]);

val good_oset_odelete = Q.store_thm ("good_oset_odelete",
`!cmp s x. good_oset cmp s ⇒ good_oset cmp (odelete cmp s x)`,
 rw [] >>
 metis_tac [delete_thm]);

val good_oset_ounion = Q.store_thm ("good_oset_ounion",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ good_oset cmp (ounion cmp s1 s2)`,
 rw [] >>
 metis_tac [union_thm]);

val good_oset_oimage = Q.store_thm ("good_oset_oimage",
`!cmp f s. good_cmp cmp ⇒ good_oset cmp (oimage cmp f s)`,
 cheat);

val oin_oinsert = Q.store_thm ("oin_oinsert",
`∀cmp x y s. good_oset cmp s ⇒ (oin cmp x (oinsert cmp y s) ⇔ cmp x y = Equal ∨ oin cmp x s)`,
 rw [] >>
 imp_res_tac insert_thm >>
 last_x_assum (qspecl_then [`()`, `y`] assume_tac) >>
 imp_res_tac lookup_thm >>
 rw [FLOOKUP_UPDATE] >>
 rfs [key_set_eq] >>
 metis_tac [good_cmp_def]);

val oin_odelete = Q.store_thm ("oin_odelete",
`!cmp s x y. good_oset cmp s ⇒ (oin cmp x (odelete cmp s y) ⇔ oin cmp x s ∧ cmp x y ≠ Equal)`,
 rw [] >>
 imp_res_tac good_oset_odelete >>
 pop_assum (qspecl_then [`y`] assume_tac) >>
 imp_res_tac delete_thm >>
 imp_res_tac lookup_thm >>
 rw [FLOOKUP_DRESTRICT, key_set_eq] >>
 eq_tac >>
 rw [] >>
 fs [FLOOKUP_DEF]);

val oin_ounion = Q.store_thm ("oin_ounion",
`!cmp x s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (oin cmp x (ounion cmp s1 s2) ⇔ oin cmp x s1 ∨ oin cmp x s2)`,
 rw [] >>
 `good_oset cmp (ounion cmp s1 s2)` by metis_tac [good_oset_ounion] >>
 imp_res_tac lookup_thm >>
 rw [] >>
 `to_fmap cmp (union cmp s1 s2) = to_fmap cmp s1 ⊌ to_fmap cmp s2` by metis_tac [union_thm] >>
 rw [FLOOKUP_FUNION] >>
 EVERY_CASE_TAC);

val oin_oimage = Q.store_thm ("oin_oimage",
`!cmp y s f. oin cmp y (oimage cmp f s) ⇔ ?x. cmp y (f x) = Equal ∧ oin cmp x s`,
 cheat);

val _ = export_theory ();

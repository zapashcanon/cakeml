open HolKernel boolLib bossLib BasicProvers Parse;
open optionTheory pairTheory stringTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open balanced_mapTheory comparisonTheory;
open lcsymtacs;

val _ = new_theory "oset";

val _ = temp_tight_equality ();

(* oset for ordered set *)
val _ = type_abbrev ("oset", ``:('a,unit) balanced_map``);

(* Basic definitions, that correspond directly to balanced tree operations *)
val _ = overload_on ("good_oset", ``(\cmp s. good_cmp cmp ∧ invariant cmp s):('a -> 'a -> comparison) -> 'a oset -> bool``);
val _ = overload_on ("oempty", ``empty:'a oset``);
val _ = overload_on ("osingleton", ``(\v. singleton v ()):'a -> 'a oset``);
val _ = overload_on ("oin", ``(\cmp v s. member cmp v s):('a -> 'a -> comparison) -> 'a -> 'a oset -> bool``);
val _ = overload_on ("oinsert", ``(\cmp v s. insert cmp v () s):('a -> 'a -> comparison) -> 'a -> 'a oset -> 'a oset``);
val _ = overload_on ("odelete", ``(\cmp s v. delete cmp v s):('a -> 'a -> comparison) -> 'a oset -> 'a -> 'a oset``);
val _ = overload_on ("ounion", ``(\cmp s1 s2. union cmp s1 s2):('a -> 'a -> comparison) -> 'a oset -> 'a oset -> 'a oset``);
val _ = overload_on ("oimage", ``(\cmp f s. map_keys cmp f s):('b -> 'b -> comparison) -> ('a -> 'b) -> 'a oset -> 'b oset``);
val _ = overload_on ("osubset", ``(\cmp s1 s2. isSubmapOf cmp s1 s2):('a -> 'a -> comparison) -> 'a oset -> 'a oset -> bool``);
val _ = overload_on ("ocompare", ``(\cmp s1 s2. compare (\(x,y) (x',y'). cmp x x') s1 s2):('a -> 'a -> comparison) -> 'a oset -> 'a oset -> comparison``);

(* Definitions of derived concepts *)

val oforall_def = Define `
oforall f s ⇔ oin bool_cmp F (oimage bool_cmp f s) = F`;

val oexists_def = Define `
oexists f s ⇔ oin bool_cmp T (oimage bool_cmp f s) = T`;

(* operations preserve good_set *)

val good_oset_oempty = Q.store_thm ("good_oset_oempty",
`!cmp. good_cmp cmp ⇒ good_oset cmp oempty`,
 rw [empty_thm]);

val good_oset_singleton = Q.store_thm ("good_oset_singleton",
`!cmp x. good_cmp cmp ⇒ good_oset cmp (osingleton x)`,
 rw [singleton_thm]);

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

val good_cmp_ocompare = Q.store_thm ("good_cmp_ocompare",
`!cmp f s. good_cmp cmp ⇒ good_cmp (ocompare cmp)`,
 rw [] >>
 `good_cmp (\(x,y:unit) (x',y':unit). cmp x x')` 
            by (rw [good_cmp_def, LAMBDA_PROD, FORALL_PROD] >>
                metis_tac [good_cmp_def]) >>
 imp_res_tac compare_thm >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 pop_assum (fn _ => all_tac) >>
 rw [] >>
 rw [good_cmp_def] >>
 metis_tac [good_cmp_def]);

(* How oin interacts with other operations *)

val oin_oempty = Q.store_thm ("oin_oinsert",
`!cmp x. oin cmp x oempty = F`,
 rw [empty_def, member_def]); 

val oin_singleton = Q.store_thm ("oin_singleton",
`∀cmp x y. oin cmp x (osingleton y) ⇔ cmp x y = Equal`,
 rw [member_def, singleton_def] >>
 EVERY_CASE_TAC);

val oin_oinsert = Q.store_thm ("oin_oinsert",
`∀cmp x y s. good_oset cmp s ⇒ (oin cmp x (oinsert cmp y s) ⇔ cmp x y = Equal ∨ oin cmp x s)`,
 rw [] >>
 imp_res_tac insert_thm >>
 last_x_assum (qspecl_then [`()`, `y`] assume_tac) >>
 imp_res_tac member_thm >>
 rw [FLOOKUP_UPDATE] >>
 rfs [key_set_eq] >>
 metis_tac [good_cmp_def]);

val oin_odelete = Q.store_thm ("oin_odelete",
`!cmp s x y. good_oset cmp s ⇒ (oin cmp x (odelete cmp s y) ⇔ oin cmp x s ∧ cmp x y ≠ Equal)`,
 rw [] >>
 imp_res_tac good_oset_odelete >>
 pop_assum (qspecl_then [`y`] assume_tac) >>
 imp_res_tac delete_thm >>
 imp_res_tac member_thm >>
 rw [FDOM_DRESTRICT, key_set_eq] >>
 eq_tac >>
 rw []);

val oin_ounion = Q.store_thm ("oin_ounion",
`!cmp x s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (oin cmp x (ounion cmp s1 s2) ⇔ oin cmp x s1 ∨ oin cmp x s2)`,
 rw [] >>
 `good_oset cmp (ounion cmp s1 s2)` by metis_tac [good_oset_ounion] >>
 imp_res_tac member_thm >>
 rw [] >>
 `to_fmap cmp (union cmp s1 s2) = to_fmap cmp s1 ⊌ to_fmap cmp s2` by metis_tac [union_thm] >>
 rw []);

val oin_oimage = Q.store_thm ("oin_oimage",
`!cmp y s f. good_cmp cmp ⇒ (oin cmp y (oimage cmp f s) ⇔ ?x. cmp y (f x) = Equal ∧ oin cmp x s)`,
 cheat);

val osubset_thm = Q.store_thm ("osubset_thm",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (osubset cmp s1 s2 ⇔ (!x. oin cmp x s1 ⇒ oin cmp x s2))`,
 cheat);

val oextension = Q.store_thm ("oextension",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (ocompare cmp s1 s2 = Equal ⇔ (!x. oin cmp x s1 ⇔ oin cmp x s2))`,
 cheat);

val _ = export_theory ();

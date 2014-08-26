(*Generated by Lem from semanticPrimitives.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory lem_list_extraTheory lem_stringTheory lem_string_extraTheory libTheory astTheory;

val _ = numLib.prefer_num();



val _ = new_theory "semanticPrimitives"

(*open import Pervasives*)
(*import List_extra*)
(*import String*)
(*import String_extra*)
(*open import Lib*)
(*open import Ast*)

(* The type that a constructor builds is either a named datatype or an exception.
 * For exceptions, we also keep the module that the exception was declared in. *)
val _ = Hol_datatype `
 tid_or_exn = 
    TypeId of typeN id
  | TypeExn of conN id`;


(*val type_defs_to_new_tdecs : maybe modN -> type_def -> set tid_or_exn*)
val _ = Define `
 (type_defs_to_new_tdecs mn tdefs =  
(LIST_TO_SET (MAP (\ (tvs,tn,ctors) .  TypeId (mk_id mn tn)) tdefs)))`;


(* Maps each constructor to its arity and which type it is from *)
val _ = type_abbrev( "flat_envC" , ``: (conN, (num # tid_or_exn)) env``);
val _ = type_abbrev( "envC" , ``: (modN, flat_envC) env # flat_envC``);

(*val merge_envC : envC -> envC -> envC*)
val _ = Define `
 (merge_envC (mcenv1,cenv1) (mcenv2,cenv2) = 
  (merge mcenv1 mcenv2, merge cenv1 cenv2))`;


(* Value forms *)
val _ = Hol_datatype `
 v =
    Litv of lit
  (* Constructor application. *)
  | Conv of  (conN # tid_or_exn)option => v list 
  (* Function closures
     The environment is used for the free variables in the function *)
  | Closure of ( (modN, ( (varN, v)env))env # envC # (varN, v) env) => varN => exp
  (* Function closure for recursive functions
   * See Closure and Letrec above
   * The last variable name indicates which function from the mutually
   * recursive bundle this closure value represents *)
  | Recclosure of ( (modN, ( (varN, v)env))env # envC # (varN, v) env) => (varN # varN # exp) list => varN
  | Loc of num
  | Vectorv of v list`;


val _ = type_abbrev( "envE" , ``: (varN, v) env``);

(* The bindings of a module *)
val _ = type_abbrev( "envM" , ``: (modN, envE) env``);

val _ = type_abbrev( "all_env" , ``: envM # envC # envE``);

val _ = Define `
 (all_env_to_menv (menv,cenv,env) = menv)`;

val _ = Define `
 (all_env_to_cenv (menv,cenv,env) = cenv)`;

val _ = Define `
 (all_env_to_env (menv,cenv,env) = env)`;


(* The result of evaluation *)
val _ = Hol_datatype `
 error_result =
    Rtype_error
  | Rraise of 'a (* Should only be a value of type exn *)
  | Rtimeout_error`;


val _ = Hol_datatype `
 result =
    Rval of 'a
  | Rerr of 'b error_result`;


(* Stores *)
val _ = Hol_datatype `
 store_v = 
  (* A ref cell *) 
    Refv of 'a 
  (* A byte array *)
  | W8array of word8 list 
  (* An array of values *) 
  | Varray of 'a list`;


(*val store_v_same_type : forall 'a. store_v 'a -> store_v 'a -> bool*)
val _ = Define `
 (store_v_same_type v1 v2 =  
((case (v1,v2) of
    (Refv _, Refv _) => T
  | (W8array _,W8array _) => T
  | (Varray _,Varray _) => T
  | _ => F
  )))`;


(* The nth item in the list is the value at location n *)
val _ = type_abbrev((*  'a *) "store" , ``: ( 'a store_v) list``);

(*val empty_store : forall 'a. store 'a*)
val _ = Define `
 (empty_store = ([]))`;


(*val store_lookup : forall 'a. nat -> store 'a -> maybe (store_v 'a)*)
val _ = Define `
 (store_lookup l st =  
(if l < LENGTH st then
    SOME (EL l st)
  else
    NONE))`;


(*val store_alloc : forall 'a. store_v 'a -> store 'a -> store 'a * nat*)
val _ = Define `
 (store_alloc v st =
  ((st ++ [v]), LENGTH st))`;


(*val store_assign : forall 'a. nat -> store_v 'a -> store 'a -> maybe (store 'a)*)
val _ = Define `
 (store_assign n v st =  
(if (n < LENGTH st) /\
     store_v_same_type (EL n st) v
  then
    SOME (LUPDATE v n st)
  else
    NONE))`;


(*val lookup_var_id : id varN -> all_env -> maybe v*)
val _ = Define `
 (lookup_var_id id (menv,cenv,env) =  
((case id of
      Short x => lookup x env
    | Long x y =>
        (case lookup x menv of
            NONE => NONE
          | SOME env => lookup y env
        )
  )))`;


(*val lookup_con_id : forall 'a. id conN -> env modN (env conN 'a) * env conN 'a -> maybe 'a*)
val _ = Define `
 (lookup_con_id id (mcenv,cenv) =  
((case id of
      Short x => lookup x cenv
    | Long x y =>
        (case lookup x mcenv of
            NONE => NONE
          | SOME cenv => lookup y cenv
        )
  )))`;


(* Other primitives *)
(* Check that a constructor is properly applied *)
(*val do_con_check : envC -> maybe (id conN) -> nat -> bool*)
val _ = Define `
 (do_con_check cenv n_opt l =  
((case n_opt of
      NONE => T
    | SOME n =>
        (case lookup_con_id n cenv of
            NONE => F
          | SOME (l',ns) => l = l'
        )
  )))`;


(*val build_conv : envC -> maybe (id conN) -> list v -> maybe v*)
val _ = Define `
 (build_conv envC cn vs =  
((case cn of
      NONE => 
        SOME (Conv NONE vs)
    | SOME id => 
        (case lookup_con_id id envC of
            NONE => NONE
          | SOME (len,t) => SOME (Conv (SOME (id_to_n id, t)) vs)
        )
  )))`;


(*val lit_same_type : lit -> lit -> bool*)
val _ = Define `
 (lit_same_type l1 l2 =  
((case (l1,l2) of
      (IntLit _, IntLit _) => T
    | (StrLit _, StrLit _) => T
    | (Bool _, Bool _) => T
    | (Unit, Unit) => T
    | (Word8 _, Word8 _) => T
    | _ => F
  )))`;


val _ = Hol_datatype `
 match_result =
    No_match
  | Match_type_error
  | Match of 'a`;


(*val same_tid : tid_or_exn -> tid_or_exn -> bool*)
 val _ = Define `
 (same_tid (TypeId tn1) (TypeId tn2) = (tn1 = tn2))
/\ (same_tid (TypeExn _) (TypeExn _) = T)
/\ (same_tid _ _ = F)`;


(*val same_ctor : conN * tid_or_exn -> conN * tid_or_exn -> bool*)
 val _ = Define `
 (same_ctor (cn1, TypeExn mn1) (cn2, TypeExn mn2) = ((cn1 = cn2) /\ (mn1 = mn2)))
/\ (same_ctor (cn1, _) (cn2, _) = (cn1 = cn2))`;


(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)
(*val pmatch : envC -> store v -> pat -> v -> envE -> match_result envE*)
 val pmatch_defn = Hol_defn "pmatch" `

(pmatch envC s (Pvar x) v' env = (Match (bind x v' env)))
/\
(pmatch envC s (Plit l) (Litv l') env =  
(if l = l' then
    Match env
  else if lit_same_type l l' then
    No_match
  else
    Match_type_error))
/\
(pmatch envC s (Pcon (SOME n) ps) (Conv (SOME (n', t')) vs) env =  
((case lookup_con_id n envC of
      SOME (l, t)=>
        if same_tid t t' /\ (LENGTH ps = l) then
          if same_ctor (id_to_n n, t) (n',t') then
            pmatch_list envC s ps vs env
          else
            No_match
        else
          Match_type_error
    | _ => Match_type_error
  )))
/\
(pmatch envC s (Pcon NONE ps) (Conv NONE vs) env =  
(if LENGTH ps = LENGTH vs then
    pmatch_list envC s ps vs env
  else
    Match_type_error))
/\
(pmatch envC s (Pref p) (Loc lnum) env =  
((case store_lookup lnum s of
      SOME (Refv v) => pmatch envC s p v env
    | SOME _ => Match_type_error
    | NONE => Match_type_error
  )))
/\
(pmatch envC _ _ _ env = Match_type_error)
/\
(pmatch_list envC s [] [] env = (Match env))
/\
(pmatch_list envC s (p::ps) (v::vs) env =  
((case pmatch envC s p v env of
      No_match => No_match
    | Match_type_error => Match_type_error
    | Match env' => pmatch_list envC s ps vs env'
  )))
/\
(pmatch_list envC s _ _ env = Match_type_error)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn pmatch_defn;

(* Bind each function of a mutually recursive set of functions to its closure *)
(*val build_rec_env : list (varN * varN * exp) -> all_env -> envE -> envE*)
val _ = Define `
 (build_rec_env funs cl_env add_to_env =  
(FOLDR 
    (\ (f,x,e) env' .  bind f (Recclosure cl_env funs f) env') 
    add_to_env 
    funs))`;


(* Lookup in the list of mutually recursive functions *)
(*val find_recfun : forall 'a 'b. varN -> list (varN * 'a * 'b) -> maybe ('a * 'b)*)
 val _ = Define `
 (find_recfun n funs =  
((case funs of
      [] => NONE
    | (f,x,e) :: funs =>
        if f = n then
          SOME (x,e)
        else
          find_recfun n funs
  )))`;


(* Check whether a value contains a closure, but don't indirect through the store *)
(*val contains_closure : v -> bool*)
 val contains_closure_defn = Hol_defn "contains_closure" `

(contains_closure (Litv l) = F)
/\
(contains_closure (Conv cn vs) = (EXISTS contains_closure vs))
/\
(contains_closure (Closure env n e) = T)
/\
(contains_closure (Recclosure env funs n) = T)
/\
(contains_closure (Loc n) = F)
/\
(contains_closure (Vectorv vs) = (EXISTS contains_closure vs))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn contains_closure_defn;

val _ = Hol_datatype `
 eq_result = 
    Eq_val of bool
  | Eq_closure
  | Eq_type_error`;


(*val do_eq : v -> v -> eq_result*)
 val do_eq_defn = Hol_defn "do_eq" `

(do_eq (Litv l1) (Litv l2) =  
(if lit_same_type l1 l2 then Eq_val (l1 = l2)
  else Eq_type_error))
/\
(do_eq (Loc l1) (Loc l2) = (Eq_val (l1 = l2)))
/\
(do_eq (Conv cn1 vs1) (Conv cn2 vs2) =  
(if (cn1 = cn2) /\ (LENGTH vs1 = LENGTH vs2) then
    do_eq_list vs1 vs2
  else
    Eq_val F))
/\
(do_eq (Vectorv vs1) (Vectorv vs2) =  
(if LENGTH vs1 = LENGTH vs2 then
    do_eq_list vs1 vs2
  else
    Eq_val F))
/\
(do_eq (Closure _ _ _) (Closure _ _ _) = Eq_closure)
/\
(do_eq (Closure _ _ _) (Recclosure _ _ _) = Eq_closure)
/\
(do_eq (Recclosure _ _ _) (Closure _ _ _) = Eq_closure)
/\
(do_eq (Recclosure _ _ _) (Recclosure _ _ _) = Eq_closure)
/\
(do_eq _ _ = Eq_type_error)
/\
(do_eq_list [] [] = (Eq_val T))
/\
(do_eq_list (v1::vs1) (v2::vs2) =  
 ((case do_eq v1 v2 of
      Eq_closure => Eq_closure
    | Eq_type_error => Eq_type_error
    | Eq_val r => 
        if ~ r then
          Eq_val F
        else
          do_eq_list vs1 vs2
  )))
/\
(do_eq_list _ _ = (Eq_val F))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn do_eq_defn;

(*val prim_exn : conN -> v*)
val _ = Define `
 (prim_exn cn = (Conv (SOME (cn, TypeExn (Short cn))) []))`;


(* Do an application *)
(*val do_opapp : list v -> maybe (all_env * exp)*)
val _ = Define `
 (do_opapp vs =  
((case vs of
    [Closure (menv, cenv, env) n e; v] =>
      SOME ((menv, cenv, bind n v env), e)
  | [Recclosure (menv, cenv, env) funs n; v] =>
      if ALL_DISTINCT (MAP (\ (f,x,e) .  f) funs) then
        (case find_recfun n funs of
            SOME (n,e) => SOME ((menv, cenv, bind n v (build_rec_env funs (menv, cenv, env) env)), e)
          | NONE => NONE
        )
      else
        NONE
  | _ => NONE
  )))`;


(* If a value represents a list, get that list. Otherwise return Nothing *)
(*val v_to_list : v -> maybe (list v)*)
 val v_to_list_defn = Hol_defn "v_to_list" `
 (v_to_list (Conv (SOME (cn, TypeId (Short tn))) []) =  
 (if (cn = "nil") /\ (tn = "list") then
    SOME []
  else
    NONE))
/\ (v_to_list (Conv (SOME (cn,TypeId (Short tn))) [v1;v2]) =  
(if (cn = "::")  /\ (tn = "list") then
    (case v_to_list v2 of
        SOME vs => SOME (v1::vs)
      | NONE => NONE
    )
  else
    NONE))
/\ (v_to_list _ = NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn v_to_list_defn;

(*val opn_lookup : opn -> integer -> integer -> integer*)
val _ = Define `
 (opn_lookup n : int -> int -> int = ((case n of
    Plus => (+)
  | Minus => (-)
  | Times => ( * )
  | Divide => (/)
  | Modulo => (%)
)))`;


(*val opb_lookup : opb -> integer -> integer -> bool*)
val _ = Define `
 (opb_lookup n : int -> int -> bool = ((case n of
    Lt => (<)
  | Gt => (>)
  | Leq => (<=)
  | Geq => (>=)
)))`;


(*val do_app : store v -> op -> list v -> maybe (store v * result v v)*)
val _ = Define `
 (do_app s op vs =  
((case (op, vs) of
      (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 =( 0 : int)) then
          SOME (s, Rerr (Rraise (prim_exn "Div")))
        else
          SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME (s, Rval (Litv (Bool (opb_lookup op n1 n2))))
    | (Equality, [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_closure => SOME (s, Rerr (Rraise (prim_exn "Eq")))
          | Eq_val b => SOME (s, Rval (Litv (Bool b)))
        )
    | (Opassign, [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s of
            SOME st => SOME (st, Rval (Litv Unit))
          | NONE => NONE
        )
    | (Opref, [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME (s', Rval (Loc n))
    | (Opderef, [Loc n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME (s,Rval v)
          | _ => NONE
        )
    | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME (s, Rerr (Rraise (prim_exn "Subscript")))
        else
          let (s',lnum) =            
(store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s)
          in 
            SOME (s', Rval (Loc lnum))
    | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME (s, Rerr (Rraise (prim_exn "Subscript")))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH ws then
                    SOME (s, Rerr (Rraise (prim_exn "Subscript")))
                  else 
                    SOME (s, Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8length, [Loc n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME (s, Rerr (Rraise (prim_exn "Subscript")))
            else 
              let n = (Num (ABS ( i))) in
                if n >= LENGTH ws then
                  SOME (s, Rerr (Rraise (prim_exn "Subscript")))
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Litv Unit))
                  )
        | _ => NONE
      )
    | (VfromList, [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME (s, Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rerr (Rraise (prim_exn "Subscript")))
        else
          let n = (Num (ABS ( i))) in
            if n >= LENGTH vs then
              SOME (s, Rerr (Rraise (prim_exn "Subscript")))
            else 
              SOME (s, Rval (EL n vs))
    | (Vlength, [Vectorv vs]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Aalloc, [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (s, Rerr (Rraise (prim_exn "Subscript")))
        else
          let (s',lnum) =            
(store_alloc (Varray (REPLICATE (Num (ABS ( n))) v)) s)
          in 
            SOME (s', Rval (Loc lnum))
    | (Asub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME (s, Rerr (Rraise (prim_exn "Subscript")))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH vs then
                    SOME (s, Rerr (Rraise (prim_exn "Subscript")))
                  else 
                    SOME (s, Rval (EL n vs))
          | _ => NONE
        )
    | (Alength, [Loc n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME (s, Rerr (Rraise (prim_exn "Subscript")))
            else 
              let n = (Num (ABS ( i))) in
                if n >= LENGTH vs then
                  SOME (s, Rerr (Rraise (prim_exn "Subscript")))
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Litv Unit))
                  )
        | _ => NONE
      )
    | _ => NONE
  )))`;


(* Do a logical operation *)
(*val do_log : lop -> v -> exp -> maybe exp*)
val _ = Define `
 (do_log l v e =  
((case (l, v) of
      (And, Litv (Bool T)) => SOME e
    | (Or, Litv (Bool F)) => SOME e
    | (_, Litv (Bool b)) => SOME (Lit (Bool b))
    | _ => NONE
  )))`;


(* Do an if-then-else *)
(*val do_if : v -> exp -> exp -> maybe exp*)
val _ = Define `
 (do_if v e1 e2 =  
(if v = Litv (Bool T) then
    SOME e1
  else if v = Litv (Bool F) then
    SOME e2
  else
    NONE))`;


(* Semantic helpers for definitions *)

(* Build a constructor environment for the type definition tds *)
(*val build_tdefs : maybe modN -> list (list tvarN * typeN * list (conN * list t)) -> flat_envC*)
val _ = Define `
 (build_tdefs mn tds =  
(REVERSE
    (FLAT
      (MAP
        (\ (tvs, tn, condefs) . 
           MAP
             (\ (conN, ts) . 
                (conN, (LENGTH ts, TypeId (mk_id mn tn))))
             condefs)
        tds))))`;


(* Checks that no constructor is defined twice in a type *)
(*val check_dup_ctors : list (list tvarN * typeN * list (conN * list t)) -> bool*)
val _ = Define `
 (check_dup_ctors tds =  
(ALL_DISTINCT (let x2 = 
  ([]) in  FOLDR
   (\(tvs, tn, condefs) x2 .  FOLDR
                                (\(n, ts) x2 .  if T then n :: x2 else x2) 
                              x2 condefs) x2 tds)))`;


(*val combine_dec_result : forall 'a 'b 'c. env 'a 'b -> result (env 'a 'b) 'c -> result (env 'a 'b) 'c*)
val _ = Define `
 (combine_dec_result env r =  
((case r of
      Rerr e => Rerr e
    | Rval env' => Rval (merge env' env)
  )))`;


(*val combine_mod_result : forall 'a 'b 'c 'd 'e. env 'a 'b -> env 'c 'd -> result (env 'a 'b * env 'c 'd) 'e -> result (env 'a 'b * env 'c 'd) 'e*)
val _ = Define `
 (combine_mod_result menv env r =  
((case r of
      Rerr e => Rerr e
    | Rval (menv',env') => Rval (merge menv' menv, merge env' env)
  )))`;


val _ = Define `
 (remove_count ((count,store),tdecls,mods) = (store,tdecls,mods))`;


(* conversions to strings *)

 val _ = Define `

(id_to_string (Short s) = s)
/\
(id_to_string (Long x y) = (STRCAT x(STRCAT"."y)))`;


val _ = Define `
 (tc_to_string tc =  
((case tc of
    TC_name id => id_to_string id
  | TC_int => "<int>"
  | TC_string => "<string>"
  | TC_bool => "<bool>"
  | TC_unit => "<unit>"
  | TC_ref => "<ref>"
  | TC_word8 => "<word8>"
  | TC_word8array => "<word8array>"
  | TC_exn => "<exn>"
  | TC_vector => "<vector>"
  | TC_array => "<array>"
  )))`;


(*val int_to_string : integer -> string*)
val _ = Define `
 (int_to_string z =  
(if z <( 0 : int) then STRCAT"~"(num_to_dec_string (Num (ABS (~ z))))
  else num_to_dec_string (Num (ABS z))))`;



 val string_escape_defn = Hol_defn "string_escape" `

(string_escape [] = "")
/\
(string_escape (c::cs) =  
  
(STRCAT(if c = #"\n" then "\\n"
   else if c = #"\t" then "\\t"
   else if c = #"\\" then "\\\\"
   else IMPLODE [c])(string_escape cs)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn string_escape_defn;

val _ = Define `
 (string_to_string s =  
(STRCAT"\""(STRCAT(string_escape (EXPLODE s))"\"")))`;

val _ = export_theory()


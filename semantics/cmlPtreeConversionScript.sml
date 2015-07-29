open HolKernel Parse boolLib bossLib

open gramTheory tokenUtilsTheory astTheory

open monadsyntax lcsymtacs

open errorStateMonadTheory

val _ = new_theory "cmlPtreeConversion"

(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

(* Use of parsing-heap means that this theory is secretly a descendent of
   pegexecTheory, where 'nt' is a constructor name.

   This is a disgusting failing of our theory mechanism.  *)
val _ = hide "nt"

(* handling constructor arities gets very complicated when "open" is
   implemented *)
val _ = Datatype`PCstate0 = <| fixities : string |-> num option ;
                               ctr_arities : string id |-> num |>`
(* recording a fixity of NONE is what you have to do to represent an
   explicit nonfix declaration *)

val _ = temp_type_abbrev
            ("M", ``:PCstate0 list -> ('a # PCstate0 list) option``)

val empty_PCstate0 = Define`
  empty_PCstate0 = <| fixities := FEMPTY ; ctr_arities := FEMPTY |>
`;

val mpushPC_scope_def = Define`
  mpushPC_scope : unit M = λpcs. SOME ((), empty_PCstate0 :: pcs)
`;

val fixity_lookup_def = Define`
  fixity_lookup nm pcs =
    case pcs of
        [] => NONE
      | pc0 :: rest =>
          case FLOOKUP pc0.fixities nm of
              NONE => fixity_lookup nm rest
            | SOME NONE => NONE
            | SOME r => r
`;


(* mfixity_lookup : string -> num M
    'fails' if the string has no fixity, even though it is perfectly
    reasonable for a string to be nonfix.
*)
val mfixity_lookup_def = Define`
  mfixity_lookup nm : num M =
    λpcs. OPTION_MAP (λr. (r, pcs)) (fixity_lookup nm pcs)
`

val mFUPD_HD_def = Define`
  mFUPD_HD f pcs =
    case pcs of
        [] => NONE
      | h :: t => SOME((), f h :: t)
`

(* msetfix : string -> num option -> unit M *)
val msetfix_def = Define`
  msetfix nm fix : unit M =
    mFUPD_HD (λs0. s0 with fixities updated_by (λfm. fm |+ (nm, fix)))
`

(* mpop_anonscope : unit M *)
val mpop_anonscope_def = Define`
  mpopscope : unit M = λpcs.
    case pcs of
      [] => NONE
    | _ :: t => SOME((), t)
`

val mpop_namedscope_def = Define`
  mpop_namedscope (s : string) : unit M = λpcs.
    case pcs of
      [] => NONE
    | [_] => NONE
    | curr :: next :: rest => SOME((), next :: rest)
`;
(* needs to be adjusted so that constructors (only) declared in the current
   scope get recorded in the next level up with the given name as a prefix.

   Does nothing different at this stage, when I expect just to be handling
   fixities (which are handled in a non-exportable way).
 *)


(* ----------------------------------------------------------------------
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------- *)

val _ = overload_on ("monad_bind", ``errorStateMonad$BIND``)
val _ = overload_on ("monad_unitbind", ``errorStateMonad$IGNORE_BIND``)
val _ = temp_overload_on ("return", ``errorStateMonad$UNIT``)

val _ = overload_on ("assert", ``errorStateMonad$ES_GUARD``)
val _ = overload_on ("++", ``errorStateMonad$ES_CHOICE``)
val _ = overload_on ("lift", ``errorStateMonad$MMAP``)
val _ = overload_on ("lift2", ``errorStateMonad$ES_LIFT2``)
val _ = overload_on ("fail", ``errorStateMonad$ES_FAIL``)

val oHD_def = Define`oHD l = case l of [] => NONE | h::_ => SOME h`
val ESHD_def = Define`(ESHD [] = fail) ∧ (ESHD (h::t) = return h)`;
val _ = overload_on ("mHD", ``ESHD``)

val ES_LIFT_OPTF_def = Define`
  ES_LIFT_OPTF (f:'a -> 'b option) (x:'a) =
    case f x of NONE => fail | SOME x => return x
`
val _ = overload_on ("optf", ``ES_LIFT_OPTF``)

val ES_LIFT_OPT_def = Define`
  ES_LIFT_OPT NONE = fail ∧
  ES_LIFT_OPT (SOME x) = return x
`;
val _ = overload_on ("opt", ``ES_LIFT_OPT``)

val safeTL_def = Define`safeTL [] = [] ∧ safeTL (h::t) = t`

val ifM_def = Define`
  ifM bM tM eM =
    do
       b <- bM;
       if b then tM else eM
    od
`

val mk_binop_def = Define`
  mk_binop a_op a1 a2 =
    if a_op = Short "::" then Con (SOME (Short "::")) [a1; a2]
    else App Opapp [App Opapp [Var a_op; a1]; a2]
`

val ptree_UQTyop_def = Define`
  ptree_UQTyop (Lf _) = fail ∧
  ptree_UQTyop (Nd nt args) =
    if nt <> mkNT nUQTyOp then fail
    else
      case args of
          [pt] =>
          do
            lf <- optf destLf pt;
            tk <- optf destTOK lf;
            optf destSymbolT tk ++ optf destAlphaT tk
          od
        | _ => fail
`;

val ptree_TyvarN_def = Define`
  ptree_TyvarN (Lf _) = fail ∧
  ptree_TyvarN (Nd nt args) =
    if nt <> mkNT nTyvarN then fail
    else
      case args of
          [tyv] => optf destTyvarPT tyv
        | _ => fail
`;

val _ = temp_overload_on ("'", ``λf a. OPTION_BIND a f``);

val ptree_Tyop_def = Define`
  ptree_Tyop (Lf _) : tvarN id M = fail ∧
  ptree_Tyop (Nd nt args) =
    if nt <> mkNT nTyOp then fail
    else
      case args of
          [pt] =>
          do
            (str,s) <- opt (destLongidT ' (destTOK ' (destLf pt)));
            return (Long str s)
          od ++
          do
            nm <- ptree_UQTyop pt;
            return (Short nm)
          od
        | _ => fail
`;

val ptree_linfix_def = Define`
  ptree_linfix topnt opn elnt (pt : mlptree) =
    case pt of
        Lf _ => fail
      | Nd nt args =>
        if nt = mkNT topnt then
          case args of
              [pt] => do e <- elnt pt; return [e] od
            | [top; op_pt; pt] => do
                assert(op_pt = Lf (TK opn));
                front <- ptree_linfix topnt opn elnt top;
                last <- elnt pt;
                return(front ++ [last])
              od
            | _ => fail
        else fail
`

val tuplify_def = Define`
  tuplify [] = NONE ∧
  tuplify [ty] = SOME ty ∧
  tuplify tys = SOME(Tapp tys TC_tup)
`

val ptree_Type_def = Define`
  (ptree_Type nt (Lf _) : t M = fail) ∧
  (ptree_Type nm (Nd nt args) =
     if nt <> mkNT nm then fail
     else if nm = nType then
       case args of
          [dt] =>
          do
            tys <- ptree_PType dt;
            optf tuplify tys
          od
        | [dt;arrowt;rt] =>
              do
                assert(arrowt = Lf (TOK ArrowT));
                dtys <- ptree_PType dt;
                dty <- optf tuplify dtys;
                rty <- ptree_Type nType rt;
                return (Tfn dty rty)
              od
            | _ => fail
     else if nm = nDType then
       case args of
           [pt] => ptree_Type nTbase pt
         | [dt; opn] => do
                          dty <- ptree_Type nDType dt;
                          opname <- ptree_Tyop opn;
                          return (Tapp [dty] (TC_name opname))
                        od
         | _ => fail
     else if nm = nTbase then
       case args of
           [pt] =>
                lift Tvar (optf destTyvarPT pt) ++
                lift (Tapp [] o TC_name) (ptree_Tyop pt)
         | [lpart; t; rpart] =>
              do
                assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
                ptree_Type nType t
              od
         | [lpart; tl; rpart; opn] =>
           do
              assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
              tylist <- ptree_Typelist2 tl;
              opname <- ptree_Tyop opn;
              return (Tapp tylist (TC_name opname))
           od
         | _ => fail
     else fail) ∧
  (ptree_Typelist2 ptree : t list M =
     case ptree of
       Lf _ => fail
     | Nd nt args =>
       if nt <> mkNT nTypeList2 then fail
       else
         case args of
           | [dt; commat; tl'] =>
             do
               assert(commat = Lf (TK CommaT));
               ty <- ptree_Type nType dt;
               tylist <- ptree_TypeList1 tl';
               return (ty::tylist)
             od
           | _ => fail) ∧
  (ptree_TypeList1 ptree : t list M =
    case ptree of
        Lf _ => fail
      | Nd nt args =>
        if nt <> mkNT nTypeList1 then fail
        else
          case args of
              [dt] =>
              do
                ty <- ptree_Type nType dt;
                return [ty]
              od
            | [dt; commat; tl] =>
              do
                assert(commat = Lf (TK CommaT));
                ty <- ptree_Type nType dt;
                tl <- ptree_TypeList1 tl;
                return (ty::tl)
              od
            | _ => fail) ∧
  (ptree_PType ptree : t list M =
     case ptree of
         Lf _ => fail
       | Nd nt args =>
         if nt <> mkNT nPType then fail
         else
           case args of
               [dty_pt] =>
               do
                 dty <- ptree_Type nDType dty_pt;
                 return [dty]
               od
             | [dty_pt; st; pty_pt] =>
               do
                 assert (st = Lf (TK StarT));
                 dty <- ptree_Type nDType dty_pt;
                 ptys <- ptree_PType pty_pt;
                 return (dty::ptys)
               od
             | _ => fail)
`;

val ptree_TypeName_def = Define`
  ptree_TypeName ptree : (tvarN list # typeN) M =
    case ptree of
      Lf _ => fail
    | Nd nt args =>
      if nt = mkNT nTypeName then
        case args of
          [oppt] => do opn <- ptree_UQTyop oppt ; return ([], opn) od
        | [sym; oppt] => do tyvn <- optf destTyvarPT sym ;
                            opn <- ptree_UQTyop oppt ;
                            return ([tyvn], opn)
                         od
        | [lp; tyvl; rp; oppt] =>
          if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then do
              tyvnms <- ptree_linfix nTyVarList CommaT ptree_TyvarN tyvl;
              opn <- ptree_UQTyop oppt;
              return (tyvnms, opn)
            od
          else fail
        | _ => fail
      else fail
`;

val ptree_UQConstructorName_def = Define`
  ptree_UQConstructorName (Lf _) = fail ∧
  ptree_UQConstructorName (Nd nm args) =
    if nm <> mkNT nUQConstructorName then fail
    else
      case args of
          [pt] => opt (destAlphaT ' (destTOK ' (destLf pt)))
        | _ => fail
`

val ptree_ConstructorName_def = Define`
  ptree_ConstructorName ast =
    case ast of
        Lf _ => fail
      | Nd nt args =>
        if nt <> mkNT nConstructorName then fail
        else
          case args of
              [pt] =>
              do
                s <- ptree_UQConstructorName pt;
                return (Short s)
              od ++
              do
                (str,s) <- opt (destLongidT ' (destTOK ' (destLf pt)));
                return (Long str s)
              od
            | _ => fail
`

val detuplify_def = Define`
  detuplify (Tapp args TC_tup) = args ∧
  detuplify ty = [ty]
`

val ptree_Dconstructor_def = Define`
  ptree_Dconstructor ast =
    case ast of
        Lf x => fail
      | Nd nt args =>
        if nt = mkNT nDconstructor then
          case args of
              [] => fail
            | t::ts =>
              do
                 cname <- ptree_UQConstructorName t;
                 types <- case ts of
                               [] => return []
                             | [oft; ty_pt] =>
                               if oft = Lf (TK OfT) then
                                 lift detuplify (ptree_Type nType ty_pt)
                               else fail
                             | _ => fail;
                 return (cname, types)
              od
            | _ :: t => fail
        else fail
`;

val ptree_DtypeDecl_def = Define`
  ptree_DtypeDecl (pt : mlptree) =
    case pt of
        Lf _ => fail
      | Nd nt args =>
        if nt = mkNT nDtypeDecl then
          case args of
              [tynm_pt; eqt; dtc_pt] => do
                assert(eqt = Lf (TK EqualsT));
                tynm <- ptree_TypeName tynm_pt;
                dtc <- ptree_linfix nDtypeCons BarT ptree_Dconstructor dtc_pt;
                return (FST tynm,SND tynm,dtc)
              od
            | _ => fail
        else fail
`;

val ptree_TypeDec_def = Define`
  ptree_TypeDec ptree : type_def M =
    case ptree of
      Lf _ => fail
    | Nd nt args =>
      if nt = mkNT nTypeDec then
        case args of
            [datatype_pt; pt] => do
              assert(datatype_pt = Lf (TK DatatypeT));
              ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt
            od
          | _ => fail
      else fail`;

val ptree_TypeAbbrevDec_def = Define`
  ptree_TypeAbbrevDec ptree : dec M =
    case ptree of
      Lf _ => fail
    | Nd nt args =>
      if nt = mkNT nTypeAbbrevDec then
        case args of
          [typetok; tynm ; eqtok ; typ_pt] => do
            assert(typetok = Lf (TK TypeT) ∧ eqtok = Lf (TK EqualsT)) ;
            (vars, nm) <- ptree_TypeName tynm;
            typ <- ptree_Type nType typ_pt;
            return (Dtabbrev vars nm typ)
          od
        | _ => fail
      else fail
`

val ptree_V_def = Define`
  ptree_V (Lf _) = fail ∧
  ptree_V (Nd nt subs) =
    if nt = mkNT nV then
      case subs of
          [Lf (TOK t)] => optf destAlphaT t ++ optf destSymbolT t ++
                          do assert (t = StarT) ; return "*" od
        | _ => fail
    else fail
`;

(* in other words constructors never take tuples as arguments, only ever
   lists of arguments *)
val mkPatApp_def = Define`
  mkPatApp cn p =
    if cn = Short "ref" then Pref p
    else
      case p of
          Pcon NONE pl => Pcon (SOME cn) pl
        | _ => Pcon (SOME cn) [p]
`;

val ptree_Pattern_def = Define`
  (ptree_Pattern nt (Lf _) = fail) ∧
  (ptree_Pattern nt (Nd nm args) =
    if mkNT nt <> nm then fail
    else if nm = mkNT nPbase then
      case args of
          [vic] =>
          ptree_Pattern nPtuple vic ++
          do
             cname <- ptree_ConstructorName vic;
             return (Pcon (SOME cname) [])
          od ++
          do vname <- ptree_V vic; return (Pvar vname) od ++
          do
            lf <- optf destLf vic;
            t <- optf destTOK lf;
            (do i <- optf destIntT t ; return (Plit (IntLit i)) od ++
             do s <- optf destStringT t ; return (Plit (StrLit s)) od ++
             do c <- optf destCharT t ; return (Plit (Char c)) od)
          od ++
          do assert(vic = Lf (TOK UnderbarT)) ; return (Pvar "_") od
        | [lb; rb] =>
          if lb = Lf (TK LbrackT) ∧ rb = Lf (TK RbrackT) then
            return (Pcon (SOME (Short "nil")) [])
          else fail
        | [lb; plistpt; rb] =>
          do
            assert (lb = Lf (TK LbrackT) ∧ rb = Lf (TK RbrackT));
            plist <- ptree_Plist plistpt;
            return (FOLDR (λp a. Pcon (SOME (Short "::")) [p; a])
                          (Pcon (SOME (Short "nil")) [])
                          plist)
          od
        | _ => fail
    else if nm = mkNT nPapp then
      case args of
          [pb] => ptree_Pattern nPbase pb
        | [cnm; ppt] =>
          do
            cn <- ptree_ConstructorName cnm;
            p <- ptree_Pattern nPbase ppt;
            return (mkPatApp cn p)
          od
        | _ => fail
    else if nm = mkNT nPattern then
      case args of
          [papt] => ptree_Pattern nPapp papt
        | [papt; cons_t; pattpt] =>
          do
            assert (cons_t = Lf (TK (SymbolT "::")));
            pa <- ptree_Pattern nPapp papt;
            patt <- ptree_Pattern nPattern pattpt;
            return (Pcon (SOME (Short "::")) [pa; patt])
          od
        | _ => fail
    else if nm = mkNT nPtuple then
      case args of
          [lp; rp] => if lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT) then
                        return (Pcon NONE [])
                      else fail
        | [lp; pl_pt; rp] =>
          do
            assert (lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT));
            pl <- ptree_Plist pl_pt;
            case pl of
                [] => fail
              | [p] => return p
              | _ => return (Pcon NONE pl)
          od
        | _ => fail
    else fail) ∧

  (ptree_Plist (Lf _) = fail) ∧
  (ptree_Plist (Nd nm args) =
     if nm <> mkNT nPatternList then fail
     else
       case args of
           [p_pt] =>
           do
             p <- ptree_Pattern nPattern p_pt;
             return [p]
           od
         | [p; ct; pl] =>
           do
             assert (ct = Lf (TOK CommaT));
             hdpat <- ptree_Pattern nPattern p;
             tlpats <- ptree_Plist pl;
             return (hdpat::tlpats)
           od
         | _ => fail)
`;

val ptree_PbaseList1_def = Define`
  (ptree_PbaseList1 (Lf _) = fail) ∧
  (ptree_PbaseList1 (Nd nm args) =
     if nm <> mkNT nPbaseList1 then fail
     else
       case args of
           [p_pt] => lift SINGL (ptree_Pattern nPbase p_pt)
         | [p_pt; pl_pt] =>
               lift2 CONS
                     (ptree_Pattern nPbase p_pt)
                     (ptree_PbaseList1 pl_pt)
        | _ => fail)
`;

val Eseq_encode_def = Define`
  (Eseq_encode [] = fail) ∧
  (Eseq_encode [e] = return e) ∧
  (Eseq_encode (e::es) =
   do
     body <- Eseq_encode es;
     return (Let NONE e body)
   od)
`

val mkAst_App_def = Define`
  mkAst_App a1 a2 =
   case a1 of
       Con (SOME (Short "ref")) [] => App Opapp [Var (Short "ref"); a2]
     | Con s [] =>
       (case a2 of
            Con NONE [] => Con s [a2]
              (* applying a constructor to unit has to be viewed as
                 applying it to one argument (unit), rather than as
                 applying it to none *)
          | Con NONE tuple => Con s tuple
          | _ => Con s [a2])
     | _ => App Opapp [a1; a2]
`

val isSymbolicConstructor_def = Define`
  isSymbolicConstructor (structopt : modN option) s =
    return (s = "::")
`;

val isConstructor_def = Define`
  isConstructor structopt s =
    do
      ifM (isSymbolicConstructor structopt s)
        (return T)
        (return (case oHD s of
                     NONE => F
                   | SOME c => isAlpha c ∧ isUpper c))
    od
`;

val ptree_OpID_def = Define`
  ptree_OpID (Lf _) = fail ∧
  ptree_OpID (Nd nt subs) =
    if nt ≠ mkNT nOpID then fail
    else
      case subs of
          [Lf (TK tk)] =>
          do
              (str,s) <- optf destLongidT tk ;
              ifM (isConstructor (SOME str) s)
                  (return (Con (SOME (Long str s)) []))
                  (return (Var (Long str s)))
          od
       | [Lf _] => fail
       | [pt] =>
         do
           s <- ptree_V pt ;
           ifM (isConstructor NONE s)
               (return (Con (SOME (Short s)) []))
               (return (Var (Short s)))
         od
       | _ => fail
`;

val dePat_def = Define`
  (dePat (Pvar v) b = (v, b)) ∧
  (dePat p b = ("", Mat (Var (Short "")) [(p, b)]))
`

val mkFun_def = Define`
  mkFun p b = UNCURRY Fun (dePat p b)
`

val ptree_Expr_def = Define`
  ptree_Expr ent (Lf _) = fail ∧
  ptree_Expr ent (Nd nt subs) =
    (if mkNT ent = nt then
      if nt = mkNT nEbase then
        case subs of
            [lpart; pt; rpart] =>
            do
              assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
              eseq <- ptree_Eseq pt;
              Eseq_encode eseq
            od ++
            do
              assert(lpart = Lf (TK LbrackT) ∧ rpart = Lf (TK RbrackT));
              elist <- ptree_Exprlist nElist1 pt;
              return (FOLDR (λe acc. Con (SOME (Short "::")) [e; acc])
                            (Con (SOME (Short "nil")) [])
                            elist)
            od
          | [single] =>
              do
                lf <- optf destLf single;
                t <- optf destTOK lf;
                (do i <- optf destIntT t ; return (Lit (IntLit i)) od ++
                 do c <- optf destCharT t ; return (Lit (Char c)) od ++
                 do s <- optf destStringT t ; return (Lit (StrLit s)) od)
              od ++
              ptree_OpID single ++
              ptree_Expr nEtuple single
          | [lp;rp] => if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then
                         return (Con NONE [])
                       else if lp = Lf (TK LbrackT) ∧ rp = Lf (TK RbrackT) then
                         return (Con (SOME (Short "nil")) [])
                       else if lp = Lf (TK OpT) then
                         ptree_OpID rp
                       else
                         fail
          | [lett;letdecs_pt;intok;ept;endt] =>
            do
              assert(lett = Lf (TOK LetT) ∧ intok = Lf (TOK InT) ∧
                     endt = Lf (TOK EndT));
              letdecs <- ptree_LetDecs letdecs_pt;
              eseq <- ptree_Eseq ept;
              e <- Eseq_encode eseq;
              return(FOLDR (λdf acc. case df of
                                       INL (v,e0) => Let (SOME v) e0 acc
                                     | INR fds => Letrec fds acc)
                           e
                           letdecs)
            od
          | _ => fail
      else if nt = mkNT nEtuple then
        case subs of
            [lpart; el2; rpart] =>
            do
              assert (lpart = Lf (TOK LparT) ∧ rpart = Lf (TOK RparT));
              es <- ptree_Exprlist nElist2 el2;
              return (Con NONE es)
            od
          | _ => fail
      else if nt = mkNT nEops then
        case subs of
            [pt] => ptree_Expr nEbase pt
          | [pt1; pt2] =>
            lift2 mkAst_App
                  (ptree_Expr nEbase pt1)
                  (ptree_Expr nEops pt2)
          | _ => fail
      else if nt = mkNT nEtyped then
        case subs of
          [t1;colon;t2] => do
            assert(colon = Lf (TOK ColonT));
            t1 <- ptree_Expr nEops t1;
            t2 <- ptree_Type nType t2;
            return t1 (* TODO: FIXME *)
          od
        | [t] => ptree_Expr nEops t
        | _ => fail
      else if nt = mkNT nElogicAND then
        case subs of
            [t1;andt;t2] => do
              assert(andt = Lf (TOK AndalsoT));
              a1 <- ptree_Expr nElogicAND t1;
              a2 <- ptree_Expr nEtyped t2;
              return (Log And a1 a2)
            od
          | [t] => ptree_Expr nEtyped t
          | _ => fail
      else if nt = mkNT nElogicOR then
        case subs of
            [t1;ort;t2] => do
              assert(ort = Lf (TOK OrelseT));
              a1 <- ptree_Expr nElogicOR t1;
              a2 <- ptree_Expr nElogicAND t2;
              return (Log Or a1 a2)
            od
          | [t] => ptree_Expr nElogicAND t
          | _ => fail
      else if nt = mkNT nEhandle then
        case subs of
            [pt] => ptree_Expr nElogicOR pt
          | [e1pt; handlet; ent] =>
            do
              assert(handlet = Lf (TOK HandleT));
              e <- ptree_Expr nElogicOR e1pt;
              pes <- ptree_PEs ent;
              return (Handle e pes)
            od
          | _ => fail
      else if nt = mkNT nE then
        case subs of
          | [t] => ptree_Expr nEhandle t
          | [raiset; ept] =>
            do
              assert(raiset = Lf (TOK RaiseT));
              e <- ptree_Expr nE ept;
              return (Raise e)
            od
          | [fnt; pnt; arrowt; ent] =>
            do
              assert (fnt = Lf (TOK FnT) ∧ arrowt = Lf (TOK DarrowT));
              p <- ptree_Pattern nPattern pnt;
              e <- ptree_Expr nE ent;
              return (mkFun p e)
            od ++ do
              assert (fnt = Lf (TOK CaseT) ∧ arrowt = Lf (TOK OfT));
              e <- ptree_Expr nE pnt;
              pes <- ptree_PEs ent;
              return (Mat e pes)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(ift = Lf (TOK IfT) ∧ thent = Lf (TOK ThenT) ∧
                     elset = Lf (TOK ElseT));
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE ee;
              return (If a1 a2 a3)
            od
          | _ => fail
      else if nt = mkNT nE' then
        case subs of
          | [t] => ptree_Expr nElogicOR t
          | [raiset; ept] =>
            do
              assert(raiset = Lf (TOK RaiseT));
              e <- ptree_Expr nE' ept;
              return (Raise e)
            od
          | [fnt; vnt; arrowt; ent] =>
            do
              assert (fnt = Lf (TOK FnT) ∧ arrowt = Lf (TOK DarrowT));
              v <- ptree_V vnt;
              e <- ptree_Expr nE' ent;
              return (Fun v e)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(ift = Lf (TOK IfT) ∧ thent = Lf (TOK ThenT) ∧
                     elset = Lf (TOK ElseT));
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE' ee;
              return (If a1 a2 a3)
            od
          | _ => fail
      else fail
    else fail) ∧
  (ptree_Exprlist nm ast =
     case ast of
         Lf _ => fail
       | Nd nt subs =>
         if nt = mkNT nElist1 then
           case subs of
               [sing] => do e <- ptree_Expr nE sing; return [e] od
             | [e;ct;el1] =>
               do
                 assert(ct = Lf (TOK CommaT));
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 return (front::back)
               od
             | _ => fail
         else if nt = mkNT nElist2 then
           case subs of
               [e;ct;el1] =>
               do
                 assert(ct = Lf (TOK CommaT));
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 return (front::back)
               od
             | _ => fail
         else fail) ∧
  ptree_AndFDecls ast =
    (case ast of
        Lf _ => fail
      | Nd nt subs =>
        if nt = mkNT nAndFDecls then
          case subs of
              [single] => do fdec <- ptree_FDecl single; return [fdec] od
            | [fdecspt;andt;fdecpt] =>
              do
                assert(andt = Lf (TOK AndT));
                fdecs <- ptree_AndFDecls fdecspt;
                fdec <- ptree_FDecl fdecpt;
                return (fdecs ++ [fdec])
              od
            | _ => fail
        else fail) ∧
  (ptree_FDecl ast =
    case ast of
        Lf _ => fail
      | Nd nt subs =>
        if nt = mkNT nFDecl then
          case subs of
              [fname_pt; pats_pt; eqt; body_pt] =>
              do
                assert(eqt = Lf (TOK EqualsT));
                fname <- ptree_V fname_pt;
                ps <- ptree_PbaseList1 pats_pt;
                p1 <- mHD ps;
                body0 <- ptree_Expr nE body_pt;
                return (fname,dePat p1 (FOLDR mkFun body0 (safeTL ps)))
              od
            | _ => fail
        else fail) ∧
  (ptree_LetDecs ptree =
    case ptree of
        Lf _ => fail
      | Nd nt args =>
        if nt <> mkNT nLetDecs then fail
        else
          case args of
              [] => return []
            | [ld_pt; lds_pt] =>
              if ld_pt = Lf (TOK SemicolonT) then ptree_LetDecs lds_pt
              else
                do
                  ld <- ptree_LetDec ld_pt;
                  lds <- ptree_LetDecs lds_pt;
                  return (ld::lds)
                od
            | _ => fail) ∧
  (ptree_LetDec ptree =
    case ptree of
        Lf _ => fail
      | Nd nt args =>
        if nt <> mkNT nLetDec then fail
        else
          case args of
              [funtok; andfdecls_pt] =>
              do
                assert (funtok = Lf (TOK FunT));
                fds <- ptree_AndFDecls andfdecls_pt;
                return (INR fds)
              od
            | [valtok; v_pt; eqtok; e_pt] =>
              do
                assert(valtok = Lf (TOK ValT) ∧ eqtok = Lf (TOK EqualsT));
                v <- ptree_V v_pt;
                e <- ptree_Expr nE e_pt;
                return (INL(v,e))
              od
            | _ => fail) ∧
  (ptree_PEs (Lf _) = fail) ∧
  (ptree_PEs (Nd nt args) =
    if nt <> mkNT nPEs then fail
    else
      case args of
          [single] =>
          do
            pe <- ptree_PE single;
            return [pe]
          od
        | [pe'_pt; bartok; pes_pt] =>
          do
            assert(bartok = Lf (TOK BarT));
            pes <- ptree_PEs pes_pt;
            pe <- ptree_PE' pe'_pt;
            return (pe::pes)
          od
        | _ => fail) ∧

  (ptree_PE (Lf _) = fail) ∧
  (ptree_PE (Nd nt args) =
     if nt <> mkNT nPE then fail
     else
       case args of
           [p_pt; arrow; e_pt] =>
           do
             assert(arrow = Lf (TOK DarrowT));
             p <- ptree_Pattern nPattern p_pt;
             e <- ptree_Expr nE e_pt;
             return (p,e)
           od
         | _ => fail) ∧

  (ptree_PE' (Lf _) = fail) ∧
  (ptree_PE' (Nd nt args) =
     if nt <> mkNT nPE' then fail
     else
       case args of
           [p_pt; arrow; e'_pt] =>
           do
             assert(arrow = Lf (TOK DarrowT));
             p <- ptree_Pattern nPattern p_pt;
             e <- ptree_Expr nE' e'_pt;
             return (p,e)
           od
         | _ => fail) ∧

  (ptree_Eseq (Lf _) = fail) ∧
  (ptree_Eseq (Nd nt args) =
    if nt <> mkNT nEseq then fail
    else
      case args of
          [single] =>
          do
            e <- ptree_Expr nE single;
            return [e]
          od
        | [e_pt; semi; seq_pt] =>
          do
            assert(semi = Lf (TOK SemicolonT));
            e <- ptree_Expr nE e_pt;
            seq <- ptree_Eseq seq_pt;
            return (e::seq)
          od
        | _ => fail)
`;


val ptree_Decl_def = Define`
  ptree_Decl pt : dec M =
    case pt of
       Lf _ => fail
     | Nd nt args =>
       if nt <> mkNT nDecl then fail
       else
         case args of
             [dt] =>
             do
               tydec <- ptree_TypeDec dt;
               return (Dtype tydec)
             od ++ ptree_TypeAbbrevDec dt
           | [funtok; fdecls] =>
             do
               assert(funtok = Lf (TOK FunT));
               fdecs <- ptree_AndFDecls fdecls;
               return (Dletrec fdecs)
             od ++
             do
               assert (funtok = Lf (TOK ExceptionT));
               (enm, etys) <- ptree_Dconstructor fdecls;
               return (Dexn enm etys)
             od
           | [valtok; patpt; eqtok; ept] =>
             do
               assert (valtok = Lf (TOK ValT) ∧ eqtok = Lf (TOK EqualsT));
               lift2 Dlet (ptree_Pattern nPattern patpt) (ptree_Expr nE ept)
             od
           | _ => fail
`

val ptree_Decls_def = Define`
  ptree_Decls (Lf _) = fail ∧
  ptree_Decls (Nd nt args) =
    if nt <> mkNT nDecls then fail
    else
      case args of
          [] => return []
        | [d_pt; ds_pt] =>
          if d_pt = Lf (TOK SemicolonT) then ptree_Decls ds_pt
          else
            lift2 CONS (ptree_Decl d_pt) (ptree_Decls ds_pt)
        | _ => fail
`

val ptree_OptTypEqn_def = Define`
  ptree_OptTypEqn (Lf _) = fail : t option M ∧
  ptree_OptTypEqn (Nd nt args) =
    if nt <> mkNT nOptTypEqn then fail
    else
      case args of
          [] => return NONE
        | [eqtok; typ_pt] =>
          do
            assert (eqtok = Lf (TOK EqualsT));
            typ <- ptree_Type nType typ_pt;
            return (SOME typ)
          od
        | _ => fail
`

val ptree_SpecLine_def = Define`
  ptree_SpecLine (Lf _) = fail ∧
  ptree_SpecLine (Nd nt args) =
    if nt <> mkNT nSpecLine then fail
    else
      case args of
          [td_pt] => lift Stype (ptree_TypeDec td_pt)
        | [exntok; dcon_pt] =>
          do
            assert (exntok = Lf (TOK ExceptionT));
            (nm,tys) <- ptree_Dconstructor dcon_pt;
            return (Sexn nm tys)
          od
        | [typetok; tynm_pt; opteqn_pt] =>
          do
            assert(typetok = Lf (TOK TypeT));
            (vs,nm) <- ptree_TypeName tynm_pt;
            opteqn <- ptree_OptTypEqn opteqn_pt;
            return (case opteqn of
                        NONE => Stype_opq vs nm
                      | SOME ty => Stabbrev vs nm ty)
          od
        | [valtok; vname_pt; coltok; type_pt] =>
          do
            assert(valtok = Lf (TOK ValT) ∧ coltok = Lf (TOK ColonT));
            lift2 Sval (ptree_V vname_pt) (ptree_Type nType type_pt)
          od
        | _ => fail
`

val ptree_SpeclineList_def = Define`
  ptree_SpeclineList (Lf _) = fail ∧
  ptree_SpeclineList (Nd nt args) =
    if nt <> mkNT nSpecLineList then fail
    else
      case args of
          [] => return []
        | [sl_pt; sll_pt] =>
          if sl_pt = Lf (TOK SemicolonT) then ptree_SpeclineList sll_pt
          else
              lift2 CONS (ptree_SpecLine sl_pt) (ptree_SpeclineList sll_pt)
        | _ => fail
`

val ptree_SignatureValue_def = Define`
  ptree_SignatureValue (Lf _) = fail ∧
  ptree_SignatureValue (Nd nt args) =
    if nt <> mkNT nSignatureValue then fail
    else
      case args of
          [sigtok; sll_pt; endtok] =>
          do
            assert(sigtok = Lf (TOK SigT) ∧ endtok = Lf (TOK EndT));
            ptree_SpeclineList sll_pt
          od
        | _ => fail
`;

val ptree_StructName_def = Define`
  ptree_StructName (Lf _) = fail ∧
  ptree_StructName (Nd nm args) =
    if nm <> mkNT nStructName then fail
    else
      case args of
          [pt] => opt (destAlphaT ' (destTOK ' (destLf pt)))
        | _ => fail
`

val ptree_Structure_def = Define`
  ptree_Structure (Lf _) = fail ∧
  ptree_Structure (Nd nt args) =
    if nt <> mkNT nStructure then fail
    else
      case args of
          [structuretok; sname_pt; asc_opt; eqtok; structtok; ds_pt; endtok] =>
          do
            assert(structtok = Lf (TOK StructT) ∧
                   structuretok = Lf (TOK StructureT) ∧
                   eqtok = Lf (TOK EqualsT) ∧ endtok = Lf (TOK EndT));
            sname <- ptree_StructName sname_pt;
            asc <- case asc_opt of
                       Lf _ => fail
                     | Nd nt args =>
                         if nt <> mkNT nOptionalSignatureAscription then fail
                         else
                           case args of
                               [] => return NONE
                             | [sealtok; sig_pt] =>
                               do
                                 assert(sealtok = Lf (TOK SealT));
                                 sigv <- ptree_SignatureValue sig_pt;
                                 return (SOME sigv)
                               od
                             | _ => fail;
            ds <- ptree_Decls ds_pt;
            return (Tmod sname asc ds)
          od
        | _ => fail
`

val ptree_TopLevelDec_def = Define`
  ptree_TopLevelDec (Lf _) = fail ∧
  ptree_TopLevelDec (Nd nt args) =
    if nt <> mkNT nTopLevelDec then fail
    else
      case args of
          [pt] =>
            ptree_Structure pt ++ lift Tdec (ptree_Decl pt)
        | _ => fail
`

val ptree_TopLevelDecs_def = Define`
  ptree_TopLevelDecs (Lf _) = fail ∧
  ptree_TopLevelDecs (Nd nt args) =
    if nt <> mkNT nTopLevelDecs then fail
    else
      case args of
          [] => return []
        | [td_pt; tds_pt] =>
          if td_pt = Lf (TOK SemicolonT) then ptree_TopLevelDecs tds_pt
          else
            lift2 CONS (ptree_TopLevelDec td_pt) (ptree_TopLevelDecs tds_pt)
        | _ => fail
`;

val ptree_REPLTop_def = Define`
  ptree_REPLTop (Lf _) = fail ∧
  ptree_REPLTop (Nd nt args) =
    if nt <> mkNT nREPLTop then fail
    else
      case args of
          [pt; semitok] =>
            ptree_TopLevelDec pt ++
            do
              e <- ptree_Expr nE pt;
              return (Tdec (Dlet (Pvar "it") e))
            od
         | _ => fail
`;


val _ = export_theory()

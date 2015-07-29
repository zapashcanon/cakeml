open HolKernel Parse boolLib bossLib

open tokensTheory grammarTheory

open lcsymtacs grammarLib monadsyntax

val _ = new_theory "gram"

(* ----------------------------------------------------------------------
    Define the CakeML Context-Free Grammar
   ---------------------------------------------------------------------- *)

val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                ("[", ``LbrackT``),
                ("]", ``RbrackT``),
                (";", ``SemicolonT``), (":=", ``SymbolT ":="``),
                (":>", ``SealT``),
                ("::", ``SymbolT "::"``), ("@", ``SymbolT "@"``),
                ("->", ``ArrowT``), ("=>", ``DarrowT``),
                ("*", ``StarT``),
                ("|", ``BarT``), ("=", ``EqualsT``), (":", ``ColonT``),
                ("_", ``UnderbarT``),
                ("and", ``AndT``),
                ("andalso", ``AndalsoT``),
                ("before", ``AlphaT "before"``),
                ("Bind", ``AlphaT "Bind"``),
                ("case", ``CaseT``),
                ("datatype", ``DatatypeT``),
                ("Div", ``AlphaT "Div"``),
                ("else", ``ElseT``),
                ("end", ``EndT``),
                ("exception", ``ExceptionT``),
                ("false", ``AlphaT "false"``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("handle", ``HandleT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("IntError", ``AlphaT "IntError"``),
                ("let", ``LetT``),
                ("nil", ``AlphaT "nil"``),
                ("o", ``AlphaT "o"``),
                ("of", ``OfT``),
                ("op", ``OpT``),
                ("orelse", ``OrelseT``),
                ("raise", ``RaiseT``),
                ("ref", ``AlphaT "ref"``),
                ("sig", ``SigT``),
                ("struct", ``StructT``),
                ("structure", ``StructureT``),
                ("then", ``ThenT``),
                ("true", ``AlphaT "true"``),
                ("type", ``TypeT``),
                ("val", ``ValT``)]
fun tokmap s =
    case Binarymap.peek(tokmap0, s) of
        NONE => raise Fail ("No token binding for "^s)
      | SOME t => t

val ginfo = { tokmap = tokmap,
              tokty = ``:token``, nt_tyname = "MMLnonT",
              start = "REPLTop",
              gname = "cmlG", mkntname = (fn s => "n" ^ s) }

val cmlG_def = mk_grammar_def ginfo
`(* types *)
 UQTyOp ::= <AlphaT> | <SymbolT>;
 TyvarN ::= <TyvarT>;
 TyOp ::= UQTyOp | <LongidT>;
 TypeList1 ::= Type | Type "," TypeList1;
 TypeList2 ::= Type "," TypeList1;
 Tbase ::= <TyvarT> | TyOp | "(" TypeList2 ")" TyOp | "(" Type ")";
 DType ::= DType TyOp | Tbase;
 PType ::= DType "*" PType | DType;
 Type ::= PType | PType "->" Type;

 (* type declarations *)
 TypeName ::= UQTyOp | "(" TyVarList ")" UQTyOp | <TyvarT> UQTyOp ;
 TyVarList ::= TyvarN | TyVarList "," TyvarN;
 Dconstructor ::= UQConstructorName "of" Type | UQConstructorName;
 DtypeCons ::= Dconstructor | DtypeCons "|" Dconstructor;
 DtypeDecl ::= TypeName "=" DtypeCons ;
 DtypeDecls ::= DtypeDecl | DtypeDecls "and" DtypeDecl;
 TypeDec ::= "datatype" DtypeDecls;
 TypeAbbrevDec ::= "type" TypeName "=" Type;

 (* expressions - base cases and function applications *)
 UQConstructorName ::= ^(``{AlphaT s | s ≠ "" ∧ isUpper (HD s)}``)
                    | "true" | "false" | "ref" | "nil";
 ConstructorName ::=
     UQConstructorName
  | ^(``{LongidT str s | str,s | s ≠ "" ∧ isAlpha (HD s) ∧ isUpper (HD s) ∨
                                 s ∈ {"true"; "false"; "ref"; "nil"}}``);
 OpID ::= ^(``{LongidT str s | str,s | s ≠ ""}``) | V ;
 V ::= ^(``{AlphaT s | s ≠ ""}``) |  ^(``{SymbolT s | s ≠ ""}``) |  "*" ;
 Ebase ::= "(" Eseq ")" | Etuple | "(" ")" | OpID | <IntT>
        |  <CharT> | <StringT> | "let" LetDecs "in" Eseq "end" | "[" "]"
        | "[" Elist1 "]" | "op" OpID ;
 Eseq ::= E ";" Eseq | E;
 Etuple ::= "(" Elist2 ")";
 Elist2 ::= E "," Elist1;
 Elist1 ::= E | E "," Elist1;

 (* expressions - binary operators *)
 Eops ::= Ebase | Ebase Eops ;
 Etyped ::= Eops | Eops ":" Type;
 ElogicAND ::= ElogicAND "andalso" Etyped | Etyped;
 ElogicOR ::= ElogicOR "orelse" ElogicAND | ElogicAND;
 Ehandle ::= ElogicOR | ElogicOR "handle" PEs ;
 E ::= "if" E "then" E "else" E | "case" E "of" PEs | "fn" Pattern "=>" E
    | "raise" E |  Ehandle;
 E' ::= "if" E "then" E "else" E' | "raise" E' | ElogicOR ;

 (* function and value declarations *)
 FDecl ::= V PbaseList1 "=" E ;
 AndFDecls ::= FDecl | AndFDecls "and" FDecl;
 Decl ::= "val" Pattern "=" E  | "fun" AndFDecls |  TypeDec
       |  "exception" Dconstructor
       | TypeAbbrevDec ;
 Decls ::= Decl Decls | ";" Decls | ;
 LetDec ::= "val" V "=" E | "fun" AndFDecls ;
 LetDecs ::= LetDec LetDecs | ";" LetDecs | ;

 (* patterns *)
 Pbase ::= OpID | <IntT> | <StringT> | <CharT> | Ptuple | "_"
        |  "[" "]" | "[" PatternList "]";
 Papp ::= ConstructorName Pbase | Pbase;
 Pattern ::= Papp "::" Pattern | Papp ;
 Ptuple ::= "(" ")" | "(" PatternList ")";
 PatternList ::= Pattern | Pattern "," PatternList ;
 PbaseList1 ::= Pbase | Pbase PbaseList1 ;
 PE ::= Pattern "=>" E;
 PE' ::= Pattern "=>" E';
 PEs ::= PE | PE' "|" PEs;

 (* modules *)
 StructName ::= ^(``{AlphaT s | s ≠ ""}``) ;
 SpecLine ::= "val" V ":" Type
           |  "type" TypeName OptTypEqn
           |  "exception" Dconstructor
           |  TypeDec ;
 OptTypEqn ::= "=" Type | ;
 SpecLineList ::= SpecLine SpecLineList | ";" SpecLineList | ;
 SignatureValue ::= "sig" SpecLineList "end" ;
 OptionalSignatureAscription ::= ":>" SignatureValue | ;
 Structure ::= "structure" StructName OptionalSignatureAscription "=" "struct" Decls "end";
 TopLevelDec ::= Structure | Decl;
 TopLevelDecs ::= TopLevelDec TopLevelDecs | ";" TopLevelDecs | ;
 REPLTop ::= TopLevelDec ";" | E ";" ;
`;

val _ = type_abbrev("NT", ``:MMLnonT inf``)
val _ = overload_on("mkNT", ``INL : MMLnonT -> NT``)

val _ = overload_on ("NN", ``\nt. NT (mkNT nt)``)
val _ = overload_on ("TK", ``TOK : token -> (token,MMLnonT)symbol``)
val _ = type_abbrev("mlptree", ``:(token, MMLnonT) parsetree``)

val nt_distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  save_thm("nt_distinct_ths",  LIST_CONJ (recurse ntlist))
end

val _ = computeLib.add_persistent_funs ["nt_distinct_ths"]

val _ = export_theory()

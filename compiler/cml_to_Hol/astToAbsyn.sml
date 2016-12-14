open HolKernel TermParse astTheory Preterm
open locn libTheory parserProg Absyn GrammarSpecials 

structure astToAbsyn =
struct

exception NotSupported of string;

(* from local def in parse_term *)
val mk_numeral =
  Literal.gen_mk_numeral
  {mk_comb  = mk_app,
  ZERO     = (QIDENT (Loc_Unknown, "num"       , "0"      )),
  ALT_ZERO = (QIDENT (Loc_Unknown, "arithmetic", "ZERO"   )),
  NUMERAL  = (QIDENT (Loc_Unknown, "arithmetic", "NUMERAL")),
  BIT1     = (QIDENT (Loc_Unknown, "arithmetic", "BIT1")   ),
  BIT2     = (QIDENT (Loc_Unknown, "arithmetic", "BIT2")   )};

fun mk_vident cl = VIDENT(Loc_None, String.implode cl);

fun absynFromLit l = case l of
    Intlit n => mk_app(mk_ident "_ inject_number", 
                       mk_numeral (Arbnum.fromInt n))
  | Char c => IDENT(Loc_Unknown, "#\"" ^ str c ^ "\"")
  | Strlit s => IDENT(Loc_Unknown, "\"" ^ String.implode s ^ "\"")
  | Word8 w8 => raise NotSupported "Word8" (* word_to_hex_string w8 ?*)
  | Word64 w64 => raise NotSupported "Word8";


(* Built-in binary operations *)
fun absynFromOpn opb = case opb of 
    Plus => "+"
  | Minus => "-"
  | Times => "*"
  | Divide => "/"
  | Modulo => "%"; (*TODO: check *)

fun abynFromOpb opb = case opb of
	Lt => "<"
  | Gt => ">"
  | Leq => "<="
  | Geq => ">=";


(*
TODO: operations on words
val _ = Hol_datatype `
 opw = Andw | Orw | Xor | Add | Sub`;
*)

(*

val _ = Hol_datatype `
 shift = Lsl | Lsr | Asr`;
*)


(* Identifiers *)
fun absynOfId i = case i of
    Short s => mk_ident s
  | Long (m, s) => QIDENT(Loc_Unknown, String.implode m, s);

(*

val _ = Hol_datatype `
 word_size = W8 | W64`;
*)


(* HERE *)
fun absynFromOp opn = case opn of
  (* Operations on integers *)
    Opn opb => mk_ident (absynFromOpn opb)
  | Opb opb => mk_ident (abynFromOpb opb)
   (* Function application *)
  | _ => raise NotSupported "unknown operation";
(*
 (* Operations on words *)
  | Opw of word_size => opw
  | Shift of word_size => shift => num
  | Equality
  (* Reference operations *)
  | Opassign raise NotSupported "References"
  | Opref raise NotSupported "References"
  | Opderef raise NotSupported "References"
  (* Word8Array operations *)
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  (* Word/integer conversions *)
  | WordFromInt of word_size
  | WordToInt of word_size
  (* Char operations *)
  | Ord
  | Chr
  | Chopb of opb
  (* String operations *)
  | Explode
  | Implode
  | Strlen
  (* Vector operations *)
  | VfromList
  | Vsub
  | Vlength
  (* Array operations *)
  | Aalloc
  | Asub
  | Alength
  | Aupdate
  (* Call a given foreign function *)
  | FFI of num` *)



(*


(* Type constructors. TODO
 * 0-ary type applications represent unparameterised types (e.g., num or string)
 *)
val _ = Hol_datatype `
 tctor =
  (* User defined types *)
    TC_name of typeN id
  (* Built-in types *)
  | TC_int
  | TC_char
  | TC_string
  | TC_ref
  | TC_word8
  | TC_word64
  | TC_word8array
  | TC_fn
  | TC_tup
  | TC_exn
  | TC_vector
  | TC_array`;
*)

(*


(* Types TODO *)
val _ = Hol_datatype `
 t =
  (* Type variables that the user writes down ('a, 'b, etc.) *)
    Tvar of tvarN
  (* deBruijn indexed type variables.
     The type system uses these internally. *)
  | Tvar_db of num
  | Tapp of t list => tctor`;
*)

fun absynFromId i = case i of
  Long (m, name) => QIDENT(Loc_Unknown,String.implode m, String.implode name)
| Short name => mk_ident(String.implode name)

(* Patterns *)
fun absynFromPat p = case p of
    Pvar v => mk_ident (String.implode v)
  | Plit l =>  absynFromLit l
  | Pcon (cid, pl) => 
	(case cid of
	  NONE => list_mk_pair(map absynFromPat pl)
	| SOME c => list_mk_app(absynFromId c, map absynFromPat pl))
  | Pref r => raise NotSupported "pattern reference"
  | Ptannot (p, t) => absynFromPat p; (* TODO type annotation *)


fun mk_absynLet(id, ab1, ab2) = 
  mk_app(mk_app(mk_ident "LET", mk_lam(mk_vident id, ab2)), ab1);

(* Expressions *)
fun absynFromExp e =  case e of
    Raise e => raise NotSupported "Exceptions"
  | Handle  l => raise NotSupported "Exceptions"
  | Lit l => absynFromLit l
  | Con (cid, el) => 
	(case cid of
	  NONE => list_mk_pair(map absynFromExp el)
	| SOME c => list_mk_app(absynFromId c, map absynFromExp el))

  | Var i => absynFromId i
  | Fun (v, e) => mk_lam(mk_vident v, absynFromExp e) 
  | Log (And, e1, e2) => mk_conj(absynFromExp e1, absynFromExp e2)
  | App (Opapp, opb :: l) => list_mk_app(absynFromExp opb, map absynFromExp l)
  | App (opb, l) => list_mk_app(absynFromOp opb, map absynFromExp l)
  | Log (Or, e1, e2) => mk_disj(absynFromExp e1, absynFromExp e2)
  | If(e1, et, ef) => list_mk_app(mk_ident "COND",[ absynFromExp e1,
                                                    absynFromExp et,
                                                    absynFromExp ef])
  | Mat (e, l) => 
      let 
        fun mk_case p e = mk_app(mk_app(mk_ident case_arrow_special,
                                        absynFromPat p),
                                 absynFromExp e)
         fun mk_split lr = 
          case lr of
               [] => raise NotSupported "Empty pattern matching"
             | (ph, eh) :: [] => mk_case ph eh
             | (ph, eh) :: t => mk_app(mk_app(QIDENT(Loc_Unknown, "bool", 
                                                    case_split_special),
                                              mk_case ph eh), 
                                       mk_split t)
      in mk_app(mk_app(mk_ident core_case_special, absynFromExp e), 
                mk_split l)
      end
  | Let (v, e1, e2) => 
		(case v of
		   NONE => mk_pair(absynFromExp e1, absynFromExp e2)
		 | SOME cl => mk_absynLet(cl, absynFromExp e1, absynFromExp e2))
(* TODO: not sure about the way we want to translate it *)
  | Letrec (l, e) => 
      let fun mklet (f,(x,ef)) e = 
            mk_absynLet(f, mk_lam(mk_vident x, absynFromExp ef), e)
      in
          foldr mklet (absynFromExp e) l 
      end
  | Tannot (e, t) => absynFromExp e; (* TODO Type annotations*)

(* Declarations *)
fun absynFromDec d = case d of
(* may be meaningless if p is a tuple *)
    Dlet (p, e) => mk_eq(absynFromPat p, absynFromExp e)
 (* Mutually recursive function definition *)
(* TODO: translate as Define ... bunch of equations *)
  | Dletrec l => (* get definition name from fst hd *)
  		list_mk_conj 
			(map (fn (f, (x, e)) => 
				  mk_eq(mk_app(mk_ident (String.implode f), 
							   mk_ident (String.implode x)), 
						absynFromExp e))
				 l)
  | Dtype td => raise NotSupported "type definition"
  | Dtabbrev (tl, name, t) => raise NotSupported "type abbrev"
  | Dexn (name, tl) => raise NotSupported "Exceptions";

fun absynFromTop t = 
  case t of
       Tmod name => raise NotSupported "open modules"
     | Tdec d => absynFromDec d;

end

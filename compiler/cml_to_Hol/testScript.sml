open parserProg
open astToAbsyn

exception ParseError;

fun makeAbsyn prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => map absynFromTop l
     | NONE => raise ParseError;

fun parse prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => map ((Parse.absyn_to_term (Parse.term_grammar())) o absynFromTop ) l
     | NONE => raise ParseError;



(* definition of Define in TotalDefn *) 
local
val ERRloc = mk_HOL_ERRloc "TotalDefn";
   fun msg alist invoc =
      String.concat
        ["Definition failed! Can't make name for storing definition\n",
         "because there is no alphanumeric identifier in: \n\n   ",
         wfrecUtils.list_to_string Lib.quote "," alist,
         ".\n\nTry \"",invoc, "\" instead.\n\n"]
   fun mk_bindstem exn invoc alist =
      Lib.first Lexis.ok_identifier alist
      handle HOL_ERR _ => (Lib.say (msg alist invoc); raise exn)
in
   fun cmlDefine q =
      let
         val absyn0 = absynFromTop q 
         val locn = Absyn.locn_of_absyn absyn0
         val (tm,names) = Defn.parse_absyn absyn0
         val bindstem =
            mk_bindstem (ERRloc "Define" locn "") "Define <quotation>" names
      in
         #1 (TotalDefn.primDefine (Defn.mk_defn bindstem tm))
         handle e => raise (wrap_exn_loc "TotalDefn" "Define" locn e)
      end
end

fun progDefine prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => map cmlDefine l
     | NONE => raise ParseError;

val testprogall = 
    "val x = let val y = 3 in 4 end;" 
  ^ "val main = let fun f x = 0 in f #\"c\" end;" 
  ^ "fun main2 x = let fun g y = y in g x end;"  
  ^ "fun main3 x = case x of 0 => 0 | 1 => 1 | _ => 2;" 
  ^ "fun main5 f x y z = f x y z;"
(*  ^ "fun fib n = if n = 0 orelse n = 1 then n else fib (n-1) + fib (n-2)";
    non-trivial termination proof *)
(*  ^ "val main4 = \"o\" @ \"k\";"  
*   string concatenation not translated *)


(* the ast *)
val myAbsyn = makeAbsyn testprogall;
(* the term *)
val myTerm = parse testprogall;

(* definition generation *)
val mydef = progDefine testprogall;




open parserProg
open astToAbsyn

exception ParseError;
(*
* debugging functions 
fun progAST prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => l
     | NONE => raise ParseError;
fun progAbsyn prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => (map absynFromTop l)
     | NONE => raise ParseError;
     *)
fun progDefine prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => (map defineFromTop l)
     | NONE => raise ParseError;

(* returns the content of a file as a string *)
fun readLoop istr =
case TextIO.inputLine istr of
     NONE => []
   | SOME s => s :: (readLoop istr)

fun read_file name = 
    concat (readLoop (TextIO.openIn name))

fun testProg() = read_file "exampleProg.cml";

(* read the cml file and produce HOL definitions *)
val mydef = progDefine (testProg());

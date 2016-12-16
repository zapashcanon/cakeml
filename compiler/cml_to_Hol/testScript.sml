open parserProg
open astToAbsyn

exception ParseError;

fun progDefine prog = 
  case (parse_prog o lexer_fun o explode) prog of
       SOME l => (map defineFromTop l; ())
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

(* definition generation *)
val mydef = progDefine testprogall;




(* manual changes:
  1) Add type one = unit at the top
  2) Fix the Char.< and Char.<= calls
  3) Deleted the CharIO module
  4) Deleted the Char and word structs. They are there only to support CakeML I think?
  5) Made peg_pegsym less polymorphic in its second argument. It was leading to value restrictions somewhere else. The second argument is never used except when it is instantiated to gram_MMLnonT
  6) Fix all the changes due to 5
  7) Replace word64 and word8 with their Word64.word and Word8.word
  8) Replace TC_char with just char
  9) wrap in a module
  *)
structure parserProg =
struct

type one = unit;

fun  hd x1 = 
  case  x1
  of  []  =>  (raise  Bind)
  |   v2::v1 =>  v2;

fun  tl x1 = 
  case  x1
  of  []  =>  (raise  Bind)
  |   v2::v1 =>  v1;

fun  append v3 v4 =
  case  v3
  of  []  =>  v4
  |   v2::v1 =>  (v2::(append v1 v4));

fun  rev v4 v3 =
  case  v4
  of  []  =>  v3
  |   v2::v1 =>  (rev v1 (v2::v3));

fun  reverse v1 =  rev v1 [] ;

fun  fst v3 =  case  v3 of  (v2,v1) =>  v2;

fun  snd v3 =  case  v3 of  (v2,v1) =>  v1;

fun  curry v1 =  (fn  v2 => (fn  v3 => v1 (v2,v3)));

fun  uncurry v1 =  (fn  v2 => v1 (fst v2) (snd v2));

fun  o_1 v2 =  (fn  v3 => (fn  v1 => v2 (v3 v1)));

fun  i v1 =  v1;

fun  c v3 =  (fn  v2 => (fn  v1 => v3 v1 v2));

fun  k v2 =  (fn  v1 => v2);

fun  s v3 =  (fn  v2 => (fn  v1 => v3 v1 (v2 v1)));

fun  update v3 = 
  (fn  v4 =>
    (fn  v2 =>
      (fn  v1 =>
        if  (v3 = v1)
        then  v4
         else  (v2 v1))));

fun  w v2 =  (fn  v1 => v2 v1 v1);

fun  the x1 = 
  case  x1
  of  NONE =>  (raise  Bind)
  |   SOME(v1) =>  v1;

fun  is_none v2 = 
  case  v2
  of  NONE =>  (0 <= 0)
  |   SOME(v1) =>  (0 < 0);

fun  is_some v2 = 
  case  v2
  of  NONE =>  (0 < 0)
  |   SOME(v1) =>  (0 <= 0);

fun  option_map v2 = 
  (fn  v3 =>
    case  v3
    of  NONE =>  NONE
    |   SOME(v1) =>  (SOME(v2 v1)));

fun  option_map2 v1 = 
  (fn  v2 =>
    (fn  v3 =>
      if  ((is_some v2) andalso  (is_some v3))
      then  (SOME(v1 (the v2) (the v3)))
      else  NONE));

datatype ( 'a  ,  'b ) sum =  Inr of  'b
                            |  Inl of  'a ;

fun  isl v3 = 
  case  v3
  of  Inl(v1) =>  (0 <= 0)
  |   Inr(v2) =>  (0 < 0);

fun  isr v3 = 
  case  v3
  of  Inl(v1) =>  (0 < 0)
  |   Inr(v2) =>  (0 <= 0);

fun  outl x1 = 
  case  x1
  of  Inl(v1) =>  v1
  |   Inr(v2) =>  (raise  Bind);

fun  outr x1 = 
  case  x1
  of  Inl(v1) =>  (raise  Bind)
  |   Inr(v2) =>  v2;

fun  f v3 = 
  (fn  v4 =>
    (fn  v5 =>
      case  v5
      of  Inl(v1) =>  (Inl(v3 v1))
      |   Inr(v2) =>  (Inr(v4 v2))));

fun  length_aux v3 v4 =
  case  v3
  of  []  =>  v4
  |   v2::v1 =>  (length_aux v1 (v4 + 1));

fun  length v1 =  length_aux v1 0;

fun  map v3 v4 =
  case  v4
  of  []  =>  []
   |   v2::v1 =>  (v3 v2::(map v3 v1));

fun  filter v3 v4 =
  case  v4
  of  []  =>  []
   |   v2::v1 =>  (if  (v3 v2)
                   then  (v2::(filter v3 v1))
                   else  (filter v3 v1));

fun  foldr v4 v3 v5 =
  case  v5
  of  []  =>  v3
  |   v2::v1 =>  (v4 v2 (foldr v4 v3 v1));

fun  foldl v4 v3 v5 =
  case  v5
  of  []  =>  v3
  |   v2::v1 =>  (foldl v4 (v4 v3 v2) v1);

fun  sum v3 =
  case  v3
  of  []  =>  0
  |   v2::v1 =>  (v2 + (sum v1));

fun  unzip v3 =
  case  v3
  of  []  =>  ([] ,[] )
  |   v2::v1 =>  (fst v2::(fst (unzip v1)),snd v2::(snd (unzip v1)));

fun  flat v3 =
  case  v3
  of  []  =>  []
   |   v2::v1 =>  (append v2 (flat v1));

fun  take v3 v4 =
  case  v4
  of  []  =>  []
   |   v2::v1 =>  (if  (v3 <= 0)
                   then  []
                    else  (v2::(take (let val  k = v3 - 1
                                       in
                                        if  (k < 0)
                                        then  0
                                         else  k
                                       end) v1)));

fun  drop v3 v4 =
  case  v4
  of  []  =>  []
   |   v2::v1 =>  (if  (v3 <= 0)
                   then  (v2::v1)
                   else  (drop (let val  k = v3 - 1
                                 in
                                  if  (k < 0)
                                  then  0
                                   else  k
                                 end) v1));

fun  snoc v4 v3 =
  case  v3
  of  []  =>  [v4]
  |   v2::v1 =>  (v2::(snoc v4 v1));

fun  every v3 v4 =
  case  v4
  of  []  =>  (0 <= 0)
  |   v2::v1 =>  ((v3 v2) andalso  (every v3 v1));

fun  exists v3 v4 =
  case  v4
  of  []  =>  (0 < 0)
  |   v2::v1 =>  ((v3 v2) orelse  (exists v3 v1));

fun  genlist v1 v2 =
  if  (v2 <= 0)
  then  []
   else  (snoc (v1 (let val  k = v2 - 1
                     in
                      if  (k < 0)
                      then  0
                       else  k
                     end)) (genlist v1 (let val  k = v2 - 1
                                         in
                                          if  (k < 0)
                                          then  0
                                           else  k
                                         end)));

fun  pad_right v1 = 
  (fn  v2 =>
    (fn  v3 =>
      append v3 (genlist (k v1) (let val  k = v2 - (length v3)
                                 in
                                   if  (k < 0)
                                   then  0
                                    else  k
                                  end))));

fun  pad_left v1 = 
  (fn  v2 =>
    (fn  v3 =>
      append (genlist (k v1) (let val  k = v2 - (length v3)
                              in
                                if  (k < 0)
                                then  0
                                 else  k
                               end)) v3));

fun  member v4 v3 =
  case  v3
  of  []  =>  (0 < 0)
  |   v2::v1 =>  ((v4 = v2) orelse  (member v4 v1));

fun  all_distinct v3 =
  case  v3
  of  []  =>  (0 <= 0)
  |   v2::v1 =>  (((member v2 v1) = (0 < 0)) andalso  (all_distinct v1));

fun  isprefix v5 v6 =
  case  v5
  of  []  =>  (0 <= 0)
  |   v4::v3 =>  (case  v6
                  of  []  =>  (0 < 0)
                  |   (v2::v1) =>  ((v4 = v2) andalso  (isprefix v3 v1)));

fun  front x1 =
  case  x1
  of  []  =>  (raise  Bind)
  |   v2::v1 =>  (if  (v1 = [] )
                  then  []
                   else  (v2::(front v1)));

fun  zip x1 =
  case  x1
  of  (v8,v7) =>  (case  v8
                   of  []  =>  (case  v7
                                of  []  =>  []
                                 |   (v2::v1) =>  (raise  Bind))
                   |   (v6::v5) =>  (case  v7
                                     of  []  =>  (raise  Bind)
                                     |   (v4::v3) =>  ((v6,v4)::(zip (v5,v3)))));

fun  el v2 v1 =
  if  (v2 <= 0)
  then  (hd v1)
  else  (el (let val  k = v2 - 1
              in
               if  (k < 0)
               then  0
                else  k
              end) (tl v1));

fun  last x1 =
  case  x1
  of  []  =>  (raise  Bind)
  |   v2::v1 =>  (if  (v1 = [] )
                  then  v2
                   else  (last v1));

fun  splitatpki v6 v7 v8 =
  case  v8
  of  []  =>  (v7 [] [] )
  |   v5::v4 =>  (if  (v6 0 v5)
                  then  (v7 [] (v5::v4))
                  else  (splitatpki (o_1 v6 (fn  v1 =>
                                              (v1 + 1))) (fn  v3 =>
                                                           (fn  v2 =>
                                                             (v7 (v5::v3) v2))) v4));

fun  part v3 v6 v4 v5 =
  case  v6
  of  []  =>  (v4,v5)
  |   v2::v1 =>  (if  (v3 v2)
                  then  (part v3 v1 (v2::v4) v5)
                  else  (part v3 v1 v4 (v2::v5)));

fun  partition v1 =  (fn  v2 => part v1 v2 [] [] );

fun  qsort v7 v8 =
  case  v8
  of  []  =>  []
   |   v6::v5 =>  (let val  v3 = partition (fn  v4 => (v7 v4 v6)) v5
                    in
                     case  v3
                     of  (v2,v1) =>  (append (append (qsort v7 v2) [v6]) (qsort v7 v1))
                   end);

fun  exp_aux v2 v3 v1 =
  if  (v3 <= 0)
  then  v1
   else  (exp_aux v2 (let val  k = v3 - 1
                       in
                        if  (k < 0)
                        then  0
                         else  k
                       end) (v2 * v1));

fun  exp v1 =  (fn  v2 => exp_aux v1 v2 1);

fun  min v1 = 
  (fn  v2 =>
    if  (v1 < v2)
    then  v1
     else  v2);

fun  max v1 = 
  (fn  v2 =>
    if  (v1 < v2)
    then  v2
     else  v1);

fun  even v1 =  (v1 mod 2) <= 0;

fun  odd v1 =  0 < (v1 mod 2);

fun  funpow v1 v2 v3 =
  if  (v2 <= 0)
  then  v3
   else  (funpow v1 (let val  k = v2 - 1
                      in
                       if  (k < 0)
                       then  0
                        else  k
                      end) (v1 v3));

fun  abs_diff v2 = 
  (fn  v1 =>
    if  (v2 < v1)
    then  (let val  k = v1 - v2
            in
             if  (k < 0)
             then  0
              else  k
            end)
    else  (let val  k = v2 - v1
            in
             if  (k < 0)
             then  0
              else  k
            end));

fun  pre v1 = 
  let val  k = v1 - 1
   in
    if  (k < 0)
    then  0
     else  k
   end;

fun charlt a b = Char.< (a,b)

fun charle a b = Char.<= (a,b)

fun  string_lt v5 v6 =
  case  v6
  of  []  =>  (0 < 0)
  |   v4::v3 =>  (case  v5
                  of  []  =>  (0 <= 0)
                  |   (v2::v1) =>  ((charlt v2 v4) orelse  ((v2 = v4) andalso  (string_lt v1 v3))));

fun  string_le v1 =  (fn  v2 => (v1 = v2) orelse  (string_lt v1 v2));

fun  string_gt v1 =  (fn  v2 => string_lt v2 v1);

fun  string_ge v1 =  (fn  v2 => string_le v2 v1);

fun  num_to_dec v1 =
  if  (v1 < 10)
  then  [Char.chr (48 + v1)]
  else  (Char.chr (48 + (v1 mod 10))::(num_to_dec (v1 div 10)));

fun  num_to_dec_string v1 =  reverse (num_to_dec v1);

fun  alookup v5 v6 =
  case  v5
  of  []  =>  NONE
  |   v4::v3 =>  (case  v4
                  of  (v2,v1) =>  (if  (v2 = v6)
                                   then  (SOME(v1))
                                   else  (alookup v3 v6)));

fun  aupdate v3 =  (fn  v4 => case  v4 of  (v2,v1) =>  ((v2,v1)::v3));

fun  aevery_aux v5 v6 v7 =
  case  v7
  of  []  =>  (0 <= 0)
  |   v4::v3 =>  (case  v4
                  of  (v2,v1) =>  (if  (member v2 v5)
                                   then  (aevery_aux v5 v6 v3)
                                   else  ((v6 (v2,v1)) andalso  (aevery_aux (v2::v5) v6 v3))));

fun  aevery v1 =  aevery_aux [] v1;

fun  amap v5 v6 =
  case  v6
  of  []  =>  []
   |   v4::v3 =>  (case  v4 of  (v2,v1) =>  ((v2,v5 v1)::(amap v5 v3)));

fun  adel v5 v6 =
  case  v5
  of  []  =>  []
   |   v4::v3 =>  (case  v4
                   of  (v2,v1) =>  (if  (v2 = v6)
                                    then  (adel v3 v6)
                                    else  ((v2,v1)::(adel v3 v6))));

fun  while_1 v1 v2 v3 =
  if  (v1 v3)
  then  (while_1 v1 v2 (v2 v3))
  else  v3;

fun  owhile v1 v2 v3 =
  if  (v1 v3)
  then  (owhile v1 v2 (v2 v3))
  else  (SOME(v3));

fun  least v3 = 
  while_1 (fn  v1 => ((v3 v1) = (0 < 0))) (fn  v2 => (v2 + 1)) 0;

fun  byte_is_nonzero v1 =  (v1 = 0w0) = (0 < 0);

datatype tokens_token =  Longidt of  char list *  char list
                      |  Symbolt of  char list
                      |  Alphat of  char list
                      |  Tyvart of  char list
                      |  Chart of  char
                      |  Stringt of  char list
                      |  Realt of  char list
                      |  Hexintt of  char list
                      |  Intt of  int
                      |  Withtypet
                      |  Witht
                      |  Whilet
                      |  Wheret
                      |  Valt
                      |  Typet
                      |  Thent
                      |  Structuret
                      |  Structt
                      |  Signaturet
                      |  Sigt
                      |  Sharingt
                      |  Rect
                      |  Raiset
                      |  Orelset
                      |  Opent
                      |  Opt
                      |  Oft
                      |  Localt
                      |  Lett
                      |  Includet
                      |  Int
                      |  Ift
                      |  Handlet
                      |  Funt
                      |  Fnt
                      |  Exceptiont
                      |  Eqtypet
                      |  Endt
                      |  Elset
                      |  Datatypet
                      |  Caset
                      |  Ast
                      |  Andalsot
                      |  Andt
                      |  Rbracet
                      |  Bart
                      |  Lbracet
                      |  Underbart
                      |  Rbrackt
                      |  Lbrackt
                      |  Darrowt
                      |  Equalst
                      |  Semicolont
                      |  Sealt
                      |  Colont
                      |  Dotst
                      |  Arrowt
                      |  Commat
                      |  Start
                      |  Rpart
                      |  Lpart
                      |  Hasht
                      |  Lexerrort
                      |  Newlinet
                      |  Whitespacet of  int;

fun  get_token v5 = 
  case  v5
  of  []  =>  Lexerrort
  |   v4::v3 =>  (case  v3
                  of  []  =>  (if  (charle v4 #";")
                               then  (if  (charle v4 #")")
                                      then  (if  (charle v4 #"'")
                                             then  (if  (v4 = #"#")
                                                    then  Hasht
                                                     else  (if  (v4 = #"'")
                                                            then  (Tyvart(v5))
                                                            else  (Symbolt(v5))))
                                             else  (if  (v4 = #"(")
                                                    then  Lpart
                                                     else  (if  (v4 = #")")
                                                            then  Rpart
                                                             else  (Symbolt(v5)))))
                                      else  (if  (charle v4 #",")
                                             then  (if  (v4 = #"*")
                                                    then  Start
                                                     else  (if  (v4 = #",")
                                                            then  Commat
                                                             else  (Symbolt(v5))))
                                             else  (if  (v4 = #":")
                                                    then  Colont
                                                     else  (if  (v4 = #";")
                                                            then  Semicolont
                                                             else  (Symbolt(v5))))))
                               else  (if  (charle v4 #"]")
                                      then  (if  (charle v4 #"Z")
                                             then  (if  ((charle #"A" v4) andalso  (charle v4 #"Z"))
                                                    then  (Alphat(v5))
                                                    else  (if  (v4 = #"=")
                                                           then  Equalst
                                                            else  (Symbolt(v5))))
                                             else  (if  (v4 = #"[")
                                                    then  Lbrackt
                                                     else  (if  (v4 = #"]")
                                                            then  Rbrackt
                                                             else  (Symbolt(v5)))))
                                      else  (if  (charle v4 #"{")
                                             then  (if  (v4 = #"_")
                                                    then  Underbart
                                                     else  (if  ((charle #"a" v4) andalso  (charle v4 #"z"))
                                                            then  (Alphat(v5))
                                                            else  (if  (v4 = #"{")
                                                                   then  Lbracet
                                                                    else  (Symbolt(v5)))))
                                             else  (if  (v4 = #"|")
                                                    then  Bart
                                                     else  (if  (v4 = #"}")
                                                            then  Rbracet
                                                             else  (Symbolt(v5)))))))
                  |   (v2::v1) =>  (if  (charlt v4 #"a")
                                    then  (if  (charle v4 #".")
                                           then  (if  (v4 = #"'")
                                                  then  (Tyvart(v5))
                                                  else  (if  (v5 = [#"-",#">"])
                                                         then  Arrowt
                                                          else  (if  (v5 = [#".",#".",#"."])
                                                                 then  Dotst
                                                                  else  (Symbolt(v5)))))
                                           else  (if  (v5 = [#":",#">"])
                                                  then  Sealt
                                                   else  (if  (v5 = [#"=",#">"])
                                                          then  Darrowt
                                                           else  (if  ((charle #"A" v4) andalso  (charle v4 #"Z"))
                                                                  then  (Alphat(v5))
                                                                  else  (Symbolt(v5))))))
                                    else  (if  (charle v4 #"z")
                                           then  (if  (charle v4 #"i")
                                                  then  (if  (charle v4 #"e")
                                                         then  (if  (charlt v4 #"e")
                                                                then  (if  (v5 = [#"a",#"n",#"d"])
                                                                       then  Andt
                                                                        else  (if  (v5 = [#"a",#"n",#"d",#"a",#"l",#"s",#"o"])
                                                                               then  Andalsot
                                                                                else  (if  (v5 = [#"a",#"s"])
                                                                                       then  Ast
                                                                                        else  (if  (v5 = [#"c",#"a",#"s",#"e"])
                                                                                               then  Caset
                                                                                                else  (if  (v5 = [#"d",#"a",#"t",#"a",#"t",#"y",#"p",#"e"])
                                                                                                       then  Datatypet
                                                                                                        else  (Alphat(v5)))))))
                                                                else  (if  (v5 = [#"e",#"l",#"s",#"e"])
                                                                       then  Elset
                                                                        else  (if  (v5 = [#"e",#"n",#"d"])
                                                                               then  Endt
                                                                                else  (if  (v5 = [#"e",#"q",#"t",#"y",#"p",#"e"])
                                                                                       then  Eqtypet
                                                                                        else  (if  (v5 = [#"e",#"x",#"c",#"e",#"p",#"t",#"i",#"o",#"n"])
                                                                                               then  Exceptiont
                                                                                                else  (Alphat(v5)))))))
                                                         else  (if  (charle v4 #"h")
                                                                then  (if  (v5 = [#"f",#"n"])
                                                                       then  Fnt
                                                                        else  (if  (v5 = [#"f",#"u",#"n"])
                                                                               then  Funt
                                                                                else  (if  (v5 = [#"h",#"a",#"n",#"d",#"l",#"e"])
                                                                                       then  Handlet
                                                                                        else  (Alphat(v5)))))
                                                                else  (if  (v5 = [#"i",#"f"])
                                                                       then  Ift
                                                                        else  (if  (v5 = [#"i",#"n"])
                                                                               then  Int
                                                                                else  (if  (v5 = [#"i",#"n",#"c",#"l",#"u",#"d",#"e"])
                                                                                       then  Includet
                                                                                        else  (Alphat(v5)))))))
                                                  else  (if  (charle v4 #"r")
                                                         then  (if  (v4 = #"l")
                                                                then  (if  (v5 = [#"l",#"e",#"t"])
                                                                       then  Lett
                                                                        else  (if  (v5 = [#"l",#"o",#"c",#"a",#"l"])
                                                                               then  Localt
                                                                                else  (Alphat(v5))))
                                                                else  (if  (v4 = #"o")
                                                                       then  (if  (v5 = [#"o",#"f"])
                                                                              then  Oft
                                                                               else  (if  (v5 = [#"o",#"p"])
                                                                                      then  Opt
                                                                                       else  (if  (v5 = [#"o",#"p",#"e",#"n"])
                                                                                              then  Opent
                                                                                               else  (if  (v5 = [#"o",#"r",#"e",#"l",#"s",#"e"])
                                                                                                      then  Orelset
                                                                                                       else  (Alphat(v5))))))
                                                                       else  (if  (v5 = [#"r",#"a",#"i",#"s",#"e"])
                                                                              then  Raiset
                                                                               else  (if  (v5 = [#"r",#"e",#"c"])
                                                                                      then  Rect
                                                                                       else  (Alphat(v5))))))
                                                         else  (if  (v4 = #"s")
                                                                then  (if  (v5 = [#"s",#"h",#"a",#"r",#"i",#"n",#"g"])
                                                                       then  Sharingt
                                                                        else  (if  (v5 = [#"s",#"i",#"g"])
                                                                               then  Sigt
                                                                                else  (if  (v5 = [#"s",#"i",#"g",#"n",#"a",#"t",#"u",#"r",#"e"])
                                                                                       then  Signaturet
                                                                                        else  (if  (v5 = [#"s",#"t",#"r",#"u",#"c",#"t"])
                                                                                               then  Structt
                                                                                                else  (if  (v5 = [#"s",#"t",#"r",#"u",#"c",#"t",#"u",#"r",#"e"])
                                                                                                       then  Structuret
                                                                                                        else  (Alphat(v5)))))))
                                                                else  (if  (charlt v4 #"w")
                                                                       then  (if  (v5 = [#"t",#"h",#"e",#"n"])
                                                                              then  Thent
                                                                               else  (if  (v5 = [#"t",#"y",#"p",#"e"])
                                                                                      then  Typet
                                                                                       else  (if  (v5 = [#"v",#"a",#"l"])
                                                                                              then  Valt
                                                                                               else  (Alphat(v5)))))
                                                                       else  (if  (v5 = [#"w",#"h",#"e",#"r",#"e"])
                                                                              then  Wheret
                                                                               else  (if  (v5 = [#"w",#"i",#"t",#"h"])
                                                                                      then  Witht
                                                                                       else  (if  (v5 = [#"w",#"i",#"t",#"h",#"t",#"y",#"p",#"e"])
                                                                                              then  Withtypet
                                                                                               else  (Alphat(v5)))))))))
                                           else  (Symbolt(v5)))));

datatype lexer_fun_symbol =  Errors
                          |  Others of  char list
                          |  Longs of  char list
                          |  Numbers of  int
                          |  Chars of  char
                          |  Strings of  char list;

fun  isspace v1 = 
  ((Char.ord v1) = 32) orelse  ((9 <= (Char.ord v1)) andalso  ((Char.ord v1) <= 13));

fun  isdigit v1 =  (48 <= (Char.ord v1)) andalso  ((Char.ord v1) <= 57);

fun  implode v3 =
  case  v3
  of  []  =>  []
   |   v2::v1 =>  (v2::(implode v1));

fun  read_while v3 v4 v5 =
  case  v4
  of  []  =>  (implode (reverse v5),[] )
  |   v2::v1 =>  (if  (v3 v2)
                  then  (read_while v3 v1 (v2::v5))
                  else  (implode (reverse v5),v2::v1));

fun  l2n v3 v4 =
  case  v4
  of  []  =>  0
  |   v2::v1 =>  ((v2 mod v3) + (v3 * (l2n v3 v1)));

fun  s2n v1 =  (fn  v2 => (fn  v3 => l2n v1 (map v2 (reverse v3))));

fun  unhex x1 = 
  if  (x1 = #"0")
  then  0
   else  (if  (x1 = #"1")
          then  1
           else  (if  (x1 = #"2")
                  then  2
                   else  (if  (x1 = #"3")
                          then  3
                           else  (if  (x1 = #"4")
                                  then  4
                                   else  (if  (x1 = #"5")
                                          then  5
                                           else  (if  (x1 = #"6")
                                                  then  6
                                                   else  (if  (x1 = #"7")
                                                          then  7
                                                           else  (if  (x1 = #"8")
                                                                  then  8
                                                                   else  (if  (x1 = #"9")
                                                                          then  9
                                                                           else  (if  (x1 = #"a")
                                                                                  then  10
                                                                                   else  (if  (x1 = #"b")
                                                                                          then  11
                                                                                           else  (if  (x1 = #"c")
                                                                                                  then  12
                                                                                                   else  (if  (x1 = #"d")
                                                                                                          then  13
                                                                                                           else  (if  (x1 = #"e")
                                                                                                                  then  14
                                                                                                                   else  (if  (x1 = #"f")
                                                                                                                          then  15
                                                                                                                           else  (if  (x1 = #"A")
                                                                                                                                  then  10
                                                                                                                                   else  (if  (x1 = #"B")
                                                                                                                                          then  11
                                                                                                                                           else  (if  (x1 = #"C")
                                                                                                                                                  then  12
                                                                                                                                                   else  (if  (x1 = #"D")
                                                                                                                                                          then  13
                                                                                                                                                           else  (if  (x1 = #"E")
                                                                                                                                                                  then  14
                                                                                                                                                                   else  (if  (x1 = #"F")
                                                                                                                                                                          then  15
                                                                                                                                                                           else  (raise  Bind))))))))))))))))))))));

fun  unhex_alt v1 = 
  if  (isdigit v1)
  then  (unhex v1)
  else  0;

fun  num_from_dec_string_alt v1 =  s2n 10 unhex_alt v1;

fun  islower v1 = 
  (97 <= (Char.ord v1)) andalso  ((Char.ord v1) <= 122);

fun  isupper v1 =  (65 <= (Char.ord v1)) andalso  ((Char.ord v1) <= 90);

fun  isalpha v1 =  (islower v1) orelse  (isupper v1);

fun  isalphanum v1 =  (isalpha v1) orelse  (isdigit v1);

fun  isalphanumprime v1 = 
  (isalphanum v1) orelse  ((v1 = #"'") orelse  (v1 = #"_"));

fun  read_string v4 v3 =
  if  (v4 = [] )
  then  (Errors,[] )
  else  (if  ((hd v4) = #"\"")
         then  (Strings(v3),tl v4)
         else  (if  ((hd v4) = #"\n")
                then  (Errors,tl v4)
                else  (if  (((hd v4) = #"\\") = (0 < 0))
                       then  (read_string (tl v4) (append v3 [hd v4]))
                       else  (case  (tl v4)
                              of  []  =>  (Errors,tl v4)
                              |   (v2::v1) =>  (if  (v2 = #"\\")
                                                then  (read_string v1 (append v3 [#"\\"]))
                                                else  (if  (v2 = #"\"")
                                                       then  (read_string v1 (append v3 [#"\""]))
                                                       else  (if  (v2 = #"n")
                                                              then  (read_string v1 (append v3 [#"\n"]))
                                                              else  (if  (v2 = #"t")
                                                                     then  (read_string v1 (append v3 [#"\t"]))
                                                                     else  (Errors,tl v4)))))))));

fun  mkchars v6 = 
  case  v6
  of  Strings(v1) =>  (if  ((length v1) = 1)
                       then  (Chars(hd v1))
                       else  Errors)
  |   Chars(v2) =>  Errors
  |   Numbers(v3) =>  Errors
  |   Longs(v4) =>  Errors
  |   Others(v5) =>  Errors
  |   Errors =>  Errors;

fun  skip_comment v5 v6 =
  case  v5
  of  []  =>  NONE
  |   v4::v3 =>  (case  v3
                  of  []  =>  NONE
                  |   (v2::v1) =>  (if  ([v4,v2] = [#"(",#"*"])
                                    then  (skip_comment v1 (v6 + 1))
                                    else  (if  ([v4,v2] = [#"*",#")"])
                                           then  (if  (v6 = 0)
                                                  then  (SOME(v1))
                                                  else  (skip_comment v1 (v6 - 1)))
                                           else  (skip_comment (v2::v1) v6))));

fun  is_single_char_symbol v1 = 
  member v1 [#"(",#")",#"[",#"]",#"{",#"}",#",",#";"];

fun  issymbol v1 = 
  member v1 [#"`",#"!",#"%",#"&",#"$",#"#",#"+",#"-",#"/",#":",#"<",#"=",#">",#"?",#"@",#"\\",#"~",#"^",#"|",#"*"];

fun  next_sym_alt v35 =
  case  v35
  of  []  =>  NONE
  |   v34::v33 =>  (if  (isspace v34)
                    then  (next_sym_alt v33)
                    else  (if  (isdigit v34)
                           then  (let val  v3 =
                                    read_while isdigit v33 []
                                   in
                                    case  v3
                                    of  (v2,v1) =>  (let val  x =
                                                       (Numbers(num_from_dec_string_alt (v34::v2)),v1)
                                                     in
                                                       SOME(x)
                                                     end)
                                  end)
                           else  (if  ((v34 = #"~") andalso  (if  (v33 = [] )
                                                              then  (0 < 0)
                                                              else  (isdigit (hd v33))))
                                  then  (let val  v6 =
                                           read_while isdigit v33 []
                                          in
                                           case  v6
                                           of  (v5,v4) =>  (let val  x =
                                                              (Numbers(0 - (num_from_dec_string_alt v5)),v4)
                                                            in
                                                              SOME(x)
                                                            end)
                                         end)
                                  else  (if  (v34 = #"'")
                                         then  (let val  v9 =
                                                  read_while isalphanumprime v33 [#"'"]
                                                in
                                                  case  v9
                                                  of  (v8,v7) =>  (let val  x =
                                                                     (Others(v8),v7)
                                                                   in
                                                                     SOME(x)
                                                                   end)
                                                end)
                                         else  (if  (v34 = #"\"")
                                                then  (let val  v12 =
                                                         read_string v33 []
                                                        in
                                                         case  v12
                                                         of  (v11,v10) =>  (let val  x =
                                                                              (v11,v10)
                                                                            in
                                                                              SOME(x)
                                                                            end)
                                                       end)
                                                else  (if  (isprefix [#"*",#")"] (v34::v33))
                                                       then  (let val  x =
                                                                (Errors,tl v33)
                                                              in
                                                                SOME(x)
                                                              end)
                                                       else  (if  (isprefix [#"#",#"\""] (v34::v33))
                                                              then  (let val  v15 =
                                                                       read_string (tl v33) []
                                                                      in
                                                                       case  v15
                                                                       of  (v14,v13) =>  (let val  x =
                                                                                            (mkchars v14,v13)
                                                                                          in
                                                                                            SOME(x)
                                                                                          end)
                                                                     end)
                                                              else  (if  (isprefix [#"(",#"*"] (v34::v33))
                                                                     then  (case  (skip_comment (tl v33) 0)
                                                                            of  NONE =>  (let val  x =
                                                                                            (Errors,[] )
                                                                                          in
                                                                                            SOME(x)
                                                                                          end)
                                                                            |   (SOME(v16)) =>  (next_sym_alt v16))
                                                                     else  (if  (is_single_char_symbol v34)
                                                                            then  (let val  x =
                                                                                     (Others([v34]),v33)
                                                                                   in
                                                                                     SOME(x)
                                                                                   end)
                                                                            else  (if  (issymbol v34)
                                                                                   then  (let val  v19 =
                                                                                            read_while issymbol v33 [v34]
                                                                                          in
                                                                                            case  v19
                                                                                            of  (v18,v17) =>  (let val  x =
                                                                                                                 (Others(v18),v17)
                                                                                                               in
                                                                                                                 SOME(x)
                                                                                                               end)
                                                                                          end)
                                                                                   else  (if  (isalpha v34)
                                                                                          then  (let val  v32 =
                                                                                                   read_while isalphanumprime v33 [v34]
                                                                                                 in
                                                                                                   case  v32
                                                                                                   of  (v31,v30) =>  (case  v30
                                                                                                                      of  []  =>  (let val  x =
                                                                                                                                     (Others(v31),v30)
                                                                                                                                   in
                                                                                                                                     SOME(x)
                                                                                                                                   end)
                                                                                                                      |   (v29::v28) =>  (if  (v29 = #".")
                                                                                                                                          then  (case  v28
                                                                                                                                                 of  []  =>  (let val  x =
                                                                                                                                                                (Errors,[] )
                                                                                                                                                              in
                                                                                                                                                                SOME(x)
                                                                                                                                                              end)
                                                                                                                                                 |   (v27::v26) =>  (if  (isalpha v27)
                                                                                                                                                                     then  (let val  v22 =
                                                                                                                                                                              read_while isalphanumprime v26 [v27]
                                                                                                                                                                            in
                                                                                                                                                                              case  v22
                                                                                                                                                                              of  (v21,v20) =>  (let val  x =
                                                                                                                                                                                                   (Longs(append (append v31 [#"."]) v21),v20)
                                                                                                                                                                                                 in
                                                                                                                                                                                                   SOME(x)
                                                                                                                                                                                                 end)
                                                                                                                                                                            end)
                                                                                                                                                                     else  (if  (issymbol v27)
                                                                                                                                                                            then  (let val  v25 =
                                                                                                                                                                                     read_while issymbol v26 [v27]
                                                                                                                                                                                   in
                                                                                                                                                                                     case  v25
                                                                                                                                                                                     of  (v24,v23) =>  (let val  x =
                                                                                                                                                                                                          (Longs(append (append v31 [#"."]) v24),v23)
                                                                                                                                                                                                        in
                                                                                                                                                                                                          SOME(x)
                                                                                                                                                                                                        end)
                                                                                                                                                                                   end)
                                                                                                                                                                            else  (let val  x =
                                                                                                                                                                                     (Errors,v26)
                                                                                                                                                                                   in
                                                                                                                                                                                     SOME(x)
                                                                                                                                                                                   end))))
                                                                                                                                          else  (let val  x =
                                                                                                                                                   (Others(v31),v30)
                                                                                                                                                 in
                                                                                                                                                   SOME(x)
                                                                                                                                                 end)))
                                                                                                 end)
                                                                                          else  (if  (v34 = #"_")
                                                                                                 then  (let val  x =
                                                                                                          (Others([#"_"]),v33)
                                                                                                        in
                                                                                                          SOME(x)
                                                                                                        end)
                                                                                                 else  (let val  x =
                                                                                                          (Errors,v33)
                                                                                                        in
                                                                                                          SOME(x)
                                                                                                        end)))))))))))));

fun  splitp v3 v4 =
  case  v4
  of  []  =>  ([] ,[] )
  |   v2::v1 =>  (if  (v3 v2)
                  then  ([] ,v2::v1)
                  else  (v2::(fst (splitp v3 v1)),snd (splitp v3 v1)));

fun  token_of_sym v12 = 
  case  v12
  of  Strings(v1) =>  (Stringt(v1))
  |   Chars(v2) =>  (Chart(v2))
  |   Numbers(v3) =>  (Intt(v3))
  |   Longs(v10) =>  (let val  v8 = splitp (fn  v9 => (v9 = #".")) v10
                       in
                        case  v8
                        of  (v7,v6) =>  (Longidt(v7,case  v6
                                                    of  []  =>  []
                                                     |   v5::v4 =>  v4))
                      end)
  |   Others(v11) =>  (get_token v11)
  |   Errors =>  Lexerrort;

fun  next_token v4 = 
  case  (next_sym_alt v4)
  of  NONE =>  NONE
  |   SOME(v3) =>  (case  v3
                    of  (v2,v1) =>  (let val  x = (token_of_sym v2,v1)
                                     in
                                       SOME(x)
                                     end));

fun  lexer_fun v4 =
  case  (next_token v4)
  of  NONE =>  []
   |   SOME(v3) =>  (case  v3 of  (v2,v1) =>  (v2::(lexer_fun v1)));

datatype ( 'a  ,  'b ) grammar_symbol =  Nt of  ('b  ,  int) sum
                                      |  Tok of  'a ;

datatype ( 'a  ,  'b ) grammar_parsetree =  Nd of  ('b  ,  int) sum *  ('a  ,  'b ) grammar_parsetree list
                                         |  Lf of  ('a  ,  'b ) grammar_symbol;

datatype gram_MMLnonT =  Naddops
                      |  Nandfdecls
                      |  Ncompops
                      |  Nconstructorname
                      |  Ndtype
                      |  Ndconstructor
                      |  Ndecl
                      |  Ndecls
                      |  Ndtypecons
                      |  Ndtypedecl
                      |  Ndtypedecls
                      |  Ne
                      |  Ne'
                      |  Neadd
                      |  Neapp
                      |  Nebase
                      |  Nebefore
                      |  Necomp
                      |  Nehandle
                      |  Nelist1
                      |  Nelist2
                      |  Nelistop
                      |  Nelogicand
                      |  Nelogicor
                      |  Nemult
                      |  Nerel
                      |  Neseq
                      |  Netuple
                      |  Netyped
                      |  Nfdecl
                      |  Nfqv
                      |  Nletdec
                      |  Nletdecs
                      |  Nlistops
                      |  Nmultops
                      |  Nnonetopleveldecs
                      |  Nopid
                      |  Nopttypeqn
                      |  Noptionalsignatureascription
                      |  Npe
                      |  Npe'
                      |  Npes
                      |  Nptype
                      |  Npapp
                      |  Npattern
                      |  Npatternlist
                      |  Npbase
                      |  Npbaselist1
                      |  Npcons
                      |  Nptuple
                      |  Nrelops
                      |  Nsignaturevalue
                      |  Nspecline
                      |  Nspeclinelist
                      |  Nstructname
                      |  Nstructure
                      |  Ntbase
                      |  Ntopleveldec
                      |  Ntopleveldecs
                      |  Ntyop
                      |  Ntyvarlist
                      |  Ntype
                      |  Ntypeabbrevdec
                      |  Ntypedec
                      |  Ntypelist1
                      |  Ntypelist2
                      |  Ntypename
                      |  Ntyvarn
                      |  Nuqconstructorname
                      |  Nuqtyop
                      |  Nv;

datatype ( 'a  , 'c ) peg_pegsym =  Not of  ('a  ,  'c ) peg_pegsym *  'c
                                          |  Rpt of  ('a  ,  'c ) peg_pegsym *  ('c list ->  'c )
                                         |  Choice of  ('a  ,  'c ) peg_pegsym *  ('a  , 'c ) peg_pegsym *  (('c  ,  'c ) sum ->  'c )
                                         |  Seq of  ('a  ,  'c ) peg_pegsym *  ('a  ,  'c ) peg_pegsym *  ('c  ->  ('c  ->  'c ) )
                                         |  Nt_1 of  (gram_MMLnonT  ,  int) sum *  ('c  ->  'c )
                                         |  Tok_1 of  ('a  ->  bool)  *  ('a  ->  'c )
                                         |  Any of  ('a  ->  'c )
                                         |  Empty of  'c ;

datatype ( 'a  ,  'c ) peg_peg =  Recordtypepeg of  ('a  ,  'c ) peg_pegsym *  ((gram_MMLnonT  ,  int) sum *  ('a  ,  'c ) peg_pegsym) list;

fun  peg_start v3 =  case  v3 of  Recordtypepeg(v2,v1) =>  v2;

fun  peg_rules v3 =  case  v3 of  Recordtypepeg(v2,v1) =>  v1;

fun  peg_start_fupd v3 = 
  (fn  v4 =>
    case  v4 of  Recordtypepeg(v2,v1) =>  (Recordtypepeg(v3 v2,v1)));

fun  peg_rules_fupd v3 = 
  (fn  v4 =>
    case  v4 of  Recordtypepeg(v2,v1) =>  (Recordtypepeg(v2,v3 v1)));

fun  pnt v1 =  Nt_1(Inl(v1),i);

fun  fupdate_list v1 =  foldl aupdate v1;

fun  sumid v3 = 
  case  v3
  of  Inl(v1) =>  v1
  |   Inr(v2) =>  v2;

fun  choicel v3 =
  case  v3
  of  []  =>  (Not(Empty([] ),[] ))
  |   v2::v1 =>  (Choice(v2,choicel v1,sumid));

fun  option_bind v3 = 
  (fn  v2 =>
    case  v3
    of  NONE =>  NONE
    |   SOME(v1) =>  (v2 v1));

fun  destalphat v12 = 
  case  v12
  of  Whitespacet(v1) =>  NONE
  |   Newlinet =>  NONE
  |   Lexerrort =>  NONE
  |   Hasht =>  NONE
  |   Lpart =>  NONE
  |   Rpart =>  NONE
  |   Start =>  NONE
  |   Commat =>  NONE
  |   Arrowt =>  NONE
  |   Dotst =>  NONE
  |   Colont =>  NONE
  |   Sealt =>  NONE
  |   Semicolont =>  NONE
  |   Equalst =>  NONE
  |   Darrowt =>  NONE
  |   Lbrackt =>  NONE
  |   Rbrackt =>  NONE
  |   Underbart =>  NONE
  |   Lbracet =>  NONE
  |   Bart =>  NONE
  |   Rbracet =>  NONE
  |   Andt =>  NONE
  |   Andalsot =>  NONE
  |   Ast =>  NONE
  |   Caset =>  NONE
  |   Datatypet =>  NONE
  |   Elset =>  NONE
  |   Endt =>  NONE
  |   Eqtypet =>  NONE
  |   Exceptiont =>  NONE
  |   Fnt =>  NONE
  |   Funt =>  NONE
  |   Handlet =>  NONE
  |   Ift =>  NONE
  |   Int =>  NONE
  |   Includet =>  NONE
  |   Lett =>  NONE
  |   Localt =>  NONE
  |   Oft =>  NONE
  |   Opt =>  NONE
  |   Opent =>  NONE
  |   Orelset =>  NONE
  |   Raiset =>  NONE
  |   Rect =>  NONE
  |   Sharingt =>  NONE
  |   Sigt =>  NONE
  |   Signaturet =>  NONE
  |   Structt =>  NONE
  |   Structuret =>  NONE
  |   Thent =>  NONE
  |   Typet =>  NONE
  |   Valt =>  NONE
  |   Wheret =>  NONE
  |   Whilet =>  NONE
  |   Witht =>  NONE
  |   Withtypet =>  NONE
  |   Intt(v2) =>  NONE
  |   Hexintt(v3) =>  NONE
  |   Realt(v4) =>  NONE
  |   Stringt(v5) =>  NONE
  |   Chart(v6) =>  NONE
  |   Tyvart(v7) =>  NONE
  |   Alphat(v8) =>  (SOME(v8))
  |   Symbolt(v9) =>  NONE
  |   Longidt(v11,v10) =>  NONE;

fun  option_guard v1 = 
  if  v1
   then  (let val  x = ()
          in
            SOME(x)
          end)
  else  NONE;

fun  bindnt v2 =  (fn  v1 => [Nd(Inl(v2),v1)]);

fun  mktoklf v1 =  [Lf(Tok(v1))];

fun  destsymbolt v12 = 
  case  v12
  of  Whitespacet(v1) =>  NONE
  |   Newlinet =>  NONE
  |   Lexerrort =>  NONE
  |   Hasht =>  NONE
  |   Lpart =>  NONE
  |   Rpart =>  NONE
  |   Start =>  NONE
  |   Commat =>  NONE
  |   Arrowt =>  NONE
  |   Dotst =>  NONE
  |   Colont =>  NONE
  |   Sealt =>  NONE
  |   Semicolont =>  NONE
  |   Equalst =>  NONE
  |   Darrowt =>  NONE
  |   Lbrackt =>  NONE
  |   Rbrackt =>  NONE
  |   Underbart =>  NONE
  |   Lbracet =>  NONE
  |   Bart =>  NONE
  |   Rbracet =>  NONE
  |   Andt =>  NONE
  |   Andalsot =>  NONE
  |   Ast =>  NONE
  |   Caset =>  NONE
  |   Datatypet =>  NONE
  |   Elset =>  NONE
  |   Endt =>  NONE
  |   Eqtypet =>  NONE
  |   Exceptiont =>  NONE
  |   Fnt =>  NONE
  |   Funt =>  NONE
  |   Handlet =>  NONE
  |   Ift =>  NONE
  |   Int =>  NONE
  |   Includet =>  NONE
  |   Lett =>  NONE
  |   Localt =>  NONE
  |   Oft =>  NONE
  |   Opt =>  NONE
  |   Opent =>  NONE
  |   Orelset =>  NONE
  |   Raiset =>  NONE
  |   Rect =>  NONE
  |   Sharingt =>  NONE
  |   Sigt =>  NONE
  |   Signaturet =>  NONE
  |   Structt =>  NONE
  |   Structuret =>  NONE
  |   Thent =>  NONE
  |   Typet =>  NONE
  |   Valt =>  NONE
  |   Wheret =>  NONE
  |   Whilet =>  NONE
  |   Witht =>  NONE
  |   Withtypet =>  NONE
  |   Intt(v2) =>  NONE
  |   Hexintt(v3) =>  NONE
  |   Realt(v4) =>  NONE
  |   Stringt(v5) =>  NONE
  |   Chart(v6) =>  NONE
  |   Tyvart(v7) =>  NONE
  |   Alphat(v8) =>  NONE
  |   Symbolt(v9) =>  (SOME(v9))
  |   Longidt(v11,v10) =>  NONE;

val  peg_v =
  choicel [Tok_1((fn  v2 =>
                   (option_bind (destalphat v2) (fn  v1 =>
                                                  (option_guard ((((v1 = [#"b",#"e",#"f",#"o",#"r",#"e"]) = (0 < 0)) andalso  (((v1 = [#"d",#"i",#"v"]) = (0 < 0)) andalso  (((v1 = [#"m",#"o",#"d"]) = (0 < 0)) andalso  (((v1 = [#"o"]) = (0 < 0)) andalso  (((v1 = [#"t",#"r",#"u",#"e"]) = (0 < 0)) andalso  (((v1 = [#"f",#"a",#"l",#"s",#"e"]) = (0 < 0)) andalso  (((v1 = [#"r",#"e",#"f"]) = (0 < 0)) andalso  ((v1 = [#"n",#"i",#"l"]) = (0 < 0))))))))) andalso  (if  (v1 = [] )
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            then  (0 < 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            else  ((isupper (hd v1)) = (0 < 0))))))) = (let val  x =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        in
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          SOME(x)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        end)),o_1 (bindnt Nv) mktoklf),Tok_1((fn  v4 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (option_bind (destsymbolt v4) (fn  v3 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (option_guard (((v3 = [#"+"]) = (0 < 0)) andalso  (((v3 = [#"-"]) = (0 < 0)) andalso  (((v3 = [#"/"]) = (0 < 0)) andalso  (((v3 = [#"<"]) = (0 < 0)) andalso  (((v3 = [#">"]) = (0 < 0)) andalso  (((v3 = [#"<",#"="]) = (0 < 0)) andalso  (((v3 = [#">",#"="]) = (0 < 0)) andalso  (((v3 = [#"<",#">"]) = (0 < 0)) andalso  (((v3 = [#":",#"="]) = (0 < 0)) andalso  (((v3 = [#"*"]) = (0 < 0)) andalso  (((v3 = [#":",#":"]) = (0 < 0)) andalso  ((v3 = [#"@"]) = (0 < 0)))))))))))))))) = (let val  x =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               ()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             in
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               SOME(x)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             end)),o_1 (bindnt Nv) mktoklf)];

fun  pegf v4 = 
  (fn  v3 => Seq(v4,Empty([] ),(fn  v2 => (fn  v1 => v3 v2))));

fun  istyvart v12 = 
  case  v12
  of  Whitespacet(v1) =>  (0 < 0)
  |   Newlinet =>  (0 < 0)
  |   Lexerrort =>  (0 < 0)
  |   Hasht =>  (0 < 0)
  |   Lpart =>  (0 < 0)
  |   Rpart =>  (0 < 0)
  |   Start =>  (0 < 0)
  |   Commat =>  (0 < 0)
  |   Arrowt =>  (0 < 0)
  |   Dotst =>  (0 < 0)
  |   Colont =>  (0 < 0)
  |   Sealt =>  (0 < 0)
  |   Semicolont =>  (0 < 0)
  |   Equalst =>  (0 < 0)
  |   Darrowt =>  (0 < 0)
  |   Lbrackt =>  (0 < 0)
  |   Rbrackt =>  (0 < 0)
  |   Underbart =>  (0 < 0)
  |   Lbracet =>  (0 < 0)
  |   Bart =>  (0 < 0)
  |   Rbracet =>  (0 < 0)
  |   Andt =>  (0 < 0)
  |   Andalsot =>  (0 < 0)
  |   Ast =>  (0 < 0)
  |   Caset =>  (0 < 0)
  |   Datatypet =>  (0 < 0)
  |   Elset =>  (0 < 0)
  |   Endt =>  (0 < 0)
  |   Eqtypet =>  (0 < 0)
  |   Exceptiont =>  (0 < 0)
  |   Fnt =>  (0 < 0)
  |   Funt =>  (0 < 0)
  |   Handlet =>  (0 < 0)
  |   Ift =>  (0 < 0)
  |   Int =>  (0 < 0)
  |   Includet =>  (0 < 0)
  |   Lett =>  (0 < 0)
  |   Localt =>  (0 < 0)
  |   Oft =>  (0 < 0)
  |   Opt =>  (0 < 0)
  |   Opent =>  (0 < 0)
  |   Orelset =>  (0 < 0)
  |   Raiset =>  (0 < 0)
  |   Rect =>  (0 < 0)
  |   Sharingt =>  (0 < 0)
  |   Sigt =>  (0 < 0)
  |   Signaturet =>  (0 < 0)
  |   Structt =>  (0 < 0)
  |   Structuret =>  (0 < 0)
  |   Thent =>  (0 < 0)
  |   Typet =>  (0 < 0)
  |   Valt =>  (0 < 0)
  |   Wheret =>  (0 < 0)
  |   Whilet =>  (0 < 0)
  |   Witht =>  (0 < 0)
  |   Withtypet =>  (0 < 0)
  |   Intt(v2) =>  (0 < 0)
  |   Hexintt(v3) =>  (0 < 0)
  |   Realt(v4) =>  (0 < 0)
  |   Stringt(v5) =>  (0 < 0)
  |   Chart(v6) =>  (0 < 0)
  |   Tyvart(v7) =>  (0 <= 0)
  |   Alphat(v8) =>  (0 < 0)
  |   Symbolt(v9) =>  (0 < 0)
  |   Longidt(v11,v10) =>  (0 < 0);

fun  destlongidt v12 = 
  case  v12
  of  Whitespacet(v1) =>  NONE
  |   Newlinet =>  NONE
  |   Lexerrort =>  NONE
  |   Hasht =>  NONE
  |   Lpart =>  NONE
  |   Rpart =>  NONE
  |   Start =>  NONE
  |   Commat =>  NONE
  |   Arrowt =>  NONE
  |   Dotst =>  NONE
  |   Colont =>  NONE
  |   Sealt =>  NONE
  |   Semicolont =>  NONE
  |   Equalst =>  NONE
  |   Darrowt =>  NONE
  |   Lbrackt =>  NONE
  |   Rbrackt =>  NONE
  |   Underbart =>  NONE
  |   Lbracet =>  NONE
  |   Bart =>  NONE
  |   Rbracet =>  NONE
  |   Andt =>  NONE
  |   Andalsot =>  NONE
  |   Ast =>  NONE
  |   Caset =>  NONE
  |   Datatypet =>  NONE
  |   Elset =>  NONE
  |   Endt =>  NONE
  |   Eqtypet =>  NONE
  |   Exceptiont =>  NONE
  |   Fnt =>  NONE
  |   Funt =>  NONE
  |   Handlet =>  NONE
  |   Ift =>  NONE
  |   Int =>  NONE
  |   Includet =>  NONE
  |   Lett =>  NONE
  |   Localt =>  NONE
  |   Oft =>  NONE
  |   Opt =>  NONE
  |   Opent =>  NONE
  |   Orelset =>  NONE
  |   Raiset =>  NONE
  |   Rect =>  NONE
  |   Sharingt =>  NONE
  |   Sigt =>  NONE
  |   Signaturet =>  NONE
  |   Structt =>  NONE
  |   Structuret =>  NONE
  |   Thent =>  NONE
  |   Typet =>  NONE
  |   Valt =>  NONE
  |   Wheret =>  NONE
  |   Whilet =>  NONE
  |   Witht =>  NONE
  |   Withtypet =>  NONE
  |   Intt(v2) =>  NONE
  |   Hexintt(v3) =>  NONE
  |   Realt(v4) =>  NONE
  |   Stringt(v5) =>  NONE
  |   Chart(v6) =>  NONE
  |   Tyvart(v7) =>  NONE
  |   Alphat(v8) =>  NONE
  |   Symbolt(v9) =>  NONE
  |   Longidt(v11,v10) =>  (let val  x = (v11,v10)
                            in
                              SOME(x)
                            end);

val  peg_longv =
  Tok_1((fn  v4 =>
          (option_bind (destlongidt v4) (fn  v3 =>
                                          (case  v3
                                           of  (v2,v1) =>  (option_guard (if  (v1 = [] )
                                                                          then  (0 < 0)
                                                                          else  (((((if  (isalpha (hd v1))
                                                                                     then  ((isupper (hd v1)) = (0 < 0))
                                                                                     else  (0 <= 0)) andalso  ((v1 = [#"r",#"e",#"f"]) = (0 < 0))) andalso  ((v1 = [#"t",#"r",#"u",#"e"]) = (0 < 0))) andalso  ((v1 = [#"f",#"a",#"l",#"s",#"e"]) = (0 < 0))) andalso  ((v1 = [#"n",#"i",#"l"]) = (0 < 0)))))))) = (let val  x =
                                                                                                                                                                                                                                                                                                                      ()
                                                                                                                                                                                                                                                                                                                    in
                                                                                                                                                                                                                                                                                                                      SOME(x)
                                                                                                                                                                                                                                                                                                                    end)),o_1 (bindnt Nfqv) mktoklf);

fun  seql v4 = 
  (fn  v3 =>
    pegf (foldr (fn  v2 =>
                  (fn  v1 => (Seq(v2,v1,append)))) (Empty([] )) v4) v3);

fun  try v1 =  choicel [v1,Empty([] )];

fun  tokeq v2 =  Tok_1((fn  v1 => v2 = v1),mktoklf);

fun  isint v12 = 
  case  v12
  of  Whitespacet(v1) =>  (0 < 0)
  |   Newlinet =>  (0 < 0)
  |   Lexerrort =>  (0 < 0)
  |   Hasht =>  (0 < 0)
  |   Lpart =>  (0 < 0)
  |   Rpart =>  (0 < 0)
  |   Start =>  (0 < 0)
  |   Commat =>  (0 < 0)
  |   Arrowt =>  (0 < 0)
  |   Dotst =>  (0 < 0)
  |   Colont =>  (0 < 0)
  |   Sealt =>  (0 < 0)
  |   Semicolont =>  (0 < 0)
  |   Equalst =>  (0 < 0)
  |   Darrowt =>  (0 < 0)
  |   Lbrackt =>  (0 < 0)
  |   Rbrackt =>  (0 < 0)
  |   Underbart =>  (0 < 0)
  |   Lbracet =>  (0 < 0)
  |   Bart =>  (0 < 0)
  |   Rbracet =>  (0 < 0)
  |   Andt =>  (0 < 0)
  |   Andalsot =>  (0 < 0)
  |   Ast =>  (0 < 0)
  |   Caset =>  (0 < 0)
  |   Datatypet =>  (0 < 0)
  |   Elset =>  (0 < 0)
  |   Endt =>  (0 < 0)
  |   Eqtypet =>  (0 < 0)
  |   Exceptiont =>  (0 < 0)
  |   Fnt =>  (0 < 0)
  |   Funt =>  (0 < 0)
  |   Handlet =>  (0 < 0)
  |   Ift =>  (0 < 0)
  |   Int =>  (0 < 0)
  |   Includet =>  (0 < 0)
  |   Lett =>  (0 < 0)
  |   Localt =>  (0 < 0)
  |   Oft =>  (0 < 0)
  |   Opt =>  (0 < 0)
  |   Opent =>  (0 < 0)
  |   Orelset =>  (0 < 0)
  |   Raiset =>  (0 < 0)
  |   Rect =>  (0 < 0)
  |   Sharingt =>  (0 < 0)
  |   Sigt =>  (0 < 0)
  |   Signaturet =>  (0 < 0)
  |   Structt =>  (0 < 0)
  |   Structuret =>  (0 < 0)
  |   Thent =>  (0 < 0)
  |   Typet =>  (0 < 0)
  |   Valt =>  (0 < 0)
  |   Wheret =>  (0 < 0)
  |   Whilet =>  (0 < 0)
  |   Witht =>  (0 < 0)
  |   Withtypet =>  (0 < 0)
  |   Intt(v2) =>  (0 <= 0)
  |   Hexintt(v3) =>  (0 < 0)
  |   Realt(v4) =>  (0 < 0)
  |   Stringt(v5) =>  (0 < 0)
  |   Chart(v6) =>  (0 < 0)
  |   Tyvart(v7) =>  (0 < 0)
  |   Alphat(v8) =>  (0 < 0)
  |   Symbolt(v9) =>  (0 < 0)
  |   Longidt(v11,v10) =>  (0 < 0);

fun  isstring v12 = 
  case  v12
  of  Whitespacet(v1) =>  (0 < 0)
  |   Newlinet =>  (0 < 0)
  |   Lexerrort =>  (0 < 0)
  |   Hasht =>  (0 < 0)
  |   Lpart =>  (0 < 0)
  |   Rpart =>  (0 < 0)
  |   Start =>  (0 < 0)
  |   Commat =>  (0 < 0)
  |   Arrowt =>  (0 < 0)
  |   Dotst =>  (0 < 0)
  |   Colont =>  (0 < 0)
  |   Sealt =>  (0 < 0)
  |   Semicolont =>  (0 < 0)
  |   Equalst =>  (0 < 0)
  |   Darrowt =>  (0 < 0)
  |   Lbrackt =>  (0 < 0)
  |   Rbrackt =>  (0 < 0)
  |   Underbart =>  (0 < 0)
  |   Lbracet =>  (0 < 0)
  |   Bart =>  (0 < 0)
  |   Rbracet =>  (0 < 0)
  |   Andt =>  (0 < 0)
  |   Andalsot =>  (0 < 0)
  |   Ast =>  (0 < 0)
  |   Caset =>  (0 < 0)
  |   Datatypet =>  (0 < 0)
  |   Elset =>  (0 < 0)
  |   Endt =>  (0 < 0)
  |   Eqtypet =>  (0 < 0)
  |   Exceptiont =>  (0 < 0)
  |   Fnt =>  (0 < 0)
  |   Funt =>  (0 < 0)
  |   Handlet =>  (0 < 0)
  |   Ift =>  (0 < 0)
  |   Int =>  (0 < 0)
  |   Includet =>  (0 < 0)
  |   Lett =>  (0 < 0)
  |   Localt =>  (0 < 0)
  |   Oft =>  (0 < 0)
  |   Opt =>  (0 < 0)
  |   Opent =>  (0 < 0)
  |   Orelset =>  (0 < 0)
  |   Raiset =>  (0 < 0)
  |   Rect =>  (0 < 0)
  |   Sharingt =>  (0 < 0)
  |   Sigt =>  (0 < 0)
  |   Signaturet =>  (0 < 0)
  |   Structt =>  (0 < 0)
  |   Structuret =>  (0 < 0)
  |   Thent =>  (0 < 0)
  |   Typet =>  (0 < 0)
  |   Valt =>  (0 < 0)
  |   Wheret =>  (0 < 0)
  |   Whilet =>  (0 < 0)
  |   Witht =>  (0 < 0)
  |   Withtypet =>  (0 < 0)
  |   Intt(v2) =>  (0 < 0)
  |   Hexintt(v3) =>  (0 < 0)
  |   Realt(v4) =>  (0 < 0)
  |   Stringt(v5) =>  (0 <= 0)
  |   Chart(v6) =>  (0 < 0)
  |   Tyvart(v7) =>  (0 < 0)
  |   Alphat(v8) =>  (0 < 0)
  |   Symbolt(v9) =>  (0 < 0)
  |   Longidt(v11,v10) =>  (0 < 0);

fun  ischart v12 = 
  case  v12
  of  Whitespacet(v1) =>  (0 < 0)
  |   Newlinet =>  (0 < 0)
  |   Lexerrort =>  (0 < 0)
  |   Hasht =>  (0 < 0)
  |   Lpart =>  (0 < 0)
  |   Rpart =>  (0 < 0)
  |   Start =>  (0 < 0)
  |   Commat =>  (0 < 0)
  |   Arrowt =>  (0 < 0)
  |   Dotst =>  (0 < 0)
  |   Colont =>  (0 < 0)
  |   Sealt =>  (0 < 0)
  |   Semicolont =>  (0 < 0)
  |   Equalst =>  (0 < 0)
  |   Darrowt =>  (0 < 0)
  |   Lbrackt =>  (0 < 0)
  |   Rbrackt =>  (0 < 0)
  |   Underbart =>  (0 < 0)
  |   Lbracet =>  (0 < 0)
  |   Bart =>  (0 < 0)
  |   Rbracet =>  (0 < 0)
  |   Andt =>  (0 < 0)
  |   Andalsot =>  (0 < 0)
  |   Ast =>  (0 < 0)
  |   Caset =>  (0 < 0)
  |   Datatypet =>  (0 < 0)
  |   Elset =>  (0 < 0)
  |   Endt =>  (0 < 0)
  |   Eqtypet =>  (0 < 0)
  |   Exceptiont =>  (0 < 0)
  |   Fnt =>  (0 < 0)
  |   Funt =>  (0 < 0)
  |   Handlet =>  (0 < 0)
  |   Ift =>  (0 < 0)
  |   Int =>  (0 < 0)
  |   Includet =>  (0 < 0)
  |   Lett =>  (0 < 0)
  |   Localt =>  (0 < 0)
  |   Oft =>  (0 < 0)
  |   Opt =>  (0 < 0)
  |   Opent =>  (0 < 0)
  |   Orelset =>  (0 < 0)
  |   Raiset =>  (0 < 0)
  |   Rect =>  (0 < 0)
  |   Sharingt =>  (0 < 0)
  |   Sigt =>  (0 < 0)
  |   Signaturet =>  (0 < 0)
  |   Structt =>  (0 < 0)
  |   Structuret =>  (0 < 0)
  |   Thent =>  (0 < 0)
  |   Typet =>  (0 < 0)
  |   Valt =>  (0 < 0)
  |   Wheret =>  (0 < 0)
  |   Whilet =>  (0 < 0)
  |   Witht =>  (0 < 0)
  |   Withtypet =>  (0 < 0)
  |   Intt(v2) =>  (0 < 0)
  |   Hexintt(v3) =>  (0 < 0)
  |   Realt(v4) =>  (0 < 0)
  |   Stringt(v5) =>  (0 < 0)
  |   Chart(v6) =>  (0 <= 0)
  |   Tyvart(v7) =>  (0 < 0)
  |   Alphat(v8) =>  (0 < 0)
  |   Symbolt(v9) =>  (0 < 0)
  |   Longidt(v11,v10) =>  (0 < 0);

fun  peg_ebaseparenfn v13 = 
  case  v13
  of  []  =>  []
   |   v12::v11 =>  (case  v11
                     of  []  =>  []
                      |   (v10::v9) =>  (case  v9
                                         of  []  =>  []
                                          |   (v8::v7) =>  (case  v7
                                                            of  []  =>  [Nd(Inl(Nebase),[v12,Nd(Inl(Neseq),[v10]),v8])]
                                                            |   (v6::v5) =>  (case  v5
                                                                              of  []  =>  []
                                                                               |   (v4::v3) =>  (case  v3
                                                                                                 of  []  =>  (if  (v8 = (Lf(Tok(Commat))))
                                                                                                              then  [Nd(Inl(Nebase),[Nd(Inl(Netuple),[v12,Nd(Inl(Nelist2),[v10,Lf(Tok(Commat)),v6]),v4])])]
                                                                                                              else  [Nd(Inl(Nebase),[v12,Nd(Inl(Neseq),[v10,v8,v6]),v4])])
                                                                                                 |   (v2::v1) =>  [] )))));

val  peg_ebaseparen =
  seql [tokeq Lpart,pnt Ne,choicel [tokeq Rpart,seql [tokeq Commat,pnt Nelist1,tokeq Rpart] i,seql [tokeq Semicolont,pnt Neseq,tokeq Rpart] i]] peg_ebaseparenfn;

fun  mk_linfix v5 v6 v7 =
  case  v7
  of  []  =>  v6
  |   v4::v3 =>  (case  v3
                  of  []  =>  v6
                  |   (v2::v1) =>  (mk_linfix v5 (Nd(v5,[v6,v4,v2])) v1));

fun  peg_linfix v7 = 
  (fn  v6 =>
    (fn  v5 =>
      Seq(v6,Rpt(Seq(v5,v6,append),flat),(fn  v4 =>
                                           (fn  v3 =>
                                             case  v4
                                             of  []  =>  []
                                              |   v2::v1 =>  [mk_linfix v7 (Nd(v7,[v2])) v3])))));

fun  islongidt v12 = 
  case  v12
  of  Whitespacet(v1) =>  (0 < 0)
  |   Newlinet =>  (0 < 0)
  |   Lexerrort =>  (0 < 0)
  |   Hasht =>  (0 < 0)
  |   Lpart =>  (0 < 0)
  |   Rpart =>  (0 < 0)
  |   Start =>  (0 < 0)
  |   Commat =>  (0 < 0)
  |   Arrowt =>  (0 < 0)
  |   Dotst =>  (0 < 0)
  |   Colont =>  (0 < 0)
  |   Sealt =>  (0 < 0)
  |   Semicolont =>  (0 < 0)
  |   Equalst =>  (0 < 0)
  |   Darrowt =>  (0 < 0)
  |   Lbrackt =>  (0 < 0)
  |   Rbrackt =>  (0 < 0)
  |   Underbart =>  (0 < 0)
  |   Lbracet =>  (0 < 0)
  |   Bart =>  (0 < 0)
  |   Rbracet =>  (0 < 0)
  |   Andt =>  (0 < 0)
  |   Andalsot =>  (0 < 0)
  |   Ast =>  (0 < 0)
  |   Caset =>  (0 < 0)
  |   Datatypet =>  (0 < 0)
  |   Elset =>  (0 < 0)
  |   Endt =>  (0 < 0)
  |   Eqtypet =>  (0 < 0)
  |   Exceptiont =>  (0 < 0)
  |   Fnt =>  (0 < 0)
  |   Funt =>  (0 < 0)
  |   Handlet =>  (0 < 0)
  |   Ift =>  (0 < 0)
  |   Int =>  (0 < 0)
  |   Includet =>  (0 < 0)
  |   Lett =>  (0 < 0)
  |   Localt =>  (0 < 0)
  |   Oft =>  (0 < 0)
  |   Opt =>  (0 < 0)
  |   Opent =>  (0 < 0)
  |   Orelset =>  (0 < 0)
  |   Raiset =>  (0 < 0)
  |   Rect =>  (0 < 0)
  |   Sharingt =>  (0 < 0)
  |   Sigt =>  (0 < 0)
  |   Signaturet =>  (0 < 0)
  |   Structt =>  (0 < 0)
  |   Structuret =>  (0 < 0)
  |   Thent =>  (0 < 0)
  |   Typet =>  (0 < 0)
  |   Valt =>  (0 < 0)
  |   Wheret =>  (0 < 0)
  |   Whilet =>  (0 < 0)
  |   Witht =>  (0 < 0)
  |   Withtypet =>  (0 < 0)
  |   Intt(v2) =>  (0 < 0)
  |   Hexintt(v3) =>  (0 < 0)
  |   Realt(v4) =>  (0 < 0)
  |   Stringt(v5) =>  (0 < 0)
  |   Chart(v6) =>  (0 < 0)
  |   Tyvart(v7) =>  (0 < 0)
  |   Alphat(v8) =>  (0 < 0)
  |   Symbolt(v9) =>  (0 < 0)
  |   Longidt(v11,v10) =>  (0 <= 0);

fun  isalphasym v12 = 
  case  v12
  of  Whitespacet(v1) =>  (0 < 0)
  |   Newlinet =>  (0 < 0)
  |   Lexerrort =>  (0 < 0)
  |   Hasht =>  (0 < 0)
  |   Lpart =>  (0 < 0)
  |   Rpart =>  (0 < 0)
  |   Start =>  (0 < 0)
  |   Commat =>  (0 < 0)
  |   Arrowt =>  (0 < 0)
  |   Dotst =>  (0 < 0)
  |   Colont =>  (0 < 0)
  |   Sealt =>  (0 < 0)
  |   Semicolont =>  (0 < 0)
  |   Equalst =>  (0 < 0)
  |   Darrowt =>  (0 < 0)
  |   Lbrackt =>  (0 < 0)
  |   Rbrackt =>  (0 < 0)
  |   Underbart =>  (0 < 0)
  |   Lbracet =>  (0 < 0)
  |   Bart =>  (0 < 0)
  |   Rbracet =>  (0 < 0)
  |   Andt =>  (0 < 0)
  |   Andalsot =>  (0 < 0)
  |   Ast =>  (0 < 0)
  |   Caset =>  (0 < 0)
  |   Datatypet =>  (0 < 0)
  |   Elset =>  (0 < 0)
  |   Endt =>  (0 < 0)
  |   Eqtypet =>  (0 < 0)
  |   Exceptiont =>  (0 < 0)
  |   Fnt =>  (0 < 0)
  |   Funt =>  (0 < 0)
  |   Handlet =>  (0 < 0)
  |   Ift =>  (0 < 0)
  |   Int =>  (0 < 0)
  |   Includet =>  (0 < 0)
  |   Lett =>  (0 < 0)
  |   Localt =>  (0 < 0)
  |   Oft =>  (0 < 0)
  |   Opt =>  (0 < 0)
  |   Opent =>  (0 < 0)
  |   Orelset =>  (0 < 0)
  |   Raiset =>  (0 < 0)
  |   Rect =>  (0 < 0)
  |   Sharingt =>  (0 < 0)
  |   Sigt =>  (0 < 0)
  |   Signaturet =>  (0 < 0)
  |   Structt =>  (0 < 0)
  |   Structuret =>  (0 < 0)
  |   Thent =>  (0 < 0)
  |   Typet =>  (0 < 0)
  |   Valt =>  (0 < 0)
  |   Wheret =>  (0 < 0)
  |   Whilet =>  (0 < 0)
  |   Witht =>  (0 < 0)
  |   Withtypet =>  (0 < 0)
  |   Intt(v2) =>  (0 < 0)
  |   Hexintt(v3) =>  (0 < 0)
  |   Realt(v4) =>  (0 < 0)
  |   Stringt(v5) =>  (0 < 0)
  |   Chart(v6) =>  (0 < 0)
  |   Tyvart(v7) =>  (0 < 0)
  |   Alphat(v8) =>  (0 <= 0)
  |   Symbolt(v9) =>  (0 <= 0)
  |   Longidt(v11,v10) =>  (0 < 0);

val  peg_typedec =
  Seq(tokeq Datatypet,peg_linfix (Inl(Ndtypedecls)) (pnt Ndtypedecl) (tokeq Andt),(fn  v2 =>
                                                                                    (fn  v1 =>
                                                                                      [Nd(Inl(Ntypedec),append v2 v1)])));

val  peg_uqconstructorname  =
  Tok_1((fn  v2 =>
          (option_bind (destalphat v2) (fn  v1 =>
                                         (option_guard ((if  (v1 = [] )
                                                         then  (0 < 0)
                                                         else  (isupper (hd v1))) orelse  ((v1 = [#"t",#"r",#"u",#"e"]) orelse  ((v1 = [#"f",#"a",#"l",#"s",#"e"]) orelse  ((v1 = [#"r",#"e",#"f"]) orelse  (v1 = [#"n",#"i",#"l"])))))))) = (let val  x =
                                                                                                                                                                                                                                                ()
                                                                                                                                                                                                                                              in
                                                                                                                                                                                                                                                SOME(x)
                                                                                                                                                                                                                                              end)),o_1 (bindnt Nuqconstructorname) mktoklf);

val  peg_structname=
  Tok_1((fn  v2 =>
          (option_bind (destalphat v2) (fn  v1 =>
                                         (option_guard ((v1 = [] ) = (0 < 0))))) = (let val  x =
                                                                                      ()
                                                                                    in
                                                                                      SOME(x)
                                                                                    end)),o_1 (bindnt Nstructname) mktoklf);

val cmlpeg =
 Recordtypepeg(pnt Ntopleveldecs,fupdate_list [] [(Inl(Nv),peg_v),(Inl(Ntyvarn),pegf (Tok_1(istyvart,mktoklf)) (bindnt Ntyvarn)),(Inl(Nfqv),choicel [pegf (pnt Nv) (bindnt Nfqv),peg_longv]),(Inl(Neapp),seql [pnt Nebase,Rpt(pnt Nebase,flat)] (fn v5 =>
 (case v5
 of [] => []
 | (v4::v3) => [foldl (fn v2 =>
 (fn v1 =>
 (Nd(Inl(Neapp),[v2,v1])))) (Nd(Inl(Neapp),[v4])) v3]))),(Inl(Nelist1),seql [pnt Ne,try (seql [tokeq Commat,pnt Nelist1] i)] (bindnt Nelist1)),(Inl(Nmultops),pegf (choicel [tokeq Start,tokeq (Symbolt([#"/"])),tokeq (Alphat([#"m",#"o",#"d"])),tokeq (Alphat([#"d",#"i",#"v"]))]) (bindnt Nmultops)),(Inl(Naddops),pegf (choicel [tokeq (Symbolt([#"+"])),tokeq (Symbolt([#"-"]))]) (bindnt Naddops)),(Inl(Nrelops),pegf (choicel [Tok_1((fn v6 =>
 Equalst = v6),mktoklf),o_1 tokeq (fn v7 =>
 (Symbolt(v7))) [#"<"],o_1 tokeq (fn v8 =>
 (Symbolt(v8))) [#">"],o_1 tokeq (fn v9 =>
 (Symbolt(v9))) [#"<",#"="],o_1 tokeq (fn v10 =>
 (Symbolt(v10))) [#">",#"="],o_1 tokeq (fn v11 =>
 (Symbolt(v11))) [#"<",#">"]]) (bindnt Nrelops)),(Inl(Nlistops),pegf (choicel [o_1 tokeq (fn v12 =>
 (Symbolt(v12))) [#":",#":"],o_1 tokeq (fn v13 =>
 (Symbolt(v13))) [#"@"]]) (bindnt Nlistops)),(Inl(Ncompops),pegf (choicel [tokeq (Symbolt([#":",#"="])),tokeq (Alphat([#"o"]))]) (bindnt Ncompops)),(Inl(Nopid),choicel [Tok_1((fn v17 =>
 (option_bind (destlongidt v17) (fn v16 =>
 (case v16
 of (v15,v14) => (option_guard ((v14 = [] ) = (0 < 0)))))) = (let val x =
 ()
 in
 SOME(x)
 end)),o_1 (bindnt Nopid) mktoklf),Tok_1((fn v19 =>
 (option_bind (destsymbolt v19) (fn v18 =>
 (option_guard ((v18 = [] ) = (0 < 0))))) = (let val x =
 ()
 in
 SOME(x)
 end)),o_1 (bindnt Nopid) mktoklf),Tok_1((fn v21 =>
 (option_bind (destalphat v21) (fn v20 =>
 (option_guard ((v20 = [] ) = (0 < 0))))) = (let val x =
 ()
 in
 SOME(x)
 end)),o_1 (bindnt Nopid) mktoklf),pegf (tokeq Start) (bindnt Nopid),pegf (tokeq Equalst) (bindnt Nopid)]),(Inl(Nebase),choicel [Tok_1(isint,o_1 (bindnt Nebase) mktoklf),Tok_1(isstring,o_1 (bindnt Nebase) mktoklf),Tok_1(ischart,o_1 (bindnt Nebase) mktoklf),seql [tokeq Lpart,tokeq Rpart] (bindnt Nebase),peg_ebaseparen,seql [tokeq Lbrackt,try (pnt Nelist1),tokeq Rbrackt] (bindnt Nebase),seql [tokeq Lett,pnt Nletdecs,tokeq Int,pnt Neseq,tokeq Endt] (bindnt Nebase),pegf (pnt Nfqv) (bindnt Nebase),pegf (pnt Nconstructorname) (bindnt Nebase),seql [tokeq Opt,pnt Nopid] (bindnt Nebase)]),(Inl(Neseq),seql [pnt Ne,try (seql [tokeq Semicolont,pnt Neseq] i)] (bindnt Neseq)),(Inl(Nemult),peg_linfix (Inl(Nemult)) (pnt Neapp) (pnt Nmultops)),(Inl(Neadd),peg_linfix (Inl(Neadd)) (pnt Nemult) (pnt Naddops)),(Inl(Nelistop),seql [pnt Neadd,try (seql [pnt Nlistops,pnt Nelistop] i)] (bindnt Nelistop)),(Inl(Nerel),peg_linfix (Inl(Nerel)) (pnt Nelistop) (pnt Nrelops)),(Inl(Necomp),peg_linfix (Inl(Necomp)) (pnt Nerel) (pnt Ncompops)),(Inl(Nebefore),peg_linfix (Inl(Nebefore)) (pnt Necomp) (tokeq (Alphat([#"b",#"e",#"f",#"o",#"r",#"e"])))),(Inl(Netyped),seql [pnt Nebefore,try (seql [tokeq Colont,pnt Ntype] i)] (bindnt Netyped)),(Inl(Nelogicand),peg_linfix (Inl(Nelogicand)) (pnt Netyped) (tokeq Andalsot)),(Inl(Nelogicor),peg_linfix (Inl(Nelogicor)) (pnt Nelogicand) (tokeq Orelset)),(Inl(Nehandle),seql [pnt Nelogicor,try (seql [tokeq Handlet,pnt Npes] i)] (bindnt Nehandle)),(Inl(Ne),choicel [seql [tokeq Raiset,pnt Ne] (bindnt Ne),pegf (pnt Nehandle) (bindnt Ne),seql [tokeq Ift,pnt Ne,tokeq Thent,pnt Ne,tokeq Elset,pnt Ne] (bindnt Ne),seql [tokeq Fnt,pnt Npattern,tokeq Darrowt,pnt Ne] (bindnt Ne),seql [tokeq Caset,pnt Ne,tokeq Oft,pnt Npes] (bindnt Ne)]),(Inl(Ne'),choicel [seql [tokeq Raiset,pnt Ne'] (bindnt Ne'),pegf (pnt Nelogicor) (bindnt Ne'),seql [tokeq Ift,pnt Ne,tokeq Thent,pnt Ne,tokeq Elset,pnt Ne'] (bindnt Ne')]),(Inl(Npes),choicel [seql [pnt Npe',tokeq Bart,pnt Npes] (bindnt Npes),pegf (pnt Npe) (bindnt Npes)]),(Inl(Npe),seql [pnt Npattern,tokeq Darrowt,pnt Ne] (bindnt Npe)),(Inl(Npe'),seql [pnt Npattern,tokeq Darrowt,pnt Ne'] (bindnt Npe')),(Inl(Nandfdecls),peg_linfix (Inl(Nandfdecls)) (pnt Nfdecl) (tokeq Andt)),(Inl(Nfdecl),seql [pnt Nv,pnt Npbaselist1,tokeq Equalst,pnt Ne] (bindnt Nfdecl)),(Inl(Npbaselist1),seql [pnt Npbase,try (pnt Npbaselist1)] (bindnt Npbaselist1)),(Inl(Ntype),seql [pnt Nptype,try (seql [tokeq Arrowt,pnt Ntype] i)] (bindnt Ntype)),(Inl(Ndtype),seql [pnt Ntbase,Rpt(pnt Ntyop,flat)] (fn v26 =>
 (case v26
 of [] => []
 | (v25::v24) => [foldl (fn v23 =>
 (fn v22 =>
 (Nd(Inl(Ndtype),[v23,v22])))) (Nd(Inl(Ndtype),[v25])) v24]))),(Inl(Ntbase),choicel [seql [tokeq Lpart,pnt Ntype,tokeq Rpart] (bindnt Ntbase),seql [tokeq Lpart,pnt Ntypelist2,tokeq Rpart,pnt Ntyop] (bindnt Ntbase),Tok_1(istyvart,o_1 (bindnt Ntbase) mktoklf),pegf (pnt Ntyop) (bindnt Ntbase)]),(Inl(Ntypelist2),seql [pnt Ntype,tokeq Commat,pnt Ntypelist1] (bindnt Ntypelist2)),(Inl(Ntypelist1),seql [pnt Ntype,try (seql [tokeq Commat,pnt Ntypelist1] i)] (bindnt Ntypelist1)),(Inl(Ntyop),pegf (choicel [pnt Nuqtyop,Tok_1(islongidt,mktoklf)]) (bindnt Ntyop)),(Inl(Nuqtyop),Tok_1(isalphasym,o_1 (bindnt Nuqtyop) mktoklf)),(Inl(Nptype),seql [pnt Ndtype,try (seql [tokeq Start,pnt Nptype] i)] (bindnt Nptype)),(Inl(Ntypename),choicel [pegf (pnt Nuqtyop) (bindnt Ntypename),seql [tokeq Lpart,pnt Ntyvarlist,tokeq Rpart,pnt Nuqtyop] (bindnt Ntypename),seql [Tok_1(istyvart,mktoklf),pnt Nuqtyop] (bindnt Ntypename)]),(Inl(Ntyvarlist),peg_linfix (Inl(Ntyvarlist)) (pnt Ntyvarn) (tokeq Commat)),(Inl(Ntypedec),peg_typedec),(Inl(Ndtypedecl),seql [pnt Ntypename,tokeq Equalst,peg_linfix (Inl(Ndtypecons)) (pnt Ndconstructor) (tokeq Bart)] (bindnt Ndtypedecl)),(Inl(Ndconstructor),seql [pnt Nuqconstructorname,try (seql [tokeq Oft,pnt Ntype] i)] (bindnt Ndconstructor)),(Inl(Nuqconstructorname),peg_uqconstructorname),(Inl(Nconstructorname),choicel [pegf (pnt Nuqconstructorname) (bindnt Nconstructorname),Tok_1((fn v30 =>
 (option_bind (destlongidt v30) (fn v29 =>
 (case v29
 of (v28,v27) => (option_guard ((if (v27 = [] )
 then (0 < 0)
 else ((isalpha (hd v27)) andalso (isupper (hd v27)))) orelse ((v27 = [#"r",#"e",#"f"]) orelse ((v27 = [#"t",#"r",#"u",#"e"]) orelse ((v27 = [#"f",#"a",#"l",#"s",#"e"]) orelse (v27 = [#"n",#"i",#"l"]))))))))) = (let val x =
 ()
 in
 SOME(x)
 end)),o_1 (bindnt Nconstructorname) mktoklf)]),(Inl(Npbase),pegf (choicel [pnt Nv,pnt Nconstructorname,Tok_1(isint,mktoklf),Tok_1(isstring,mktoklf),Tok_1(ischart,mktoklf),pnt Nptuple,tokeq Underbart,seql [tokeq Lbrackt,try (pnt Npatternlist),tokeq Rbrackt] i]) (bindnt Npbase)),(Inl(Npapp),choicel [seql [pnt Nconstructorname,pnt Npbase] (bindnt Npapp),pegf (pnt Npbase) (bindnt Npapp)]),(Inl(Npcons),seql [pnt Npapp,try (seql [tokeq (Symbolt([#":",#":"])),pnt Npcons] i)] (bindnt Npcons)),(Inl(Npattern),seql [pnt Npcons,try (seql [tokeq Colont,pnt Ntype] i)] (bindnt Npattern)),(Inl(Npatternlist),seql [pnt Npattern,try (seql [tokeq Commat,pnt Npatternlist] i)] (bindnt Npatternlist)),(Inl(Nptuple),choicel [seql [tokeq Lpart,tokeq Rpart] (bindnt Nptuple),seql [tokeq Lpart,pnt Npatternlist,tokeq Rpart] (bindnt Nptuple)]),(Inl(Nletdec),choicel [seql [tokeq Valt,pnt Nv,tokeq Equalst,pnt Ne] (bindnt Nletdec),seql [tokeq Funt,pnt Nandfdecls] (bindnt Nletdec)]),(Inl(Nletdecs),choicel [seql [pnt Nletdec,pnt Nletdecs] (bindnt Nletdecs),seql [tokeq Semicolont,pnt Nletdecs] (bindnt Nletdecs),pegf (Empty([] )) (bindnt Nletdecs)]),(Inl(Ndecl),choicel [seql [tokeq Valt,pnt Npattern,tokeq Equalst,pnt Ne] (bindnt Ndecl),seql [tokeq Funt,pnt Nandfdecls] (bindnt Ndecl),seql [tokeq Exceptiont,pnt Ndconstructor] (bindnt Ndecl),seql [pnt Ntypedec] (bindnt Ndecl),seql [pnt Ntypeabbrevdec] (bindnt Ndecl)]),(Inl(Ntypeabbrevdec),seql [tokeq Typet,pnt Ntypename,tokeq Equalst,pnt Ntype] (bindnt Ntypeabbrevdec)),(Inl(Ndecls),choicel [seql [pnt Ndecl,pnt Ndecls] (bindnt Ndecls),seql [tokeq Semicolont,pnt Ndecls] (bindnt Ndecls),pegf (Empty([] )) (bindnt Ndecls)]),(Inl(Nopttypeqn),choicel [seql [tokeq Equalst,pnt Ntype] (bindnt Nopttypeqn),pegf (Empty([] )) (bindnt Nopttypeqn)]),(Inl(Nspecline),choicel [seql [tokeq Valt,pnt Nv,tokeq Colont,pnt Ntype] (bindnt Nspecline),seql [tokeq Typet,pnt Ntypename,pnt Nopttypeqn] (bindnt Nspecline),seql [tokeq Exceptiont,pnt Ndconstructor] (bindnt Nspecline),pegf (pnt Ntypedec) (bindnt Nspecline)]),(Inl(Nspeclinelist),choicel [seql [pnt Nspecline,pnt Nspeclinelist] (bindnt Nspeclinelist),seql [tokeq Semicolont,pnt Nspeclinelist] (bindnt Nspeclinelist),pegf (Empty([] )) (bindnt Nspeclinelist)]),(Inl(Nsignaturevalue),seql [tokeq Sigt,pnt Nspeclinelist,tokeq Endt] (bindnt Nsignaturevalue)),(Inl(Noptionalsignatureascription),pegf (try (seql [tokeq Sealt,pnt Nsignaturevalue] i)) (bindnt Noptionalsignatureascription)),(Inl(Nstructname),peg_structname),(Inl(Nstructure),seql [tokeq Structuret,pnt Nstructname,pnt Noptionalsignatureascription,tokeq Equalst,tokeq Structt,pnt Ndecls,tokeq Endt] (bindnt Nstructure)),(Inl(Ntopleveldec),pegf (choicel [pnt Nstructure,pnt Ndecl]) (bindnt Ntopleveldec)),(Inl(Ntopleveldecs),choicel [seql [pnt Ne,tokeq Semicolont,pnt Ntopleveldecs] (bindnt Ntopleveldecs),seql [pnt Ntopleveldec,pnt Nnonetopleveldecs] (bindnt Ntopleveldecs),seql [tokeq Semicolont,pnt Ntopleveldecs] (bindnt Ntopleveldecs),pegf (Empty([] )) (bindnt Ntopleveldecs)]),(Inl(Nnonetopleveldecs),choicel [seql [pnt Ntopleveldec,pnt Nnonetopleveldecs] (bindnt Nnonetopleveldecs),seql [tokeq Semicolont,pnt Ntopleveldecs] (bindnt Nnonetopleveldecs),pegf (Empty([] )) (bindnt Nnonetopleveldecs)])]);

datatype ( 'atok  ,  'cvalue ) pegexec_kont =  Failed
                                                     |  Done
                                                     |  Listsym of  ('atok  ,  'cvalue ) peg_pegsym *  ('cvalue list ->  'cvalue )  *  ('atok  ,  'cvalue ) pegexec_kont
                                                     |  Poplist of  ('cvalue list ->  'cvalue )  *  ('atok  ,  'cvalue ) pegexec_kont
                                                     |  Returnto of  'atok list *  'cvalue option list *  ('atok  ,  'cvalue ) pegexec_kont
                                                     |  Appf2 of  ('cvalue  ->  ('cvalue  ->  'cvalue ) )  *  ('atok  ,  'cvalue ) pegexec_kont
                                                     |  Appf1 of  ('cvalue  ->  'cvalue )  *  ('atok  ,  'cvalue ) pegexec_kont
                                                     |  Ksym of  ('atok  ,  'cvalue ) peg_pegsym *  ('atok  ,  'cvalue ) pegexec_kont *  ('atok  ,  'cvalue ) pegexec_kont;

datatype ( 'atok  ,  'cvalue ) pegexec_evalcase =  Looped
                                                         |  Result of  ('atok list *  'cvalue ) option
                                                         |  Ap of  ('atok  ,  'cvalue ) pegexec_kont *  'atok list *  'cvalue option list
                                                         |  Ev of  ('atok  ,  'cvalue ) peg_pegsym *  'atok list *  'cvalue option list *  ('atok  ,  'cvalue ) pegexec_kont *  ('atok  ,  'cvalue ) pegexec_kont;

fun  poplist_aux v4 v5 =
  case  v5
  of  []  =>  (v4,[] )
  |   v3::v2 =>  (case  v3
                  of  NONE =>  (v4,v2)
                  |   (SOME(v1)) =>  (poplist_aux (v1::v4) v2));

fun  poplistval v4 = 
  (fn  v5 =>
    let val  v3 = poplist_aux [] v5
     in
      case  v3 of  (v2,v1) =>  (SOME(v4 v2)::v1)
    end);

fun  coreloop v71 = 
  (fn  v72 =>
    owhile (fn  v10 =>
             (case  v10
              of  (Ev(v5,v4,v3,v2,v1)) =>  (0 <= 0)
              |   (Ap(v8,v7,v6)) =>  (0 <= 0)
              |   (Result(v9)) =>  (0 < 0)
              |   Looped =>  (0 <= 0))) (fn  v70 =>
                                          (case  v70
                                           of  (Ev(v38,v37,v36,v35,v34)) =>  (case  v38
                                                                              of  (Empty(v11)) =>  (Ap(v35,v37,SOME(v11)::v36))
                                                                              |   (Any(v14)) =>  (case  v37
                                                                                                  of  []  =>  (Ap(v34,v37,v36))
                                                                                                  |   (v13::v12) =>  (Ap(v35,v12,SOME(v14 v13)::v36)))
                                                                              |   (Tok_1(v18,v17)) =>  (case  v37
                                                                                                        of  []  =>  (Ap(v34,v37,v36))
                                                                                                        |   (v16::v15) =>  (if  (v18 v16)
                                                                                                                            then  (Ap(v35,v15,SOME(v17 v16)::v36))
                                                                                                                            else  (Ap(v34,v37,v36))))
                                                                              |   (Nt_1(v21,v20)) =>  (case  (alookup (peg_rules v71) v21)
                                                                                                       of  NONE =>  (Result(NONE))
                                                                                                       |   (SOME(v19)) =>  (Ev(v19,v37,v36,Appf1(v20,v35),v34)))
                                                                              |   (Seq(v24,v23,v22)) =>  (Ev(v24,v37,v36,Ksym(v23,Appf2(v22,v35),Returnto(v37,v36,v34)),v34))
                                                                              |   (Choice(v29,v28,v27)) =>  (Ev(v29,v37,v36,Appf1(o_1 v27 (fn  v25 =>
                                                                                                                                            (Inl(v25))),v35),Returnto(v37,v36,Ksym(v28,Appf1(o_1 v27 (fn  v26 =>
                                                                                                                                                                                                       (Inr(v26))),v35),v34))))
                                                                              |   (Rpt(v31,v30)) =>  (Ev(v31,v37,NONE::v36,Listsym(v31,v30,v35),Poplist(v30,v35)))
                                                                              |   (Not(v33,v32)) =>  (Ev(v33,v37,v36,Returnto(v37,v36,v34),Returnto(v37,SOME(v32)::v36,v35))))
                                           |   (Ap(v68,v67,v66)) =>  (case  v68
                                                                      of  (Ksym(v41,v40,v39)) =>  (Ev(v41,v67,v66,v40,v39))
                                                                      |   (Appf1(v46,v45)) =>  (case  v66
                                                                                                of  []  =>  Looped
                                                                                                |   (v44::v43) =>  (case  v44
                                                                                                                    of  NONE =>  Looped
                                                                                                                    |   (SOME(v42)) =>  (Ap(v45,v67,SOME(v46 v42)::v43))))
                                                                      |   (Appf2(v54,v53)) =>  (case  v66
                                                                                                of  []  =>  Looped
                                                                                                |   (v52::v51) =>  (case  v51
                                                                                                                    of  []  =>  Looped
                                                                                                                    |   (v50::v49) =>  (case  v50
                                                                                                                                        of  NONE =>  Looped
                                                                                                                                        |   (SOME(v48)) =>  (case  v52
                                                                                                                                                             of  NONE =>  Looped
                                                                                                                                                             |   (SOME(v47)) =>  (Ap(v53,v67,SOME(v54 v48 v47)::v49))))))
                                                                      |   (Returnto(v57,v56,v55)) =>  (Ap(v55,v57,v56))
                                                                      |   (Poplist(v59,v58)) =>  (Ap(v58,v67,poplistval v59 v66))
                                                                      |   (Listsym(v62,v61,v60)) =>  (Ev(v62,v67,v66,Listsym(v62,v61,v60),Poplist(v61,v60)))
                                                                      |   Done =>  (Result(case  v66
                                                                                           of  []  =>  NONE
                                                                                           |   v65::v64 =>  (case  v65
                                                                                                             of  NONE =>  NONE
                                                                                                             |   (SOME(v63)) =>  (let val  x =
                                                                                                                                    (v67,v63)
                                                                                                                                  in
                                                                                                                                    SOME(x)
                                                                                                                                  end))))
                                                                      |   Failed =>  (Result(NONE)))
                                           |   (Result(v69)) =>  (Result(v69))
                                           |   Looped =>  Looped)) v72);

fun  peg_exec v2 = 
  (fn  v3 =>
    (fn  v5 =>
      (fn  v7 =>
        (fn  v6 =>
          (fn  v4 =>
            case  (coreloop v2 (Ev(v3,v5,v7,v6,v4)))
            of  NONE =>  Looped
            |   SOME(v1) =>  v1)))));

fun  ptree_head v4 = 
  case  v4
  of  Lf(v1) =>  v1
  |   Nd(v3,v2) =>  (Nt(v3));

datatype 'a ast_id =  Long of  char list *  'a
                    |  Short of  'a ;

datatype ast_tctor =  Tc_array
                   |  Tc_vector
                   |  Tc_exn
                   |  Tc_tup
                   |  Tc_fn
                   |  Tc_word8array
                   |  Tc_word64
                   |  Tc_word8
                   |  Tc_ref
                   |  Tc_string
                   |  Tc_char
                   |  Tc_int
                   |  Tc_name of  char list ast_id;

datatype ast_t =  Tapp of  ast_t list *  ast_tctor
               |  Tvar_db of  int
               |  Tvar of  char list;

datatype ast_lit =  Word64 of  Word64.word
                 |  Word8 of  Word8.word
                 |  Strlit of  char list
                 |  Char of  char
                 |  Intlit of  int;

datatype ast_pat =  Ptannot of  ast_pat *  ast_t
                 |  Pref of  ast_pat
                 |  Pcon of  char list ast_id option *  ast_pat list
                 |  Plit of  ast_lit
                 |  Pvar of  char list;

datatype ast_lop =  Or
                 |  And;

datatype ast_opb =  Geq
                 |  Leq
                 |  Gt
                 |  Lt;

datatype ast_word_size =  W64
                       |  W8;

datatype ast_shift =  Asr
                   |  Lsr
                   |  Lsl;

datatype ast_opw =  Sub
                 |  Add
                 |  Xor
                 |  Orw
                 |  Andw;

datatype ast_opn =  Modulo
                 |  Divide
                 |  Times
                 |  Minus
                 |  Plus;

datatype ast_op =  Ffi of  int
                |  Aupdate
                |  Alength
                |  Asub
                |  Aalloc
                |  Vlength
                |  Vsub
                |  Vfromlist
                |  Strlen
                |  Implode
                |  Explode
                |  Chopb of  ast_opb
                |  Chr
                |  Ord
                |  Wordtoint of  ast_word_size
                |  Wordfromint of  ast_word_size
                |  Aw8update
                |  Aw8length
                |  Aw8sub
                |  Aw8alloc
                |  Opderef
                |  Opref
                |  Opassign
                |  Opapp
                |  Equality
                |  Shift of  ast_word_size *  ast_shift *  int
                |  Opw of  ast_word_size *  ast_opw
                |  Opb of  ast_opb
                |  Opn of  ast_opn;

datatype ast_exp =  Tannot of  ast_exp *  ast_t
                 |  Letrec of  (char list *  (char list *  ast_exp)) list *  ast_exp
                 |  Let of  char list option *  ast_exp *  ast_exp
                 |  Mat of  ast_exp *  (ast_pat *  ast_exp) list
                 |  If of  ast_exp *  ast_exp *  ast_exp
                 |  Log of  ast_lop *  ast_exp *  ast_exp
                 |  App of  ast_op *  ast_exp list
                 |  Fun of  char list *  ast_exp
                 |  Var of  char list ast_id
                 |  Con of  char list ast_id option *  ast_exp list
                 |  Lit of  ast_lit
                 |  Handle of  ast_exp *  (ast_pat *  ast_exp) list
                 |  Raise of  ast_exp;

fun  option_choice v3 = 
  (fn  v2 =>
    case  v3
    of  NONE =>  v2
    |   SOME(v1) =>  (SOME(v1)));

fun  destlf v4 = 
  case  v4
  of  Lf(v1) =>  (SOME(v1))
  |   Nd(v3,v2) =>  NONE;

fun  desttok v3 = 
  case  v3
  of  Tok(v1) =>  (SOME(v1))
  |   Nt(v2) =>  NONE;

fun  destintt v12 = 
  case  v12
  of  Whitespacet(v1) =>  NONE
  |   Newlinet =>  NONE
  |   Lexerrort =>  NONE
  |   Hasht =>  NONE
  |   Lpart =>  NONE
  |   Rpart =>  NONE
  |   Start =>  NONE
  |   Commat =>  NONE
  |   Arrowt =>  NONE
  |   Dotst =>  NONE
  |   Colont =>  NONE
  |   Sealt =>  NONE
  |   Semicolont =>  NONE
  |   Equalst =>  NONE
  |   Darrowt =>  NONE
  |   Lbrackt =>  NONE
  |   Rbrackt =>  NONE
  |   Underbart =>  NONE
  |   Lbracet =>  NONE
  |   Bart =>  NONE
  |   Rbracet =>  NONE
  |   Andt =>  NONE
  |   Andalsot =>  NONE
  |   Ast =>  NONE
  |   Caset =>  NONE
  |   Datatypet =>  NONE
  |   Elset =>  NONE
  |   Endt =>  NONE
  |   Eqtypet =>  NONE
  |   Exceptiont =>  NONE
  |   Fnt =>  NONE
  |   Funt =>  NONE
  |   Handlet =>  NONE
  |   Ift =>  NONE
  |   Int =>  NONE
  |   Includet =>  NONE
  |   Lett =>  NONE
  |   Localt =>  NONE
  |   Oft =>  NONE
  |   Opt =>  NONE
  |   Opent =>  NONE
  |   Orelset =>  NONE
  |   Raiset =>  NONE
  |   Rect =>  NONE
  |   Sharingt =>  NONE
  |   Sigt =>  NONE
  |   Signaturet =>  NONE
  |   Structt =>  NONE
  |   Structuret =>  NONE
  |   Thent =>  NONE
  |   Typet =>  NONE
  |   Valt =>  NONE
  |   Wheret =>  NONE
  |   Whilet =>  NONE
  |   Witht =>  NONE
  |   Withtypet =>  NONE
  |   Intt(v2) =>  (SOME(v2))
  |   Hexintt(v3) =>  NONE
  |   Realt(v4) =>  NONE
  |   Stringt(v5) =>  NONE
  |   Chart(v6) =>  NONE
  |   Tyvart(v7) =>  NONE
  |   Alphat(v8) =>  NONE
  |   Symbolt(v9) =>  NONE
  |   Longidt(v11,v10) =>  NONE;

fun  destchart v12 = 
  case  v12
  of  Whitespacet(v1) =>  NONE
  |   Newlinet =>  NONE
  |   Lexerrort =>  NONE
  |   Hasht =>  NONE
  |   Lpart =>  NONE
  |   Rpart =>  NONE
  |   Start =>  NONE
  |   Commat =>  NONE
  |   Arrowt =>  NONE
  |   Dotst =>  NONE
  |   Colont =>  NONE
  |   Sealt =>  NONE
  |   Semicolont =>  NONE
  |   Equalst =>  NONE
  |   Darrowt =>  NONE
  |   Lbrackt =>  NONE
  |   Rbrackt =>  NONE
  |   Underbart =>  NONE
  |   Lbracet =>  NONE
  |   Bart =>  NONE
  |   Rbracet =>  NONE
  |   Andt =>  NONE
  |   Andalsot =>  NONE
  |   Ast =>  NONE
  |   Caset =>  NONE
  |   Datatypet =>  NONE
  |   Elset =>  NONE
  |   Endt =>  NONE
  |   Eqtypet =>  NONE
  |   Exceptiont =>  NONE
  |   Fnt =>  NONE
  |   Funt =>  NONE
  |   Handlet =>  NONE
  |   Ift =>  NONE
  |   Int =>  NONE
  |   Includet =>  NONE
  |   Lett =>  NONE
  |   Localt =>  NONE
  |   Oft =>  NONE
  |   Opt =>  NONE
  |   Opent =>  NONE
  |   Orelset =>  NONE
  |   Raiset =>  NONE
  |   Rect =>  NONE
  |   Sharingt =>  NONE
  |   Sigt =>  NONE
  |   Signaturet =>  NONE
  |   Structt =>  NONE
  |   Structuret =>  NONE
  |   Thent =>  NONE
  |   Typet =>  NONE
  |   Valt =>  NONE
  |   Wheret =>  NONE
  |   Whilet =>  NONE
  |   Witht =>  NONE
  |   Withtypet =>  NONE
  |   Intt(v2) =>  NONE
  |   Hexintt(v3) =>  NONE
  |   Realt(v4) =>  NONE
  |   Stringt(v5) =>  NONE
  |   Chart(v6) =>  (SOME(v6))
  |   Tyvart(v7) =>  NONE
  |   Alphat(v8) =>  NONE
  |   Symbolt(v9) =>  NONE
  |   Longidt(v11,v10) =>  NONE;

fun  deststringt v12 = 
  case  v12
  of  Whitespacet(v1) =>  NONE
  |   Newlinet =>  NONE
  |   Lexerrort =>  NONE
  |   Hasht =>  NONE
  |   Lpart =>  NONE
  |   Rpart =>  NONE
  |   Start =>  NONE
  |   Commat =>  NONE
  |   Arrowt =>  NONE
  |   Dotst =>  NONE
  |   Colont =>  NONE
  |   Sealt =>  NONE
  |   Semicolont =>  NONE
  |   Equalst =>  NONE
  |   Darrowt =>  NONE
  |   Lbrackt =>  NONE
  |   Rbrackt =>  NONE
  |   Underbart =>  NONE
  |   Lbracet =>  NONE
  |   Bart =>  NONE
  |   Rbracet =>  NONE
  |   Andt =>  NONE
  |   Andalsot =>  NONE
  |   Ast =>  NONE
  |   Caset =>  NONE
  |   Datatypet =>  NONE
  |   Elset =>  NONE
  |   Endt =>  NONE
  |   Eqtypet =>  NONE
  |   Exceptiont =>  NONE
  |   Fnt =>  NONE
  |   Funt =>  NONE
  |   Handlet =>  NONE
  |   Ift =>  NONE
  |   Int =>  NONE
  |   Includet =>  NONE
  |   Lett =>  NONE
  |   Localt =>  NONE
  |   Oft =>  NONE
  |   Opt =>  NONE
  |   Opent =>  NONE
  |   Orelset =>  NONE
  |   Raiset =>  NONE
  |   Rect =>  NONE
  |   Sharingt =>  NONE
  |   Sigt =>  NONE
  |   Signaturet =>  NONE
  |   Structt =>  NONE
  |   Structuret =>  NONE
  |   Thent =>  NONE
  |   Typet =>  NONE
  |   Valt =>  NONE
  |   Wheret =>  NONE
  |   Whilet =>  NONE
  |   Witht =>  NONE
  |   Withtypet =>  NONE
  |   Intt(v2) =>  NONE
  |   Hexintt(v3) =>  NONE
  |   Realt(v4) =>  NONE
  |   Stringt(v5) =>  (SOME(v5))
  |   Chart(v6) =>  NONE
  |   Tyvart(v7) =>  NONE
  |   Alphat(v8) =>  NONE
  |   Symbolt(v9) =>  NONE
  |   Longidt(v11,v10) =>  NONE;

fun  ptree_v v13 = 
  case  v13
  of  Lf(v1) =>  NONE
  |   Nd(v12,v11) =>  (if  (v12 = (Inl(Nv)))
                       then  (case  v11
                              of  []  =>  NONE
                              |   (v10::v9) =>  (case  v10
                                                 of  (Lf(v6)) =>  (case  v6
                                                                   of  (Tok(v4)) =>  (case  v9
                                                                                      of  []  =>  (option_choice (destalphat v4) (destsymbolt v4))
                                                                                      |   (v3::v2) =>  NONE)
                                                                   |   (Nt(v5)) =>  NONE)
                                                 |   (Nd(v8,v7)) =>  NONE))
                       else  NONE);

fun  ptree_fqv v14 = 
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  ((v13 = (Inl(Nfqv))) = (0 < 0))
                       then  NONE
                        else  (case  v12
                               of  []  =>  NONE
                               |   (v11::v10) =>  (case  v10
                                                   of  []  =>  (option_choice (option_map (fn  v2 =>
                                                                                            (Short(v2))) (ptree_v v11)) (case  (case  (case  (destlf v11)
                                                                                                                                       of  NONE =>  NONE
                                                                                                                                       |   (SOME(v3)) =>  (desttok v3))
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v4)) =>  (destlongidt v4))
                                                                                                                         of  NONE =>  NONE
                                                                                                                         |   (SOME(v7)) =>  (case  v7
                                                                                                                                             of  (v6,v5) =>  (SOME(Long(v6,v5))))))
                                                   |   (v9::v8) =>  NONE)));

fun  ptree_uqconstructorname v10 = 
  case  v10
  of  Lf(v1) =>  NONE
  |   Nd(v9,v8) =>  (if  ((v9 = (Inl(Nuqconstructorname))) = (0 < 0))
                     then  NONE
                      else  (case  v8
                             of  []  =>  NONE
                             |   (v7::v6) =>  (case  v6
                                               of  []  =>  (case  (case  (destlf v7)
                                                                   of  NONE =>  NONE
                                                                   |   (SOME(v2)) =>  (desttok v2))
                                                            of  NONE =>  NONE
                                                            |   (SOME(v3)) =>  (destalphat v3))
                                               |   (v5::v4) =>  NONE)));

fun  ptree_constructorname v14 = 
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  ((v13 = (Inl(Nconstructorname))) = (0 < 0))
                       then  NONE
                        else  (case  v12
                               of  []  =>  NONE
                               |   (v11::v10) =>  (case  v10
                                                   of  []  =>  (option_choice (case  (ptree_uqconstructorname v11)
                                                                               of  NONE =>  NONE
                                                                               |   (SOME(v2)) =>  (SOME(Short(v2)))) (case  (case  (case  (destlf v11)
                                                                                                                                    of  NONE =>  NONE
                                                                                                                                    |   (SOME(v3)) =>  (desttok v3))
                                                                                                                             of  NONE =>  NONE
                                                                                                                             |   (SOME(v4)) =>  (destlongidt v4))
                                                                                                                      of  NONE =>  NONE
                                                                                                                      |   (SOME(v7)) =>  (case  v7
                                                                                                                                          of  (v6,v5) =>  (SOME(Long(v6,v5))))))
                                                   |   (v9::v8) =>  NONE)));

fun  ifm v2 = 
  (fn  v4 =>
    (fn  v3 =>
      case  v2
      of  NONE =>  NONE
      |   SOME(v1) =>  (if  v1
                         then  v4
                         else  v3)));

fun  issymbolicconstructor v2 =  (fn  v1 => SOME(v1 = [#":",#":"]));

fun  ohd v3 = 
  case  v3
  of  []  =>  NONE
  |   v2::v1 =>  (SOME(v2));

fun  isconstructor v3 = 
  (fn  v2 =>
    ifm (issymbolicconstructor v3 v2) (SOME(0 <= 0)) (SOME(case  (ohd v2)
                                                           of  NONE =>  (0 < 0)
                                                           |   SOME(v1) =>  ((isalpha v1) andalso  (isupper v1)))));

fun  ptree_opid v18 = 
  case  v18
  of  Lf(v1) =>  NONE
  |   Nd(v17,v16) =>  (if  ((v17 = (Inl(Nopid))) = (0 < 0))
                       then  NONE
                        else  (case  v16
                               of  []  =>  NONE
                               |   (v15::v14) =>  (case  v15
                                                   of  (Lf(v11)) =>  (case  v11
                                                                      of  (Tok(v9)) =>  (case  v14
                                                                                         of  []  =>  (option_choice (option_choice (option_choice (case  (destalphat v9)
                                                                                                                                                   of  NONE =>  NONE
                                                                                                                                                   |   (SOME(v2)) =>  (ifm (isconstructor NONE v2) (SOME(Con(SOME(Short(v2)),[] ))) (SOME(Var(Short(v2)))))) (case  (destsymbolt v9)
                                                                                                                                                                                                                                                              of  NONE =>  NONE
                                                                                                                                                                                                                                                              |   (SOME(v3)) =>  (ifm (issymbolicconstructor NONE v3) (SOME(Con(SOME(Short(v3)),[] ))) (SOME(Var(Short(v3))))))) (case  (destlongidt v9)
                                                                                                                                                                                                                                                                                                                                                                                  of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                                                                  |   (SOME(v6)) =>  (case  v6
                                                                                                                                                                                                                                                                                                                                                                                                      of  (v5,v4) =>  (ifm (isconstructor (SOME(v5)) v4) (SOME(Con(SOME(Long(v5,v4)),[] ))) (SOME(Var(Long(v5,v4)))))))) (if  (v9 = Start)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then  (ifm (issymbolicconstructor NONE [#"*"]) (SOME(Con(SOME(Short([#"*"])),[] ))) (SOME(Var(Short([#"*"])))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else  (if  (v9 = Equalst)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 then  (SOME(Var(Short([#"="]))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 else  NONE)))
                                                                                         |   (v8::v7) =>  NONE)
                                                                      |   (Nt(v10)) =>  NONE)
                                                   |   (Nd(v13,v12)) =>  NONE)));

fun  eseq_encode v6 =
  case  v6
  of  []  =>  NONE
  |   v5::v4 =>  (case  v4
                  of  []  =>  (SOME(v5))
                  |   (v3::v2) =>  (case  (eseq_encode (v3::v2))
                                    of  NONE =>  NONE
                                    |   (SOME(v1)) =>  (SOME(Let(NONE,v5,v1)))));

fun  dest_conk v27 = 
  (fn  v28 =>
    (fn  v29 =>
      case  v27
      of  Raise(v1) =>  v29
      |   Handle(v3,v2) =>  v29
      |   Lit(v4) =>  v29
      |   Con(v6,v5) =>  (v28 v6 v5)
      |   Var(v7) =>  v29
      |   Fun(v9,v8) =>  v29
      |   App(v11,v10) =>  v29
      |   Log(v14,v13,v12) =>  v29
      |   If(v17,v16,v15) =>  v29
      |   Mat(v19,v18) =>  v29
      |   Let(v22,v21,v20) =>  v29
      |   Letrec(v24,v23) =>  v29
      |   Tannot(v26,v25) =>  v29));

fun  null v3 = 
  case  v3
  of  []  =>  (0 <= 0)
  |   v2::v1 =>  (0 < 0);

fun  mkast_app v5 = 
  (fn  v6 =>
    dest_conk v5 (fn  v4 =>
                   (fn  v3 =>
                     (if  ((null v3) = (0 < 0))
                      then  (App(Opapp,[v5,v6]))
                      else  (if  (v4 = (SOME(Short([#"r",#"e",#"f"]))))
                             then  (App(Opapp,[Var(Short([#"r",#"e",#"f"])),v6]))
                             else  (dest_conk v6 (fn  v2 =>
                                                   (fn  v1 =>
                                                     (if  ((v2 = NONE) andalso  ((null v1) = (0 < 0)))
                                                      then  (Con(v4,v1))
                                                      else  (Con(v4,[v6]))))) (Con(v4,[v6]))))))) (App(Opapp,[v5,v6])));

fun  ptree_op v11 = 
  case  v11
  of  Lf(v1) =>  NONE
  |   Nd(v10,v9) =>  (if  (v10 = (Inl(Nmultops)))
                      then  (if  (v9 = [Lf(Tok(Start))])
                             then  (SOME(Short([#"*"])))
                             else  (if  (v9 = [Lf(Tok(Symbolt([#"/"])))])
                                    then  (SOME(Short([#"/"])))
                                    else  (if  (v9 = [Lf(Tok(Alphat([#"m",#"o",#"d"])))])
                                           then  (SOME(Short([#"m",#"o",#"d"])))
                                           else  (if  (v9 = [Lf(Tok(Alphat([#"d",#"i",#"v"])))])
                                                  then  (SOME(Short([#"d",#"i",#"v"])))
                                                  else  NONE))))
                      else  (if  (v10 = (Inl(Naddops)))
                             then  (if  (v9 = [Lf(Tok(Symbolt([#"+"])))])
                                    then  (SOME(Short([#"+"])))
                                    else  (if  (v9 = [Lf(Tok(Symbolt([#"-"])))])
                                           then  (SOME(Short([#"-"])))
                                           else  NONE))
                             else  (if  (v10 = (Inl(Nlistops)))
                                    then  (if  (v9 = [Lf(Tok(Symbolt([#":",#":"])))])
                                           then  (SOME(Short([#":",#":"])))
                                           else  (if  (v9 = [Lf(Tok(Symbolt([#"@"])))])
                                                  then  (SOME(Short([#"@"])))
                                                  else  NONE))
                                    else  (if  (v10 = (Inl(Nrelops)))
                                           then  (case  v9
                                                  of  []  =>  NONE
                                                  |   (v8::v7) =>  (case  v7
                                                                    of  []  =>  (option_choice (case  (case  (case  (destlf v8)
                                                                                                              of  NONE =>  NONE
                                                                                                              |   (SOME(v2)) =>  (desttok v2))
                                                                                                       of  NONE =>  NONE
                                                                                                       |   (SOME(v3)) =>  (destsymbolt v3))
                                                                                                of  NONE =>  NONE
                                                                                                |   (SOME(v4)) =>  (SOME(Short(v4)))) (if  (v8 = (Lf(Tok(Equalst))))
                                                                                                                                       then  (SOME(Short([#"="])))
                                                                                                                                       else  NONE))
                                                                    |   (v6::v5) =>  NONE))
                                           else  (if  (v10 = (Inl(Ncompops)))
                                                  then  (if  (v9 = [Lf(Tok(Symbolt([#":",#"="])))])
                                                         then  (SOME(Short([#":",#"="])))
                                                         else  (if  (v9 = [Lf(Tok(Alphat([#"o"])))])
                                                                then  (SOME(Short([#"o"])))
                                                                else  NONE))
                                                  else  NONE)))));

fun  mk_binop v3 = 
  (fn  v1 =>
    (fn  v2 =>
      if  (v3 = (Short([#":",#":"])))
      then  (Con(SOME(Short([#":",#":"])),[v1,v2]))
      else  (App(Opapp,[App(Opapp,[Var(v3),v1]),v2]))));

fun  tuplify v5 = 
  case  v5
  of  []  =>  NONE
  |   v4::v3 =>  (case  v3
                  of  []  =>  (SOME(v4))
                  |   (v2::v1) =>  (SOME(Tapp(v4::v2::v1,Tc_tup))));

fun  tfn v1 =  (fn  v2 => Tapp([v1,v2],Tc_fn));

fun  ptree_uqtyop v10 = 
  case  v10
  of  Lf(v1) =>  NONE
  |   Nd(v9,v8) =>  (if  ((v9 = (Inl(Nuqtyop))) = (0 < 0))
                     then  NONE
                      else  (case  v8
                             of  []  =>  NONE
                             |   (v7::v6) =>  (case  v6
                                               of  []  =>  (case  (destlf v7)
                                                            of  NONE =>  NONE
                                                            |   (SOME(v3)) =>  (case  (desttok v3)
                                                                                of  NONE =>  NONE
                                                                                |   (SOME(v2)) =>  (option_choice (destsymbolt v2) (destalphat v2))))
                                               |   (v5::v4) =>  NONE)));

fun  ptree_tyop v14 = 
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  ((v13 = (Inl(Ntyop))) = (0 < 0))
                       then  NONE
                        else  (case  v12
                               of  []  =>  NONE
                               |   (v11::v10) =>  (case  v10
                                                   of  []  =>  (option_choice (case  (case  (case  (destlf v11)
                                                                                             of  NONE =>  NONE
                                                                                             |   (SOME(v2)) =>  (desttok v2))
                                                                                      of  NONE =>  NONE
                                                                                      |   (SOME(v3)) =>  (destlongidt v3))
                                                                               of  NONE =>  NONE
                                                                               |   (SOME(v6)) =>  (case  v6
                                                                                                   of  (v5,v4) =>  (SOME(Long(v5,v4))))) (case  (ptree_uqtyop v11)
                                                                                                                                          of  NONE =>  NONE
                                                                                                                                          |   (SOME(v7)) =>  (SOME(Short(v7)))))
                                                   |   (v9::v8) =>  NONE)));

fun  desttyvarpt v17 = 
  case  v17
  of  Lf(v14) =>  (case  v14
                   of  (Tok(v12)) =>  (case  v12
                                       of  (Whitespacet(v1)) =>  NONE
                                       |   Newlinet =>  NONE
                                       |   Lexerrort =>  NONE
                                       |   Hasht =>  NONE
                                       |   Lpart =>  NONE
                                       |   Rpart =>  NONE
                                       |   Start =>  NONE
                                       |   Commat =>  NONE
                                       |   Arrowt =>  NONE
                                       |   Dotst =>  NONE
                                       |   Colont =>  NONE
                                       |   Sealt =>  NONE
                                       |   Semicolont =>  NONE
                                       |   Equalst =>  NONE
                                       |   Darrowt =>  NONE
                                       |   Lbrackt =>  NONE
                                       |   Rbrackt =>  NONE
                                       |   Underbart =>  NONE
                                       |   Lbracet =>  NONE
                                       |   Bart =>  NONE
                                       |   Rbracet =>  NONE
                                       |   Andt =>  NONE
                                       |   Andalsot =>  NONE
                                       |   Ast =>  NONE
                                       |   Caset =>  NONE
                                       |   Datatypet =>  NONE
                                       |   Elset =>  NONE
                                       |   Endt =>  NONE
                                       |   Eqtypet =>  NONE
                                       |   Exceptiont =>  NONE
                                       |   Fnt =>  NONE
                                       |   Funt =>  NONE
                                       |   Handlet =>  NONE
                                       |   Ift =>  NONE
                                       |   Int =>  NONE
                                       |   Includet =>  NONE
                                       |   Lett =>  NONE
                                       |   Localt =>  NONE
                                       |   Oft =>  NONE
                                       |   Opt =>  NONE
                                       |   Opent =>  NONE
                                       |   Orelset =>  NONE
                                       |   Raiset =>  NONE
                                       |   Rect =>  NONE
                                       |   Sharingt =>  NONE
                                       |   Sigt =>  NONE
                                       |   Signaturet =>  NONE
                                       |   Structt =>  NONE
                                       |   Structuret =>  NONE
                                       |   Thent =>  NONE
                                       |   Typet =>  NONE
                                       |   Valt =>  NONE
                                       |   Wheret =>  NONE
                                       |   Whilet =>  NONE
                                       |   Witht =>  NONE
                                       |   Withtypet =>  NONE
                                       |   (Intt(v2)) =>  NONE
                                       |   (Hexintt(v3)) =>  NONE
                                       |   (Realt(v4)) =>  NONE
                                       |   (Stringt(v5)) =>  NONE
                                       |   (Chart(v6)) =>  NONE
                                       |   (Tyvart(v7)) =>  (SOME(v7))
                                       |   (Alphat(v8)) =>  NONE
                                       |   (Symbolt(v9)) =>  NONE
                                       |   (Longidt(v11,v10)) =>  NONE)
                   |   (Nt(v13)) =>  NONE)
  |   Nd(v16,v15) =>  NONE;

fun  ptree_type v39 v40 =
  case  v40
  of  Lf(v1) =>  NONE
  |   Nd(v38,v37) =>  (if  ((v38 = (Inl(v39))) = (0 < 0))
                       then  NONE
                        else  (if  (v39 = Ntype)
                               then  (case  v37
                                      of  []  =>  NONE
                                      |   (v13::v12) =>  (case  v12
                                                          of  []  =>  (case  (ptree_ptype v13)
                                                                       of  NONE =>  NONE
                                                                       |   (SOME(v2)) =>  (tuplify v2))
                                                          |   (v11::v10) =>  (case  v10
                                                                              of  []  =>  NONE
                                                                              |   (v9::v8) =>  (case  v8
                                                                                                of  []  =>  (if  (v11 = (Lf(Tok(Arrowt))))
                                                                                                             then  (case  (ptree_ptype v13)
                                                                                                                    of  NONE =>  NONE
                                                                                                                    |   (SOME(v5)) =>  (case  (tuplify v5)
                                                                                                                                        of  NONE =>  NONE
                                                                                                                                        |   (SOME(v4)) =>  (case  (ptree_type Ntype v9)
                                                                                                                                                            of  NONE =>  NONE
                                                                                                                                                            |   (SOME(v3)) =>  (SOME(tfn v4 v3)))))
                                                                                                             else  NONE)
                                                                                                |   (v7::v6) =>  NONE))))
                               else  (if  (v39 = Ndtype)
                                      then  (case  v37
                                             of  []  =>  NONE
                                             |   (v21::v20) =>  (case  v20
                                                                 of  []  =>  (ptree_type Ntbase v21)
                                                                 |   (v19::v18) =>  (case  v18
                                                                                     of  []  =>  (case  (ptree_type Ndtype v21)
                                                                                                  of  NONE =>  NONE
                                                                                                  |   (SOME(v15)) =>  (case  (ptree_tyop v19)
                                                                                                                       of  NONE =>  NONE
                                                                                                                       |   (SOME(v14)) =>  (SOME(Tapp([v15],Tc_name(v14))))))
                                                                                     |   (v17::v16) =>  NONE)))
                                      else  (if  (v39 = Ntbase)
                                             then  (case  v37
                                                    of  []  =>  NONE
                                                    |   (v36::v35) =>  (case  v35
                                                                        of  []  =>  (option_choice (option_map (fn  v22 =>
                                                                                                                 (Tvar(v22))) (desttyvarpt v36)) (option_map (o_1 (fn  v23 =>
                                                                                                                                                                    (Tapp([] ,v23))) (fn  v24 =>
                                                                                                                                                                                       (Tc_name(v24)))) (ptree_tyop v36)))
                                                                        |   (v34::v33) =>  (case  v33
                                                                                            of  []  =>  NONE
                                                                                            |   (v32::v31) =>  (case  v31
                                                                                                                of  []  =>  (if  ((v36 = (Lf(Tok(Lpart)))) andalso  (v32 = (Lf(Tok(Rpart)))))
                                                                                                                             then  (ptree_type Ntype v34)
                                                                                                                             else  NONE)
                                                                                                                |   (v30::v29) =>  (case  v29
                                                                                                                                    of  []  =>  (if  ((v36 = (Lf(Tok(Lpart)))) andalso  (v32 = (Lf(Tok(Rpart)))))
                                                                                                                                                 then  (case  (ptree_typelist2 v34)
                                                                                                                                                        of  NONE =>  NONE
                                                                                                                                                        |   (SOME(v26)) =>  (case  (ptree_tyop v30)
                                                                                                                                                                             of  NONE =>  NONE
                                                                                                                                                                             |   (SOME(v25)) =>  (SOME(Tapp(v26,Tc_name(v25))))))
                                                                                                                                                 else  NONE)
                                                                                                                                    |   (v28::v27) =>  NONE)))))
                                             else  NONE))))
and  ptree_typelist2 v14 =
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  ((v13 = (Inl(Ntypelist2))) = (0 < 0))
                       then  NONE
                        else  (case  v12
                               of  []  =>  NONE
                               |   (v11::v10) =>  (case  v10
                                                   of  []  =>  NONE
                                                   |   (v9::v8) =>  (case  v8
                                                                     of  []  =>  NONE
                                                                     |   (v7::v6) =>  (case  v6
                                                                                       of  []  =>  (if  (v9 = (Lf(Tok(Commat))))
                                                                                                    then  (case  (ptree_type Ntype v11)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v3)) =>  (case  (ptree_typelist1 v7)
                                                                                                                               of  NONE =>  NONE
                                                                                                                               |   (SOME(v2)) =>  (SOME(v3::v2))))
                                                                                                    else  NONE)
                                                                                       |   (v5::v4) =>  NONE)))))
and  ptree_typelist1 v15 =
  case  v15
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  ((v14 = (Inl(Ntypelist1))) = (0 < 0))
                       then  NONE
                        else  (case  v13
                               of  []  =>  NONE
                               |   (v12::v11) =>  (case  v11
                                                   of  []  =>  (case  (ptree_type Ntype v12)
                                                                of  NONE =>  NONE
                                                                |   (SOME(v2)) =>  (SOME([v2])))
                                                   |   (v10::v9) =>  (case  v9
                                                                      of  []  =>  NONE
                                                                      |   (v8::v7) =>  (case  v7
                                                                                        of  []  =>  (if  (v10 = (Lf(Tok(Commat))))
                                                                                                     then  (case  (ptree_type Ntype v12)
                                                                                                            of  NONE =>  NONE
                                                                                                            |   (SOME(v4)) =>  (case  (ptree_typelist1 v8)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v3)) =>  (SOME(v4::v3))))
                                                                                                     else  NONE)
                                                                                        |   (v6::v5) =>  NONE)))))
and  ptree_ptype v15 =
  case  v15
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  ((v14 = (Inl(Nptype))) = (0 < 0))
                       then  NONE
                        else  (case  v13
                               of  []  =>  NONE
                               |   (v12::v11) =>  (case  v11
                                                   of  []  =>  (case  (ptree_type Ndtype v12)
                                                                of  NONE =>  NONE
                                                                |   (SOME(v2)) =>  (SOME([v2])))
                                                   |   (v10::v9) =>  (case  v9
                                                                      of  []  =>  NONE
                                                                      |   (v8::v7) =>  (case  v7
                                                                                        of  []  =>  (if  (v10 = (Lf(Tok(Start))))
                                                                                                     then  (case  (ptree_type Ndtype v12)
                                                                                                            of  NONE =>  NONE
                                                                                                            |   (SOME(v4)) =>  (case  (ptree_ptype v8)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v3)) =>  (SOME(v4::v3))))
                                                                                                     else  NONE)
                                                                                        |   (v6::v5) =>  NONE)))));

fun  mkpatapp v10 = 
  (fn  v9 =>
    if  (v10 = (Short([#"r",#"e",#"f"])))
    then  (Pref(v9))
    else  (case  v9
           of  (Pvar(v1)) =>  (Pcon(SOME(v10),[v9]))
           |   (Plit(v2)) =>  (Pcon(SOME(v10),[v9]))
           |   (Pcon(v5,v4)) =>  (case  v5
                                  of  NONE =>  (Pcon(SOME(v10),v4))
                                  |   (SOME(v3)) =>  (Pcon(SOME(v10),[v9])))
           |   (Pref(v6)) =>  (Pcon(SOME(v10),[v9]))
           |   (Ptannot(v8,v7)) =>  (Pcon(SOME(v10),[v9]))));

fun  ptree_pattern v63 v64 =
  case  v64
  of  Lf(v1) =>  NONE
  |   Nd(v62,v61) =>  (if  (((Inl(v63)) = v62) = (0 < 0))
                       then  NONE
                        else  (if  (v62 = (Inl(Npbase)))
                               then  (case  v61
                                      of  []  =>  NONE
                                      |   (v19::v18) =>  (case  v18
                                                          of  []  =>  (option_choice (option_choice (option_choice (option_choice (ptree_pattern Nptuple v19) (case  (ptree_constructorname v19)
                                                                                                                                                               of  NONE =>  NONE
                                                                                                                                                               |   (SOME(v2)) =>  (SOME(Pcon(SOME(v2),[] ))))) (case  (ptree_v v19)
                                                                                                                                                                                                                of  NONE =>  NONE
                                                                                                                                                                                                                |   (SOME(v3)) =>  (SOME(Pvar(v3))))) (case  (destlf v19)
                                                                                                                                                                                                                                                       of  NONE =>  NONE
                                                                                                                                                                                                                                                       |   (SOME(v8)) =>  (case  (desttok v8)
                                                                                                                                                                                                                                                                           of  NONE =>  NONE
                                                                                                                                                                                                                                                                           |   (SOME(v7)) =>  (option_choice (option_choice (case  (destintt v7)
                                                                                                                                                                                                                                                                                                                             of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                             |   (SOME(v4)) =>  (SOME(Plit(Intlit(v4))))) (case  (deststringt v7)
                                                                                                                                                                                                                                                                                                                                                                           of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                                                           |   (SOME(v5)) =>  (SOME(Plit(Strlit(v5)))))) (case  (destchart v7)
                                                                                                                                                                                                                                                                                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                                                                                                          |   (SOME(v6)) =>  (SOME(Plit(Char(v6))))))))) (if  (v19 = (Lf(Tok(Underbart))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then  (SOME(Pvar([#"_"])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else  NONE))
                                                          |   (v17::v16) =>  (case  v16
                                                                              of  []  =>  (if  ((v19 = (Lf(Tok(Lbrackt)))) andalso  (v17 = (Lf(Tok(Rbrackt)))))
                                                                                           then  (SOME(Pcon(SOME(Short([#"n",#"i",#"l"])),[] )))
                                                                                           else  NONE)
                                                                              |   (v15::v14) =>  (case  v14
                                                                                                  of  []  =>  (if  ((v19 = (Lf(Tok(Lbrackt)))) andalso  (v15 = (Lf(Tok(Rbrackt)))))
                                                                                                               then  (case  (ptree_plist v17)
                                                                                                                      of  NONE =>  NONE
                                                                                                                      |   (SOME(v11)) =>  (SOME(foldr (fn  v10 =>
                                                                                                                                                        (fn  v9 =>
                                                                                                                                                          (Pcon(SOME(Short([#":",#":"])),[v10,v9])))) (Pcon(SOME(Short([#"n",#"i",#"l"])),[] )) v11)))
                                                                                                               else  NONE)
                                                                                                  |   (v13::v12) =>  NONE))))
                               else  (if  (v62 = (Inl(Npapp)))
                                      then  (case  v61
                                             of  []  =>  NONE
                                             |   (v27::v26) =>  (case  v26
                                                                 of  []  =>  (ptree_pattern Npbase v27)
                                                                 |   (v25::v24) =>  (case  v24
                                                                                     of  []  =>  (case  (ptree_constructorname v27)
                                                                                                  of  NONE =>  NONE
                                                                                                  |   (SOME(v21)) =>  (case  (ptree_pattern Npbase v25)
                                                                                                                       of  NONE =>  NONE
                                                                                                                       |   (SOME(v20)) =>  (SOME(mkpatapp v21 v20))))
                                                                                     |   (v23::v22) =>  NONE)))
                                      else  (if  (v62 = (Inl(Npcons)))
                                             then  (case  v61
                                                    of  []  =>  NONE
                                                    |   (v37::v36) =>  (case  v36
                                                                        of  []  =>  (ptree_pattern Npapp v37)
                                                                        |   (v35::v34) =>  (case  v34
                                                                                            of  []  =>  NONE
                                                                                            |   (v33::v32) =>  (case  v32
                                                                                                                of  []  =>  (if  (v35 = (Lf(Tok(Symbolt([#":",#":"])))))
                                                                                                                             then  (case  (ptree_pattern Npapp v37)
                                                                                                                                    of  NONE =>  NONE
                                                                                                                                    |   (SOME(v29)) =>  (case  (ptree_pattern Npcons v33)
                                                                                                                                                         of  NONE =>  NONE
                                                                                                                                                         |   (SOME(v28)) =>  (SOME(Pcon(SOME(Short([#":",#":"])),[v29,v28])))))
                                                                                                                             else  NONE)
                                                                                                                |   (v31::v30) =>  NONE))))
                                             else  (if  (v62 = (Inl(Npattern)))
                                                    then  (case  v61
                                                           of  []  =>  NONE
                                                           |   (v47::v46) =>  (case  v46
                                                                               of  []  =>  (ptree_pattern Npcons v47)
                                                                               |   (v45::v44) =>  (case  v44
                                                                                                   of  []  =>  NONE
                                                                                                   |   (v43::v42) =>  (case  v42
                                                                                                                       of  []  =>  (if  (v45 = (Lf(Tok(Colont))))
                                                                                                                                    then  (case  (ptree_pattern Npcons v47)
                                                                                                                                           of  NONE =>  NONE
                                                                                                                                           |   (SOME(v39)) =>  (case  (ptree_type Ntype v43)
                                                                                                                                                                of  NONE =>  NONE
                                                                                                                                                                |   (SOME(v38)) =>  (SOME(Ptannot(v39,v38)))))
                                                                                                                                    else  NONE)
                                                                                                                       |   (v41::v40) =>  NONE))))
                                                    else  (if  (v62 = (Inl(Nptuple)))
                                                           then  (case  v61
                                                                  of  []  =>  NONE
                                                                  |   (v60::v59) =>  (case  v59
                                                                                      of  []  =>  NONE
                                                                                      |   (v58::v57) =>  (case  v57
                                                                                                          of  []  =>  (if  ((v60 = (Lf(Tok(Lpart)))) andalso  (v58 = (Lf(Tok(Rpart)))))
                                                                                                                       then  (SOME(Pcon(NONE,[] )))
                                                                                                                       else  NONE)
                                                                                                          |   (v56::v55) =>  (case  v55
                                                                                                                              of  []  =>  (if  ((v60 = (Lf(Tok(Lpart)))) andalso  (v56 = (Lf(Tok(Rpart)))))
                                                                                                                                           then  (case  (ptree_plist v58)
                                                                                                                                                  of  NONE =>  NONE
                                                                                                                                                  |   (SOME(v52)) =>  (case  v52
                                                                                                                                                                       of  []  =>  NONE
                                                                                                                                                                       |   (v51::v50) =>  (case  v50
                                                                                                                                                                                           of  []  =>  (SOME(v51))
                                                                                                                                                                                           |   (v49::v48) =>  (SOME(Pcon(NONE,v52))))))
                                                                                                                                           else  NONE)
                                                                                                                              |   (v54::v53) =>  NONE))))
                                                           else  NONE))))))
and  ptree_plist v15 =
  case  v15
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  ((v14 = (Inl(Npatternlist))) = (0 < 0))
                       then  NONE
                        else  (case  v13
                               of  []  =>  NONE
                               |   (v12::v11) =>  (case  v11
                                                   of  []  =>  (case  (ptree_pattern Npattern v12)
                                                                of  NONE =>  NONE
                                                                |   (SOME(v2)) =>  (SOME([v2])))
                                                   |   (v10::v9) =>  (case  v9
                                                                      of  []  =>  NONE
                                                                      |   (v8::v7) =>  (case  v7
                                                                                        of  []  =>  (if  (v10 = (Lf(Tok(Commat))))
                                                                                                     then  (case  (ptree_pattern Npattern v12)
                                                                                                            of  NONE =>  NONE
                                                                                                            |   (SOME(v4)) =>  (case  (ptree_plist v8)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v3)) =>  (SOME(v4::v3))))
                                                                                                     else  NONE)
                                                                                        |   (v6::v5) =>  NONE)))));

fun  depat v8 = 
  (fn  v9 =>
    case  v8
    of  Pvar(v1) =>  (v1,v9)
    |   Plit(v2) =>  ([] ,Mat(Var(Short([] )),[(Plit(v2),v9)]))
    |   Pcon(v4,v3) =>  ([] ,Mat(Var(Short([] )),[(Pcon(v4,v3),v9)]))
    |   Pref(v5) =>  ([] ,Mat(Var(Short([] )),[(Pref(v5),v9)]))
    |   Ptannot(v7,v6) =>  ([] ,Mat(Var(Short([] )),[(Ptannot(v7,v6),v9)])));

fun  mkfun v4 = 
  (fn  v3 => case  (depat v4 v3) of  (v2,v1) =>  (Fun(v2,v1)));

fun  ptree_pbaselist1 v13 =
  case  v13
  of  Lf(v1) =>  NONE
  |   Nd(v12,v11) =>  (if  ((v12 = (Inl(Npbaselist1))) = (0 < 0))
                       then  NONE
                        else  (case  v11
                               of  []  =>  NONE
                               |   (v10::v9) =>  (case  v9
                                                  of  []  =>  (option_map (fn  v2 =>
                                                                            [v2]) (ptree_pattern Npbase v10))
                                                  |   (v8::v7) =>  (case  v7
                                                                    of  []  =>  (option_map2 (fn  v4 =>
                                                                                               (fn  v3 =>
                                                                                                 (v4::v3))) (ptree_pattern Npbase v10) (ptree_pbaselist1 v8))
                                                                    |   (v6::v5) =>  NONE))));

fun  safetl v3 = 
  case  v3
  of  []  =>  []
   |   v2::v1 =>  v1;

fun  ptree_expr v200 v201 =
  case  v201
  of  Lf(v1) =>  NONE
  |   Nd(v199,v198) =>  (if  ((Inl(v200)) = v199)
                         then  (if  (v199 = (Inl(Nebase)))
                                then  (case  v198
                                       of  []  =>  NONE
                                       |   (v33::v32) =>  (case  v32
                                                           of  []  =>  (option_choice (option_choice (option_choice (case  (destlf v33)
                                                                                                                     of  NONE =>  NONE
                                                                                                                     |   (SOME(v6)) =>  (case  (desttok v6)
                                                                                                                                         of  NONE =>  NONE
                                                                                                                                         |   (SOME(v5)) =>  (option_choice (option_choice (case  (destintt v5)
                                                                                                                                                                                           of  NONE =>  NONE
                                                                                                                                                                                           |   (SOME(v2)) =>  (SOME(Lit(Intlit(v2))))) (case  (destchart v5)
                                                                                                                                                                                                                                        of  NONE =>  NONE
                                                                                                                                                                                                                                        |   (SOME(v3)) =>  (SOME(Lit(Char(v3)))))) (case  (deststringt v5)
                                                                                                                                                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                                                                                                                                                    |   (SOME(v4)) =>  (SOME(Lit(Strlit(v4)))))))) (case  (ptree_fqv v33)
                                                                                                                                                                                                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                    |   (SOME(v7)) =>  (SOME(Var(v7))))) (case  (ptree_constructorname v33)
                                                                                                                                                                                                                                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                                                          |   (SOME(v8)) =>  (SOME(Con(SOME(v8),[] ))))) (ptree_expr Netuple v33))
                                                           |   (v31::v30) =>  (case  v30
                                                                               of  []  =>  (if  ((v33 = (Lf(Tok(Lpart)))) andalso  (v31 = (Lf(Tok(Rpart)))))
                                                                                            then  (SOME(Con(NONE,[] )))
                                                                                            else  (if  ((v33 = (Lf(Tok(Lbrackt)))) andalso  (v31 = (Lf(Tok(Rbrackt)))))
                                                                                                   then  (SOME(Con(SOME(Short([#"n",#"i",#"l"])),[] )))
                                                                                                   else  (if  (v33 = (Lf(Tok(Opt))))
                                                                                                          then  (ptree_opid v31)
                                                                                                          else  NONE)))
                                                                               |   (v29::v28) =>  (case  v28
                                                                                                   of  []  =>  (option_choice (if  ((v33 = (Lf(Tok(Lpart)))) andalso  (v29 = (Lf(Tok(Rpart)))))
                                                                                                                               then  (case  (ptree_eseq v31)
                                                                                                                                      of  NONE =>  NONE
                                                                                                                                      |   (SOME(v9)) =>  (eseq_encode v9))
                                                                                                                               else  NONE) (if  ((v33 = (Lf(Tok(Lbrackt)))) andalso  (v29 = (Lf(Tok(Rbrackt)))))
                                                                                                                                            then  (case  (ptree_exprlist Nelist1 v31)
                                                                                                                                                   of  NONE =>  NONE
                                                                                                                                                   |   (SOME(v12)) =>  (SOME(foldr (fn  v11 =>
                                                                                                                                                                                     (fn  v10 =>
                                                                                                                                                                                       (Con(SOME(Short([#":",#":"])),[v11,v10])))) (Con(SOME(Short([#"n",#"i",#"l"])),[] )) v12)))
                                                                                                                                            else  NONE))
                                                                                                   |   (v27::v26) =>  (case  v26
                                                                                                                       of  []  =>  NONE
                                                                                                                       |   (v25::v24) =>  (case  v24
                                                                                                                                           of  []  =>  (if  (((v33 = (Lf(Tok(Lett)))) andalso  (v29 = (Lf(Tok(Int))))) andalso  (v25 = (Lf(Tok(Endt)))))
                                                                                                                                                        then  (case  (ptree_letdecs v31)
                                                                                                                                                               of  NONE =>  NONE
                                                                                                                                                               |   (SOME(v21)) =>  (case  (ptree_eseq v27)
                                                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                                                    |   (SOME(v20)) =>  (case  (eseq_encode v20)
                                                                                                                                                                                                         of  NONE =>  NONE
                                                                                                                                                                                                         |   (SOME(v19)) =>  (SOME(foldr (fn  v18 =>
                                                                                                                                                                                                                                           (fn  v17 =>
                                                                                                                                                                                                                                             (case  v18
                                                                                                                                                                                                                                              of  (Inl(v15)) =>  (case  v15
                                                                                                                                                                                                                                                                  of  (v14,v13) =>  (Let(SOME(v14),v13,v17)))
                                                                                                                                                                                                                                              |   (Inr(v16)) =>  (Letrec(v16,v17))))) v19 v21)))))
                                                                                                                                                        else  NONE)
                                                                                                                                           |   (v23::v22) =>  NONE))))))
                                else  (if  (v199 = (Inl(Neapp)))
                                       then  (case  v198
                                              of  []  =>  NONE
                                              |   (v41::v40) =>  (case  v40
                                                                  of  []  =>  (ptree_expr Nebase v41)
                                                                  |   (v39::v38) =>  (case  v38
                                                                                      of  []  =>  (case  (ptree_expr Neapp v41)
                                                                                                   of  NONE =>  NONE
                                                                                                   |   (SOME(v35)) =>  (case  (ptree_expr Nebase v39)
                                                                                                                        of  NONE =>  NONE
                                                                                                                        |   (SOME(v34)) =>  (SOME(mkast_app v35 v34))))
                                                                                      |   (v37::v36) =>  NONE)))
                                       else  (if  (v199 = (Inl(Netuple)))
                                              then  (case  v198
                                                     of  []  =>  NONE
                                                     |   (v50::v49) =>  (case  v49
                                                                         of  []  =>  NONE
                                                                         |   (v48::v47) =>  (case  v47
                                                                                             of  []  =>  NONE
                                                                                             |   (v46::v45) =>  (case  v45
                                                                                                                 of  []  =>  (if  ((v50 = (Lf(Tok(Lpart)))) andalso  (v46 = (Lf(Tok(Rpart)))))
                                                                                                                              then  (case  (ptree_exprlist Nelist2 v48)
                                                                                                                                     of  NONE =>  NONE
                                                                                                                                     |   (SOME(v42)) =>  (SOME(Con(NONE,v42))))
                                                                                                                              else  NONE)
                                                                                                                 |   (v44::v43) =>  NONE))))
                                              else  (if  (v199 = (Inl(Nemult)))
                                                     then  (case  v198
                                                            of  []  =>  NONE
                                                            |   (v61::v60) =>  (case  v60
                                                                                of  []  =>  (ptree_expr Neapp v61)
                                                                                |   (v59::v58) =>  (case  v58
                                                                                                    of  []  =>  NONE
                                                                                                    |   (v57::v56) =>  (case  v56
                                                                                                                        of  []  =>  (case  (ptree_expr Nemult v61)
                                                                                                                                     of  NONE =>  NONE
                                                                                                                                     |   (SOME(v53)) =>  (case  (ptree_op v59)
                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                          |   (SOME(v52)) =>  (case  (ptree_expr Neapp v57)
                                                                                                                                                                               of  NONE =>  NONE
                                                                                                                                                                               |   (SOME(v51)) =>  (SOME(mk_binop v52 v53 v51)))))
                                                                                                                        |   (v55::v54) =>  NONE))))
                                                     else  (if  (v199 = (Inl(Neadd)))
                                                            then  (case  v198
                                                                   of  []  =>  NONE
                                                                   |   (v72::v71) =>  (case  v71
                                                                                       of  []  =>  (ptree_expr Nemult v72)
                                                                                       |   (v70::v69) =>  (case  v69
                                                                                                           of  []  =>  NONE
                                                                                                           |   (v68::v67) =>  (case  v67
                                                                                                                               of  []  =>  (case  (ptree_expr Neadd v72)
                                                                                                                                            of  NONE =>  NONE
                                                                                                                                            |   (SOME(v64)) =>  (case  (ptree_op v70)
                                                                                                                                                                 of  NONE =>  NONE
                                                                                                                                                                 |   (SOME(v63)) =>  (case  (ptree_expr Nemult v68)
                                                                                                                                                                                      of  NONE =>  NONE
                                                                                                                                                                                      |   (SOME(v62)) =>  (SOME(mk_binop v63 v64 v62)))))
                                                                                                                               |   (v66::v65) =>  NONE))))
                                                            else  (if  (v199 = (Inl(Nelistop)))
                                                                   then  (case  v198
                                                                          of  []  =>  NONE
                                                                          |   (v83::v82) =>  (case  v82
                                                                                              of  []  =>  (ptree_expr Neadd v83)
                                                                                              |   (v81::v80) =>  (case  v80
                                                                                                                  of  []  =>  NONE
                                                                                                                  |   (v79::v78) =>  (case  v78
                                                                                                                                      of  []  =>  (case  (ptree_expr Neadd v83)
                                                                                                                                                   of  NONE =>  NONE
                                                                                                                                                   |   (SOME(v75)) =>  (case  (ptree_op v81)
                                                                                                                                                                        of  NONE =>  NONE
                                                                                                                                                                        |   (SOME(v74)) =>  (case  (ptree_expr Nelistop v79)
                                                                                                                                                                                             of  NONE =>  NONE
                                                                                                                                                                                             |   (SOME(v73)) =>  (SOME(mk_binop v74 v75 v73)))))
                                                                                                                                      |   (v77::v76) =>  NONE))))
                                                                   else  (if  (v199 = (Inl(Nerel)))
                                                                          then  (case  v198
                                                                                 of  []  =>  NONE
                                                                                 |   (v94::v93) =>  (case  v93
                                                                                                     of  []  =>  (ptree_expr Nelistop v94)
                                                                                                     |   (v92::v91) =>  (case  v91
                                                                                                                         of  []  =>  NONE
                                                                                                                         |   (v90::v89) =>  (case  v89
                                                                                                                                             of  []  =>  (case  (ptree_expr Nerel v94)
                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                          |   (SOME(v86)) =>  (case  (ptree_op v92)
                                                                                                                                                                               of  NONE =>  NONE
                                                                                                                                                                               |   (SOME(v85)) =>  (case  (ptree_expr Nelistop v90)
                                                                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                                                                    |   (SOME(v84)) =>  (SOME(mk_binop v85 v86 v84)))))
                                                                                                                                             |   (v88::v87) =>  NONE))))
                                                                          else  (if  (v199 = (Inl(Necomp)))
                                                                                 then  (case  v198
                                                                                        of  []  =>  NONE
                                                                                        |   (v105::v104) =>  (case  v104
                                                                                                              of  []  =>  (ptree_expr Nerel v105)
                                                                                                              |   (v103::v102) =>  (case  v102
                                                                                                                                    of  []  =>  NONE
                                                                                                                                    |   (v101::v100) =>  (case  v100
                                                                                                                                                          of  []  =>  (case  (ptree_expr Necomp v105)
                                                                                                                                                                       of  NONE =>  NONE
                                                                                                                                                                       |   (SOME(v97)) =>  (case  (ptree_op v103)
                                                                                                                                                                                            of  NONE =>  NONE
                                                                                                                                                                                            |   (SOME(v96)) =>  (case  (ptree_expr Nerel v101)
                                                                                                                                                                                                                 of  NONE =>  NONE
                                                                                                                                                                                                                 |   (SOME(v95)) =>  (SOME(mk_binop v96 v97 v95)))))
                                                                                                                                                          |   (v99::v98) =>  NONE))))
                                                                                 else  (if  (v199 = (Inl(Nebefore)))
                                                                                        then  (case  v198
                                                                                               of  []  =>  NONE
                                                                                               |   (v115::v114) =>  (case  v114
                                                                                                                     of  []  =>  (ptree_expr Necomp v115)
                                                                                                                     |   (v113::v112) =>  (case  v112
                                                                                                                                           of  []  =>  NONE
                                                                                                                                           |   (v111::v110) =>  (case  v110
                                                                                                                                                                 of  []  =>  (if  (v113 = (Lf(Tok(Alphat([#"b",#"e",#"f",#"o",#"r",#"e"])))))
                                                                                                                                                                              then  (case  (ptree_expr Nebefore v115)
                                                                                                                                                                                     of  NONE =>  NONE
                                                                                                                                                                                     |   (SOME(v107)) =>  (case  (ptree_expr Necomp v111)
                                                                                                                                                                                                           of  NONE =>  NONE
                                                                                                                                                                                                           |   (SOME(v106)) =>  (SOME(mk_binop (Short([#"b",#"e",#"f",#"o",#"r",#"e"])) v107 v106))))
                                                                                                                                                                              else  NONE)
                                                                                                                                                                 |   (v109::v108) =>  NONE))))
                                                                                        else  (if  (v199 = (Inl(Netyped)))
                                                                                               then  (case  v198
                                                                                                      of  []  =>  NONE
                                                                                                      |   (v125::v124) =>  (case  v124
                                                                                                                            of  []  =>  (ptree_expr Nebefore v125)
                                                                                                                            |   (v123::v122) =>  (case  v122
                                                                                                                                                  of  []  =>  NONE
                                                                                                                                                  |   (v121::v120) =>  (case  v120
                                                                                                                                                                        of  []  =>  (if  (v123 = (Lf(Tok(Colont))))
                                                                                                                                                                                     then  (case  (ptree_expr Nebefore v125)
                                                                                                                                                                                            of  NONE =>  NONE
                                                                                                                                                                                            |   (SOME(v117)) =>  (case  (ptree_type Ntype v121)
                                                                                                                                                                                                                  of  NONE =>  NONE
                                                                                                                                                                                                                  |   (SOME(v116)) =>  (SOME(Tannot(v117,v116)))))
                                                                                                                                                                                     else  NONE)
                                                                                                                                                                        |   (v119::v118) =>  NONE))))
                                                                                               else  (if  (v199 = (Inl(Nelogicand)))
                                                                                                      then  (case  v198
                                                                                                             of  []  =>  NONE
                                                                                                             |   (v135::v134) =>  (case  v134
                                                                                                                                   of  []  =>  (ptree_expr Netyped v135)
                                                                                                                                   |   (v133::v132) =>  (case  v132
                                                                                                                                                         of  []  =>  NONE
                                                                                                                                                         |   (v131::v130) =>  (case  v130
                                                                                                                                                                               of  []  =>  (if  (v133 = (Lf(Tok(Andalsot))))
                                                                                                                                                                                            then  (case  (ptree_expr Nelogicand v135)
                                                                                                                                                                                                   of  NONE =>  NONE
                                                                                                                                                                                                   |   (SOME(v127)) =>  (case  (ptree_expr Netyped v131)
                                                                                                                                                                                                                         of  NONE =>  NONE
                                                                                                                                                                                                                         |   (SOME(v126)) =>  (SOME(Log(And,v127,v126)))))
                                                                                                                                                                                            else  NONE)
                                                                                                                                                                               |   (v129::v128) =>  NONE))))
                                                                                                      else  (if  (v199 = (Inl(Nelogicor)))
                                                                                                             then  (case  v198
                                                                                                                    of  []  =>  NONE
                                                                                                                    |   (v145::v144) =>  (case  v144
                                                                                                                                          of  []  =>  (ptree_expr Nelogicand v145)
                                                                                                                                          |   (v143::v142) =>  (case  v142
                                                                                                                                                                of  []  =>  NONE
                                                                                                                                                                |   (v141::v140) =>  (case  v140
                                                                                                                                                                                      of  []  =>  (if  (v143 = (Lf(Tok(Orelset))))
                                                                                                                                                                                                   then  (case  (ptree_expr Nelogicor v145)
                                                                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                                                                          |   (SOME(v137)) =>  (case  (ptree_expr Nelogicand v141)
                                                                                                                                                                                                                                of  NONE =>  NONE
                                                                                                                                                                                                                                |   (SOME(v136)) =>  (SOME(Log(Or,v137,v136)))))
                                                                                                                                                                                                   else  NONE)
                                                                                                                                                                                      |   (v139::v138) =>  NONE))))
                                                                                                             else  (if  (v199 = (Inl(Nehandle)))
                                                                                                                    then  (case  v198
                                                                                                                           of  []  =>  NONE
                                                                                                                           |   (v155::v154) =>  (case  v154
                                                                                                                                                 of  []  =>  (ptree_expr Nelogicor v155)
                                                                                                                                                 |   (v153::v152) =>  (case  v152
                                                                                                                                                                       of  []  =>  NONE
                                                                                                                                                                       |   (v151::v150) =>  (case  v150
                                                                                                                                                                                             of  []  =>  (if  (v153 = (Lf(Tok(Handlet))))
                                                                                                                                                                                                          then  (case  (ptree_expr Nelogicor v155)
                                                                                                                                                                                                                 of  NONE =>  NONE
                                                                                                                                                                                                                 |   (SOME(v147)) =>  (case  (ptree_pes v151)
                                                                                                                                                                                                                                       of  NONE =>  NONE
                                                                                                                                                                                                                                       |   (SOME(v146)) =>  (SOME(Handle(v147,v146)))))
                                                                                                                                                                                                          else  NONE)
                                                                                                                                                                                             |   (v149::v148) =>  NONE))))
                                                                                                                    else  (if  (v199 = (Inl(Ne)))
                                                                                                                           then  (case  v198
                                                                                                                                  of  []  =>  NONE
                                                                                                                                  |   (v177::v176) =>  (case  v176
                                                                                                                                                        of  []  =>  (ptree_expr Nehandle v177)
                                                                                                                                                        |   (v175::v174) =>  (case  v174
                                                                                                                                                                              of  []  =>  (if  (v177 = (Lf(Tok(Raiset))))
                                                                                                                                                                                           then  (case  (ptree_expr Ne v175)
                                                                                                                                                                                                  of  NONE =>  NONE
                                                                                                                                                                                                  |   (SOME(v156)) =>  (SOME(Raise(v156))))
                                                                                                                                                                                           else  NONE)
                                                                                                                                                                              |   (v173::v172) =>  (case  v172
                                                                                                                                                                                                    of  []  =>  NONE
                                                                                                                                                                                                    |   (v171::v170) =>  (case  v170
                                                                                                                                                                                                                          of  []  =>  (option_choice (if  ((v177 = (Lf(Tok(Fnt)))) andalso  (v173 = (Lf(Tok(Darrowt)))))
                                                                                                                                                                                                                                                      then  (case  (ptree_pattern Npattern v175)
                                                                                                                                                                                                                                                             of  NONE =>  NONE
                                                                                                                                                                                                                                                             |   (SOME(v158)) =>  (case  (ptree_expr Ne v171)
                                                                                                                                                                                                                                                                                   of  NONE =>  NONE
                                                                                                                                                                                                                                                                                   |   (SOME(v157)) =>  (SOME(mkfun v158 v157))))
                                                                                                                                                                                                                                                      else  NONE) (if  ((v177 = (Lf(Tok(Caset)))) andalso  (v173 = (Lf(Tok(Oft)))))
                                                                                                                                                                                                                                                                   then  (case  (ptree_expr Ne v175)
                                                                                                                                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                                                                                                                                          |   (SOME(v160)) =>  (case  (ptree_pes v171)
                                                                                                                                                                                                                                                                                                of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                |   (SOME(v159)) =>  (SOME(Mat(v160,v159)))))
                                                                                                                                                                                                                                                                   else  NONE))
                                                                                                                                                                                                                          |   (v169::v168) =>  (case  v168
                                                                                                                                                                                                                                                of  []  =>  NONE
                                                                                                                                                                                                                                                |   (v167::v166) =>  (case  v166
                                                                                                                                                                                                                                                                      of  []  =>  (if  (((v177 = (Lf(Tok(Ift)))) andalso  (v173 = (Lf(Tok(Thent))))) andalso  (v169 = (Lf(Tok(Elset)))))
                                                                                                                                                                                                                                                                                   then  (case  (ptree_expr Ne v175)
                                                                                                                                                                                                                                                                                          of  NONE =>  NONE
                                                                                                                                                                                                                                                                                          |   (SOME(v163)) =>  (case  (ptree_expr Ne v171)
                                                                                                                                                                                                                                                                                                                of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                |   (SOME(v162)) =>  (case  (ptree_expr Ne v167)
                                                                                                                                                                                                                                                                                                                                      of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                      |   (SOME(v161)) =>  (SOME(If(v163,v162,v161))))))
                                                                                                                                                                                                                                                                                   else  NONE)
                                                                                                                                                                                                                                                                      |   (v165::v164) =>  NONE)))))))
                                                                                                                           else  (if  (v199 = (Inl(Ne')))
                                                                                                                                  then  (case  v198
                                                                                                                                         of  []  =>  NONE
                                                                                                                                         |   (v197::v196) =>  (case  v196
                                                                                                                                                               of  []  =>  (ptree_expr Nelogicor v197)
                                                                                                                                                               |   (v195::v194) =>  (case  v194
                                                                                                                                                                                     of  []  =>  (if  (v197 = (Lf(Tok(Raiset))))
                                                                                                                                                                                                  then  (case  (ptree_expr Ne' v195)
                                                                                                                                                                                                         of  NONE =>  NONE
                                                                                                                                                                                                         |   (SOME(v178)) =>  (SOME(Raise(v178))))
                                                                                                                                                                                                  else  NONE)
                                                                                                                                                                                     |   (v193::v192) =>  (case  v192
                                                                                                                                                                                                           of  []  =>  NONE
                                                                                                                                                                                                           |   (v191::v190) =>  (case  v190
                                                                                                                                                                                                                                 of  []  =>  (if  ((v197 = (Lf(Tok(Fnt)))) andalso  (v193 = (Lf(Tok(Darrowt)))))
                                                                                                                                                                                                                                              then  (case  (ptree_v v195)
                                                                                                                                                                                                                                                     of  NONE =>  NONE
                                                                                                                                                                                                                                                     |   (SOME(v180)) =>  (case  (ptree_expr Ne' v191)
                                                                                                                                                                                                                                                                           of  NONE =>  NONE
                                                                                                                                                                                                                                                                           |   (SOME(v179)) =>  (SOME(Fun(v180,v179)))))
                                                                                                                                                                                                                                              else  NONE)
                                                                                                                                                                                                                                 |   (v189::v188) =>  (case  v188
                                                                                                                                                                                                                                                       of  []  =>  NONE
                                                                                                                                                                                                                                                       |   (v187::v186) =>  (case  v186
                                                                                                                                                                                                                                                                             of  []  =>  (if  (((v197 = (Lf(Tok(Ift)))) andalso  (v193 = (Lf(Tok(Thent))))) andalso  (v189 = (Lf(Tok(Elset)))))
                                                                                                                                                                                                                                                                                          then  (case  (ptree_expr Ne v195)
                                                                                                                                                                                                                                                                                                 of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                 |   (SOME(v183)) =>  (case  (ptree_expr Ne v191)
                                                                                                                                                                                                                                                                                                                       of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                       |   (SOME(v182)) =>  (case  (ptree_expr Ne' v187)
                                                                                                                                                                                                                                                                                                                                             of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                                             |   (SOME(v181)) =>  (SOME(If(v183,v182,v181))))))
                                                                                                                                                                                                                                                                                          else  NONE)
                                                                                                                                                                                                                                                                             |   (v185::v184) =>  NONE)))))))
                                                                                                                                  else  NONE)))))))))))))))
                         else  NONE)
and  ptree_exprlist v25 v26 =
  case  v26
  of  Lf(v1) =>  NONE
  |   Nd(v24,v23) =>  (if  (v24 = (Inl(Nelist1)))
                       then  (case  v23
                              of  []  =>  NONE
                              |   (v12::v11) =>  (case  v11
                                                  of  []  =>  (case  (ptree_expr Ne v12)
                                                               of  NONE =>  NONE
                                                               |   (SOME(v2)) =>  (SOME([v2])))
                                                  |   (v10::v9) =>  (case  v9
                                                                     of  []  =>  NONE
                                                                     |   (v8::v7) =>  (case  v7
                                                                                       of  []  =>  (if  (v10 = (Lf(Tok(Commat))))
                                                                                                    then  (case  (ptree_expr Ne v12)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v4)) =>  (case  (ptree_exprlist Nelist1 v8)
                                                                                                                               of  NONE =>  NONE
                                                                                                                               |   (SOME(v3)) =>  (SOME(v4::v3))))
                                                                                                    else  NONE)
                                                                                       |   (v6::v5) =>  NONE))))
                       else  (if  (v24 = (Inl(Nelist2)))
                              then  (case  v23
                                     of  []  =>  NONE
                                     |   (v22::v21) =>  (case  v21
                                                         of  []  =>  NONE
                                                         |   (v20::v19) =>  (case  v19
                                                                             of  []  =>  NONE
                                                                             |   (v18::v17) =>  (case  v17
                                                                                                 of  []  =>  (if  (v20 = (Lf(Tok(Commat))))
                                                                                                              then  (case  (ptree_expr Ne v22)
                                                                                                                     of  NONE =>  NONE
                                                                                                                     |   (SOME(v14)) =>  (case  (ptree_exprlist Nelist1 v18)
                                                                                                                                          of  NONE =>  NONE
                                                                                                                                          |   (SOME(v13)) =>  (SOME(v14::v13))))
                                                                                                              else  NONE)
                                                                                                 |   (v16::v15) =>  NONE))))
                              else  NONE))
and  ptree_andfdecls v15 =
  case  v15
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  (v14 = (Inl(Nandfdecls)))
                       then  (case  v13
                              of  []  =>  NONE
                              |   (v12::v11) =>  (case  v11
                                                  of  []  =>  (case  (ptree_fdecl v12)
                                                               of  NONE =>  NONE
                                                               |   (SOME(v2)) =>  (SOME([v2])))
                                                  |   (v10::v9) =>  (case  v9
                                                                     of  []  =>  NONE
                                                                     |   (v8::v7) =>  (case  v7
                                                                                       of  []  =>  (if  (v10 = (Lf(Tok(Andt))))
                                                                                                    then  (case  (ptree_andfdecls v12)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v4)) =>  (case  (ptree_fdecl v8)
                                                                                                                               of  NONE =>  NONE
                                                                                                                               |   (SOME(v3)) =>  (SOME(append v4 [v3]))))
                                                                                                    else  NONE)
                                                                                       |   (v6::v5) =>  NONE))))
                       else  NONE)
and  ptree_fdecl v18 =
  case  v18
  of  Lf(v1) =>  NONE
  |   Nd(v17,v16) =>  (if  (v17 = (Inl(Nfdecl)))
                       then  (case  v16
                              of  []  =>  NONE
                              |   (v15::v14) =>  (case  v14
                                                  of  []  =>  NONE
                                                  |   (v13::v12) =>  (case  v12
                                                                      of  []  =>  NONE
                                                                      |   (v11::v10) =>  (case  v10
                                                                                          of  []  =>  NONE
                                                                                          |   (v9::v8) =>  (case  v8
                                                                                                            of  []  =>  (if  (v11 = (Lf(Tok(Equalst))))
                                                                                                                         then  (case  (ptree_v v15)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v5)) =>  (case  (ptree_pbaselist1 v13)
                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                    |   (SOME(v4)) =>  (case  (ohd v4)
                                                                                                                                                                        of  NONE =>  NONE
                                                                                                                                                                        |   (SOME(v3)) =>  (case  (ptree_expr Ne v9)
                                                                                                                                                                                            of  NONE =>  NONE
                                                                                                                                                                                            |   (SOME(v2)) =>  (let val  x =
                                                                                                                                                                                                                  (v5,depat v3 (foldr mkfun v2 (safetl v4)))
                                                                                                                                                                                                                in
                                                                                                                                                                                                                  SOME(x)
                                                                                                                                                                                                                end)))))
                                                                                                                         else  NONE)
                                                                                                            |   (v7::v6) =>  NONE)))))
                       else  NONE)
and  ptree_letdecs v12 =
  case  v12
  of  Lf(v1) =>  NONE
  |   Nd(v11,v10) =>  (if  ((v11 = (Inl(Nletdecs))) = (0 < 0))
                       then  NONE
                        else  (case  v10
                               of  []  =>  (SOME([] ))
                               |   (v9::v8) =>  (case  v8
                                                 of  []  =>  NONE
                                                 |   (v7::v6) =>  (case  v6
                                                                   of  []  =>  (if  (v9 = (Lf(Tok(Semicolont))))
                                                                                then  (ptree_letdecs v7)
                                                                                else  (case  (ptree_letdec v9)
                                                                                       of  NONE =>  NONE
                                                                                       |   (SOME(v3)) =>  (case  (ptree_letdecs v7)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v2)) =>  (SOME(v3::v2)))))
                                                                   |   (v5::v4) =>  NONE))))
and  ptree_letdec v17 =
  case  v17
  of  Lf(v1) =>  NONE
  |   Nd(v16,v15) =>  (if  ((v16 = (Inl(Nletdec))) = (0 < 0))
                       then  NONE
                        else  (case  v15
                               of  []  =>  NONE
                               |   (v14::v13) =>  (case  v13
                                                   of  []  =>  NONE
                                                   |   (v12::v11) =>  (case  v11
                                                                       of  []  =>  (if  (v14 = (Lf(Tok(Funt))))
                                                                                    then  (case  (ptree_andfdecls v12)
                                                                                           of  NONE =>  NONE
                                                                                           |   (SOME(v2)) =>  (SOME(Inr(v2))))
                                                                                    else  NONE)
                                                                       |   (v10::v9) =>  (case  v9
                                                                                          of  []  =>  NONE
                                                                                          |   (v8::v7) =>  (case  v7
                                                                                                            of  []  =>  (if  ((v14 = (Lf(Tok(Valt)))) andalso  (v10 = (Lf(Tok(Equalst)))))
                                                                                                                         then  (case  (ptree_v v12)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v4)) =>  (case  (ptree_expr Ne v8)
                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                    |   (SOME(v3)) =>  (SOME(let val  x =
                                                                                                                                                                               (v4,v3)
                                                                                                                                                                             in
                                                                                                                                                                               Inl(x)
                                                                                                                                                                             end))))
                                                                                                                         else  NONE)
                                                                                                            |   (v6::v5) =>  NONE))))))
and  ptree_pes v15 =
  case  v15
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  ((v14 = (Inl(Npes))) = (0 < 0))
                       then  NONE
                        else  (case  v13
                               of  []  =>  NONE
                               |   (v12::v11) =>  (case  v11
                                                   of  []  =>  (case  (ptree_pe v12)
                                                                of  NONE =>  NONE
                                                                |   (SOME(v2)) =>  (SOME([v2])))
                                                   |   (v10::v9) =>  (case  v9
                                                                      of  []  =>  NONE
                                                                      |   (v8::v7) =>  (case  v7
                                                                                        of  []  =>  (if  (v10 = (Lf(Tok(Bart))))
                                                                                                     then  (case  (ptree_pes v8)
                                                                                                            of  NONE =>  NONE
                                                                                                            |   (SOME(v4)) =>  (case  (ptree_pe' v12)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v3)) =>  (SOME(v3::v4))))
                                                                                                     else  NONE)
                                                                                        |   (v6::v5) =>  NONE)))))
and  ptree_pe v14 =
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  ((v13 = (Inl(Npe))) = (0 < 0))
                       then  NONE
                        else  (case  v12
                               of  []  =>  NONE
                               |   (v11::v10) =>  (case  v10
                                                   of  []  =>  NONE
                                                   |   (v9::v8) =>  (case  v8
                                                                     of  []  =>  NONE
                                                                     |   (v7::v6) =>  (case  v6
                                                                                       of  []  =>  (if  (v9 = (Lf(Tok(Darrowt))))
                                                                                                    then  (case  (ptree_pattern Npattern v11)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v3)) =>  (case  (ptree_expr Ne v7)
                                                                                                                               of  NONE =>  NONE
                                                                                                                               |   (SOME(v2)) =>  (let val  x =
                                                                                                                                                     (v3,v2)
                                                                                                                                                   in
                                                                                                                                                     SOME(x)
                                                                                                                                                   end)))
                                                                                                    else  NONE)
                                                                                       |   (v5::v4) =>  NONE)))))
and  ptree_pe' v14 =
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  ((v13 = (Inl(Npe'))) = (0 < 0))
                       then  NONE
                        else  (case  v12
                               of  []  =>  NONE
                               |   (v11::v10) =>  (case  v10
                                                   of  []  =>  NONE
                                                   |   (v9::v8) =>  (case  v8
                                                                     of  []  =>  NONE
                                                                     |   (v7::v6) =>  (case  v6
                                                                                       of  []  =>  (if  (v9 = (Lf(Tok(Darrowt))))
                                                                                                    then  (case  (ptree_pattern Npattern v11)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v3)) =>  (case  (ptree_expr Ne' v7)
                                                                                                                               of  NONE =>  NONE
                                                                                                                               |   (SOME(v2)) =>  (let val  x =
                                                                                                                                                     (v3,v2)
                                                                                                                                                   in
                                                                                                                                                     SOME(x)
                                                                                                                                                   end)))
                                                                                                    else  NONE)
                                                                                       |   (v5::v4) =>  NONE)))))
and  ptree_eseq v15 =
  case  v15
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  ((v14 = (Inl(Neseq))) = (0 < 0))
                       then  NONE
                        else  (case  v13
                               of  []  =>  NONE
                               |   (v12::v11) =>  (case  v11
                                                   of  []  =>  (case  (ptree_expr Ne v12)
                                                                of  NONE =>  NONE
                                                                |   (SOME(v2)) =>  (SOME([v2])))
                                                   |   (v10::v9) =>  (case  v9
                                                                      of  []  =>  NONE
                                                                      |   (v8::v7) =>  (case  v7
                                                                                        of  []  =>  (if  (v10 = (Lf(Tok(Semicolont))))
                                                                                                     then  (case  (ptree_expr Ne v12)
                                                                                                            of  NONE =>  NONE
                                                                                                            |   (SOME(v4)) =>  (case  (ptree_eseq v8)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v3)) =>  (SOME(v4::v3))))
                                                                                                     else  NONE)
                                                                                        |   (v6::v5) =>  NONE)))));

datatype ast_dec =  Dexn of  char list *  ast_t list
                 |  Dtabbrev of  char list list *  char list *  ast_t
                 |  Dtype of  (char list list *  (char list *  (char list *  ast_t list) list)) list
                 |  Dletrec of  (char list *  (char list *  ast_exp)) list
                 |  Dlet of  ast_pat *  ast_exp;

datatype ast_spec =  Sexn of  char list *  ast_t list
                  |  Stype_opq of  char list list *  char list
                  |  Stabbrev of  char list list *  char list *  ast_t
                  |  Stype of  (char list list *  (char list *  (char list *  ast_t list) list)) list
                  |  Sval of  char list *  ast_t;

datatype ast_top =  Tdec of  ast_dec
                 |  Tmod of  char list *  ast_spec list option *  ast_dec list;

fun  ptree_structname v10 = 
  case  v10
  of  Lf(v1) =>  NONE
  |   Nd(v9,v8) =>  (if  ((v9 = (Inl(Nstructname))) = (0 < 0))
                     then  NONE
                      else  (case  v8
                             of  []  =>  NONE
                             |   (v7::v6) =>  (case  v6
                                               of  []  =>  (case  (case  (destlf v7)
                                                                   of  NONE =>  NONE
                                                                   |   (SOME(v2)) =>  (desttok v2))
                                                            of  NONE =>  NONE
                                                            |   (SOME(v3)) =>  (destalphat v3))
                                               |   (v5::v4) =>  NONE)));

fun  ptree_linfix v18 v16 v15 v17 =
  case  v17
  of  Lf(v1) =>  NONE
  |   Nd(v14,v13) =>  (if  (v14 = (Inl(v18)))
                       then  (case  v13
                              of  []  =>  NONE
                              |   (v12::v11) =>  (case  v11
                                                  of  []  =>  (case  (v15 v12)
                                                               of  NONE =>  NONE
                                                               |   (SOME(v2)) =>  (SOME([v2])))
                                                  |   (v10::v9) =>  (case  v9
                                                                     of  []  =>  NONE
                                                                     |   (v8::v7) =>  (case  v7
                                                                                       of  []  =>  (if  (v10 = (Lf(Tok(v16))))
                                                                                                    then  (case  (ptree_linfix v18 v16 v15 v12)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v4)) =>  (case  (v15 v8)
                                                                                                                               of  NONE =>  NONE
                                                                                                                               |   (SOME(v3)) =>  (SOME(append v4 [v3]))))
                                                                                                    else  NONE)
                                                                                       |   (v6::v5) =>  NONE))))
                       else  NONE);

fun  ptree_tyvarn v8 = 
  case  v8
  of  Lf(v1) =>  NONE
  |   Nd(v7,v6) =>  (if  ((v7 = (Inl(Ntyvarn))) = (0 < 0))
                     then  NONE
                      else  (case  v6
                             of  []  =>  NONE
                             |   (v5::v4) =>  (case  v4
                                               of  []  =>  (desttyvarpt v5)
                                               |   (v3::v2) =>  NONE)));

fun  ptree_typename v19 = 
  case  v19
  of  Lf(v1) =>  NONE
  |   Nd(v18,v17) =>  (if  (v18 = (Inl(Ntypename)))
                       then  (case  v17
                              of  []  =>  NONE
                              |   (v16::v15) =>  (case  v15
                                                  of  []  =>  (case  (ptree_uqtyop v16)
                                                               of  NONE =>  NONE
                                                               |   (SOME(v2)) =>  (let val  x =
                                                                                     ([] ,v2)
                                                                                   in
                                                                                     SOME(x)
                                                                                   end))
                                                  |   (v14::v13) =>  (case  v13
                                                                      of  []  =>  (case  (desttyvarpt v16)
                                                                                   of  NONE =>  NONE
                                                                                   |   (SOME(v4)) =>  (case  (ptree_uqtyop v14)
                                                                                                       of  NONE =>  NONE
                                                                                                       |   (SOME(v3)) =>  (let val  x =
                                                                                                                             ([v4],v3)
                                                                                                                           in
                                                                                                                             SOME(x)
                                                                                                                           end)))
                                                                      |   (v12::v11) =>  (case  v11
                                                                                          of  []  =>  NONE
                                                                                          |   (v10::v9) =>  (case  v9
                                                                                                             of  []  =>  (if  ((v16 = (Lf(Tok(Lpart)))) andalso  (v12 = (Lf(Tok(Rpart)))))
                                                                                                                          then  (case  (ptree_linfix Ntyvarlist Commat ptree_tyvarn v14)
                                                                                                                                 of  NONE =>  NONE
                                                                                                                                 |   (SOME(v6)) =>  (case  (ptree_uqtyop v10)
                                                                                                                                                     of  NONE =>  NONE
                                                                                                                                                     |   (SOME(v5)) =>  (let val  x =
                                                                                                                                                                           (v6,v5)
                                                                                                                                                                         in
                                                                                                                                                                           SOME(x)
                                                                                                                                                                         end)))
                                                                                                                          else  NONE)
                                                                                                             |   (v8::v7) =>  NONE)))))
                       else  NONE);

fun  detuplify v6 = 
  case  v6
  of  Tvar(v1) =>  [Tvar(v1)]
  |   Tvar_db(v2) =>  [Tvar_db(v2)]
  |   Tapp(v5,v4) =>  (case  v4
                       of  (Tc_name(v3)) =>  [Tapp(v5,Tc_name(v3))]
                       |   Tc_int =>  [Tapp(v5,Tc_int)]
                       |   Tc_char =>  [Tapp(v5,Tc_char)]
                       |   Tc_string =>  [Tapp(v5,Tc_string)]
                       |   Tc_ref =>  [Tapp(v5,Tc_ref)]
                       |   Tc_word8 =>  [Tapp(v5,Tc_word8)]
                       |   Tc_word64 =>  [Tapp(v5,Tc_word64)]
                       |   Tc_word8array =>  [Tapp(v5,Tc_word8array)]
                       |   Tc_fn =>  [Tapp(v5,Tc_fn)]
                       |   Tc_tup =>  v5
                       |   Tc_exn =>  [Tapp(v5,Tc_exn)]
                       |   Tc_vector =>  [Tapp(v5,Tc_vector)]
                       |   Tc_array =>  [Tapp(v5,Tc_array)]);

fun  ptree_dconstructor v14 = 
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  (v13 = (Inl(Ndconstructor)))
                       then  (case  v12
                              of  []  =>  NONE
                              |   (v11::v10) =>  (case  (ptree_uqconstructorname v11)
                                                  of  NONE =>  NONE
                                                  |   (SOME(v9)) =>  (case  (case  v10
                                                                             of  []  =>  (SOME([] ))
                                                                             |   (v7::v6) =>  (case  v6
                                                                                               of  []  =>  NONE
                                                                                               |   (v5::v4) =>  (case  v4
                                                                                                                 of  []  =>  (if  (v7 = (Lf(Tok(Oft))))
                                                                                                                              then  (option_map detuplify (ptree_type Ntype v5))
                                                                                                                              else  NONE)
                                                                                                                 |   (v3::v2) =>  NONE)))
                                                                      of  NONE =>  NONE
                                                                      |   (SOME(v8)) =>  (let val  x =
                                                                                            (v9,v8)
                                                                                          in
                                                                                            SOME(x)
                                                                                          end))))
                       else  NONE);

fun  ptree_dtypedecl v14 = 
  case  v14
  of  Lf(v1) =>  NONE
  |   Nd(v13,v12) =>  (if  (v13 = (Inl(Ndtypedecl)))
                       then  (case  v12
                              of  []  =>  NONE
                              |   (v11::v10) =>  (case  v10
                                                  of  []  =>  NONE
                                                  |   (v9::v8) =>  (case  v8
                                                                    of  []  =>  NONE
                                                                    |   (v7::v6) =>  (case  v6
                                                                                      of  []  =>  (if  (v9 = (Lf(Tok(Equalst))))
                                                                                                   then  (case  (ptree_typename v11)
                                                                                                          of  NONE =>  NONE
                                                                                                          |   (SOME(v3)) =>  (case  (ptree_linfix Ndtypecons Bart ptree_dconstructor v7)
                                                                                                                              of  NONE =>  NONE
                                                                                                                              |   (SOME(v2)) =>  (let val  x =
                                                                                                                                                    (fst v3,(snd v3,v2))
                                                                                                                                                  in
                                                                                                                                                    SOME(x)
                                                                                                                                                  end)))
                                                                                                   else  NONE)
                                                                                      |   (v5::v4) =>  NONE))))
                       else  NONE);

fun  ptree_typedec v10 = 
  case  v10
  of  Lf(v1) =>  NONE
  |   Nd(v9,v8) =>  (if  (v9 = (Inl(Ntypedec)))
                     then  (case  v8
                            of  []  =>  NONE
                            |   (v7::v6) =>  (case  v6
                                              of  []  =>  NONE
                                              |   (v5::v4) =>  (case  v4
                                                                of  []  =>  (if  (v7 = (Lf(Tok(Datatypet))))
                                                                             then  (ptree_linfix Ndtypedecls Andt ptree_dtypedecl v5)
                                                                             else  NONE)
                                                                |   (v3::v2) =>  NONE)))
                     else  NONE);

fun  ptree_opttypeqn v11 = 
  case  v11
  of  Lf(v1) =>  NONE
  |   Nd(v10,v9) =>  (if  ((v10 = (Inl(Nopttypeqn))) = (0 < 0))
                      then  NONE
                       else  (case  v9
                              of  []  =>  (SOME(NONE))
                              |   (v8::v7) =>  (case  v7
                                                of  []  =>  NONE
                                                |   (v6::v5) =>  (case  v5
                                                                  of  []  =>  (if  (v8 = (Lf(Tok(Equalst))))
                                                                               then  (case  (ptree_type Ntype v6)
                                                                                      of  NONE =>  NONE
                                                                                      |   (SOME(v2)) =>  (SOME(SOME(v2))))
                                                                               else  NONE)
                                                                  |   (v4::v3) =>  NONE))));

fun  ptree_specline v25 = 
  case  v25
  of  Lf(v1) =>  NONE
  |   Nd(v24,v23) =>  (if  ((v24 = (Inl(Nspecline))) = (0 < 0))
                       then  NONE
                        else  (case  v23
                               of  []  =>  NONE
                               |   (v22::v21) =>  (case  v21
                                                   of  []  =>  (case  (ptree_typedec v22)
                                                                of  NONE =>  NONE
                                                                |   (SOME(v2)) =>  (SOME(Stype(v2))))
                                                   |   (v20::v19) =>  (case  v19
                                                                       of  []  =>  (if  (v22 = (Lf(Tok(Exceptiont))))
                                                                                    then  (case  (ptree_dconstructor v20)
                                                                                           of  NONE =>  NONE
                                                                                           |   (SOME(v5)) =>  (case  v5
                                                                                                               of  (v4,v3) =>  (SOME(Sexn(v4,v3)))))
                                                                                    else  NONE)
                                                                       |   (v18::v17) =>  (case  v17
                                                                                           of  []  =>  (if  (v22 = (Lf(Tok(Typet))))
                                                                                                        then  (case  (ptree_typename v20)
                                                                                                               of  NONE =>  NONE
                                                                                                               |   (SOME(v10)) =>  (case  v10
                                                                                                                                    of  (v9,v8) =>  (case  (ptree_opttypeqn v18)
                                                                                                                                                     of  NONE =>  NONE
                                                                                                                                                     |   (SOME(v7)) =>  (SOME(case  v7
                                                                                                                                                                              of  NONE =>  (Stype_opq(v9,v8))
                                                                                                                                                                              |   SOME(v6) =>  (Stabbrev(v9,v8,v6)))))))
                                                                                                        else  NONE)
                                                                                           |   (v16::v15) =>  (case  v15
                                                                                                               of  []  =>  (if  ((v22 = (Lf(Tok(Valt)))) andalso  (v18 = (Lf(Tok(Colont)))))
                                                                                                                            then  (case  (ptree_v v20)
                                                                                                                                   of  NONE =>  NONE
                                                                                                                                   |   (SOME(v12)) =>  (case  (ptree_type Ntype v16)
                                                                                                                                                        of  NONE =>  NONE
                                                                                                                                                        |   (SOME(v11)) =>  (SOME(Sval(v12,v11)))))
                                                                                                                            else  NONE)
                                                                                                               |   (v14::v13) =>  NONE))))));

fun  ptree_speclinelist v12 =
  case  v12
  of  Lf(v1) =>  NONE
  |   Nd(v11,v10) =>  (if  ((v11 = (Inl(Nspeclinelist))) = (0 < 0))
                       then  NONE
                        else  (case  v10
                               of  []  =>  (SOME([] ))
                               |   (v9::v8) =>  (case  v8
                                                 of  []  =>  NONE
                                                 |   (v7::v6) =>  (case  v6
                                                                   of  []  =>  (if  (v9 = (Lf(Tok(Semicolont))))
                                                                                then  (ptree_speclinelist v7)
                                                                                else  (case  (ptree_specline v9)
                                                                                       of  NONE =>  NONE
                                                                                       |   (SOME(v3)) =>  (case  (ptree_speclinelist v7)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v2)) =>  (SOME(v3::v2)))))
                                                                   |   (v5::v4) =>  NONE))));

fun  ptree_signaturevalue v12 = 
  case  v12
  of  Lf(v1) =>  NONE
  |   Nd(v11,v10) =>  (if  ((v11 = (Inl(Nsignaturevalue))) = (0 < 0))
                       then  NONE
                        else  (case  v10
                               of  []  =>  NONE
                               |   (v9::v8) =>  (case  v8
                                                 of  []  =>  NONE
                                                 |   (v7::v6) =>  (case  v6
                                                                   of  []  =>  NONE
                                                                   |   (v5::v4) =>  (case  v4
                                                                                     of  []  =>  (if  ((v9 = (Lf(Tok(Sigt)))) andalso  (v5 = (Lf(Tok(Endt)))))
                                                                                                  then  (ptree_speclinelist v7)
                                                                                                  else  NONE)
                                                                                     |   (v3::v2) =>  NONE)))));

fun  ptree_typeabbrevdec v18 = 
  case  v18
  of  Lf(v1) =>  NONE
  |   Nd(v17,v16) =>  (if  (v17 = (Inl(Ntypeabbrevdec)))
                       then  (case  v16
                              of  []  =>  NONE
                              |   (v15::v14) =>  (case  v14
                                                  of  []  =>  NONE
                                                  |   (v13::v12) =>  (case  v12
                                                                      of  []  =>  NONE
                                                                      |   (v11::v10) =>  (case  v10
                                                                                          of  []  =>  NONE
                                                                                          |   (v9::v8) =>  (case  v8
                                                                                                            of  []  =>  (if  ((v15 = (Lf(Tok(Typet)))) andalso  (v11 = (Lf(Tok(Equalst)))))
                                                                                                                         then  (case  (ptree_typename v13)
                                                                                                                                of  NONE =>  NONE
                                                                                                                                |   (SOME(v5)) =>  (case  v5
                                                                                                                                                    of  (v4,v3) =>  (case  (ptree_type Ntype v9)
                                                                                                                                                                     of  NONE =>  NONE
                                                                                                                                                                     |   (SOME(v2)) =>  (SOME(Dtabbrev(v4,v3,v2))))))
                                                                                                                         else  NONE)
                                                                                                            |   (v7::v6) =>  NONE)))))
                       else  NONE);

fun  ptree_decl v21 = 
  case  v21
  of  Lf(v1) =>  NONE
  |   Nd(v20,v19) =>  (if  ((v20 = (Inl(Ndecl))) = (0 < 0))
                       then  NONE
                        else  (case  v19
                               of  []  =>  NONE
                               |   (v18::v17) =>  (case  v17
                                                   of  []  =>  (option_choice (case  (ptree_typedec v18)
                                                                               of  NONE =>  NONE
                                                                               |   (SOME(v2)) =>  (SOME(Dtype(v2)))) (ptree_typeabbrevdec v18))
                                                   |   (v16::v15) =>  (case  v15
                                                                       of  []  =>  (option_choice (if  (v18 = (Lf(Tok(Funt))))
                                                                                                   then  (case  (ptree_andfdecls v16)
                                                                                                          of  NONE =>  NONE
                                                                                                          |   (SOME(v3)) =>  (SOME(Dletrec(v3))))
                                                                                                   else  NONE) (if  (v18 = (Lf(Tok(Exceptiont))))
                                                                                                                then  (case  (ptree_dconstructor v16)
                                                                                                                       of  NONE =>  NONE
                                                                                                                       |   (SOME(v6)) =>  (case  v6
                                                                                                                                           of  (v5,v4) =>  (SOME(Dexn(v5,v4)))))
                                                                                                                else  NONE))
                                                                       |   (v14::v13) =>  (case  v13
                                                                                           of  []  =>  NONE
                                                                                           |   (v12::v11) =>  (case  v11
                                                                                                               of  []  =>  (if  ((v18 = (Lf(Tok(Valt)))) andalso  (v14 = (Lf(Tok(Equalst)))))
                                                                                                                            then  (case  (ptree_pattern Npattern v16)
                                                                                                                                   of  NONE =>  NONE
                                                                                                                                   |   (SOME(v8)) =>  (case  (ptree_expr Ne v12)
                                                                                                                                                       of  NONE =>  NONE
                                                                                                                                                       |   (SOME(v7)) =>  (SOME(Dlet(v8,v7)))))
                                                                                                                            else  NONE)
                                                                                                               |   (v10::v9) =>  NONE))))));

fun  ptree_decls v12 =
  case  v12
  of  Lf(v1) =>  NONE
  |   Nd(v11,v10) =>  (if  ((v11 = (Inl(Ndecls))) = (0 < 0))
                       then  NONE
                        else  (case  v10
                               of  []  =>  (SOME([] ))
                               |   (v9::v8) =>  (case  v8
                                                 of  []  =>  NONE
                                                 |   (v7::v6) =>  (case  v6
                                                                   of  []  =>  (if  (v9 = (Lf(Tok(Semicolont))))
                                                                                then  (ptree_decls v7)
                                                                                else  (case  (ptree_decl v9)
                                                                                       of  NONE =>  NONE
                                                                                       |   (SOME(v3)) =>  (case  (ptree_decls v7)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v2)) =>  (SOME(v3::v2)))))
                                                                   |   (v5::v4) =>  NONE))));

fun  ptree_structure v33 = 
  case  v33
  of  Lf(v1) =>  NONE
  |   Nd(v32,v31) =>  (if  ((v32 = (Inl(Nstructure))) = (0 < 0))
                       then  NONE
                        else  (case  v31
                               of  []  =>  NONE
                               |   (v30::v29) =>  (case  v29
                                                   of  []  =>  NONE
                                                   |   (v28::v27) =>  (case  v27
                                                                       of  []  =>  NONE
                                                                       |   (v26::v25) =>  (case  v25
                                                                                           of  []  =>  NONE
                                                                                           |   (v24::v23) =>  (case  v23
                                                                                                               of  []  =>  NONE
                                                                                                               |   (v22::v21) =>  (case  v21
                                                                                                                                   of  []  =>  NONE
                                                                                                                                   |   (v20::v19) =>  (case  v19
                                                                                                                                                       of  []  =>  NONE
                                                                                                                                                       |   (v18::v17) =>  (case  v17
                                                                                                                                                                           of  []  =>  (if  ((((v22 = (Lf(Tok(Structt)))) andalso  (v30 = (Lf(Tok(Structuret))))) andalso  (v24 = (Lf(Tok(Equalst))))) andalso  (v18 = (Lf(Tok(Endt)))))
                                                                                                                                                                                        then  (case  (ptree_structname v28)
                                                                                                                                                                                               of  NONE =>  NONE
                                                                                                                                                                                               |   (SOME(v14)) =>  (case  (case  v26
                                                                                                                                                                                                                           of  (Lf(v2)) =>  NONE
                                                                                                                                                                                                                           |   (Nd(v11,v10)) =>  (if  ((v11 = (Inl(Noptionalsignatureascription))) = (0 < 0))
                                                                                                                                                                                                                                                  then  NONE
                                                                                                                                                                                                                                                   else  (case  v10
                                                                                                                                                                                                                                                          of  []  =>  (SOME(NONE))
                                                                                                                                                                                                                                                          |   (v9::v8) =>  (case  v8
                                                                                                                                                                                                                                                                            of  []  =>  NONE
                                                                                                                                                                                                                                                                            |   (v7::v6) =>  (case  v6
                                                                                                                                                                                                                                                                                              of  []  =>  (if  (v9 = (Lf(Tok(Sealt))))
                                                                                                                                                                                                                                                                                                           then  (case  (ptree_signaturevalue v7)
                                                                                                                                                                                                                                                                                                                  of  NONE =>  NONE
                                                                                                                                                                                                                                                                                                                  |   (SOME(v3)) =>  (SOME(SOME(v3))))
                                                                                                                                                                                                                                                                                                           else  NONE)
                                                                                                                                                                                                                                                                                              |   (v5::v4) =>  NONE)))))
                                                                                                                                                                                                                    of  NONE =>  NONE
                                                                                                                                                                                                                    |   (SOME(v13)) =>  (case  (ptree_decls v20)
                                                                                                                                                                                                                                         of  NONE =>  NONE
                                                                                                                                                                                                                                         |   (SOME(v12)) =>  (SOME(Tmod(v14,v13,v12))))))
                                                                                                                                                                                        else  NONE)
                                                                                                                                                                           |   (v16::v15) =>  NONE)))))))));

fun  ptree_topleveldec v9 = 
  case  v9
  of  Lf(v1) =>  NONE
  |   Nd(v8,v7) =>  (if  ((v8 = (Inl(Ntopleveldec))) = (0 < 0))
                     then  NONE
                      else  (case  v7
                             of  []  =>  NONE
                             |   (v6::v5) =>  (case  v5
                                               of  []  =>  (option_choice (ptree_structure v6) (option_map (fn  v2 =>
                                                                                                             (Tdec(v2))) (ptree_decl v6)))
                                               |   (v4::v3) =>  NONE)));

fun  ptree_topleveldecs v16 =
  case  v16
  of  Lf(v1) =>  NONE
  |   Nd(v15,v14) =>  (if  ((v15 = (Inl(Ntopleveldecs))) = (0 < 0))
                       then  NONE
                        else  (case  v14
                               of  []  =>  (SOME([] ))
                               |   (v13::v12) =>  (case  v12
                                                   of  []  =>  NONE
                                                   |   (v11::v10) =>  (case  v10
                                                                       of  []  =>  (if  (v13 = (Lf(Tok(Semicolont))))
                                                                                    then  (ptree_topleveldecs v11)
                                                                                    else  (case  (ptree_topleveldec v13)
                                                                                           of  NONE =>  NONE
                                                                                           |   (SOME(v3)) =>  (case  (ptree_nonetopleveldecs v11)
                                                                                                               of  NONE =>  NONE
                                                                                                               |   (SOME(v2)) =>  (SOME(v3::v2)))))
                                                                       |   (v9::v8) =>  (case  v8
                                                                                         of  []  =>  (if  (v11 = (Lf(Tok(Semicolont))))
                                                                                                      then  (case  (ptree_expr Ne v13)
                                                                                                             of  NONE =>  NONE
                                                                                                             |   (SOME(v5)) =>  (case  (ptree_topleveldecs v9)
                                                                                                                                 of  NONE =>  NONE
                                                                                                                                 |   (SOME(v4)) =>  (SOME(Tdec(Dlet(Pvar([#"i",#"t"]),v5))::v4))))
                                                                                                      else  NONE)
                                                                                         |   (v7::v6) =>  NONE)))))
and  ptree_nonetopleveldecs v12 =
  case  v12
  of  Lf(v1) =>  NONE
  |   Nd(v11,v10) =>  (if  ((v11 = (Inl(Nnonetopleveldecs))) = (0 < 0))
                       then  NONE
                        else  (case  v10
                               of  []  =>  (SOME([] ))
                               |   (v9::v8) =>  (case  v8
                                                 of  []  =>  NONE
                                                 |   (v7::v6) =>  (case  v6
                                                                   of  []  =>  (if  (v9 = (Lf(Tok(Semicolont))))
                                                                                then  (ptree_topleveldecs v7)
                                                                                else  (case  (ptree_topleveldec v9)
                                                                                       of  NONE =>  NONE
                                                                                       |   (SOME(v3)) =>  (case  (ptree_nonetopleveldecs v7)
                                                                                                           of  NONE =>  NONE
                                                                                                           |   (SOME(v2)) =>  (SOME(v3::v2)))))
                                                                   |   (v5::v4) =>  NONE))));

fun  destresult v10 = 
  case  v10
  of  Ev(v5,v4,v3,v2,v1) =>  NONE
  |   Ap(v8,v7,v6) =>  NONE
  |   Result(v9) =>  v9
  |   Looped =>  NONE;

fun  parse_prog v6 = 
  option_bind (destresult (peg_exec cmlpeg (pnt Ntopleveldecs) v6 [] Done Failed)) (fn  v5 =>
                                                                                     (case  v5
                                                                                      of  (v4,v3) =>  (option_bind (ohd v3) (fn  v2 =>
                                                                                                                              (option_bind (ptree_topleveldecs v2) (fn  v1 =>
                                                                                                                                                                     (if  ((v4 = [] ) = (0 < 0))
                                                                                                                                                                      then  NONE
                                                                                                                                                                       else  (SOME(v1)))))))));
end

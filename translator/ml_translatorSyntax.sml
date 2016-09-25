structure ml_translatorSyntax :> ml_translatorSyntax =
struct

open HolKernel boolLib ml_translatorTheory semanticPrimitivesSyntax;

val ERR = Feedback.mk_HOL_ERR "ml_translatorSyntax";

val monop = HolKernel.syntax_fns1 "ml_translator"

val (EqualityType,mk_EqualityType,dest_EqualityType,is_EqualityType) = monop "EqualityType";
val (CONTAINER,mk_CONTAINER,dest_CONTAINER,is_CONTAINER) = monop "CONTAINER";
val (PRECONDITION,mk_PRECONDITION,dest_PRECONDITION,is_PRECONDITION) = monop "PRECONDITION";

val BOOL        = prim_mk_const{Thy="ml_translator",Name="BOOL"}
val WORD       = prim_mk_const{Thy="ml_translator",Name="WORD"}
val NUM         = prim_mk_const{Thy="ml_translator",Name="NUM"}
val INT         = prim_mk_const{Thy="ml_translator",Name="INT"}
val CHAR        = prim_mk_const{Thy="ml_translator",Name="CHAR"}
val STRING_TYPE = prim_mk_const{Thy="ml_translator",Name="STRING_TYPE"}
val UNIT_TYPE   = prim_mk_const{Thy="ml_translator",Name="UNIT_TYPE"}

val (LIST_TYPE,mk_LIST_TYPE,dest_LIST_TYPE,is_LIST_TYPE) = HolKernel.syntax_fns3 "ml_translator" "LIST_TYPE";

val TRUE  = prim_mk_const{Thy="ml_translator",Name="TRUE"}
val FALSE = prim_mk_const{Thy="ml_translator",Name="FALSE"}

val binop = HolKernel.syntax_fns2 "ml_translator"

val (TAG,mk_TAG,dest_TAG,is_TAG) = binop "TAG";
val (PreImp,mk_PreImp,dest_PreImp,is_PreImp) = binop "PreImp";
val (lookup_cons,mk_lookup_cons,dest_lookup_cons,is_lookup_cons) = binop "lookup_cons";

fun mk_vector_type ty = mk_thy_type{Thy="ml_translator",Tyop="vector",Args=[ty]};

fun dest_vector_type ty =
  case total dest_thy_type ty
  of SOME {Thy="ml_translator", Tyop="vector", Args=[ty]} => ty
   | _ => raise ERR "dest_vector_type" ""

val is_vector_type = can dest_vector_type;

val ffi = mk_itself(mk_vartype"'ffi")

val (Eval,mk_Eval4,dest_Eval4,is_Eval) = HolKernel.syntax_fns4 "ml_translator" "Eval";

fun mk_Eval(t1,t2,t3) = mk_Eval4(ffi,t1,t2,t3)

fun dest_Eval t =
  let
    val (_,t1,t2,t3) = dest_Eval4 t
  in (t1,t2,t3) end

fun mk_Eq(t1,t2) = let
  val (Eq,mk_Eq4,_,_) = HolKernel.syntax_fns4 "ml_translator" "Eq";
  val v1 = mk_var("v1",type_of t2)
  val v2 = mk_var("v2",v_ty)
  in mk_Eq4(t1,t2,v1,v2) |> rator |> rator end

fun list_of_quintuple (a,b,c,d,e) = [a,b,c,d,e]
fun dest_quinop c e tm =
  case with_exn strip_comb tm e of
    (t, [t1,t2,t3,t4,t5]) =>
      if same_const t c then (t1,t2,t3,t4,t5) else raise e
  | _ => raise e

val (Arrow,mk_Arrow5,dest_Arrow5,is_Arrow) =
  HolKernel.syntax_fns {n=5,
    make= (fn tm => HolKernel.list_mk_icomb tm o list_of_quintuple),
    dest= dest_quinop } "ml_translator" "Arrow";

fun mk_Arrow(t1,t2) = let
  val a = t1 |> type_of |> dest_type |> snd |> hd
  val b = t2 |> type_of |> dest_type |> snd |> hd
  val v1 = mk_var("v1",mk_type("fun",[a,b]))
  val v2 = mk_var("v1",v_ty)
  in mk_Arrow5(ffi,t1,t2,v1,v2) |> rator |> rator end

fun dest_Arrow t = let
  val t1 = t |> rator |> rand
  val t2 = t |> rand
  val a = t1 |> type_of |> dest_type |> snd |> hd
  val b = t2 |> type_of |> dest_type |> snd |> hd
  val v1 = mk_var ("v1", mk_type ("fun",[a,b]))
  val v2 = mk_var ("v2", v_ty)
  val (_, t1', t2', _, _) = dest_Arrow5 (list_mk_comb (t, [v1, v2]))
  in (t1', t2') end

fun is_Arrow t = can dest_Arrow t

fun strip_Arrow t = let
  val (t1, t2) = dest_Arrow t
in
  if is_Arrow t2 then
    let val (t2_args, t2_ret) = strip_Arrow t2
    in (t1::t2_args, t2_ret) end
  else
    ([t1], t2)
end

val (write,mk_write,dest_write,is_write) = HolKernel.syntax_fns3 "ml_prog" "write";

end

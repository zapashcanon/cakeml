open
  preamble
  ml_translatorLib
  ml_progLib
  TextIOProgTheory
  mlapplistTheory

val _ = (
  new_theory "AppListProg";
  translation_extends "TextIOProg";
  generate_sigs := true;
  register_type ``:'a app_list``;
  ml_prog_update (open_module "AppList")
)

fun tr name def = (
  next_ml_names := [name];
  translate def
)

val _ = tr "fromArray" fromArray_def
val _ = tr "fromVector" fromVector_def

val sigs = module_signatures [
  "fromArray",
  "fromVector"
]

val _ = ml_prog_update (close_module (SOME sigs))
val _ = export_theory ()

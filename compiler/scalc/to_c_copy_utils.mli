open Shared_ast

val format_types_deep_copy :
  ?module_name:ModuleName.t ->
  ppc:Format.formatter ->
  pph:Format.formatter ->
  decl_ctx ->
  TypeIdent.t list ->
  unit
(** [format_types_deep_copy ?module_name ~ppc ~pph decl_ctx types]

    Prints deep copy function of Catala values independently of the catala
    stack. Copies values will persist even after calling `catala_free`. *)

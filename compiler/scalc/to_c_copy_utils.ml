open Catala_utils
open Shared_ast
module Runtime = Catala_runtime

(* Helpers *)

let copy = "catala_copy"
let _free = "catala_free"
let pp f = Format.fprintf f
let str f = Format.asprintf f

(* Returns true iff the type in argument is built-in.
   Built-in types already have their copy function defined in catala_runtime.h,
   so we do not need to generate them. *)
let is_builtin typ =
  match Mark.remove (Type.unquantify typ) with TLit _ -> true | _ -> false

let rec format_typ fmt typ =
  match Mark.remove (Type.unquantify typ) with
  | TLit TUnit -> pp fmt "unit"
  | TLit TMoney -> pp fmt "money"
  | TLit TInt -> pp fmt "int"
  | TLit TRat -> pp fmt "dec" (* For 'decimal' *)
  | TLit TDate -> pp fmt "date"
  | TLit TDuration -> pp fmt "duration"
  | TLit TBool -> pp fmt "bool"
  | TLit TPos -> pp fmt "position"
  | TTuple ts ->
    (* May lead to diplicate representation of types (for tuples within
        tuples): prefixing & suffixing with '_'. *)
    Format.fprintf fmt "_tuple_%a_" format_typ_list ts
  | TStruct s -> pp fmt "%s" (StructName.base s)
  | TOption t -> pp fmt "option_%a" format_typ t
  | TDefault t -> pp fmt "default_%a" format_typ t
  | TEnum e -> pp fmt "%s" (EnumName.base e)
  | TAbstract t -> pp fmt "abstract_%s" (AbstractType.base t)
  | TArrow (tl, t2) ->
    (* Not sure we want to copy/free this one *)
    pp fmt "arrow_%a_%a" format_typ_list tl format_typ t2
  | TArray t -> pp fmt "array_%a" format_typ t
  | TVar v -> pp fmt "var_%i" (Bindlib.uid_of v)
  | TForAll _ | TError -> assert false
  | TClosureEnv -> pp fmt "closure"

and format_typ_list fmt =
  (Format.pp_print_list
     ~pp_sep:(fun fmt _ -> Format.fprintf fmt "_")
     format_typ)
    fmt

(* Module's main part *)

type typ_data = {
  type_repr : string; (* The normalized text to use in function names *)
  is_public : bool; (* States if the functions must be exposed *)
}

type ctx = {
  decl_ctx : decl_ctx; (* The base context *)
  module_name : string; (* Used to disambiguate local funtions *)
  typ_map : typ_data Type.Map.t; (* Maps types to their data *)
}

type pp_fun = {
  pp_decl : Format.formatter -> unit; (* Prints the declaration of a function *)
  pp_def : Format.formatter -> unit; (* Prints the function's definition *)
}

(* Creates a fresh context. *)
let fresh_ctx ?module_name decl_ctx =
  let module_name =
    match module_name with
    | None -> "MAIN"
    | Some m -> ModuleName.(to_string (normalise m))
  in
  { decl_ctx; module_name; typ_map = Type.Map.empty }

(* Returns true iff the type in argument is public.
   Public types must have their copy function exported. *)
let is_public_type ctx t = (Type.Map.find t ctx.typ_map).is_public

(* Returns the copy function name for a given type. *)
let copy_fun_for_type ctx t =
  let data = Type.Map.find t ctx.typ_map in
  if data.is_public || is_builtin t then
    Format.sprintf "%s_%s" copy (Type.Map.find t ctx.typ_map).type_repr
  else
    (* Sometimes, two files will create a same copy function for a private type.
       We need to disambiguate by adding the module name. *)
    Format.sprintf "%s_%s_%s" copy ctx.module_name
      (Type.Map.find t ctx.typ_map).type_repr

(* Registers a type in the context, it will then be used to generate printers. *)
let add_type_to_context ?(is_public = false) ctx typ =
  if Type.Map.mem typ ctx.typ_map then ctx
  else
    let type_repr = Format.asprintf "%a" format_typ typ in
    { ctx with typ_map = Type.Map.add typ { type_repr; is_public } ctx.typ_map }

(* TODO: tailrec *)
(* Recursively registers a type and its subtypes to the context. *)
let rec fill_ctx_with_typ (ctx : ctx) typ =
  let ctx = add_type_to_context ctx typ in
  match Mark.remove (Type.unquantify typ) with
  | TLit _ -> ctx
  | TTuple tl -> List.fold_left fill_ctx_with_typ ctx tl
  | TOption t | TDefault t | TArray t -> fill_ctx_with_typ ctx t
  | TStruct s ->
    let m = StructName.Map.find s ctx.decl_ctx.ctx_structs in
    StructField.Map.fold (fun _ t ctx -> fill_ctx_with_typ ctx t) m ctx
  | TEnum e ->
    let m = EnumName.Map.find e ctx.decl_ctx.ctx_enums in
    EnumConstructor.Map.fold (fun _ t ctx -> fill_ctx_with_typ ctx t) m ctx
  | TAbstract _ -> ctx
  | TArrow (tl, t) ->
    List.fold_left fill_ctx_with_typ (fill_ctx_with_typ ctx t) tl
  | TVar _ -> ctx
  | TForAll _ | TError -> assert false
  | TClosureEnv -> ctx

(* Registers a type ident and all its subtypes *)
let add_typeident_and_subtypes_to_context ctx tident =
  let typ =
    match tident with
    | TypeIdent.Struct s -> Mark.ghost (TStruct s)
    | Enum e -> Mark.ghost (TEnum e)
    | Abstract a -> Mark.ghost (TAbstract a)
  and is_public = TypeIdent.Set.mem tident ctx.decl_ctx.ctx_public_types in
  let ctx = add_type_to_context ~is_public ctx typ in
  fill_ctx_with_typ ctx typ

(* Returns an expression calling the copy option helper for variable [arg] with
   the right copy function given [arg]'s type [typ]. *)
let copy_option ~ctx ~typ arg =
  match copy_fun_for_type ctx typ with
  | copy_fun ->
    str "catala_copy_option(%s,(const void *(*)(const void *))%s)" arg copy_fun
  | exception Not_found ->
    Format.kasprintf invalid_arg "To_c_copy_utils.copy_option for type %a"
      Type.format typ

(* Same as [copy_option], but for array. *)
let copy_array ~ctx ~typ arg =
  match copy_fun_for_type ctx typ with
  | copy_fun ->
    str "catala_copy_array(%s,(const void *(*)(const void *))%s)" arg copy_fun
  | exception Not_found ->
    Format.kasprintf invalid_arg "To_c_copy_utils.copy_option for type %a"
      Type.format typ

(* Pretty prints a list of copy funs to be used as arguments of "catala_copy_tuple". *)
let pp_list_copy_funs fmt l =
  (Format.pp_print_list
     ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
     (fun fmt s -> Format.fprintf fmt "(const void *(*)(const void *))%s" s))
    fmt l

(* Same as [copy_option], but for tuples. *)
let copy_tuple ~(ctx : ctx) ~tl arg : string =
  let size = List.length tl in
  let copy_funs = List.map (copy_fun_for_type ctx) tl in
  str "catala_copy_tuple(%s, %i, %a)" arg size pp_list_copy_funs copy_funs

(* Returns a printer for a structure type. *)
let format_struct_copy
    ~ctx
    ~typ
    struct_name
    (struct_fields : typ StructField.Map.t) =
  let tname = StructName.base struct_name in
  let sign =
    Format.asprintf "const %s* %s(const %s *arg)" tname
      (copy_fun_for_type ctx typ)
      tname
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>  " sign;
    (* Start fun *)
    pp fmt "%s *res;" tname;
    pp fmt "@,res = malloc(sizeof(%s));" tname;
    pp fmt "@,if (!res) return NULL;";
    (* Copying the fields *)
    StructField.Map.iter
      (fun (struct_field : StructField.t) typ ->
        pp fmt "@,res->%a = %s(arg->%a);" StructField.format struct_field
          (copy_fun_for_type ctx typ)
          StructField.format struct_field)
      struct_fields;
    (* Copy complete *)
    pp fmt "@,return res;";
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for an enum type. *)
let format_enum_copy ~ctx ~typ enum_name enum_cons =
  let tname = EnumName.base enum_name in
  let sign =
    Format.asprintf "const %s* %s(const %s *arg)" tname
      (copy_fun_for_type ctx typ)
      tname
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>  " sign;
    (* Start fun *)
    pp fmt "%s *res;" tname;
    pp fmt "@,res = malloc(sizeof(%s));" tname;
    pp fmt "@,if (!res) return NULL;";
    (* Copy the code *)
    pp fmt "@,res->code = arg->code;";
    (* Copying the fields given the case *)
    pp fmt "@,switch (arg->code) {@,@[<v 2>  ";
    (* Start switch *)
    EnumConstructor.Map.iter
      (fun enum_case typ ->
        pp fmt "case %a: {@,@[<v 2>  " (* Start case *) EnumConstructor.format
          enum_case;
        pp fmt "res->payload.%a = %s(arg->payload.%a);" EnumConstructor.format
          enum_case
          (copy_fun_for_type ctx typ)
          EnumConstructor.format enum_case;
        pp fmt "@,break;";
        pp fmt "@]@,}@," (* End case *))
      enum_cons;
    pp fmt "default: return NULL;";
    pp fmt "@]@,}";
    (* End switch *)
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for an abstract type.
   For now, such function only returns NULL. *)
let format_abstract_copy ~ctx ~typ tid =
  let tname = AbstractType.base tid in
  let sign =
    Format.asprintf "const %s* %s_abstract(const %s *arg)" tname
      (copy_fun_for_type ctx typ)
      tname
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>  " sign;
    (* Start fun *)
    pp fmt "return NULL;";
    (* TODO? *)
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for a closure.
   For now, such function only returns NULL. *)
let format_closure_copy ~ctx ~typ =
  let sign =
    Format.asprintf "const catala_closure* %s(const catala_closure*arg)"
      (copy_fun_for_type ctx typ)
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>  " sign;
    (* Start fun *)
    pp fmt "return NULL;";
    (* TODO? *)
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for an option type. *)
let format_option_copy ~ctx ~typ sub_typ =
  let sign =
    Format.asprintf "const CATALA_OPTION(X) %s(const CATALA_OPTION(X) arg)"
      (copy_fun_for_type ctx typ)
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>  " sign;
    (* Start fun *)
    pp fmt "return %s;" (copy_option ~ctx ~typ:sub_typ "arg");
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for a tuple type. *)
let format_tuple_copy ~ctx ~typ tl =
  let sign =
    Format.asprintf "const CATALA_TUPLE(X) %s(const CATALA_TUPLE(X) arg)"
      (copy_fun_for_type ctx typ)
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>" sign;
    (* Start fun *)
    pp fmt "return %s;" (copy_tuple ~ctx ~tl "arg");
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for an array type. *)
let format_array_copy ~ctx ~typ sub_typ =
  let sign =
    Format.asprintf "const CATALA_ARRAY(X) %s(const CATALA_ARRAY(X) arg)"
      (copy_fun_for_type ctx typ)
  in
  let pp_decl fmt = pp fmt "@,%s;" sign
  and pp_def fmt =
    pp fmt "@,%s {@,@[<v 2>  " sign;
    (* Start fun *)
    pp fmt "return %s;" (copy_array ~ctx ~typ:sub_typ "arg");
    pp fmt "@]@,}@," (* End fun *)
  in
  { pp_decl; pp_def }

(* Returns a printer for a given type, if supported (otherwise, returns None). *)
let format_type_deep_copy ~ctx typ =
  match Mark.remove (Type.unquantify typ) with
  | TError -> None
  | TLit _ -> None (* Defined in catala_runtime.c/h *)
  | TStruct s ->
    if StructName.path s = [] then
      Some
        (let def = StructName.Map.find s ctx.decl_ctx.ctx_structs in
         format_struct_copy ~ctx ~typ s def)
    else None
  | TEnum e ->
    if EnumName.path e = [] && not (EnumName.equal e ConstantNames.option_enum)
    then
      (* Options are handled from TOption *)
      let def = EnumName.Map.find e ctx.decl_ctx.ctx_enums in
      Some (format_enum_copy ~ctx ~typ e def)
    else None
  | TAbstract tid ->
    if AbstractType.path tid = [] then Some (format_abstract_copy ~ctx ~typ tid)
    else None
  | TTuple [_; (TClosureEnv, _)] -> Some (format_closure_copy ~ctx ~typ)
  | TTuple l -> Some (format_tuple_copy ~ctx ~typ l)
  | TArray t -> Some (format_array_copy ~ctx ~typ t)
  | TOption o -> Some (format_option_copy ~ctx ~typ o)
  | TClosureEnv | TArrow _ | TDefault _ | TVar _ | TForAll _ -> None

(* Main entry point of the module. *)
let format_types_deep_copy ?module_name ~ppc ~pph decl_ctx type_ordering =
  let ctx = fresh_ctx ?module_name decl_ctx in
  (* Mapping types to a flag stating if they are public or not.
     This map also will serve as the collection of types to
     iterate on. *)
  let ctx =
    List.fold_left
      (fun ctx t -> add_typeident_and_subtypes_to_context ctx t)
      ctx type_ordering
  in
  (* Generating printers for all types. *)
  let printers =
    Type.Map.fold
      (fun typ_or_subtyp _ printers ->
        match format_type_deep_copy ~ctx typ_or_subtyp with
        | None -> printers
        | Some pp -> (typ_or_subtyp, pp) :: printers)
      ctx.typ_map []
  in
  (* Writing declarations in .h and in .c in advance. *)
  List.iter
    (fun (typ_or_subtyp, pp_f) ->
      (* Writing declaration in .h *)
      if is_public_type ctx typ_or_subtyp then begin
        pp pph "@,";
        pp_f.pp_decl pph
      end;
      (* Writing pre-declaration in .c *)
      pp ppc "@,";
      pp_f.pp_decl ppc)
    printers;
  (* Now functions have been declared in the .c,
     we can use them without taking care of their definition order.
   *)
  List.iter
    (fun (_, pp_f) ->
      pp ppc "@,";
      pp_f.pp_def ppc)
    printers

(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* naming and local environment *)


type ident = {
  num : int;        (* a unique index *)
  source : string;  (* the original name in the source *)
  is_generated : bool;
  is_reset : bool;
}

let is_reset id = id.is_reset

type var_ident = ident

let num = ref 0

let ident_compare id1 id2 = compare id1.num id2.num

(* used only for debuging *)
let name id =
  if id.is_generated then
    id.source ^ "_" ^ (string_of_int id.num)
  else
    id.source

(* used only for debuging *)
let print_ident ff id = Format.fprintf ff "%s" (name id)

module M = struct
  type t = ident
  let compare = ident_compare
  let print_t = print_ident
end

module Env =
struct
  include (Map.Make(M))

  let append env0 env =
    fold (fun key v env -> add key v env) env0 env

  (* Environments union *)
  let union env1 env2 =
    fold (fun name elt env -> add name elt env) env2 env1

  (* Environments difference : env1 - env2 *)
  let diff env1 env2 =
    fold (fun name _ env -> remove name env) env2 env1

  (* Environments partition *)
  let partition p env =
    fold
      (fun key elt (env1,env2) ->
         if p(key)
         then ((add key elt env1),env2)
         else (env1,(add key elt env2)))
      env
      (empty, empty)

  (* Print Env *)
  let print_t print_value ff m =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a => %a,@ " M.print_t k print_value v) m;
    Format.fprintf ff "}@]";
end

module IdentSet = struct
  include (Set.Make(M))

  let print_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a,@ " M.print_t e) s;
    Format.fprintf ff "}@]";
end

module S = Set.Make (struct type t = string
                            let compare = Pervasives.compare end)


(** Module used to generate unique string (inside a node) per ident.
    /!\ Any pass generating a name must call [enter_node] and use gen_fresh *)
module UniqueNames =
struct
  open Names
  let used_names = ref (ref NamesSet.empty) (** Used strings in the current node *)
  let env = ref Env.empty (** Map idents to their string *)
  let current_node = ref Names.dummy_qualname (** Stores the current node *)
  let (node_env : NamesSet.t ref QualEnv.t ref) = ref QualEnv.empty

  (** This function should be called every time we enter a node *)
  let enter_node n =
    current_node := n;
    (if not (QualEnv.mem n !node_env)
    then node_env := QualEnv.add n (ref NamesSet.empty) !node_env);
    used_names := QualEnv.find n !node_env
  
  let clone_node f f' =
    let f'env =
      try QualEnv.find f' !node_env
      with Not_found -> ref NamesSet.empty
    in
    NamesSet.iter (fun s -> f'env := NamesSet.add s !f'env) !(QualEnv.find f !node_env);
    node_env := QualEnv.add f' f'env !node_env

  (** @return a unique string for each identifier. Idents corresponding
      to variables defined in the source file have the same name unless
      there is a collision. *)
  let assign_name n =
    let num = ref 1 in
    let fresh s =
      num := !num + 1;
      s ^ "_" ^ (string_of_int !num) in
    let rec fresh_string base =
      let fs = fresh base in
      if NamesSet.mem fs !(!used_names) then fresh_string base else fs in
    if not (Env.mem n !env) then
      (let s = n.source in
       let s = if NamesSet.mem s !(!used_names) then fresh_string s else s in
       !used_names := NamesSet.add s !(!used_names);
       env := Env.add n s !env)

  let name id =
    Env.find id !env
end

let gen_fresh pass_name kind_to_string ?(reset=false) kind =
  let s = kind_to_string kind in
  let s = if !Compiler_options.full_name then "__"^pass_name ^ "_" ^ s else s in
  num := !num + 1;
  let id = { num = !num; source = s; is_generated = true; is_reset = reset } in
    UniqueNames.assign_name id; id

let gen_var pass_name ?(reset=false) name =
  gen_fresh pass_name (fun () -> name) ~reset:reset ()

let ident_of_name ?(reset=false) s =
  num := !num + 1;
  let id = { num = !num; source = s; is_generated = false; is_reset = reset } in
    UniqueNames.assign_name id; id

let source_name id = id.source
let name id = UniqueNames.name id
let enter_node n = UniqueNames.enter_node n
let clone_node f f' = UniqueNames.clone_node f f'

let local_qn name = { Names.qual = Names.LocalModule (Names.QualModule !UniqueNames.current_node);
                      Names.name = name }

let print_ident ff id = Format.fprintf ff "%s" (name id)

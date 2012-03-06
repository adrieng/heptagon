open Names
open Location
open Signature


type error =
  | Eckvar_unbound_input of name option * name
  | Eckvar_unbound_ouput of name option * name

exception SignatureError of name option * name

let message loc (s,e) =
  Format.eprintf "%aInfered signature :@\n%a@\n"
    print_location loc
    Global_printer.print_interface_value ("",s);
  begin match e with
  | Eckvar_unbound_input(var_name,ck_name) ->
      let a,name = match var_name with None -> "A","" | Some n -> "The"," "^n in
      Format.eprintf "%s sampled input%s should come together with its sampling variable %s.@."
        a name ck_name
  | Eckvar_unbound_ouput (var_name,ck_name) ->
      let a,name = match var_name with None -> "A","" | Some n -> "The"," "^n in
      Format.eprintf "%s sampled ouput%s should be returned with its sampling value %s.@."
        a name ck_name
  end;
  Format.eprintf "@.";
  if not !Compiler_options.no_clocking_error then raise Errors.Error


(** @raise Errors.Error after printing the error *)
let check_signature s =
  (* a simple env of defined names will be used, represented by a Set *)
  let rec append env sa_l = match sa_l with
    | [] -> env
    | sa::sa_l -> match sa.a_name with
        | None -> append env sa_l
        | Some x -> append (NamesSet.add x env) sa_l
  in
  (* the clock of [arg] is correct if all the vars used are in [env] *)
  let check env arg =
    let n = arg.a_name in
    let rec f = function
      | Cbase -> ()
      | Con(ck,_,x) ->
          if not (NamesSet.mem x env)
          then raise (SignatureError (n,x));
          f ck
    in
    f arg.a_clock
  in
  (*initial env with only the inputs*)
  let env = append NamesSet.empty s.node_inputs in
  (try List.iter (check env) s.node_inputs
  with SignatureError (x,c) ->
    message s.node_loc (s, Eckvar_unbound_input (x,c)));
  let env = append env s.node_outputs in
  try List.iter (check env) s.node_outputs
  with SignatureError (x,c) ->
    message s.node_loc (s, Eckvar_unbound_ouput (x,c))

(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* scheduling of equations *)


open Misc
open Minils
open Mls_utils
open Graph
open Dep

(* possible overlapping between clocks *)
let join ck1 ck2 =
  let n1 = Vars.head ck1
  and n2 = Vars.head ck2 in
  (* C1(x1) on ... on Cn(xn) with C'1(x'1) on ... on C'k(x'k) *)
  match n1, n2 with
      [], [] -> true
    | x1 ::_, x2 ::_ when x1 = x2 -> true
    | _ -> false

let join eq1 eq2 = join (Vars.clock eq1) (Vars.clock eq2)

(* TODO *)
(* possible overlapping between nodes *)
(*let head e =
  match e with
    | Emerge(_, c_e_list) -> List.fold (fun acc e -> Vars.head (clock e) :: acc)
    | e -> [Vars.head (clock e)]

(* e1 define a pieces of control structures with *)
  (* paths on clock C1(x1) on ... on Cn(xn) ... *)
  (* e1 can be merged if *)
let n1_list = head e1 in
  let n2_list = head e2 in
*)

(* clever scheduling *)
let schedule eq_list =
  let rec recook = function
    | [] -> []
    | node :: node_list -> node >> (recook node_list)

  and (>>) node node_list =
    try
      insert node node_list
    with
        Not_found -> node :: node_list

  and insert node = function
    | [] -> raise Not_found
    | node1 :: node_list ->
        if linked node node1 then raise Not_found
        else
          try
            node1 :: (insert node node_list)
          with
            | Not_found ->
                if join (containt node) (containt node1)
                then node :: node1 :: node_list
                else raise Not_found in

  let node_list, _ = DataFlowDep.build eq_list in
  let node_list = recook (topological node_list) in
  let node_list = List.rev node_list in
  let node_list = recook node_list in
  let node_list = List.rev node_list in
  List.map containt node_list

let eqs funs () eq_list =
  let eqs, () = Mls_mapfold.eqs funs () eq_list in
    schedule eqs, ()

let edesc _ () = function
  | Eiterator(it, ({ a_op = Enode f } as app),
              n, [], e_list, r) when Itfusion.is_anon_node f ->
    let nd = Itfusion.find_anon_node f in
    let nd = { nd with n_equs = schedule nd.n_equs } in
      Itfusion.replace_anon_node f nd;
      Eiterator(it, app, n, [], e_list, r), ()
  | _ -> raise Errors.Fallback

let program p =
  let p, () = Mls_mapfold.program_it
                { Mls_mapfold.defaults with Mls_mapfold.eqs = eqs;
                    Mls_mapfold.edesc = edesc } () p in p

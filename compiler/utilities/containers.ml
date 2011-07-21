
module ListMap (Ord:Map.OrderedType) =
struct
  include Map.Make(Ord)

  let add_element k v m =
    try
      add k (v::(find k m)) m
    with
      | Not_found -> add k [v] m

  let add_elements k vl m =
    try
      add k (vl @ (find k m)) m
    with
      | Not_found -> add k vl m
end

(** Utils *)
module StringOrdering = struct
  type t = string
  let compare = Pervasives.compare
end
module StringMap = Map.Make(StringOrdering)
module StringSet = Set.Make(StringOrdering)

let order_comp x y =
  if x = 0 then y else x

let order_concat l =
  let rec aux last = function
    | [] -> last
    | (h::t) ->
      if last <> 0 then last else aux (order_comp last (Lazy.force h)) t
  in aux 0 l

let compare_list cmp l1 l2 =
  let l = Pervasives.compare (List.length l1) (List.length l2) in
  if l == 0 then
    order_concat (List.map
                    (fun (el1, el2) -> lazy (cmp el1 el2))
                    (List.combine l1 l2))
  else
    l

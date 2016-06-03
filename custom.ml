(* signature *)
module type T = sig
  type t

  (* Data structures *)
  val equal: t -> t -> bool
  val hash: t -> int
  val compare: t -> t -> int
  val dump: Format.formatter -> t -> unit
end

module Pair(X : T)(Y : T) = struct

  type t = X.t * Y.t
  let compare (x1,y1) (x2,y2) =
    let c = X.compare x1 x2 in if c <> 0 then c
    else Y.compare y1 y2
  let equal (x1,y1) (x2,y2) = (X.equal x1 x2) && (Y.equal y1 y2)
  let hash (x,y) = X.hash x + 65599 * Y.hash y
  let dump ppf (x,y) = Format.fprintf ppf "(%a,%a)" X.dump x Y.dump y
end

(* the list printer *)
let dump_list ?(bra=1) ?(sep="; ") f ppf l = (* ?(sep="; ") means either to input a separator or to take the default separator("; ") *)
  let (left,right) = 
      if bra = 0 then ("( ", " )") 
      else if bra = 1 then ("[ ", " ]")
      else ("{ ", " }")
  in
  Format.pp_print_string ppf left;
  (match l with
     | [] -> ()
     | [hd] -> f ppf hd
     | hd::tl ->
         f ppf hd;
         List.iter (fun x -> Format.pp_print_string ppf sep; f ppf x) tl
  );
  Format.pp_print_string ppf right



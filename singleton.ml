module Make(X : Custom.T) = struct
  module SList = SortedList.Make(X)
  module Pair = Custom.Pair(SList)(SList)
  include SortedList.Make(Pair) (* [ ([ P ],[ N ]); ... ] *)

(*
1: [([a],[]), ([b],[]), ... ]
2: [[][a,b,...]]
*)
  let empty = [ ]
  let full  = [ [],[] ]

  let atom x = [ [x],[] ]
(* The following can be rewrite to make it effective as it needn't sort or check  *)

  let may_remove (p1,n1) (p2,n2) = (* true if (p1,n1) is a subtype of (p2, n2) *)
    (SList.subset p2 p1) && (SList.subset n2 n1) (* ([a,b],[]) = a^b  is a subtype of ([a],[]) = a *)

  let rec fold2_aux f a x = function (* fold2_aux : ('a -> 'b -> 'c -> 'a) -> 'b -> 'a -> 'c list -> 'a   *)
    | [] -> x
    | h :: t -> fold2_aux f a (f x a h) t

  let rec fold2 f x l1 l2 = (* val fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a  *)
    match l1 with
      | [] -> x
      | h :: t -> fold2 f (fold2_aux f h x l2) t l2

  let rec should_add x = function (* true if x should by added *)
    | [] -> true
    | y::rem -> if may_remove x y then false else should_add x rem

  let rec clean_add accu x = function (* add the elements in l into accu which are not the subtype of x *)
    | [] -> accu
    | y::rem ->
        if may_remove y x then clean_add accu x rem
        else clean_add (y::accu) x rem


  let cup t s = (* the union of t and s *)
    let remove a l = SList.diff l [a] in 
    let rec cup12 t n =        
        match t with 
        |[] -> [[],n]
        |([a],[])::t' -> cup12 t' (remove a n) 
        |_::t' -> cup12 t' n
    in 
    if t == s then t
    else match (t,s) with
      | [],s -> s
      | t,[] -> t
      | [ [], [] ], _ | _, [ [], [] ] -> full
      | ((a,[])::t', (b,[])::s') -> cup s t
      | ((a,[])::t', [[],n]) -> cup12 t n
      | ([[],n], (a,[])::t') -> cup12 s n
      | ([[],nt], [[],ns]) -> [[], (SList.cap nt ns)] 
      | _ ->
          let s= (* to filter some types,each of which exists a super type in t, in s *)
            filter (* filter = SortedList.Make(Pair).filter = List.filter *)
              (fun (p,n) -> not (exists (may_remove (p,n)) t)) s in
          let t= (* to filter some types,each of which exists a super type in s, in t *)
            filter
              (fun (p,n) -> not (exists (may_remove (p,n)) s)) t in
          cup s t (* SortedList.cup *)


  let cap s t = (* the intersection of s and t *)
    let rec cap12 t n =
        match n with 
        |[] -> t
        |a::n' -> cap12 (diff t ([[a],[]])) n'
    in
    if s == t then s
    else match (s,t) with
         | [[],[]],s -> s
         | t,[[],[]] -> t
         | [], _ | _, [] -> empty
         |((a,[])::t', (b,[])::s') -> cap s t
         |((a,[])::t', [[],n]) -> cap12 s n
         |([[],n], (a,[])::t') -> cap12 t n
         |([[],nt], [[],ns]) -> [[], (SList.cup nt ns)] 
         |_ ->
      let (lines1,common,lines2) = split s t in
      let rec aux lines (p1,n1) (p2,n2) =
          if (SList.disjoint p1 n2) && (SList.disjoint p2 n1)
          then
            let x = (SList.cup p1 p2, SList.cup n1 n2) in
            if should_add x lines then clean_add [x] x lines else lines
          else lines (* if p1 ^ n2 != empty or p2 ^ n1 != empty then (p1,n1) ^ (p2,n2) = empty *)
      in
      from_list
        (fold2 aux (get common) (get lines1) (get lines2))


  let diff1 c1 c2 = (* c1 - c2 *)
    if (c2 == full) || (c1 == c2) then empty
    else if (c1 == empty) || (c2 == empty) then c1
    else
      let c1 = diff c1 c2 in (* diff = SortedList.Make(Pair).diff *)
      let line (p,n) =
        let acc = SList.fold (fun acc a -> ([], [a]) :: acc) [] p in (* [p1; p2; ...] -> [...; ([],[p2]); ([],[p1])] *)
        let acc = SList.fold (fun acc a -> ([a], []) :: acc) acc n in (* [n1; n2; ...] -> [...; ([n2],[]); ([n1],[])] *)
        from_list acc
      in
      fold (fun c1 l -> cap c1 (line l)) c1 c2 (* fold = SortedList.Make(Pair).fold *) (* c1 - all line e (in c2) *)

 let neg t = 
    let rec neg12 t n =
       match t with
       |[] -> [[],n]
       |([a],[])::t' -> neg12 t' (SList.add a n)
       |_::t' -> neg12 t' n
    in
    let rec neg21 n t =
        match n with
        |[] -> t
        |a::n' -> neg21 n' (cup [[a],[]] t)
    in
    if t == full then empty
    else if t == empty then full
    else match t with 
    | ([a],[])::t' -> neg12 t []
    | [[],n] -> neg21 n []
    | _ -> diff1 full t

 let diff  s t =    
    if (t == full) || (s == t) then empty
    else if (s == empty) || (t == empty) then s
    else cap s (neg t)

  let is_empty = function [] -> true | _ -> false

  let disjoint a b = cap a b = [] (* true if a ^ b = empty *)

let atom2string = function `Singleton s -> s | _ -> "any"
let tostring0 (p,n) =
    if List.length p > 0 then atom2string (List.hd p)
    else let ns = List.map atom2string n in
    List.fold_left (fun s t -> s^"_not_"^t) "" ns     
let tostring = function [] -> "none" | [[],[]] -> "atom" | (p,n)::tl -> tostring0 (p,n)

  let dump ppf l = List.iter (fun t -> Format.fprintf ppf "%a" Pair.dump t) l (* printer *)

  let dump ppf l = 
  Format.pp_print_string ppf "[ ";
  (match l with
     | [] -> ()
     | [hd] -> Pair.dump ppf hd
     | hd::tl ->
         Pair.dump ppf hd;
         List.iter (fun x -> Format.pp_print_string ppf "; "; Pair.dump ppf x) tl
  );
  Format.pp_print_string ppf " ]"


end

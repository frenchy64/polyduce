(* functor *)
module Make(X : Custom.T) = struct
    type t = X.t list (* t is a sorted list, ascending *)

    type elem = X.t

    let rec equal l1 l2 =
      (l1 == l2) ||
      match (l1,l2) with
        | x1::l1, x2::l2 -> (X.equal x1 x2) && (equal l1 l2)
        | _ -> false

    let rec hash accu = function (* int -> t list -> int *)
      | [] -> 1 + accu
      | x::l -> hash (17 * accu + X.hash x) l

    let hash l = hash 1 l

    let rec compare l1 l2 =
      if l1 == l2 then 0
      else match (l1,l2) with
        | x1::l1, x2::l2 ->
            let c = X.compare x1 x2 in if c <> 0 then c
            else compare l1 l2
        | [],_ -> -1
        | _ -> 1

    let iter = List.iter

    let filter = List.filter (* filter p l returns all the elements of the list l that satisfy the predicate p. The order of the elements in the input list is preserved. *)
    let exists = List.exists (* exists p [a1; ...; an] checks if at least one element of the list satisfies the predicate p. That is, it returns (p a1) || (p a2) || ... || (p an). *)
    let fold = List.fold_left (* List.fold_left f a [b1; ...; bn] is f (... (f (f a b1) b2) ...) bn. *)
    external get: t -> elem list = "%identity" (* ?? *)

    let is_empty l = l = []
    let empty = []

    let rec disjoint l1 l2 = (* true if l1 and l2 are disjoint *)
      match (l1,l2) with
        | (t1::q1, t2::q2) -> 
            let c = X.compare t1 t2 in
            if c < 0 then disjoint q1 l2
            else if c > 0 then disjoint l1 q2
            else false
        | _ -> true
            
    let rec cup l1 l2 = (* union of l1 and l2 *)
      match (l1,l2) with
        | (t1::q1, t2::q2) ->
            let c = X.compare t1 t2 in
            if c = 0 then t1::(cup q1 q2)
            else if c < 0 then t1::(cup q1 l2)
            else t2::(cup l1 q2)
        | ([],l2) -> l2
        | (l1,[]) -> l1

    let add x l = cup [x] l
            
    let rec split l1 l2 = (* split the commom elements between l1 and l2, return (l1-com, com, l2-com) *)
      match (l1,l2) with
        | (t1::q1, t2::q2) ->
            let c = X.compare t1 t2 in
            if c = 0 then       let (l1,i,l2) = split q1 q2 in (l1,t1::i,l2)
            else if c < 0 then  let (l1,i,l2) = split q1 l2 in (t1::l1,i,l2)
            else                let (l1,i,l2) = split l1 q2 in (l1,i,t2::l2)
        | _ -> (l1,[],l2)
            
            
    let rec diff l1 l2 = (* l1 - l2 *)
      match (l1,l2) with
        | (t1::q1, t2::q2) ->
            let c = X.compare t1 t2 in
            if c = 0 then diff q1 q2
            else if c < 0 then t1::(diff q1 l2)
            else diff l1 q2
        | _ -> l1

    let rec cap l1 l2 = (* intersection of l1 and l2 *)
      match (l1,l2) with
        | (t1::q1, t2::q2) ->
            let c = X.compare t1 t2 in
            if c = 0 then t1::(cap q1 q2)
            else if c < 0 then cap q1 l2
            else cap l1 q2
        | _ -> []

            
    let rec subset l1 l2 = (* return true if l1 is a subset of l2 *)
      match (l1,l2) with
        | (t1::q1, t2::q2) ->
            let c = X.compare t1 t2 in
            if c = 0 then subset q1 q2
            else if c < 0 then false
            else subset l1 q2
        | [],_ -> true
        | _ -> false
            
    let from_list l = (* readjust the list l *)
      let rec initlist = function
        | [] -> []
        | e::rest -> [e] :: initlist rest in
      let rec merge2 = function
        | l1::l2::rest -> cup l1 l2 :: merge2 rest
        | x -> x in
      let rec mergeall = function
        | [] -> []
        | [l] -> l
        | llist -> mergeall (merge2 llist) in
      mergeall (initlist l)
        
    let map f l =
      from_list (List.map f l)

    let rec mem l x = (* true if x is in l *)
      match l with
        | [] -> false
        | t::q -> 
            let c = X.compare x t in
            (c = 0) || ((c > 0) && (mem q x))

    let rec check = function (* to check whether the list is ascending *)
      | a::(b::_ as t) -> assert (a < b); check t
      | _ -> ()

    let dump = Custom.dump_list X.dump (* printer *)

end

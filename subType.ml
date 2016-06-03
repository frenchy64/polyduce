open Ast

module Atom =
    struct
        type t = Ast.term
        let compare = Ast.compare (*Pervasives.compare*)
        let hash = Hashtbl.hash
        let equal s t  = Ast.equal s t (* special equality function *)
        let dump ppf t = Ast.dump ppf t
    end

module ST = Singleton.Make(Atom)
module B = Boolean.Make(Atom)
module AL = B.SList

let dump_nfs = B.dump

(* some functions definition here.... *)
let return a = [a]
let bind m f = List.flatten (List.map f m)
let mplus = List.append
let add_elem a l = if List.mem a l then l else a::l

let rec subsets = function
    |[] -> return []
    |h :: t ->
            bind (subsets t) (fun t1 ->
                mplus
                (bind (return t1) (fun t2 -> return (h :: t2)))
                (return t1)
            )

let vars t = 
    let rec aux t vs = match t with
        |`Arrow(t1,t2) 
        |`Prod(t1,t2)  
        |`Cup(t1,t2)   
        |`Cap(t1,t2) -> aux t2 (aux t1 vs) 
        |`Not(t')    
        |`Mu(_,t')   -> aux t' vs 
        |`TVar _      -> AL.cup [t] vs
        |_ -> vs
     in aux t AL.empty

let issubset vl1 vl2 = AL.subset vl1 vl2  (* return true if vl1 is a subset of vl2 *)

(* substitute A w.r.t tbl(A) *)
let subst t tbl =
    let rec aux tbl = function
        |`TVar(_,s) as t-> begin try List.assoc s tbl with Not_found -> t end 
        |`Arrow(t1,t2)  -> `Arrow(aux tbl t1,aux tbl t2)
        |`Prod(t1,t2)   -> `Prod (aux tbl t1,aux tbl t2)
        |`Cup(t1,t2)    -> `Cup  (aux tbl t1,aux tbl t2) 
        |`Cap(t1,t2)    -> `Cap  (aux tbl t1,aux tbl t2)
        |`Not(t)        -> `Not  (aux tbl t)
        |`Mu(x,t)       -> `Mu   (x,aux tbl t) 
        |t              -> t
    in
    if tbl = [] then t else aux tbl t 

(* substitute (TVar A) w.r.t tbl(TVar A) *)
let rec assoc t tbl =
    match tbl with
    |[] -> raise Not_found
    |(a,b)::tbl' -> if Ast.equal t a then b else assoc t tbl'
let subst_mark t tbl =
    let rec aux tbl = function
        |`TVar(_,_) as t-> begin try assoc t tbl with Not_found -> t end (* List.assoc *)
        |`Arrow(t1,t2)  -> `Arrow(aux tbl t1,aux tbl t2)
        |`Prod(t1,t2)   -> `Prod (aux tbl t1,aux tbl t2)
        |`Cup(t1,t2)    -> `Cup  (aux tbl t1,aux tbl t2) 
        |`Cap(t1,t2)    -> `Cap  (aux tbl t1,aux tbl t2)
        |`Not(t)        -> `Not  (aux tbl t)
        |`Mu(x,t)       -> `Mu   (x,aux tbl t) 
        |t              -> t
    in
    if tbl = [] then t else aux tbl t 

(* normal forms without simplifing and unfolding recursive types *)
let dnfMu ( t : Ast.term ) : B.t = 
    let rec nfs_cap l1 l2 l =
        match l1 with 
        |[] -> l
        |(p,n)::l' -> nfs_cap l' l2 (B.cup (nfs_cap' (p,n) l2 []) l) 
    and nfs_cap' (p,n) l2 l =
        match l2 with
        |[] -> l
        |(p',n')::l' -> nfs_cap' (p,n) l' (B.cup [(AL.cup p' p),(AL.cup n' n)] l) 
    in
    let rec nfs_pos = function
        |`Cup(t1,t2) -> B.cup (nfs_pos t1) (nfs_pos t2)
        |`Cap(t1,t2) -> nfs_cap (nfs_pos t1) (nfs_pos t2) []
        |`Not(t) -> nfs_neg t
        |`Any -> [[],[]]
        | _  as t -> [[t], []]

    and nfs_neg  = function
        |`Cup(t1,t2) -> nfs_cap (nfs_neg t1) (nfs_neg t2) []
        |`Cap(t1,t2) -> B.cup  (nfs_neg t1) (nfs_neg t2)
        |`Not(t) -> nfs_pos t
        |`Any -> []
        | _  as t -> [[], [t]]
    in
    let isnonempty l =  List.filter (function (p,n) -> AL.disjoint p n) l
    in isnonempty (nfs_pos t)

let chkatoms l =
    let chkatom (bint,bbool,batom, prod, arrow) a  =
	match a with
	|`Bool | `True |`False ->(bint, bbool+1, batom, prod, arrow)
	|`SingletonAny | `Singleton _ ->(bint, bbool, batom+1, prod, arrow)
        |`IntAny | `Left _ | `Right _ | `Bounded(_,_) -> (bint+1, bbool, batom, prod, arrow)
	|`Prod(_,_) -> (bint, bbool, batom, prod+1, arrow)
	|`Arrow(_,_) -> (bint, bbool,batom, prod, arrow+1)
	|_ -> (bint, bbool, batom, prod, arrow)
    in List.fold_left chkatom (0,0,0,0,0) l

let isbasic = function (`Prod (_,_) | `Arrow(_,_)) -> false | _ -> true
let isint = function (`IntAny |`Left _ | `Right _ | `Bounded(_,_)| `TVar _ | `MVar _ | `Mu(_,_)) -> true | _ -> false
let isbool = function (`Bool |`True |`False | `TVar _ | `MVar _ | `Mu(_,_)) -> true | _ -> false
let isatom = function (`SingletonAny|`Singleton _| `TVar _ | `MVar _ | `Mu(_,_)) -> true | _ -> false
let isprod  = function (`Prod (_,_) | `TVar _ | `MVar _ | `Mu(_,_)) -> true | _ -> false 
let isarrow = function (`Arrow (_,_) | `TVar _ | `MVar _ | `Mu(_,_)) -> true | _ -> false 
let isvar = function `TVar _ -> true | t -> false
 
let isint1 = function (`IntAny |`Left _ | `Right _ | `Bounded(_,_)) -> true | _ -> false
let isbool1 = function (`Bool |`True |`False) -> true | _ -> false
let isatom1 = function (`SingletonAny|`Singleton _) -> true | _ -> false
let isprod1  = function `Prod (_,_)  -> true | _ -> false 
let isarrow1 = function `Arrow (_,_)  -> true | _ -> false  
let isbasic1 a = isint1 a || isatom1 a || isbool1 a

let get_prod = function `Prod(t,s) -> (t,s) | _ -> failwith "prod"
let get_arrow = function `Arrow(t,s) -> (t,s) | _ -> failwith "arrow"
let get_tyvar = function `TVar(_,s) -> s | _ -> failwith "tyvar"

let simplify (p,n) =
    let (bints, bbools, batoms, prods, arrows) = chkatoms p in
    if (bints > 0 && bbools > 0)  ||
       (bints > 0 && batoms > 0)  ||
       (bints > 0 && prods > 0)   ||
       (bints > 0 && arrows > 0)  ||
       (bbools > 0 && batoms > 0) ||
       (bbools > 0 && prods > 0)  ||
       (bbools > 0 && arrows > 0) ||
       (batoms > 0 && prods > 0)  ||
       (batoms > 0 && arrows > 0) ||
       (prods > 0 && arrows > 0) then []
    (*else if bints > 0 then [(p, List.filter isint n)]
    else if batoms > 0 then [(p, List.filter isatom n)]
    else if prods > 0  then [(p, List.filter isprod n)]
    else if arrows > 0 then [(p, List.filter isarrow n)]*)
    else [(p,n)] 

let compare (p1,n1) (p2,n2) =
    let (bis1,bbs1,bas1,ps1,as1) = chkatoms p1 in
    let (bis2,bbs2,bas2,ps2,as2) = chkatoms p2 in
    if bis1 = 0 && bbs1 = 0 && bas1 = 0 && ps1 = 0 && as1 = 0 then -1
    else if bis2 = 0 && bbs2 = 0 && bas2 = 0 && ps2 = 0 && as2 = 0 then 1
    else if bis1 > 0 then -1
    else if bis2 > 0 then 1
    else if bbs1 > 0 then -1
    else if bbs2 > 0 then 1
    else if bas1 > 0 then -1
    else if bas2 > 0 then 1
    else if as1 > 0 then -1
    else if as2 > 0 then 1
    else if ps1 > 0 then -1
    else if ps2 > 0 then 1
    else -1

let dnfRM ( t : Ast.term ) = List.sort compare (List.concat (List.map simplify (dnfMu t)))
let dnfRM1 ( t : Ast.term ) = List.concat (List.map simplify (dnfMu t))

(* single normal form => type *)
(*let snf2t (p,n) : Ast.term =
    let f1 a b = `Cap(a,b) in 
    let f2 a b = `Cap(a, `Not(b)) 
    in
    List.fold_left f2 (List.fold_left f1 `Any p) n *)

(*let snf2t' (p,n) : Ast.term =
    let f1 a b = `Cap(a,b) in 
    let f2 a b = `Cup(a,b) in
    `Cap( List.fold_left f1 `Any p, 
       `Not(List.fold_left f2 (`Not (`Any)) n) ) *)

let snf2t (p,n) : Ast.term =
    let f1 a b = `Cap(a,b) in 
    let f2 a b = `Cap(a, `Not(b)) in
    let f3 p = match p with
      |[] -> `Any
      |[a] -> a
      |th::tl -> List.fold_left f1 th tl
    in let f4 n = match n with
      |[] -> `Any
      |[a] -> `Not(a)
      |th::tl -> List.fold_left f2 (`Not(th)) tl
    in match (p,n) with
    |([],[]) -> `Any
    |([],n) -> f4 n
    |(p,[]) -> f3 p
    |(p,n) -> `Cap(f3 p, f4 n)

(* normal forms => type *)
(*let nfs2t nfs : Ast.term =
    let f3 a b = `Cup(a,b) in
    if nfs = [] then `Not(`Any)
    else List.fold_left f3 (`Not(`Any)) (List.map snf2t nfs)*)

let nfs2t nfs : Ast.term =
    match nfs with
    |[] -> `Not(`Any)
    |[(p,n)] -> snf2t (p,n)
    |(p,n)::tl -> List.fold_left (fun a b -> `Cup(a,b)) (snf2t (p,n)) (List.map snf2t tl)

let is_any = function `Any -> true | _ -> false
let is_empty = function `Not(`Any) -> true | _ -> false

module StringSet = Set.Make(String)
let rec simple_empty t =
  match t with
  | `Cup (t1, t2) ->
      let st1,v1 = simple_empty t1 in
      let st2,v2 = simple_empty t2 in
      if is_empty st1 then st2,v2 else
        if is_empty st2 then st1,v1 else
          if is_any st1 || is_any st2 then `Any, StringSet.empty
          else `Cup (st1, st2), (StringSet.union v1 v2)
  | `Cap (t1, t2) ->
      let st1, v1 = simple_empty t1 in
      let st2, v2 = simple_empty t2 in
      if is_any st1 then st2, v2 else
        if is_any st2 then st1, v1 else
          if is_empty st1 || is_empty st2 then `Not(`Any), StringSet.empty
          else `Cap (st1, st2), (StringSet.union v1 v2)
  | `Not t -> let st, v = simple_empty t in `Not(st), v
  | `Arrow (t1, t2) ->
            let st1,v1 = simple_empty t1 in
            let st2,v2 = simple_empty t2 in
            `Arrow (st1, st2), (StringSet.union v1 v2)
  | `Prod(t1, t2) ->
      let st1, v1 = simple_empty t1 in
      let st2, v2 = simple_empty t2 in
      if is_empty st1 || is_empty st2 then `Not(`Any), StringSet.empty
      else `Prod(st1, st2), (StringSet.union v1 v2)
  | `Mu(x, t) ->
      let st,v  = simple_empty t in
      if is_empty st then `Not(`Any), StringSet.empty
      else if StringSet.mem x v then `Mu(x, st), (StringSet.remove x v)
      else st,(StringSet.remove x v)
  | `MVar x -> `MVar x, StringSet.singleton x
  | x -> x, StringSet.empty

let simple0 t = fst (simple_empty (nfs2t (dnfRM1 t))) (*(dnfMu t)*)

(* generate a fresh variable *)
let fresh =
  let counter = ref 0 in
  fun dep ->
      incr counter;
      Printf.sprintf "__var_%s_%d" dep !counter

(* new mu variable *)
let fresh_mu = 
  let counter_mu = ref 0 in
  fun dep ->
      incr counter_mu;
      Printf.sprintf "__mvar_%s_%d" dep !counter_mu
(* rename mu variables to make distinguish *)
let rename_mu t = 
    let rec aux = 
      let rec rename_mu' x s = function (* rename x as s in t *)
        |`Mu(x',t') -> if x' = x then `Mu(x',t') else `Mu(x', rename_mu' x s t')
        |`MVar x' -> if x' = x then `MVar s else `MVar x'
        |`Arrow(t1,t2) -> `Arrow(rename_mu' x s t1, rename_mu' x s t2)
        |`Prod(t1,t2)  -> `Prod(rename_mu' x s t1, rename_mu' x s t2)
        |`Cup(t1,t2)   -> `Cup(rename_mu' x s t1, rename_mu' x s t2)
        |`Cap(t1,t2)   -> `Cap(rename_mu' x s t1, rename_mu' x s t2) 
        |`Not(t')       -> `Not(rename_mu' x s t') 
	| t            -> t
      in function 
        |`Mu(x',t') -> let s = fresh_mu x' in `Mu(s, aux (rename_mu' x' s t'))         
        |`Arrow(t1,t2) -> `Arrow(aux t1, aux t2)
        |`Prod(t1,t2)  -> `Prod(aux t1, aux t2)
        |`Cup(t1,t2)   -> `Cup(aux t1, aux t2)
        |`Cap(t1,t2)   -> `Cap(aux t1, aux t2) 
        |`Not(t')       -> `Not(aux t') 
	| t            -> t
     in aux t 

(* toplevel mu variables *)
let tlmuv t =     
    let rec aux acc = function 
        |`MVar s -> s::acc
        |`Cup(t1,t2) -> aux (aux acc t1) t2
        |`Cap(t1,t2) -> aux (aux acc t1) t2
        |`Not(t1)    -> aux acc t1
        |`Mu(x,t)   -> aux acc t
        |_ -> acc
    in aux [] t

(* unfold a recursive type once s.t. no top-level mu operator *)
let unfold_once mut =
  let rec aux_unfold tbl mut =
    match mut with
    |`MVar s as t  -> begin try List.assoc s tbl with Not_found -> t end 
    |`Arrow(t1,t2) -> `Arrow(aux_nonfold tbl t1,aux_nonfold tbl t2)
    |`Prod(t1,t2)  -> `Prod (aux_nonfold tbl t1,aux_nonfold tbl t2)
    |`Cup(t1,t2)   -> `Cup  (aux_unfold  tbl t1,aux_unfold  tbl t2) 
    |`Cap(t1,t2)   -> `Cap  (aux_unfold  tbl t1,aux_unfold  tbl t2)
    |`Not(t)       -> `Not  (aux_unfold  tbl t)
    |`Mu(s,t)      -> 
          let tbl0 = (s,(`MVar s))::tbl in
          let mus = aux_nonfold tbl0 t in (* s is not at the top level in t *)
          let tbl1 = (s,(`Mu(s,mus)))::tbl in aux_unfold tbl1 t
    |t             -> t 
  and aux_nonfold tbl mut =
    match mut with
    |`MVar s as t  -> begin try List.assoc s tbl with Not_found -> t end 
    |`Arrow(t1,t2) -> `Arrow(aux_nonfold tbl t1,aux_nonfold tbl t2)
    |`Prod(t1,t2)  -> `Prod (aux_nonfold tbl t1,aux_nonfold tbl t2)
    |`Cup(t1,t2)   -> `Cup  (aux_nonfold tbl t1,aux_nonfold tbl t2) 
    |`Cap(t1,t2)   -> `Cap  (aux_nonfold tbl t1,aux_nonfold tbl t2)
    |`Not(t)       -> `Not  (aux_nonfold tbl t)
    |`Mu(s,t)      -> let tbl1 = (s,(`MVar s))::tbl in `Mu(s, aux_nonfold tbl1 t)
    |t             -> t 
  in aux_unfold [] mut

let dump_list ppf tlist = Custom.dump_list Ast.dump ppf tlist
(*let dumptbl ppf tbl = let (x,t) = List.hd tbl in Format.fprintf ppf "(%a -> %a )" Ast.dump x Ast.dump t
let dumptbl_list ppf tbls = Custom.dump_list dumptbl ppf tbls*)

let rec tobuffer_empty nps buf = 
   let rec aux nps buf = 
	match nps with
	|[] -> buf (* t maybe empty [] -> BBSet.add [] buf *)
	|(p,n)::nps' -> 
           let t1 = snf2t (p,n) in           
           let buf' = t1::buf in 
           aux nps' buf'
   in aux nps buf

let rec conver1 t s = match (t,s) with 
    |(`TVar (i1,s1), `TVar (i2,s2)) -> (s1 = s2) && ((i1 = i2) || (i1 = -i2)) 
    |(`Cup (t1,t2), `Cup (s1,s2))
    |(`Cap (t1,t2), `Cap (s1,s2)) 
    |(`Arrow (t1,t2), `Arrow (s1,s2))
    |(`Prod (t1,t2), `Prod (s1,s2)) ->
       (conver1 t1 s1) && (conver1 t2 s2)       
    |(`Not t1, `Not s1) -> conver1 t1 s1
    |(`MVar x1 , `MVar x2)  
    |(`Mu(x1,_), `Mu(x2,_)) ->  x1 = x2
    |(_,_) -> t = s

let membuf buf (p,n) =
    let t = snf2t (p,n) in
    let rec aux buf = 
       match buf with
       |[] -> false
       |th::buff -> if conver1 t th then true else aux buff
    in aux buf

let one = `Cup(`Cup(`Cup(`Cup(`Bool,`SingletonAny),`IntAny), `Prod(`Any,`Any)), `Arrow(`Not(`Any),`Any))
let inter1 t =  `Cap(t,one)  

let is_empty_atom (p,n) = 
      let atom_pos = function
        |`SingletonAny -> ST.full
        |`Singleton _  as t -> [[t],[]]
        | _ -> ST.empty
      and atom_neg = function 
        |`SingletonAny -> ST.empty
        |`Singleton _  as t -> [[],[t]]
        |_ -> ST.full
      in let pos = List.map atom_pos p and neg = List.map atom_neg n
      in let atom = List.fold_left ST.cap ST.full (pos@neg)
      in (ST.is_empty atom, ST.tostring atom) 
let is_empty_bool (p,n) =
      let atom_pos = function
        |`Bool -> [([`Singleton("true")],[]);([`Singleton("false")],[])]
        |`True -> [([`Singleton("true")],[])]
        |`False -> [([`Singleton("false")],[])]
        | _ -> ST.empty
      and atom_neg = function 
        |`Bool -> [([],[`Singleton("true");`Singleton("false")])]
        |`True -> [([],[`Singleton("true")])]
        |`False -> [([],[`Singleton("false")])]
        |_ -> ST.full
      in let pos = List.map atom_pos p and neg = List.map atom_neg n
      in let atom = List.fold_left ST.cap ST.full (pos@neg)
      in (ST.is_empty atom, ST.tostring atom) 
let is_empty_int (p,n) =
      let atom_pos = function
        |`IntAny -> Interval.any 
        |(`Left _ | `Right _ | `Bounded(_,_)) as t -> [t]
        | _ -> Interval.empty
      and atom_neg = function 
        |`IntAny -> Interval.empty
        |(`Left _ | `Right _ | `Bounded(_,_)) as t -> Interval.neg [t]
        |_ -> Interval.any
      in let pos = List.map atom_pos p and neg = List.map atom_neg n
      in let atom = List.fold_left Interval.cap Interval.any (pos@neg)
      in (Interval.is_empty atom, Interval.tostring atom)

let bigconj f s =
    let conj p = (List.fold_left (fun s t -> `Cap(s,t)) `Any p) in
    conj (List.map (fun t -> f (get_prod t)) s)


let rec eval (t, ns, ps) = 
  (*Format.fprintf Format.std_formatter "evaling: %a \n@?" Ast.dump t;
  Format.fprintf Format.std_formatter "Buffer: %a\n@?" CduceTypes.dump_list ns;*)
   let nfs = dnfRM t in   
   let (bezero, unknown) = List.partition (membuf ns) nfs in
   if List.length unknown = 0 then begin     
   (*Format.fprintf Format.std_formatter "Memoize successfully!\n@?"; *)
   (false, Basic([], "none"), ns, ps) end
   else begin 
   let unt = nfs2t unknown in
   let tmu = unfold_once unt in
   let unnfs = dnfRM tmu in 
   let ns0 = tobuffer_empty unknown ns in
   match eval_nfs (unnfs, ns0, ps) with
   |(true, v, ns', ps') -> (true, v, ns, ((unt,v)::ps))
   |(false, v, ns', ps') -> (false, v, ns', ps')
   end
and eval_nfs (nfs, ns, ps) = 
    match nfs with
    |[] -> (false, Basic([], "none"), ns, ps)
    |(p,n)::nfs' -> 
       begin match eval_nf ((p,n), ns, ps) with
       |(true, v, ns', ps') -> (true, v, ns', ps')
       |(false, v, ns', ps') -> eval_nfs (nfs',ns',ps') 
       end
and eval_nf ((p,n), ns, ps) = 
   let (pv, pc) = List.partition isvar p and (nv,nc) = List.partition isvar n in
   let pvs = List.map (function `TVar (_,s) -> s | _ -> "lab") pv in
   if List.length (pc@nc) = 0 then (true, Basic(pvs,"any"), ns, ps)
   else if List.length pc = 0 then 
      let nfs' = dnfRM (inter1 (snf2t (p,nc))) in eval_nfs (nfs', ns, ps)
   else let a = List.hd pc in (* make sure |pc| > 0 *)
   match a with
   |`Prod(_,_) -> let nc = List.filter isprod1 nc in prod ((pc,nc,pvs), ns, ps) (* product *)
   |`Arrow(_,_) -> let nc = List.filter isarrow1 nc in arrow ((pc,nc,pvs), ns, ps) (* arrow *) 
   |`SingletonAny | `Singleton _ -> (* atom *)
      let nc = List.filter isatom1 nc in 
      let (b,v) = is_empty_atom (pc,nc) in
      if b then (false, Basic([], v), ns, ps) 
      else (true, Basic(pvs, v), ns, ps) 
   |`IntAny | `Left _ | `Right _ | `Bounded(_,_) -> (* int *)
      let nc = List.filter isint1 nc in 
      let (b,v) = is_empty_int (pc,nc) in
      if b then (false, Basic([], v), ns, ps) 
      else (true, Basic(pvs, v), ns, ps) 
   |`Bool | `True  | `False -> (* bool *)
      let nc = List.filter isbool1 nc in 
      let (b,v) = is_empty_bool (pc,nc) in
      if b then (false, Basic([], v), ns, ps) 
      else (true, Basic(pvs, v), ns, ps) 
   |_ -> (true, Basic([],"anyx"), ns, ps)
and prod ((p,n,pvs), ns, ps) =
    let t1 = bigconj fst p and t2 = bigconj snd p in
    match eval (t1, ns, ps) with
    |(false, _, ns1, ps1) -> (false, Basic([],"none"), ns1, ps1)
    |(true, v1, ns1, ps1) ->
       begin match eval (t2, ns1, ps1) with
       |(false, _, ns2, ps2) -> (false, Basic([],"none"), ns2, ps2)
       |(true, v2, ns2, ps2) -> prod' (t1, v1, t2, v2, n, pvs, ns2, ps2) 
       end
and prod' (t1,v1,t2,v2,n,pvs,ns,ps) =
    match n with
    |[] -> (true, Product(pvs,v1,v2), ns, ps)
    |s :: n' ->
            let (s1,s2) = get_prod s in
            let t1' = `Cap(t1, `Not(s1)) in
            let t2' = `Cap(t2, `Not(s2)) in
            let (b1, v11, ns1, ps1) = eval(t1',ns,ps) in            
            if b1 then 
               begin match prod'(t1',v11,t2,v2,n',pvs,ns1,ps1) with
               |(true,v,ns2,ps2) -> (true, v, ns2, ps2)
               |(false,_,ns2,ps2) -> 
                   let (b2, v22, ns3, ps3) = eval(t2',ns2,ps2) in
                   if b2 then prod'(t1,v1,t2',v22,n',pvs,ns3,ps3) 
                   else (false, Basic([],"none"), ns3, ps3)
               end
            else 
            let (b2, v22, ns2, ps2) = eval(t2',ns1,ps1) in
            if b2 then prod'(t1,v1,t2',v22,n',pvs,ns2,ps2) 
            else (false, Basic([],"none"), ns2, ps2)
and arrow ((p,n,pvs), ns, ps) = 
   match n with
    |[] -> (true, Function(pvs,[]), ns, ps)
    |t::n' -> let (t0,s0) = get_arrow(t) in
            let (b1, v1, ns1, ps1) = eval(t0,ns,ps) in
            if b1 then
               let (bb,vv,nss,pss) = eval((`Not(s0)),ns1,ps1) in
               let v0 = if bb then vv else Basic([],"omega") in (*Basic([],"any")*)
               let (b2, v2, ns2, ps2) = arrow'(t0,v1,`Any,v0,s0,p,ns1,ps1) in
               if b2 then
                  let (b3, v3, ns3, ps3) = arrow((p,n',pvs), ns, ps) in
                  if b3 then
                     let values_union v1 v2 = match v2 with 
                        | Function(labs, l) -> Function (labs, v1::l)
                        | _ -> Function(pvs, [v1])
                     in (true, (values_union v2 v3), ns3, ps3)
                  else (false, Basic([],"none"), ns3, ps3)
               else (false, Basic([],"none"), ns2, ps2)
            else (false, Basic([],"none"), ns1, ps1)
and arrow'(t0,vt,ss,vs,s0,p,ns,ps) = 
    match p with
    |[] -> (true,Product([],vt,vs),ns,ps)
    |s :: p' ->
            let (s1,s2) = get_arrow (s) in 
            let t0' = `Cap(t0, `Not(s1)) in 
            let ss' = `Cap(ss, s2) in 
            let (b1, v1, ns1, ps1) = eval(t0',ns,ps) in            
            if b1 then 
               begin match arrow'(t0',v1,ss,vs,s0,p',ns1,ps1) with
               |(true,v,ns2,ps2) -> (true, v, ns2, ps2)
               |(false,_,ns2,ps2) -> 
                   let (b2, v2, ns3, ps3) = eval((`Cap(ss', `Not(s0))),ns2,ps2) in
                   if b2 then arrow'(t0,vt,ss',v2,s0,p',ns3,ps3) 
                   else (false, Basic([],"none"), ns3, ps3)
               end
            else 
            let (b2, v2, ns2, ps2) = eval((`Cap(ss', `Not(s0))),ns1,ps1) in
            if b2 then arrow'(t0,vt,ss',v2,s0,p',ns2,ps2) 
            else (false, Basic([],"none"), ns2, ps2)

let sub2empty t s = rename_mu (`Cap (t, `Not(s)))
let sub t s = eval((sub2empty t s), [],[]) 
let sub2 t s = let (b,v,ns,ps) = eval((sub2empty t s), [],[]) in not b
let isempty t = eval(t,[],[])
let isempty2 t = let (b,v,ns,ps) = eval(t,[],[]) in not b

let simple t = simple0 t
(*    let nfs = dnfRM1 t in
    let rec aux_union l_pre l_cur = 
        match l_cur with
        |[] -> l_pre
        |(p,n)::l_next ->
          let t_cur = snf2t (p,n) in
          let t_left = nfs2t (l_pre@l_next) in
          if sub2 t_cur t_left then aux_union l_pre l_next
          else aux_union (l_pre@[(p,n)]) l_next
    in let rec aux_inter_p p_pre p_cur n =
        match p_cur with
        |[] -> p_pre
        |a::p_next -> 
          let t_left = snf2t (p_pre@p_next, n) in
          if sub2 t_left a then aux_inter_p p_pre p_next n
          else aux_inter_p (p_pre@[a]) p_next n
    in let rec aux_inter_n n_pre n_cur p =
        match n_cur with
        |[] -> n_pre
        |a::n_next ->
          let t_left = snf2t (p, n_pre@n_next) in 
          if sub2 t_left (`Not(a)) then aux_inter_n n_pre n_next p
          else aux_inter_n (n_pre@[a]) n_next p
    in let aux_inter (p,n) =
       if List.length p > 1 then
          let p1 = aux_inter_p [] p n in
          let n1 = aux_inter_n [] n p1 in (p1,n1)
       else (p,n)
    in let rec aux_nfs nfs = Format.fprintf Format.std_formatter "aux_nfs: %a \n@?" Ast.dump (nfs2t nfs);
       let aux_inter_prod (p,n) = aux_inter (aux_prod (p,n)) in
       match nfs with
       |[] -> `Not(`Any)
       |[(p,n)] -> snf2t (aux_inter_prod (p,n))
       |_  -> 
          let nfs0 = aux_union [] nfs in
          let nfs1 = List.map aux_inter_prod nfs0 in
          nfs2t nfs1 
     and aux_prod (p,n) =
       let (prods, nonprods) = List.partition isprod1 p in
       if List.length prods > 0 then
          let t1 = bigconj fst prods and t2 = bigconj snd prods in
          let t11 = aux_nfs (dnfRM1 t1) and t22 = aux_nfs (dnfRM1 t2) in
          (`Prod(t11,t22)::nonprods, n)
       else (p,n)
     in let tt = aux_nfs nfs in Format.fprintf Format.std_formatter "done in simple \n@?"; tt
*)

(* move the union in t from inside to outside?? *)
let rec exp_union t =
    let nfs = dnfRM1 t in
    let rec prod_n (t1, t2, n) = 
       match n with
       |[] -> [(t1,t2)]
       |s::n' ->
          let (s1,s2) = get_prod s in
          let t1' = `Cap(t1, `Not(s1)) in
          let t2' = `Cap(t2, `Not(s2)) in
           (prod_n (t1,t2',n')) @ (prod_n (t1',t2, n'))
    in
    let rec prod_union (t1,t2) =
       let nfs1 = exp_union t1 and nfs2 = exp_union t2 in
       let fab a b = [(snf2t a, snf2t b)] in
       let fal l a = List.concat (List.map (fab a) l) in
       List.concat (List.map (fal nfs2) nfs1) 
    in
    let aux (p,n) =
       let (pp, pnp) = List.partition isprod1 p in
       let (np, nnp) = List.partition isprod1 n in
       if (List.length pp > 0) then (* && (List.length nnp = 0)*)
          let t1 = bigconj fst pp and t2 = bigconj snd pp in
          let prods1 = prod_n (t1,t2,np) in
          let prods2 = List.concat (List.map prod_union prods1)
          in List.map (fun (t1,t2) -> ([`Prod(t1,t2)]@pnp,nnp)) prods2
       else [(p,n)]
    in List.concat (List.map aux nfs)
    

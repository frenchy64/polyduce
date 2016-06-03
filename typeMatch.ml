open Ast
open Support.Error

module SL = SubType.AL


(* unfold the recursive type variables in t w.r.t tbl *)
let unfold_tbl t tbl = 
    let rec aux tbl = function
        |`MVar s as t  -> begin try List.assoc s tbl with Not_found -> t end 
        |`Arrow(t1,t2) -> `Arrow(aux tbl t1,aux tbl t2)
        |`Prod(t1,t2)  -> `Prod (aux tbl t1,aux tbl t2)
        |`Cup(t1,t2)   -> `Cup  (aux tbl t1,aux tbl t2) 
        |`Cap(t1,t2)   -> `Cap  (aux tbl t1,aux tbl t2)
        |`Not(t)       -> `Not  (aux tbl t)
        |`Mu(s,t)      -> let tbl1 = (s,(`MVar(s)))::tbl in `Mu(s, aux tbl1 t) 
        |t             -> t
    in
    if tbl = [] then t else aux tbl t 


(* occurrences *)
let rec occpos t = match t with
       |`Arrow(t1,t2)  -> t::((occneg t1)@(occpos t2))
       |`Prod(t1,t2)   
       |`Cup(t1,t2)    
       |`Cap(t1,t2)    -> t::((occpos t1)@(occpos t2))
       |`Not(t1)       -> t::(occneg t1)
       |`Mu(s,t1)      -> 
           let negs = occneg t1 in
           if List.exists (Ast.equal (`MVar s)) negs then negs@(t::(occpos t1)) (* List.mem *)
           else t::(occpos t1)
       |t              -> [t]
and occneg t = match t with
       |`Arrow(t1,t2)  -> (occpos t1)@(occneg t2)
       |`Prod(t1,t2)   
       |`Cup(t1,t2)    
       |`Cap(t1,t2)    -> (occneg t1)@(occneg t2)
       |`Not(t1)       -> occpos t1
       |`Mu(s,t1)      -> 
           let negs = occneg t1 in
           if List.exists (Ast.equal  (`MVar s)) negs then negs@(occpos t1)
           else negs
       |t              -> []

let isposin t t' = List.exists (Ast.equal t') (occpos t)
let isnegin t t' = List.exists (Ast.equal t') (occneg t)

(* positive and negative polymorphic type variables *)
let rec varspos t vs = match t with
       |`Arrow(t1,t2)  -> varsneg t1 (varspos t2 vs)
       |`Prod(t1,t2)   
       |`Cup(t1,t2)    
       |`Cap(t1,t2)    -> varspos t1 (varspos t2 vs)
       |`Not(t1)       -> varsneg t1 vs
       |`Mu(s,t1)      -> 
           let vs' = varspos t1 vs in
           let negs = occneg t1 in
           if List.exists (Ast.equal (`MVar s)) negs then varsneg t1 vs' 
           else vs'
       |`TVar (i,s) as v -> if i >= 0 then SL.cup [v] vs else vs
       |_            -> vs

and varsneg t vs = match t with
       |`Arrow(t1,t2)  -> varspos t1 (varsneg t2 vs)
       |`Prod(t1,t2)   
       |`Cup(t1,t2)    
       |`Cap(t1,t2)    -> varsneg t1 (varsneg t2 vs)
       |`Not(t1)       -> varspos t1 vs
       |`Mu(s,t1)      -> 
           let vs' = varsneg t1 vs in
           let negs = occneg t1 in
           if List.exists (Ast.equal  (`MVar s)) negs then varspos t1 vs'
           else vs';
       |_  -> vs

(* only positive and only negative polymorphic type variables *)
let varsmono t =
     let pos = varspos t [] and neg = varsneg t [] in
     ((SL.diff pos neg), (SL.diff neg pos))

let subst_smp t tbl =
    let rec aux tbl = function
        |`TVar(_,_) as t-> begin try SubType.assoc t tbl with Not_found -> t end (* List.assoc *)
        |`Arrow(t1,t2)  -> `Arrow(aux tbl t1,aux tbl t2)
        |`Prod(t1,t2)   -> `Prod (aux tbl t1,aux tbl t2)
        |`Cup(t1,t2)    -> 
              let t11 = aux tbl t1 and t22 = aux tbl t2 in
              if SubType.sub2 t11 t22 then t22
              else if SubType.sub2 t22 t11 then t11
              else `Cup (t11, t22) 
        |`Cap(t1,t2)    ->
              let t11 = aux tbl t1 and t22 = aux tbl t2 in
              if SubType.sub2 t11 t22 then t11
              else if SubType.sub2 t22 t11 then t22
              else `Cap  (t11, t22)
        |`Not(t)        -> 
              let tt = aux tbl t in
              if SubType.isempty2 tt then `Any
              else if SubType.isempty2 (`Not (tt)) then `Not(`Any)
              else `Not(tt)
        |`Mu(x,t)       -> `Mu   (x,aux tbl t) 
        |t              -> t
    in
    if tbl = [] then t else aux tbl t 


let minimal t delta =
    let (pos', neg') = varsmono t in
    let pos = SL.diff pos' delta and neg = SL.diff neg' delta in
    let totbl l b = List.map (fun a -> (a,b)) l in
    let tbl = (totbl pos (`Not(`Any))) @ (totbl neg (`Any)) in
    (*SubType.subst_mark t tbl*) subst_smp t tbl

(* no type variables in negation *)
let isdomain t =   
    let rec pos1 t = 
      match t with
      |`Cup(t1,t2) | `Cap(t1,t2) -> (pos1 t1) && (pos1 t2)
      |`Prod(t1,t2)| `Arrow(t1,t2) -> (pos1 (SubType.simple t1)) && (pos1 (SubType.simple t2))
      |`Not(t1) -> neg1 t1
      |`Mu(s,t1) -> 
           (*let ttt = isnegin t1 (`MVar(s)) in Format.fprintf Format.std_formatter ">> %s occurs negative in %a? %s \r\n@?" s Ast.dump t1 (string_of_bool (ttt));*)
           let neg = isnegin t1 (`MVar(s)) in
           let tt = if neg then (unfold_tbl t1 [(s,t1)]) else t1 in
           pos1 (SubType.simple tt)
      |_ -> true
    and neg1 t =
      match t with
      |`Cup(t1,t2) | `Cap(t1,t2) -> (neg1 t1) && (neg1 t2)
      |`Prod(t1,t2)| `Arrow(t1,t2) -> (neg1 (SubType.simple t1)) && (neg1 (SubType.simple t2))
      |`Not(t1) -> neg1 t1
      |`Mu(s,t1) -> 
           (*let ttt = isnegin t1 (`MVar(s)) in Format.fprintf Format.std_formatter ">> %s occurs negative in %a? %s \r\n@?" s Ast.dump t1 (string_of_bool (ttt));*)
           let neg = isnegin t1 (`MVar(s)) in
           let tt = if neg then (unfold_tbl t1 [(s,t1)]) else t1 in
           neg1 (SubType.simple tt)
      |`TVar _ -> false
      |_ -> true
    in pos1 (SubType.simple t)

let rec isground t =
    match t with
      |`Cup(t1,t2) | `Cap(t1,t2) 
      |`Prod(t1,t2)| `Arrow(t1,t2) -> (isground t1) && (isground t2)
      |`Not(t1) -> isground t1
      |`Mu(_,t1)-> isground t1
      |`TVar _ -> false
      |_ -> true 

(* ceiling and floor *)
let ceiling t = 
   let rec pos t =
     match t with 
      |`Cup(t1,t2) -> `Cup(pos t1, pos t2)
      |`Cap(t1,t2) -> `Cap(pos t1, pos t2)
      |`Prod(t1,t2)-> `Prod(pos t1, pos t2) 
      |`Arrow(t1,t2) -> `Arrow(neg t1, pos t2)
      |`Not(t1) -> `Not(neg t1)
      |`Mu(s,t1)->  
         if (not (isground t1)) && (isnegin t1 (`MVar(s))) then 
         `Mu(s, pos (unfold_tbl t1 [(s,t1)])) 
         else `Mu(s, pos t1)
      |`TVar _ -> `Any
      |t -> t 
   and neg t =
     match t with 
      |`Cup(t1,t2) -> `Cup(neg t1, neg t2)
      |`Cap(t1,t2) -> `Cap(neg t1, neg t2)
      |`Prod(t1,t2)-> `Prod(neg t1, neg t2) 
      |`Arrow(t1,t2) -> `Arrow(pos t1, neg t2)
      |`Not(t1) -> `Not(pos t1)
      |`Mu(s,t1)->  
         if (not (isground t1)) && (isnegin t1 (`MVar(s))) then 
         `Mu(s, neg (unfold_tbl t1 [(s,t1)])) 
         else `Mu(s, neg t1)
      |`TVar _ -> `Not(`Any)
      |t -> t 
   in pos t

let floor t = 
   let rec pos t =
     match t with 
      |`Cup(t1,t2) -> `Cup(pos t1, pos t2)
      |`Cap(t1,t2) -> `Cap(pos t1, pos t2)
      |`Prod(t1,t2)-> `Prod(pos t1, pos t2) 
      |`Arrow(t1,t2) -> `Arrow(neg t1, pos t2)
      |`Not(t1) -> `Not(neg t1)
      |`Mu(s,t1)->  
         if (not (isground t1)) && (isnegin t1 (`MVar(s))) then 
         `Mu(s, pos (unfold_tbl t1 [(s,t1)])) 
         else `Mu(s, pos t1)
      |`TVar _ -> `Not(`Any)
      |t -> t 
   and neg t =
     match t with 
      |`Cup(t1,t2) -> `Cup(neg t1, neg t2)
      |`Cap(t1,t2) -> `Cap(neg t1, neg t2)
      |`Prod(t1,t2)-> `Prod(neg t1, neg t2) 
      |`Arrow(t1,t2) -> `Arrow(pos t1, neg t2)
      |`Not(t1) -> `Not(pos t1)
      |`Mu(s,t1)->  
         if (not (isground t1)) && (isnegin t1 (`MVar(s))) then 
         `Mu(s, neg (unfold_tbl t1 [(s,t1)])) 
         else `Mu(s, neg t1)
      |`TVar _ -> `Any
      |t -> t 
   in pos t


(* return true if con1 is a subset of con2 : the solutions to con1 include those to con2 *)
(* con2 is more restricted than con1 *)
let sub_constrs (con1,u1) (con2,u2) =
  let rec aux con1 con2 =
     match (con1,con2) with
     |(a,ta1,ta2,ca)::con11, (b,tb1,tb2,cb)::con22 ->
       let c = Ast.compare a b in
       if c = 0 then
          if (SubType.sub2 ta1 tb1 && SubType.sub2 tb2 ta2) then aux con11 con22
          else false
        else if c < 0 then false
        else aux con1 con22
     |[],_ -> true
     |_ -> false
   in aux con1 con2

(* return true if there exists a subset of con in l *)
let rec exist_sub con l =
    match l with 
    |[] -> false
    |con'::l' -> if sub_constrs con' con then true else exist_sub con l'

(* remove those more restricted and redundant constraint sets *)
let constrs_simple l =
    let rec aux l_cur l_new =
    match l_cur with
    |[] -> l_new
    |con::l_nxt ->
       let l_new = if exist_sub con (l_new@l_nxt) then l_new else l_new@[con] in
       aux l_nxt l_new
    in aux l []

(* the union of two sets of constraint sets *)
let constrs_union s1 s2 = 
   match (s1,s2) with
   |([], _) -> s2
   |(_, []) -> s1
   |([([],_)], _)
   |(_, [([],_)]) -> [([],1)]  
   |(l1, l2) -> (*Cons (l1 @ l2)*)
     let mayadd l con = not (exist_sub con l) in
     let l22 = List.filter (mayadd l1) l2 in
     let l11 = List.filter (mayadd l22) l1 in
     l11@l22

(* the intersection of two constraint sets *)
let rec join_constr l1 l2 =
     match (l1,l2) with
     |(a,ta1,ta2,ca)::tl1, (b,tb1,tb2,cb)::tl2 ->
       let c = Ast.compare a b in
       if c = 0 then
         begin match (ca,cb) with
         |(1,1) -> 
            let t1 = (*if SubType.sub2 ta1 *)SubType.simple (`Cup(ta1,tb1)) in
            (*let m = if SubType.sub2 t1 ta1 then 0 else 1 in *)
            (a,t1,ta2,1) :: (join_constr tl1 tl2)
         |(1,2) -> (a,ta1,tb2,3) :: (join_constr tl1 tl2)
         |(1,3) -> 
            let t1 = SubType.simple (`Cup(ta1,tb1)) in
            (a,t1,tb2,3) :: (join_constr tl1 tl2)
         |(2,1) -> (a,tb1,ta2,3) :: (join_constr tl1 tl2)
         |(2,2) -> 
            let t2 = SubType.simple (`Cap(ta2,tb2)) in
            (a,ta1,t2,2) :: (join_constr tl1 tl2)
         |(2,3) -> 
            let t2 = SubType.simple (`Cap(ta2,tb2)) in
            (a,tb1,t2,3) :: (join_constr tl1 tl2)
         |(3,1) -> 
            let t1 = SubType.simple (`Cup(ta1,tb1)) in
            (a,t1,ta2,3) :: (join_constr tl1 tl2)  
         |(3,2) -> 
            let t2 = SubType.simple (`Cap(ta2,tb2)) in
            (a,ta1,t2,3) :: (join_constr tl1 tl2)
         |(_,_) -> 
            let t1 = SubType.simple (`Cup(ta1,tb1)) in
            let t2 = SubType.simple (`Cap(ta2,tb2)) in
            (a,t1,t2,3) :: (join_constr tl1 tl2)
          end
        else if c < 0 then (a,ta1,ta2,ca) :: (join_constr tl1 l2)
        else (b,tb1,tb2,cb) :: (join_constr l1 tl2)
     |[],_ -> l2
     |_ -> l1

(* the intersection of two sets of constraint sets *)
and constrs_inter ls1 ls2 = 
   match (ls1,ls2) with
   |([], _) -> []
   |(_, []) -> []
   |([([],_)], _) -> ls2
   |(_, [([],_)]) -> ls1
   |(l1, l2) -> 
      let joinlist la lb = 
	let union (a,ua) (b,ub) = (join_constr a b, ua*ub) in
  	let unionlist l a = List.map (union a) l in
	List.flatten (List.map (unionlist lb) la)
      in (joinlist l1 l2)
      (*let l = (joinlist l1 l2) in
      constrs_saturate (Cons l)*)

(* if contain (A <= 0), then true *)
let constrs_iszero (l,u) =
  let rec aux l = 
    match l with
    |[] -> false
    |(a,t1,t2,c)::tl -> if SubType.isempty2 t2 then true else aux tl
  in aux l

(* if contain contraint from trivial type (ie, (0->t) or (0,t) or (t,0)), then true *)
let constrs_isuseless (l,u) = if u = 0 then true else false


(* -(p,n) to type *)
let snf2t_neg (p,n) = 
    let f1 a b = `Cup(a, `Not(b)) in 
    let f2 a b = `Cup(a,b) in
    let f3 p = match p with
      |[] -> `Not(`Any)
      |[a] -> `Not(a)
      |th::tl -> List.fold_left f1 (`Not(th)) tl
    in let f4 n = match n with
      |[] -> `Not(`Any)
      |[a] -> a
      |th::tl -> List.fold_left f2 th tl
    in match (p,n) with
    |([],[]) -> `Not(`Any)
    |([],n) -> f4 n
    |(p,[]) -> f3 p
    |(p,n) -> `Cup(f3 p, f4 n)


(* has mu variables *)
let hasmuv t =     
    let rec aux = function 
        |`MVar s -> true
        |`Cup(t1,t2) -> aux t1 || aux t2 
        |`Cap(t1,t2) -> aux t1 || aux t2
        |`Not(t1)    -> aux t1
        |`Mu(x,t)   -> true
        |`Arrow(t1,t2) -> aux t1 || aux t2
        |`Prod(t1,t2) -> aux t1 || aux t2
        |_ -> false
    in aux t
let hasmuv1 (p,n) = 
    let rec aux l = match l with
    |[] -> false
    |th::tl -> if hasmuv th then true else aux tl
    in aux (p@n)

(* to generate a representive constraint  *)
let singleout (p,n) =
   let aux_sup a (p,n) =  [([(a, `Not(`Any), snf2t_neg (p,n), 2)], 1)] in
   let aux_inf a (p,n) =  [([(a, SubType.snf2t (p,n), `Any, 1)], 1)] in
   let rec aux_p p p_pre (o,cons) =
      match p with
      |[] -> (o, cons)
      |(`TVar(ov, _)) as hv ::p' -> 
             if (ov >= 0) && (o < 0 || ov < o) then 
                let cons' = aux_sup hv ((p_pre@p'), n) in
                aux_p p' (p_pre@[hv]) (ov, cons')
             else aux_p p' (p_pre@[hv]) (o, cons)
      | _ as h ::p' -> aux_p p' (p_pre@[h]) (o, cons)
   and aux_n n n_pre (o, cons) =
      match n with
      |[] -> (o, cons)
      |(`TVar(ov, _)) as hv ::n' -> 
             if (ov >= 0) && (o < 0 || ov < o) then 
                let cons' = aux_inf hv (p, (n_pre@n')) in
                aux_n n' (n_pre@[hv]) (ov, cons')
             else aux_n n' (n_pre@[hv]) (o, cons)
      | _ as h ::n' -> aux_n n' (n_pre@[h]) (o, cons)
   in 
   let o = -1 and cons = [] in
   aux_n n [] (aux_p p [] (o, cons))


(* order, delta *)
let rec norm (t, mem) =  
   (*Format.fprintf Format.std_formatter "\nevaling: %a \n@?" Ast.dump t;
   Format.fprintf Format.std_formatter "\nBuffer: %a\n@?" SubType.dump_list mem;*)
   let nfs = SubType.dnfRM  t in
   if List.length nfs = 0 then ([([],1)]) else
   (*let (muvs, unmuvs) = List.partition hasmuv1 nfs in 
   let (bezero, unknown1) = List.partition (SubType.membuf mem) muvs in
   let unknown = unmuvs@unknown1 in*)
   let (bezero, unknown) = List.partition (SubType.membuf mem) nfs in
   if List.length unknown = 0 then ([([],1)])
   (*begin     
   (*Format.fprintf Format.std_formatter "Memoize successfully!\n@?";*)
   (* Sets [[(((`TVar (0, SubType.fresh "Mem")), 0, t), 1)]] *)
   end*)
   else begin 
   let unt = SubType.nfs2t unknown in
   let tmu = SubType.unfold_once unt in
   let unnfs = SubType.dnfRM tmu in 
   let mem0 = SubType.tobuffer_empty unknown mem in
    norm_nfs (unnfs, mem0)
   (*match norm_nfs (unnfs, mem0) with
   |(COmega _, mem') -> (COmega 1, mem )
   |(Cons _ as cons, mem') -> (cons, mem')*)
   end

and norm_nfs (nfs, mem) =
    match nfs with
    |[] -> [([],1)]
    |(p,n)::nfs' -> (* find the heuristic number for m *)
       begin match norm_nf ((p,n), mem) with
       |[] -> []
       |cons -> 
          let (constl) = norm_nfs (nfs', mem) in
          (constrs_inter cons constl)
       end

and norm_nf ((p,n), mem) = 
   let (o, constlv) = singleout (p,n) in
   let cons =
     let (pv, pc) = List.partition SubType.isvar p and (nv,nc) = List.partition SubType.isvar n in 
     if List.length pc = 0 then ([])
     else begin match List.hd pc with (* clearly |pc| > 0 *)
     |`Prod (_) -> let nc' = List.filter SubType.isprod1 nc in norm_prod ((pc,nc'), mem) (* product *)
     |`Arrow (_)  -> let nc' = List.filter SubType.isarrow1 nc in norm_arrow ((pc,nc'), mem) (* arrow *)
     |`SingletonAny | `Singleton _ -> (* atom *)
      let nc' = List.filter SubType.isatom1 nc in
      let (b,v) = SubType.is_empty_atom (pc,nc') in
      if b then ([([],1)]) else ([])
     |`IntAny | `Left _ | `Right _ | `Bounded(_) -> (* int *)
      let nc' = List.filter SubType.isint1 nc in
      let (b,v) = SubType.is_empty_int (pc,nc') in
      if b then ([([],1)]) else ([]) 
     |`Bool | `True | `False -> (* bool *)
      let nc' = List.filter SubType.isbool1 nc in
      let (b,v) = SubType.is_empty_bool (pc,nc') in
      if b then ([([],1)]) else ([]) 
     |_ -> ([])
     end
    in
   match (constlv, cons) with
   |_, [([],i)] -> [([],i)]
   |[], _ -> cons
   |_, _ -> constlv 

and norm_prod ((p,n), mem) =
    let t1 = SubType.bigconj fst p and t2 = SubType.bigconj snd p in
    let (con1) = norm (t1, mem) in
    let (con2) = norm (t2, mem) in
    let (con0) = norm_prod' (t1, t2, n, mem) in
    ((constrs_union (constrs_union con1 con2) con0))

and norm_prod' (t1, t2, n, mem) =
    match n with
    |[] -> ([])
    |s :: n' ->
            let (s1,s2) = SubType.get_prod s in
            let t1' = `Cap(t1, `Not(s1)) in
            let t2' = `Cap(t2, `Not(s2)) in
            let (con1) = norm (t1', mem) in
            let (con2) = norm (t2', mem) in
            let (con10) = norm_prod'(t1', t2, n', mem) in
            let (con20) = norm_prod'(t1, t2', n', mem) in
            let con11 = constrs_union con1 con10 in
            let con22 = constrs_union con2 con20 in
            ((constrs_inter con11 con22))
(* 
con1 + con2 => t1 * t2 <: s1 * s2 
con10 + con20 => \E v{ss} \in n' s.t. t1 * t2 <: v{ss}
con1 + con20 => \E v{ss} \in n' s.t. t' * s' <: v{ss}   and (t1 * t2) <: ((t' ^ s1) * (s' v s2))  
con2 + con10 => \E v{ss} \in n' s.t. t' * s' <: v{ss}   and (t1 * t2) <: ((t' v s1) * (s' ^ s2)) 
counts : a[0] = 1, a[n] = (a[n-1]+1)*(a[n-1]+1)
*)

and norm_arrow ((p,n), mem) = 
    match n with
    |[] -> ([])
    |t::n' ->
            let (t0,s0) = SubType.get_arrow(t) in
            let (con1) = norm (t0, mem) in
            let (con2) = norm_arrow'(t0, `Any, s0, p, mem) in
            let (con0) = norm_arrow((p,n'), mem) in
            ((constrs_union (constrs_union con1 con2) con0))
and norm_arrow'(t0, ss, s0, p, mem) = 
    match p with
    |[] -> ([])
    |s :: p' ->
            let (s1,s2) = SubType.get_arrow (s) in 
            let t0' = `Cap(t0, `Not(s1)) in 
            let ss' = `Cap(ss, s2) in
            let (con1) = norm (t0', mem) in
            let (con2) = norm ((`Cap(ss',`Not(s0))), mem) in
            let (con10) = norm_arrow'(t0', ss, s0, p', mem) in
            let (con20) = norm_arrow'(t0, ss', s0, p', mem) in
            let con11 = constrs_union con1 con10 in
            let con22 = constrs_union con2 con20 in
            ((constrs_inter con11 con22))
(* 
con1 + con2 => s1-> s2 <: t0 -> s0 
con10 + con20 => \E ^{ss} \in p' s.t. ^{ss} <: t0 -> s0
con1 + con20 => \E ^{ss} \in p' s.t. ^{ss} <: t' -> s' and (t' ^ s1) -> (s' ^ s2) <: t0 -> s0
con2 + con10 => \E ^{ss} \in p' s.t. ^{ss} <: t' -> s' and (t' v s1) -> (s' v s2) <: t0 -> s0
*)

(* saturate a set of constraint sets *)
let rec satus mem cons =
    match cons with
    |[] -> []
    |[([],u)] -> [([],u)]
    |l -> 
       let ls = List.map (satu mem) l in
       List.fold_left constrs_union ([]) ls

(* saturate a constraint set *)
and satu mem (cs,u) =
  let rec aux cs_cur cs_pre =
      match cs_cur with
      |[] -> [(cs_pre,u)]
      |(a,ta1,ta2,ca)::cs' -> 
          if ca <> 3 then aux cs' (cs_pre@[(a,ta1,ta2,ca)])
          else 
          let nfs = SubType.dnfRM  (`Cap(ta1,`Not(ta2))) in
          (*if List.length nfs = 0 then aux cs' (cs_pre@[(a,ta1,ta2,ca,ma)])
          else*)
          let (bezero, unknown) = List.partition (SubType.membuf mem) nfs in
          if List.length unknown = 0 then aux cs' (cs_pre@[(a,ta1,ta2,ca)])
          else 
          let mem' = SubType.tobuffer_empty unknown mem in
          let css_satu = norm_nfs (unknown, []) in
         (*Format.fprintf Format.std_formatter "---evaling: %a <= %a \n@?" Ast.dump t1 Ast.dump t2;
         Format.fprintf Format.std_formatter "---Possible constraints: %a\n" Ast.dump_solus css_satu;*)
          begin match css_satu with
          |[] -> []
          |[([],u)] -> aux cs' (cs_pre@[(a,ta1,ta2,ca)])
          |_ -> 
             let l = cs_pre@[(a,ta1,ta2,ca)]@cs' in
             satus mem' (constrs_inter css_satu ([(l,u)]))
         end
  in aux cs []
     


(* return the first non-recursive constraint *)
let get_nonrecur cstr =
  let rec aux cstr cl_pre =
    match cstr with
    |[] -> ([], cl_pre)
    |(a,t1,t2,c)::tl ->
      let vs = (SubType.vars t1)@(SubType.vars t2) in
      if List.exists (Ast.equal a) vs then aux tl (cl_pre@[(a,t1,t2,c)])
      else ([(a,t1,t2,c)], cl_pre@tl)
  in aux cstr []

(* from the recursive constraints to recursive types *)
let get_recur cstr =
   let cstr2recur (a,t1,t2,c) =
      let tyva = SubType.get_tyvar a in
      let mvsa = "x_"^tyva in
      let mva = (`MVar (mvsa)) in
      let muta1 = SubType.subst_mark t1 ([(a,mva)]) in (* tyva *)
      let muta2 = SubType.subst_mark t2 ([(a,mva)]) in
      let muta = if c = 1 then `Cup(a,muta1) (* muta1 *) (* a is fresh?? *)
                 else if c = 2 then `Cap(a,muta2) (* muta2 *)
                 else (`Cup(muta1, `Cap(a,muta2)))
      in 
      let mua = (`Mu (mvsa, muta)) in
      (a,mua,mva) (* tyvaca *)
   in 
   let rec aux mul =
      match mul with
      |[] -> []
      |(s,mut,mvs)::tl ->
          let subst_muts (s1,mut1,mvs1) = 
             let mut' = SubType.subst_mark mut ([(s1,mvs1)]) in
             let mut1' = SubType.subst_mark mut1 ([(s,mut')]) in
             (s1,mut1',mvs1) in
          let mutl = List.map subst_muts tl in 
          let tbltl = aux mutl in
          let mutt = SubType.simple(SubType.subst_mark mut tbltl) in
          let mutt1 = if SubType.isempty2 mutt then (`Not(`Any)) else mutt in
          (s,mutt1)::tbltl 
    in
    let tblmvs = List.map cstr2recur cstr in
    aux tblmvs
     

(* from a constraint set to a substitution *)
let cstr2tbl cstr =
   let rec aux cstr =
      match cstr with
      |[] -> []
      |_ ->
        let (top, tl) = get_nonrecur cstr in
        if List.length top = 0 then get_recur cstr
        else begin 
        let (a,t1,t2,c) = List.hd top in
        let fresha a = 
		match a with
		| `TVar(i,s) -> `TVar(i, SubType.fresh s) 
		| _ -> failwith "fresh type variable"
	in 
        let tyta = match a with
                   |`TVar(0,_) -> t1
                   |_ -> let fa = fresha a in SubType.simple (`Cup(t1,`Cap(fa,t2)))
        in
        let tbla = [(a,tyta)] in (*tyva *)
        let subst_cstr (a,t1,t2,c) = 
            let t11 = SubType.subst_mark t1 tbla in
            let t22 = SubType.subst_mark t2 tbla in
            (a,t11,t22,c) in
        let ctl = List.map subst_cstr tl in 
        let tbltl = aux ctl in
        let tyta1 = SubType.simple(SubType.subst_mark tyta tbltl) in
        (a,tyta1)::tbltl
        (*let tbl = (a,tyta1)::tbltl (* tyva *) in
        Format.fprintf Format.std_formatter "\nSubstitutions: %a\n@?" Ast.dump_substs ([tbl]); tbl*)
       end
    in aux cstr

(* from a set of constraint sets to substitutions *)
let cstrs2tbls cstrs =
   match cstrs with
   |[] -> []
   |ls ->
      let aux (l,u) = cstr2tbl l in
      List.map aux ls
(*
(* find constraint sets for s <= t *)
let matching t s source =
   (*if source >= 3 then *)
    let tt = tyfrom t 1 and ss = tyfrom s 2 in 
    let ts = (`Cap(ss, `Not(tt))) in (* SubType.rename_mu *)
    match eval(ts, source, 1, [],[]) with
    |(COmega i, ns, ps) -> COmega i
    |(Cons l, ns, ps) ->  Cons (constrs_simple l) (* *)

(* find constraint sets for s <= t with filter *)
let matchingF t s source =
   (*if source >= 3 then *)
    let tt = tyfrom t 1 and ss = tyfrom s 2 in 
    let ts = (`Cap(ss, `Not(tt))) in (* SubType.rename_mu *)
    match eval(ts, source, 1, [],[]) with
    |(COmega i, ns, ps) -> COmega i
    |(Cons l, ns, ps) -> (* Sets l *)(*(sort_constr l)*)
         let (useless, useful) = List.partition constrs_isuseless (constrs_simple l) in
         let (zero,nonzero) = List.partition constrs_iszero useful in
         if List.length nonzero > 0 then Cons nonzero 
         else if List.length zero > 0 then Cons zero
         else Cons useless

*)



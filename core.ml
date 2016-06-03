open Ast
open Support.Error

module SL = SubType.AL

exception NoRuleApplies 
exception PiArguError
exception DivZero

let isnumericval e = match e with
    |TmInt(_,_) -> true
    |_ -> false

let getint e = match e with
    |TmInt(_,v) -> v
    |_ -> 0 (* error fi*)

let iszero e = match e with
    |TmInt(_,v) -> if v == 0 then true else false
    |_ -> false

let isconst e = match e with
    | TmBool(_,_) -> true
    | TmInt (_,_) -> true
    | TmNil _ -> true
    | _ -> false

let const2bool e = match e with
    | TmBool(_,b) -> b
    | TmInt(_,v) -> not (v == 0)
    | _ -> false (* error *)

let rec isval e = match e with
    | TmNil _ -> true
    | TmBool(_,_) -> true
    | TmInt(_,_) -> true
    | TmPair(_,e1,e2) -> (isval e1) && (isval e2)
    (*| TmVar(_,_) -> true*)
    | TmFun(_,_,_,_,_) -> true
    | _ -> false (* function?? error *)

let rec isnonfunval e = match e with
    | TmNil _ -> true
    | TmBool(_,_) -> true
    | TmInt(_,_) -> true
    | TmPair(_,e1,e2) -> (isnonfunval e1) && (isnonfunval e2)
    | TmVar(_,_) -> true
    (*| TmFun(_,_,_,_,_) -> true*)
    | _ -> false (* function?? error *)

let redinfun e = not (isnonfunval e)

(* 
renaming the type variables in t
*)
let typerenaming t mono poly k =
    let find_order order v =
        try List.assoc v order with Not_found -> -1
    in
    let rec aux t mono poly k =
        match t with
        |`Arrow(t1,t2) -> 
            let (t1',poly1,k1) = aux t1 mono poly k in
            let (t2',poly2,k2) = aux t2 mono poly1 k1 in
            (`Arrow(t1',t2'), poly2, k2)
        |`Prod(t1,t2)  ->
            let (t1',poly1,k1) = aux t1 mono poly k in
            let (t2',poly2,k2) = aux t2 mono poly1 k1 in
            (`Prod(t1',t2'), poly2, k2)
        |`Cup(t1,t2)   ->
            let (t1',poly1,k1) = aux t1 mono poly k in
            let (t2',poly2,k2) = aux t2 mono poly1 k1 in
            (`Cup(t1',t2'), poly2, k2)
        |`Cap(t1,t2)  ->
            let (t1',poly1,k1) = aux t1 mono poly k in
            let (t2',poly2,k2) = aux t2 mono poly1 k1 in
            (`Cap(t1',t2'), poly2, k2)
        |`Not(t1)  ->
            let (t1',poly1,k1) = aux t1 mono poly k in
            (`Not(t1'), poly1, k1)  
        |`Mu(s,t1)   -> 
            let (t1',poly1,k1) = aux t1 mono poly k in
            (`Mu(s,t1'), poly1, k1) 
        |`TVar (i,s) as v -> 
            let mi = find_order mono v in
            if mi >= 0 then (`TVar(-mi, s), poly, k)
            else let pi = find_order poly v in
            if pi >= 0 then (`TVar(pi,s), poly, k)
            else let poly' = (v,k)::poly in
            (`TVar(k,s), poly', k+1)
        |_ -> (t, poly, k)
      in aux t mono poly k

let funrenaming ts mono poly k =  
  let rec aux ts mono poly k =
    match ts with 
    |[] -> ([],poly,k)
    |(s1,s2)::tl -> 
       let (s1',poly1,k1) = typerenaming s1 mono poly k in
       let (s2',poly2,k2) = typerenaming s2 mono poly1 k1 in
       let (tl',poly3,k3) = aux tl mono poly2 k2 in
       ((s1',s2')::tl', poly3,k3)
  in aux ts mono poly k

(* 
renaming the type variables in e, starting from k
*)
let termrenaming e k =
  let rec aux e delta k =
    match e with
    (* bool *)
    | TmNil fi -> (e,k)  
    | TmBool(fi,b) -> (e,k)
    | TmBoolAnd (fi,e1,e2) -> 
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmBoolAnd (fi,e1',e2') in
        (e',k2)
    | TmBoolOr (fi,e1,e2) -> 
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmBoolOr (fi,e1',e2') in
        (e',k2)
    | TmBoolNeg (fi,e1) ->
        let (e1',k1) = aux e1 delta k in
        let e' = TmBoolNeg (fi,e1') in
        (e',k1)
    (* int *)
    | TmInt(fi,i) -> (e,k)
    | TmIntAdd (fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntAdd (fi,e1',e2') in
        (e',k2)
    | TmIntMinus (fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntMinus (fi,e1',e2') in
        (e',k2)
    | TmIntTimes (fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntTimes (fi,e1',e2') in
        (e',k2)
    | TmIntDiv (fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntDiv (fi,e1',e2') in
        (e',k2)
    | TmIntMod (fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntMod (fi,e1',e2') in
        (e',k2)
    | TmIntUMinus (fi,e1) ->  
        let (e1',k1) = aux e1 delta k in
        let e' = TmIntUMinus (fi,e1') in
        (e',k1)
    | TmIntLt(fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntLt (fi,e1',e2') in
        (e',k2)
    | TmIntEq(fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmIntEq (fi,e1',e2') in
        (e',k2)
    (* product *)
    | TmPair(fi,e1,e2) ->  
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmPair (fi,e1',e2') in
        (e',k2)
    | TmPi1(fi,e1) ->  
        let (e1',k1) = aux e1 delta k in
        let e' = TmPi1 (fi,e1') in
        (e',k1)
    | TmPi2(fi,e1) ->  
        let (e1',k1) = aux e1 delta k in
        let e' = TmPi2 (fi,e1') in
        (e',k1)
    (* arrow *)
    | TmVar(fi,x) -> (e,k)
    | TmFun(fi,f,t,x,e1) -> 
       let (t',poly1,k1) = funrenaming t delta [] k in
       let delta1 = poly1@delta in
       let (e1',k2) = aux e1 delta1 k1 in
       let e' = TmFun(fi,f,t',x,e1') in
       (e',k2)
    | TmApp(fi,e1,e2) -> 
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmApp (fi,e1',e2') in
        (e',k2)
    | TmCase(fi,x,e1,t,e2,e3) -> 
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let (e3',k3) = aux e3 delta k2 in
        let e' = TmCase(fi,x,e1',t,e2',e3') in
        (e',k3)
    | TmLet(fi,v,e1,e2) -> 
        let (e1',k1) = aux e1 delta k in
        let (e2',k2) = aux e2 delta k1 in
        let e' = TmLet (fi,v,e1',e2') in
        (e',k2)
  in aux e [] k


let rec subst_expr tbl expr =
    if tbl = [] then expr
    else begin
    match expr with
    (*| TmBool(fi,b) -> TmBool(fi,b) *)
    | TmBoolAnd(fi,e1,e2) -> TmBoolAnd(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmBoolOr(fi,e1,e2) -> TmBoolOr(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmBoolNeg(fi,e1) -> TmBoolNeg(fi, subst_expr tbl e1) 
    (*| TmInt(fi,v) -> TmInt(fi,v) *)
    | TmIntAdd(fi,e1,e2) -> TmIntAdd(fi, subst_expr tbl e1, subst_expr tbl e2) 
    | TmIntMinus(fi,e1,e2) -> TmIntMinus(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmIntTimes(fi,e1,e2) -> TmIntTimes(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmIntDiv(fi,e1,e2) -> TmIntDiv(fi, subst_expr tbl e1, subst_expr tbl e2) 
    | TmIntMod(fi,e1,e2) -> TmIntMod(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmIntUMinus(fi,e) -> TmIntUMinus(fi, subst_expr tbl e)
    | TmIntLt(fi,e1,e2) -> TmIntLt(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmIntEq(fi,e1,e2) -> TmIntEq(fi, subst_expr tbl e1, subst_expr tbl e2)
    (* product *)
    | TmPair(fi,e1,e2) -> TmPair(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmPi1(fi,e1) -> TmPi1(fi, subst_expr tbl e1) 
    | TmPi2(fi,e1) -> TmPi2(fi, subst_expr tbl e1) 
    | TmVar(fi,x) as e -> begin try List.assoc x tbl with Not_found -> e end
    | TmFun(fi,f,t,x,e1) -> 
        (*let tbl1 = List.remove_assoc f tbl in
        let tbl2 = List.remove_assoc x tbl1 in*)
        let tbl2 = (f, TmVar(fi,f))::((x,TmVar(fi,x))::tbl) in
        TmFun(fi,f,t,x, subst_expr tbl2 e1)
    | TmApp(fi,e1,e2) -> TmApp(fi, subst_expr tbl e1, subst_expr tbl e2)
    | TmCase(fi,x,e1,t,e2,e3) -> TmCase(fi,x, subst_expr tbl e1, t, subst_expr tbl e2, subst_expr tbl e3)
    | TmLet(fi,v,e1,e2) -> 
        let tbl2 = (v, TmVar(fi,v))::tbl in TmLet(fi,v, subst_expr tbl e1, subst_expr tbl2 e2)
    | e -> e
    end


(* product *)
let rec justprods (p,n) = match p with [] -> true | th::tl -> (SubType.isprod th) && (justprods (tl,n))(* *** *)
let get_prods t = 
    let t0 = SubType.unfold_once t in
    let nfs = SubType.dnfRM (`Cap(`Prod(`Any,`Any), t0)) in 
    let prods = List.filter justprods nfs in
    let keepprods (p,n) = (List.filter SubType.isprod1 p, List.filter SubType.isprod1 n) in
    List.map keepprods prods
let bigconj f p n = (* f: fst or snd *)
    let conj t0 l = List.fold_left (fun s t -> `Cap(s,t)) t0 l in
    let pp = List.map (fun t -> f (SubType.get_prod t)) p in (* get_prod? *)
    let nn = List.map (fun t -> (`Not(f (SubType.get_prod t)))) n in 
    conj (conj (`Any) pp) nn
let type_pi f t =  (* f: fst or snd *)
    let nfs = get_prods t in
    let np2ts (p,n) = 
       let ns = SubType.subsets n in
       let nns = List.map (bigconj f p) ns in
       List.fold_left (fun s t -> `Cup(s,t)) (`Not(`Any)) nns
    in 
    let tts = List.map np2ts nfs in
    let resty = List.fold_left (fun s t -> `Cup(s,t)) (`Not(`Any)) tts in
    SubType.simple resty


(* The following are used for arrows *)
let type4inter t =  match t with 
    |[] -> `Any
    |[(s1,s2)] -> `Arrow(s1,s2)
    |(s1,s2)::tl -> List.fold_left (fun s (b1,b2) -> (`Cap(s,`Arrow(b1,b2)))) (`Arrow(s1,s2)) tl

let rec justarrows (p,n) = match p with [] -> true | th::tl -> (SubType.isarrow th) && (justarrows (tl,n))(* *** *)
let get_arrows t = 
    let t0 = SubType.unfold_once t in
    let nfs = SubType.dnfRM (`Cap(`Arrow(`Not(`Any),`Any), t0)) in 
    let arrows = List.filter justarrows nfs in
    let keeparrows (p,n) = (List.filter SubType.isarrow1 p, List.filter SubType.isarrow1 n) in
    List.map keeparrows arrows
(* get the domain of functions *)
let nfs_dom nfs =
    (*let nfs = get_arrows t in*)
    let dom_snf (p,n) = 
        let pp = List.map (fun t -> fst (SubType.get_arrow t)) p in
        List.fold_left (fun s t ->`Cup(s,t)) (`Not(`Any)) pp
    in let tys = List.map dom_snf nfs in
    List.fold_left (fun s t -> `Cap(s,t)) `Any tys
(* get the type pairs for functions *)
let nfs_ph nfs =
    let ph_snf (p,n) = 
       (* let ps = SubType.subsets p in  minus p *)
       let rec arrowpairs t0 s0 p = 
         match p with
         |[] -> [(t0,s0)] 
         |ts :: p' ->
            let (t1,s1) = SubType.get_arrow ts in 
            let p1 = arrowpairs (`Cup(t0, t1)) s0 p' in 
            let p2 = arrowpairs t0 (`Cap(s0, s1)) p' in            
            p1@p2
       in List.tl (arrowpairs (`Not(`Any)) (`Any) p)
    in let pairs = List.map ph_snf nfs in
    List.fold_left (fun s t -> s@t) [] pairs 

(* application of t s with matching *)
(*
let type_app t s =
    let nfst = get_arrows t in
    let dty = nfs_dom nfst in
    let substs  =  TypeMatch.matchingF dty s 2 in 
    Format.fprintf Format.std_formatter "\n>> Possible constraints: %a\n" Ast.dump_solus substs;
    match substs with 
    |COmega _ -> `Singleton("omega")
    |Cons [([],_)] -> 
        let pairs = nfs_ph nfst in
        let pairs' = List.filter (fun (s1,s2) -> not (SubType.sub2 s s1)) pairs in
        let resty = List.fold_left (fun t (s1,s2) -> `Cup(t,s2)) (`Not(`Any)) pairs' in
        SubType.simple resty 
    |Cons ls ->
        let solus = TypeMatch.cstrs2tbls substs in
        if List.length solus = 0 then `Singleton("omega")
        else begin
        let ts = List.map (SubType.subst_mark t) solus in
        let ss = List.map (SubType.subst_mark s) solus in
        let t' = List.fold_left (fun a b -> (`Cap(a,b))) (`Any) ts in
        let s' = List.fold_left (fun a b -> (`Cap(a,b))) (`Any) ss in
        let tt = SubType.simple t' and ss = SubType.simple s' in
        let pairs = nfs_ph (get_arrows tt) in
        let pairs' = List.filter (fun (s1,s2) -> not (SubType.sub2 ss s1)) pairs in
        Format.fprintf Format.std_formatter "\n>> Possible substitutions: %a\n@?" Ast.dump_substs solus;
        let resty = List.fold_left (fun t (s1,s2) -> `Cup(t,s2)) (`Not(`Any)) pairs' in
        SubType.simple resty
        end
*)

(*
(* order polymorphic type variables *)
let mark_order delta order t k = 
    (*let vars = SubType.vars t in*)
    let rec find_order order v =
        match order with
        |[] -> -1
        |(vv,oi)::order' -> if Ast.equal vv v then oi else find_order order' v
    in
    let rec aux order t k =
        match t with
        |`Arrow(t1,t2) -> 
            let (t1',order1,k1) = aux order t1 k in
            let (t2',order2,k2) = aux order1 t2 k1 in
            (`Arrow(t1',t2'), order2, k2)
        |`Prod(t1,t2)  ->
            let (t1',order1,k1) = aux order t1 k in
            let (t2',order2,k2) = aux order1 t2 k1 in
            (`Prod(t1',t2'), order2, k2)
        |`Cup(t1,t2)   ->
            let (t1',order1,k1) = aux order t1 k in
            let (t2',order2,k2) = aux order1 t2 k1 in
            (`Cup(t1',t2'), order2, k2)
        |`Cap(t1,t2)  ->
            let (t1',order1,k1) = aux order t1 k in
            let (t2',order2,k2) = aux order1 t2 k1 in
            (`Cap(t1',t2'), order2, k2)
        |`Not(t')  ->
            let (t1',order1,k1) = aux order t' k in
            (`Not(t1'), order1, k1)  
        |`Mu(s,t')   -> 
            let (t1',order1,k1) = aux order t' k in
            (`Mu(s,t1'), order1, k1) 
        |`TVar (i,s) as v -> 
            if List.exists (Ast.equal v) delta then (`TVar(-1,s), order, k)
            else let vo = find_order order v in
                 if vo >= 0 then (`TVar(vo,s),order,k)
                 else let order' = (v,k)::order in
                 (`TVar(k,s),order', k+1)
        |t -> (t,order,k)
      in aux order t k
*)

(* heuristic number for the copies of the type of the function *)
(* do not consider the product yet *)
let heurN s =
    let s0 = SubType.unfold_once s in
    let nfs = SubType.dnfRM s0 in 
    List.length nfs

(* heuristic number for the copies of the type of the argument *)
(* t must be a function type *)
(* do not consider the product yet *)
let heurM t = 
	let tpair = get_arrows t in
	let tdom = nfs_dom tpair in
	let nfs = SubType.dnfRM tdom in
	let cpn (p,n) = List.length (p@n) in
	let cs = List.map cpn nfs in	
	List.fold_left (+) 0 cs

let rec freshinst t delta =
	let tv = SubType.vars t in
	let polytv = SL.diff tv delta in
	let freshv = function `TVar(i,s) -> (`TVar(i,s), `TVar(i, SubType.fresh s)) | _ -> failwith "freshvar" in
	let tbl = List.map freshv polytv in
	SubType.subst_mark t tbl
 
let expand t n delta =
   let rec aux tt n =
      if n > 0 then
         let ft = freshinst t delta in
         let nt = (`Cap (tt, ft)) in
         aux nt (n-1)
      else tt
   in aux t (n-1)


(* application of t s with (1,1)*)
let type_appl delta t s =
    (* alpha renaming??? *)
   (* let (ss, order1, k1) = mark_order [] [] s 1 in
    let (tt, order2, k2) = mark_order [] order1 t k1 in*)
    let resty = `TVar (0, "resty") in
    (*let funty = `Arrow (`Not(`Any), `Any) in
    let cty1 = `Cap (t, `Not(funty)) in
    let cty2 = `Cap ( `Cap(t, funty), `Not(`Arrow(s,resty)) ) in
    let cty = `Cup (cty1, cty2) in*)

    (* heuristic number *)
    let tt = ref t and ss = ref s in
    let i = ref 1 and j = ref 1 in
    let p = heurN s and q = heurM t in
    let rty = ref (`Singleton("omega")) in
    let loop = ref true in

    while !loop do
   (* Format.fprintf Format.std_formatter "Function: %a\n@?" Ast.dump !tt;
    Format.fprintf Format.std_formatter "Argument: %a\n@?" Ast.dump !ss;
    Format.fprintf Format.std_formatter "Expansion: (%d,%d)\n@?" !i !j;*)

    let cty = `Cap(!tt, `Not(`Arrow(!ss,resty))) in
    let normcons = TypeMatch.norm (cty, []) in
    (*Format.fprintf Format.std_formatter "Step 1:%d\n@?" (List.length normcons);*) (*Ast.dump_constrsets normcons*)
    match normcons with
    |[]-> rty := `Singleton("omega"); loop := false
    | cons ->
        let solus_satu = TypeMatch.satus [] cons in
	(*Format.fprintf Format.std_formatter "Step 2:%d\n@?" (List.length solus_satu);*) (*Ast.dump_constrsets solus_satu;*)
        let substs = TypeMatch.cstrs2tbls solus_satu in
        let toresty t tbl = 
		let mono = SubType.vars (`Cap (!tt,!ss)) in
		TypeMatch.minimal (SubType.subst_mark t tbl) mono 
        in
        begin match substs with
        |[] -> 
		let ttg = TypeMatch.isground !tt and ssg = TypeMatch.isground !ss in
		if (not ttg) && (!i <= p) && ( ssg || (!j > q) || ( !i < !j ) ) then   
			begin i := !i + 1; let nt = freshinst t delta in tt := (`Cap(!tt,nt)) end (* expand t !i delta *)
		else if (not ssg) && (!j <= q) && ( ttg || (!i > p) || (!j <= !i) ) then
			begin j := !j + 1; let ns = freshinst s delta in ss := (`Cap(!ss,ns)) end (* expand s !j delta *)
		else begin rty := `Singleton("omega"); loop := false end
        |[tbl] -> rty := toresty resty tbl; loop := false
        |tbl::tbls -> 
           let resty0 = toresty resty tbl in
           let restys = List.map (toresty resty) tbls in
           let min = List.fold_left (fun s t -> `Cap(s,t)) resty0 restys in
           (*Format.fprintf Format.std_formatter "\n>> Possible substitution: %a\n@?" Ast.dump_substs substs;*)
	   (*SubType.simple*)
           rty := min; loop := false
       end
    done;
    !rty


let mark_bound t =
    let rec aux = function
      |`Cup(t1,t2) -> `Cup(aux t1, aux t2)
      |`Cap(t1,t2) -> `Cap(aux t1, aux t2)
      |`Prod(t1,t2)-> `Prod(aux t1, aux t2) 
      |`Arrow(t1,t2) -> `Arrow(aux t1, aux t2)
      |`Not(t1) -> `Not(aux t1)
      |`Mu(s,t1)-> `Mu(s, aux t1)
      |`TVar(i, s) -> if i >= 0 then `TVar(-i,s) else `TVar(i, s) 
      |t -> t 
    in aux t  

let fresh_tyvar t = 
     let vs = SubType.vars t in
     let fresh_var = function
         |`TVar(i,s) -> 
              if i < 0 then (s, `TVar(i,s))
              else (s, `TVar(0, SubType.fresh s))
         | _ -> failwith "fresh tyvar"
     in
     let tbl = List.map fresh_var vs in
     SubType.subst t tbl



let rec typeof delta tyctx e = 
    match e with 
    | TmNil _ -> (`Singleton("nil"))
    (* Boolean *)
    | TmBool(fi, b) -> if b then (`True) else (`False)
    | TmBoolAnd(fi,e1,e2) ->
       if (SubType.sub2  (typeof delta tyctx e1) (`Bool) ) 
       && (SubType.sub2  (typeof delta tyctx e2) (`Bool) ) then 
         (`Bool) 
       else error fi "arguments of '&&' are not booleans"
    | TmBoolOr(fi,e1,e2) ->
       if (SubType.sub2  (typeof delta tyctx e1) (`Bool) ) 
       && (SubType.sub2  (typeof delta tyctx e2) (`Bool) ) then 
         (`Bool) 
       else error fi "arguments of '||' are not booleans" 
    | TmBoolNeg(fi,e1) ->
       if (SubType.sub2 (typeof delta tyctx e1) (`Bool) ) then 
         (`Bool) 
       else error fi "argument of '!' is not an integer" 
    (* Integer *)
    | TmInt(fi,i) -> (`Bounded(i,i))
    | TmIntAdd(fi,e1,e2) ->
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny ) && (SubType.sub2 (typeof delta tyctx e2) `IntAny ) then 
         (`IntAny)
         (*let e' = eval e in SType(`Bounded(getint e', getint e'))*)
       else error fi "arguments of '+' are not integers"
    | TmIntMinus(fi,e1,e2) ->
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny ) && (SubType.sub2 (typeof delta tyctx e2) `IntAny ) then
         (`IntAny) 
       else error fi "arguments of '-' are not integers"
    | TmIntTimes(fi,e1,e2) ->
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny ) && (SubType.sub2 (typeof delta tyctx e2) `IntAny ) then 
         (`IntAny) 
       else error fi "arguments of '*' are not integers"
    | TmIntDiv(fi,e1,e2) ->
       let t2 = (typeof delta tyctx e2) in 
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny) && (SubType.sub2 t2 `IntAny) then 
             if (SubType.sub2 t2 (`Bounded(0,0)) ) then error fi "Division_by_zero"
             else (`IntAny)
       else error fi "arguments of '/' are not integers"
    | TmIntMod(fi,e1,e2) ->
       let t2 = (typeof delta tyctx e2) in 
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny) && (SubType.sub2 t2 `IntAny) then 
             if (SubType.sub2 t2 (`Bounded(0,0)) ) then error fi "Division_by_zero"
             else (`IntAny) 
       else error fi "arguments of '%' are not integers"
    | TmIntUMinus(fi,e1) ->
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny ) then 
         (`IntAny)
       else error fi "argument of '-' is not an integer"
    | TmIntLt(fi,e1,e2) ->
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny ) && (SubType.sub2 (typeof delta tyctx e2) `IntAny ) then 
         (`Bool) 
       else error fi "arguments of '<' are not integers"        
    | TmIntEq(fi,e1,e2) ->
       if (SubType.sub2 (typeof delta tyctx e1) `IntAny ) && (SubType.sub2 (typeof delta tyctx e2) `IntAny ) then 
         (`Bool) 
       else error fi "arguments of '==' are not integers" 
    (* Pair *)
    | TmPair(fi,e1,e2) ->
(* polymorphic type varialbes in e1 and e2 have different names *)
         let ty1 = typeof delta tyctx e1 in let ty2 = typeof delta tyctx e2 in 
         begin match (ty1,ty2) with
         |(`Singleton("omega"), _) 
         |(_, `Singleton("omega"))  -> `Singleton("omega")
         |(`Not(`Any), _) 
         |(_, `Not(`Any)) -> (`Not(`Any))
         | _ -> (`Prod(ty1,ty2))
         end
    | TmPi1(fi,e1) -> 
         let t = (typeof delta tyctx e1) in (*type_pi fst t*)
         if SubType.sub2 t (`Prod(`Any,`Any)) then type_pi fst t  
         else `Singleton("omega")
    | TmPi2(fi,e1) -> 
         let t = (typeof delta tyctx e1) in (*type_pi snd t*)
         if SubType.sub2 t (`Prod(`Any,`Any)) then type_pi snd t 
         else `Singleton("omega")        
    (* arrows *)
    | TmVar(fi,x)  -> 
 (* mark the type variable not in delta as polymorphic (different names) *)
         begin try List.assoc x tyctx with Not_found -> `Singleton("omega") end
    | TmFun(fi,f,t,x,e1) -> 
         let tyf = (type4inter t) in
         let chk (s1,s2) = 
             let delta' = SubType.vars(tyf)@delta in
             let tyfb = mark_bound tyf in
             let tyctx1 = (f,(tyfb))::((x,(s1))::tyctx) in (* *)
             SubType.sub2 (typeof delta' tyctx1 e1) s2  
         in
         let (pos,neg) = List.partition chk t in
         if List.length neg <= 0 then tyf else `Singleton("omega")
    | TmApp(fi,e1,e2) -> 
(* polymorphic type varialbes in t1 and t2 have different names *)
         let t1 = (typeof delta tyctx e1) and t2 = (typeof delta tyctx e2) in
         type_appl delta t1 t2
         (*if SubType.sub2 t1 (`Arrow(`Not(`Any), `Any)) then 
            begin match t2 with
            |`Singleton("omega") -> `Singleton("omega")
            | _ -> 
               let t11 = fresh_tyvar t1 and t22 = fresh_tyvar t2
               in type_app t11 t22
            end
         else `Singleton("omega") *)
    | TmCase(fi,x,e1,t,e2,e3) -> 
(* polymorphic type varialbes in e2 and e3 have different names *)
         let t0 = typeof delta tyctx e1 in
         begin match t0 with
         |`Singleton("omega") -> `Singleton("omega")
         |`Not(`Any) -> `Not(`Any)
         |_ -> 
            let chk t t0 e = 
               let s = `Cap(t, t0) in
               let tyctx' = (x,s)::tyctx in
               if SubType.sub2 s (`Not(`Any)) then (`Not(`Any))
               else typeof delta tyctx' e
            in
            let t2 = chk t t0 e2 and t3 = chk (`Not(t)) t0 e3 in 
            begin match (t2,t3) with
            |(`Singleton("omega"), _) 
            |(_, `Singleton("omega")) -> `Singleton("omega")
            |(`Not(`Any), s)
            |(s, `Not(`Any)) -> s
            | _ -> SubType.simple (`Cup(t2,t3))
            end
         end
    | TmLet(fi, s, e1, e2) ->
(* polymorphic type varialbes in e1 and e2 have different names *)
         let tys = typeof delta tyctx e1 in
         if tys = `Singleton("omega") then `Singleton("omega") 
         else 
         let tys1 = mark_bound tys in
         let tyctx1 = (s,(tys1))::tyctx 
         in typeof delta tyctx1 e2
    (*|_ -> `Singleton("omega") (*raise NoRuleApplies*)*)
    (*in 
    let resty = aux tyctx e in  
    Format.fprintf Format.std_formatter ">>>>%a :: %a \r\n@?" Ast.dump_expr e Ast.dump resty; resty*)        
 
let rec eval1 valctx tyctx e = (*Format.fprintf Format.std_formatter "Now : %a \r\n\n@?" Ast.dump_expr e;*) 
    match e with 
    (* Boolean *)
    | TmBoolAnd(fi, TmBool(_,b1), TmBool(_,b2)) ->
       TmBool(fi, b1 && b2) 
    | TmBoolAnd(fi, (TmBool(_,b1) as e1), e2) ->
       let e2' = eval1 valctx tyctx e2 in TmBoolAnd(fi,e1,e2') 
    | TmBoolAnd(fi, e1, e2) ->
       let e1' = eval1 valctx tyctx e1 in TmBoolAnd(fi,e1',e2) 
    | TmBoolOr(fi, TmBool(_,b1), TmBool(_,b2)) ->
       TmBool(fi, b1 || b2) 
    | TmBoolOr(fi, (TmBool(_,b1) as e1), e2) ->
       let e2' = eval1 valctx tyctx e2 in TmBoolOr(fi,e1,e2') 
    | TmBoolOr(fi, e1, e2) ->
       let e1' = eval1 valctx tyctx e1 in TmBoolOr(fi,e1',e2) 
    | TmBoolNeg(fi, TmBool(_,b1)) ->
         TmBool(fi, not b1)
    | TmBoolNeg(fi,e1) ->
         let e1' = eval1 valctx tyctx e1 in TmBoolNeg(fi, e1')
    (* Integer *)
    | TmIntAdd(fi, TmInt(_,v1), TmInt(_,v2)) -> 
         TmInt(fi, v1 + v2)
    | TmIntAdd(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntAdd(fi, e1, e2')        
    | TmIntAdd(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntAdd(fi, e1', e2)
    | TmIntMinus(fi, TmInt(_,v1), TmInt(_,v2)) -> 
         TmInt(fi, v1 - v2)
    | TmIntMinus(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntMinus(fi, e1, e2')        
    | TmIntMinus(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntMinus(fi, e1', e2)    
    | TmIntTimes(fi, TmInt(_,v1), TmInt(_,v2)) -> 
         TmInt(fi, v1 * v2)
    | TmIntTimes(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntTimes(fi, e1, e2')        
    | TmIntTimes(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntTimes(fi, e1', e2)
    | TmIntDiv(fi, TmInt(_,v1), TmInt(_,v2)) -> 
         if v2 == 0 then raise DivZero else TmInt(fi, v1 / (v2))
    | TmIntDiv(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntDiv(fi, e1, e2')        
    | TmIntDiv(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntDiv(fi, e1', e2)
    | TmIntMod(fi, TmInt(_,v1), TmInt(_,v2)) -> 
         if v2 == 0 then raise DivZero else TmInt(fi, v1 mod (v2))
    | TmIntMod(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntMod(fi, e1, e2')        
    | TmIntMod(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntMod(fi, e1', e2)
    | TmIntUMinus(fi, TmInt(_,v1)) -> 
         TmInt(fi, -v1)       
    | TmIntUMinus(fi,e1) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntUMinus(fi, e1')
    | TmIntLt(fi, TmInt(_,v1), TmInt(_,v2)) ->
         TmBool(fi, v1 < v2)
    | TmIntLt(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntLt(fi,e1,e2')
    | TmIntLt(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntLt(fi, e1', e2)   
    | TmIntEq(fi, TmInt(_,v1), TmInt(_,v2)) ->
         TmBool(fi, v1 == v2)
    | TmIntEq(fi, (TmInt(_,v1) as e1), e2) ->
         let e2' = eval1 valctx tyctx e2 in TmIntEq(fi,e1,e2')
    | TmIntEq(fi,e1,e2) -> 
         let e1' = eval1 valctx tyctx e1 in TmIntEq(fi, e1', e2)  
    (* Pair *)
    | TmPair(fi,e1,e2) when isval e1 ->
         let e2' = eval1 valctx tyctx e2 in TmPair(fi,e1,e2')
    | TmPair(fi,e1,e2) ->
         let e1' = eval1 valctx tyctx e1 in TmPair(fi,e1',e2) 
    | TmPi1(fi,e1) when isval e1 -> 
         begin match e1 with TmPair(_,v1,_) -> v1 | _ -> raise NoRuleApplies end
    | TmPi1(fi,e1) ->
         let e1' = eval1 valctx tyctx e1 in TmPi1(fi,e1')   
    | TmPi2(fi,e1) when isval e1 -> 
         begin match e1 with TmPair(_,_,v2) -> v2 | _ -> raise NoRuleApplies end
    | TmPi2(fi,e1) ->
         let e1' = eval1 valctx tyctx e1 in TmPi2(fi,e1')  
    (* application *)
    | (TmApp(fi, (TmFun(_,f,t,x,e1) as fe), e2))  when isval e2 ->
         (* how about relabeling??*)
         let tbl = [(f,fe);(x,e2)] in subst_expr tbl e1
         (*let ee = subst_expr tbl e1 in 
         Format.fprintf Format.std_formatter ":::%a ==> %a \r\n@?" Ast.dump_expr eapp Ast.dump_expr ee; ee *)        
    | TmApp(fi, e1, e2) when isval e1 ->
         let e2' = eval1 valctx tyctx e2 in TmApp(fi,e1,e2')
    | TmApp(fi, e1, e2) ->
         let e1' = eval1 valctx tyctx e1 in TmApp(fi,e1',e2)
    (* case *)
    | TmCase(fi, x, e1, t, e2, e3) when (isval e1) -> (* typeof [] e1 == 0? *)
          let tbl = [(x,e1)] in 
          if (SubType.sub2 (typeof [] tyctx e1) t) then subst_expr tbl e2 else subst_expr tbl e3
    | TmCase(fi, x, e1, t, e2, e3) ->
         let e1' = eval1 valctx tyctx e1 in TmCase(fi, x, e1', t, e2, e3)
    (* let *)
    | TmLet(fi, s, e1, e2) when (isval e1) -> 
          let tbl = [(s,e1)] in 
          let ee = subst_expr tbl e2 in
          Format.fprintf Format.std_formatter ":::%a ==> %a \r\n@?" Ast.dump_expr e2 Ast.dump_expr ee;ee
    | TmLet(fi, s, e1, e2) ->
         let e1' = eval1 valctx tyctx e1 in TmLet(fi, s, e1', e2)
    | TmVar(fi,x)  -> 
         begin try List.assoc x valctx with Not_found -> raise NoRuleApplies end
    (*| TmFun(fi, f, t, x, e) when redinfun e ->
         let e' = eval valctx tyctx e in TmFun(fi, f, t, x, e')*)
    |_ -> raise NoRuleApplies

and eval valctx tyctx e =
    try let e' = eval1 valctx tyctx e in eval valctx tyctx e' 
    with NoRuleApplies -> subst_expr valctx e (*?? e *)
    | DivZero -> e

         
           


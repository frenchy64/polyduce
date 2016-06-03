open Support.Error

type interval = [
    `Bounded of int * int (* [a, b] *)
  | `Left of int (* [.., b] *)
  | `Right of int (* [a, ..] *)
  | `IntAny (* [.., ..] *)
]

type boolean = [
     `Bool
    |`True
    |`False
]

type singleton = [
   `Singleton of string (* singleton type *)
 | `SingletonAny
]

type 'a t = [
    | `Cup of 'a * 'a (* union *)
    | `Cap of 'a * 'a (* intersection *)
    | `Not of 'a (* negation  *)
    | `Arrow of 'a * 'a (* function *)
    | `Prod of 'a * 'a (* product *)
    | `Any (* top *)
    (* int :: < 0 ==> monomorphic ; > 0 ==> polymorphic and order; = 0 ==> checked *)
    | `TVar of int * string (* type variable *)
    | `MVar of string (* mu variable *)
    | `Mu of string * 'a (* recursive *)
    | interval
    | boolean
    | singleton
](* polymorphic variants type *)

type term = term t (* 'a = term *)

type value =
       Basic of string list * string (* string list --> label list *)
     | Product of string list * value * value
     | Function of string list * value list (* value list --> product list *)

(* interface for functions *)
type interface = (term * term) list

type expr =
      TmNil of info
    (* Boolean *)
    | TmBool of info * bool
    | TmBoolAnd of info * expr * expr
    | TmBoolOr of info * expr * expr
    | TmBoolNeg of info * expr
    (* Integer *)
    | TmInt of info * int
    | TmIntAdd of info * expr * expr
    | TmIntMinus of info * expr * expr
    | TmIntTimes of info * expr * expr
    | TmIntDiv of info * expr * expr
    | TmIntMod of info * expr * expr
    | TmIntUMinus of info * expr
    | TmIntLt of info * expr * expr
    | TmIntEq of info * expr * expr
    (* product *)
    | TmPair of info * expr * expr
    | TmPi1 of info * expr
    | TmPi2 of info * expr
    (* arrow *)
    | TmVar of info * string
    | TmFun of info * string * interface * string * expr
    | TmApp of info * expr * expr
    (* case *) (* should have variable binding ... *)
    | TmCase of info * string * expr * term * expr * expr
    (* let *)
    | TmLet of info * string * expr * expr

type command =
      Eval of info * string * expr
    | MatTy of info * term * term
    | SubTy of info * term * term
    | AppTy of info * term * term
    | UnfTy of info * term

(*
type scheme =
      SType of term
    | SArrows of interface
    | SProd of scheme * scheme
    | SCup of scheme * scheme
    | SOMEGA
    (* term :: type varialbes and recursive types *)
    | SCapVar of term * scheme
*)

let exprInfo expr = match expr with
    | TmNil fi -> fi
    | TmBool(fi,_) -> fi
    | TmBoolAnd (fi,_,_) -> fi
    | TmBoolOr (fi,_,_) -> fi
    | TmBoolNeg (fi,_) -> fi
    | TmInt (fi,_) -> fi
    | TmIntAdd (fi,_,_) -> fi
    | TmIntMinus (fi,_,_) -> fi
    | TmIntTimes (fi,_,_) -> fi
    | TmIntDiv (fi,_,_) -> fi
    | TmIntMod (fi,_,_) -> fi
    | TmIntUMinus (fi,_) -> fi
    | TmIntLt(fi,_,_) -> fi
    | TmIntEq(fi,_,_) -> fi
    (* product *)
    | TmPair(fi,_,_) -> fi
    | TmPi1(fi,_) -> fi
    | TmPi2(fi,_) -> fi
    (* arrow *)
    | TmVar(fi,_) -> fi
    | TmFun(fi,_,_,_,_) -> fi
    | TmApp(fi,_,_) -> fi
    (* case *)
    | TmCase(fi,_,_,_,_,_) -> fi
    (* let *)
    | TmLet(fi,_,_,_) -> fi

(* constraint :: (a,t1,t2,case) *)
type constr = (term * term * term * int)
(* sets of constraint sets :: [([constaint], rank)] *)
type constrsets = ((constr list) *int) list

(* constraint :: (a,t1,t2,case,modified) *)
type cstr = (term * term * term * int * int)
(* constraint set :: ([constaint], rank) *)
type cstrs = ((cstr list) * int)
(* set of constraint sets *)
type solus = COmega of int | Cons of cstrs list

(* two lists: one for 0->t, (0,t2), (t1,0), and one for the others *)

let rec dump_interval ppf = function
    | `Bounded (i,j) -> Format.fprintf ppf "[%d -- %d]" i j
    | `Left i -> Format.fprintf ppf "[ -- %d]" i
    | `Right j -> Format.fprintf ppf "[%d -- ]" j
    | `IntAny -> Format.pp_print_string ppf "Int"

let rec dump_singleton ppf = function
    | `Singleton t  -> Format.fprintf ppf "%s" t (* Singleton *)
    | `SingletonAny -> Format.pp_print_string ppf "all singletons"

let rec dump_boolean ppf = function
    | `Bool  -> Format.pp_print_string ppf "Bool"
    | `True  -> Format.pp_print_string ppf "True"
    | `False  -> Format.pp_print_string ppf "False"


let rec dump ppf = function
    | `TVar (i,t) -> Format.fprintf ppf "%s" t
    |#singleton as t -> dump_singleton ppf t
    | `Cup (t1,t2) -> Format.fprintf ppf "(%a v %a)" dump t1 dump t2
    | `Cap (t1,t2) -> Format.fprintf ppf "(%a ^ %a)" dump t1 dump t2
    | `Arrow (t1,t2) -> Format.fprintf ppf "(%a -> %a)" dump t1 dump t2
    | `Prod (t1,t2) -> Format.fprintf ppf "(%a , %a)" dump t1 dump t2

    | `Not `Any -> Format.pp_print_string ppf "0"
    | `Any -> Format.pp_print_string ppf "1"

    | `Not t -> Format.fprintf ppf "- %a" dump t
    | `Mu (s1, `Cup(`Prod(t, `MVar s2), `Singleton "nil"))
    | `Mu (s1, `Cup(`Singleton "nil", `Prod(t, `MVar s2))) when s1 = s2-> Format.fprintf ppf "[ %a ]" dump t
    | `Mu (s,t) -> Format.fprintf ppf "(mu %s . %a)" s dump t
    | `MVar (s) -> Format.fprintf ppf "%s" s
    |#interval as t -> dump_interval ppf t (* #interval is a shorthand for the or-pattern *)
    |#boolean as t -> dump_boolean ppf t

let rec dump_interval_xzw ppf = function
    | `Bounded (i,j) -> Format.fprintf ppf "(Bound ( %d , %d ))" i j
    | `Left i -> Format.fprintf ppf "(Left (%d))" i
    | `Right j -> Format.fprintf ppf "(Right (%d))" j
    | `IntAny -> Format.pp_print_string ppf "(IntAny)"

let rec dump_singleton_xzw ppf = function
    | `Singleton t  -> Format.fprintf ppf "(atom (%s))" t (* Singleton *)
    | `SingletonAny -> Format.pp_print_string ppf "(all singletons)"

let rec dump_xzw ppf = function
    |#singleton as t ->  dump_singleton_xzw ppf t
    | `TVar (i,t) -> Format.fprintf ppf "(TVar %s)" t
    | `Cup (t1,t2) -> Format.fprintf ppf "(Cup ( %a , %a ))" dump_xzw t1 dump_xzw t2
    | `Cap (t1,t2) -> Format.fprintf ppf "Cap ( %a , %a )" dump_xzw t1 dump_xzw t2
    | `Arrow (t1,t2) -> Format.fprintf ppf "(Arrow ( %a , %a ))" dump_xzw t1 dump_xzw t2
    | `Prod (t1,t2) -> Format.fprintf ppf "(Prod ( %a , %a ))" dump_xzw t1 dump_xzw t2

    | `Not `Any -> Format.pp_print_string ppf "(Not Any)"
    | `Any -> Format.pp_print_string ppf "(Any)"

    | `Not t -> Format.fprintf ppf "(Not %a)" dump_xzw t
    | `Mu (s,t) -> Format.fprintf ppf "(Mu %s. (%a) )" s dump_xzw t
    | `MVar (s) -> Format.fprintf ppf "(MVar ( %s ))" s
    |#interval as t -> dump_interval_xzw ppf t (* #interval is a shorthand for the or-pattern *)
    |#boolean as t -> dump_boolean ppf t

let rec string_of_type = function
    | `Bounded (i,j) -> Printf.sprintf "[%d -- %d]" i j
    | `Left i -> Printf.sprintf "[ -- %d]" i
    | `Right j -> Printf.sprintf "[%d -- ]" j
    | `IntAny -> "int"
    | `Singleton t  -> t
    | `SingletonAny -> "singleton"
    | `Not `Any -> "0"
    | `Any -> "1"
    | `TVar (i,t) -> t  (* t ^ (string_of_int i)*)
    | `Cup (t1,t2) -> "(" ^ (string_of_type t1) ^ " v " ^ (string_of_type t2) ^ ")"
    | `Cap (t1,t2) -> "(" ^ (string_of_type t1) ^ " ^ " ^ (string_of_type t2) ^ ")"
    | `Arrow (t1,t2) -> "(" ^ (string_of_type t1) ^ " -> " ^ (string_of_type t2) ^ ")"
    | `Prod (t1,t2) -> "(" ^ (string_of_type t1) ^ " * " ^ (string_of_type t2) ^ ")"
    | `Not t ->  "- " ^ (string_of_type t)
    | `Mu (s1, `Cup(`Prod(t, `MVar s2), `Singleton "nil"))
    | `Mu (s1, `Cup(`Singleton "nil", `Prod(t, `MVar s2))) when s1 = s2-> "[ " ^ string_of_type t ^ " ]"
    | `Mu (s,t) -> "(mu " ^ s ^ " . " ^ (string_of_type t) ^ ")"
    | `MVar (s) -> s
    | `Bool -> "bool"
    | `True -> "true"
    | `False -> "false"


let dump_list ppf dump_f l =
    Format.fprintf ppf "{{";
    let () = 
    match l with
      |[] -> ()
      |[hd] -> dump_f ppf hd
      |hd::tl -> dump_f ppf hd; List.iter (fun x ->  Format.fprintf ppf ";"; dump_f ppf x) tl 
    in Format.fprintf ppf "}}"

let dump_labs ppf labs = dump_list ppf (fun ppf lab -> Format.fprintf ppf "%s" lab)  labs

let rec dump_value ppf = function
     |Basic(labs, v) -> Format.fprintf ppf "%s" v;
                        if List.length labs > 0 then Format.fprintf ppf "^%a" dump_labs labs
     |Product(labs, v1, v2) -> Format.fprintf ppf "(%a , %a)" dump_value v1 dump_value v2;
                               if List.length labs > 0 then Format.fprintf ppf "^%a" dump_labs labs
     |Function(labs, l) ->
        (*let dump_fun ppf (v1,v2) = Format.fprintf ppf "(%a , %a)" dump_value v1 dump_value v2 in*)
        (*let dump_funs ppf l = Custom.dump_list ~bra:2 dump_value ppf l in
        Format.fprintf ppf "{ %a }" dump_funs l;*)
        Custom.dump_list ~bra:2 dump_value ppf l;
        if List.length labs > 0 then Format.fprintf ppf "^%a" dump_labs labs

let value_table = Hashtbl.create 17
let enter_values v labs =
  List.iter (fun lab ->
    let s = try Hashtbl.find value_table lab  with Not_found -> [] in
    Hashtbl.replace value_table lab (v :: s)
  ) labs

let pr_union_type ppf l =
  match l with
    [] -> ()
  | [ t ] -> Format.fprintf ppf "%s" t
  | t :: r -> Format.fprintf ppf "%s" t;
      List.iter (fun t -> Format.fprintf ppf " v %s" t) r

let _buf = Buffer.create 17
let _fmt = Format.formatter_of_buffer _buf
let asprintf  x =
  Format.kfprintf (fun _ ->
    Format.pp_print_flush _fmt ();
    let s = Buffer.contents _buf in
    Buffer.reset _buf; s) _fmt  x


let dump_value_with_constraints ppf v =
  let rec loop ppf v =
    let labs, vstr =
    match v with
      Basic(labs, v) ->
        let vstr = v in
        labs, vstr
    | Product(labs, v1, v2) ->
        let vstr = asprintf "(%a, %a)" loop v1 loop v2
        in
        labs, vstr
    | Function (labs, l) ->
        let vstr = asprintf "%a" (Custom.dump_list ~bra:2 loop) l in
        labs, vstr
    in
    enter_values vstr labs;
    Format.fprintf ppf "%s" vstr
  in
  Hashtbl.clear value_table;
  loop ppf v;
  Format.fprintf ppf " using substitution:@\n";
  Hashtbl.iter (fun lab types -> Format.fprintf ppf "\t%s := %a  @\n"
      lab pr_union_type types
  ) value_table;
  Format.pp_print_flush ppf ()
    


let dump_pair ppf (t,s) = Format.fprintf ppf "%a -> %a" dump t dump s
let dump_interface ppf l = Custom.dump_list ~bra:0 dump_pair ppf l
let rec dump_expr ppf = function
    | TmNil fi -> Format.fprintf ppf "nil"
    | TmBool(fi,b) -> let ss = string_of_bool(b) in Format.fprintf ppf "%s" ss
    | TmBoolAnd (fi,e1,e2) -> Format.fprintf ppf "(%a) && (%a)" dump_expr e1 dump_expr e2
    | TmBoolOr (fi,e1,e2) -> Format.fprintf ppf "(%a) || (%a)" dump_expr e1 dump_expr e2
    | TmBoolNeg (fi,e) -> Format.fprintf ppf "!(%a)" dump_expr e
    (* int *)
    | TmInt(fi,i) -> Format.fprintf ppf "%d" i
    | TmIntAdd (fi,e1,e2) -> Format.fprintf ppf "(%a) + (%a)" dump_expr e1 dump_expr e2
    | TmIntMinus (fi,e1,e2) -> Format.fprintf ppf "(%a) - (%a)" dump_expr e1 dump_expr e2
    | TmIntTimes (fi,e1,e2) -> Format.fprintf ppf "(%a) * (%a)" dump_expr e1 dump_expr e2
    | TmIntDiv (fi,e1,e2) -> Format.fprintf ppf "(%a) / (%a)" dump_expr e1 dump_expr e2
    | TmIntMod (fi,e1,e2) -> Format.fprintf ppf "(%a) / (%a)" dump_expr e1 dump_expr e2
    | TmIntUMinus (fi,e) -> Format.fprintf ppf "-(%a)" dump_expr e
    | TmIntLt(fi,e1,e2) -> Format.fprintf ppf "(%a) < (%a)" dump_expr e1 dump_expr e2
    | TmIntEq(fi,e1,e2) -> Format.fprintf ppf "(%a) == (%a)" dump_expr e1 dump_expr e2
    (* product *)
    | TmPair(fi,e1,e2) -> Format.fprintf ppf "((%a) , (%a))" dump_expr e1 dump_expr e2
    | TmPi1(fi,e) -> Format.fprintf ppf "pi1 (%a)" dump_expr e
    | TmPi2(fi,e) -> Format.fprintf ppf "pi2 (%a)" dump_expr e
    (* arrow *)
    | TmVar(fi,x) -> Format.fprintf ppf "%s" x
    | TmFun(fi,f,t,x,e) -> (* Format.fprintf ppf "fun" *)
        if String.length f > 0 then Format.fprintf ppf "mu %s %a lambda %s . %a" f dump_interface t x dump_expr e
        else Format.fprintf ppf "lambda %a %s . %a" dump_interface t x dump_expr e
    | TmApp(fi,e1,e2) -> Format.fprintf ppf "(%a) (%a)" dump_expr e1 dump_expr e2
    | TmCase(fi,x,e1,t,e2,e3) ->
        if x = "_" then Format.fprintf ppf "(%a) in %a ? (%a) : (%a)" dump_expr e1 dump t dump_expr e2 dump_expr e3
        else Format.fprintf ppf "(%s = %a) in %a ? (%a) : (%a)" x dump_expr e1 dump t dump_expr e2 dump_expr e3
    | TmLet(fi,v,e1,e2) -> Format.fprintf ppf "let %s = (%a) in (%a)" v dump_expr e1 dump_expr e2
(*
let rec dump_scheme ppf = function
    | SType(t) -> Format.fprintf ppf "%a" dump t
    | SArrows(intf) -> Format.fprintf ppf "[ %a ]" dump_interface intf
    | SProd(s1,s2) -> Format.fprintf ppf "(%a ,, %a)" dump_scheme s1 dump_scheme s2
    | SCup(s1,s2) -> Format.fprintf ppf "(%a VV %a)" dump_scheme s1 dump_scheme s2
    | SOMEGA -> Format.fprintf ppf "OMEGA"
    | SCapVar(t,s) -> Format.fprintf ppf "(%a ^^ %a)" dump t dump_scheme s
*)
let dump_constr ppf (a,t1,t2,c) =
	match c with
        | 1 -> Format.fprintf ppf "(%a >= %a)" dump a dump t1
	| 2 -> Format.fprintf ppf "(%a <= %a)" dump a dump t2
	| _ -> Format.fprintf ppf "(%a <= %a <= %a)" dump t1 dump a dump t2

let dump_constrs ppf (l, u) = Custom.dump_list dump_constr ppf l
    (*let aux ppf l = Custom.dump_list dump_cstr ppf l in
    Format.fprintf ppf "\r\n%i::[%a]" u aux l*)

let dump_constrsets ppf =  Custom.dump_list dump_constrs ppf

let dump_substs ppf subs =
    let dump_pair ppf (s,t) = Format.fprintf ppf "(%a := %a)" dump s dump t in
    let dump_pair_list ppf l = Custom.dump_list dump_pair ppf l in
    (*dump_list ppf dump_pair_list subs*)
    Custom.dump_list ~sep:";\r\n" dump_pair_list ppf subs


(* *)
let compare t s =
    match t,s with
    (*|`MVar _ , `MVar _ ->*)
    |`Cup (t1,t2), `Cup (s1,s2)
    |`Cap (t1,t2), `Cap (s1,s2)
    |`Arrow (t1,t2), `Arrow (s1,s2)
    |`Prod (t1,t2), `Prod (s1,s2) ->
            let c = compare t1 s1 in
            if c = 0 then compare t2 s2 else c
            (*Pervasives.compare (compare t1 s1) (compare t2 s2)*)
    |`Not t, `Not s -> compare t s
    |`Mu (x1,t), `Mu (x2,s) ->
            let c = Pervasives.compare x1 x2 in
            if c = 0 then compare t s else c
            (*Pervasives.compare (Pervasives.compare x1 x2) (compare t s)*)
    |`TVar(i1,s1), `TVar(i2,s2) ->
           let c  = Pervasives.compare s1 s2 in
           if c <> 0 then c
           else if ((i1 = i2) || (i1 = -i2)) then c
           else i2 - i1
    |_,_ -> Pervasives.compare t s (* structural equality *)

let equal s t = compare s t = 0

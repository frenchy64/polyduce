
let pred i = i - 1
let succ i = i + 1
let lt i j = i < j
let gt i j = i > j
let le i j = i <= j
let ge i j = i >= j


type t = Ast.interval list (* the interval list type, its form as : [ (`Left b)?, (`Bound (a,b))*, (`Right a)] *)

let empty = []
let any = [`IntAny]

let bounded a b =
  if le a b then [`Bounded (a,b)] else empty

let left a = [`Left a]
let right a = [`Right a]
let atom a = bounded a a

let rec iadd_left l b = match l with (* add [`Left b] into the list l *)
  | [] -> [`Left b]
  | (`Bounded (a1,_) | `Right a1) :: _
      when (lt b (pred a1)) ->
      `Left b :: l
  | `Bounded (_,b1) :: l' ->
      iadd_left l' (max b b1)
  | `Left b1 :: _ when le b b1-> l
  | `Left _ :: l' ->
      iadd_left l' b
  | _ -> any

let rec iadd_bounded l a b = match l with (* add [`Bounded (a b)] into the list l *)
  | [] ->
      [`Bounded (a,b)]
  | (`Bounded (a1,_) | `Right a1) :: _
      when (lt b (pred a1)) ->
      `Bounded (a,b) :: l
  | ((`Bounded (_,b1) | `Left b1) as i') :: l'
      when (lt (succ b1) a) ->
      i'::(iadd_bounded l' a b)
  | `Bounded (a1,b1) :: l' ->
      iadd_bounded l' (min a a1) (max b b1)
  | `Left b1 :: l' ->
      iadd_left l' (max b b1)
  | `Right a1 :: _ -> [`Right (min a a1)]
  | `IntAny :: _ -> any

let rec iadd_right l a = match l with (* add [`Right a] into the list l *)
  | [] -> [`Right a]
  | ((`Bounded (_,b1) | `Left b1) as i') :: l'
      when (lt (succ b1) a) ->
      i'::(iadd_right l' a)
  | (`Bounded (a1,_) | `Right a1) :: _ ->
      [`Right (min a a1)]
  | _ -> any

let iadd l = function (* add interval into the list l *)
  | `Bounded (a,b) -> iadd_bounded l a b
  | `Left b -> iadd_left l b
  | `Right a -> iadd_right l a
  | `IntAny -> any

let rec neg' start l = match l with (* the negative of the list and the domain starts from (start) *)
  | [] -> [`Right start]
  | `Bounded (a,b) :: l' ->
      `Bounded (start, pred a) :: (neg' (succ b) l')
  | `Right a :: l' ->
      [`Bounded (start, pred a)]
  | _ -> assert false (* no alternative for (`Left b) *)

let neg = function (* negative *)
  | `IntAny :: _ -> []
  | [] -> any
  | `Left b :: l -> neg' (succ b) l
  | `Right a :: _ -> [`Left (pred a)] (* the tail of the list is empty, because the list is ascending *)
  | `Bounded (a,b) :: l -> `Left (pred a) :: neg' (succ b) l

let cup i1 i2 = (* the union of i1 and i2 *)
  List.fold_left iadd i1 i2 

let cap i1 i2 = (* the intersection of i1 and i2 *)
  neg (cup (neg i1) (neg i2))

let diff i1 i2 = (* i1 - i2 *)
  neg (cup (neg i1) i2)

let is_empty = function [] -> true | _ -> false

let rec disjoint a b = (* true if a ^ b = empty *)
  match (a,b) with
    | [],_ | _,[] -> true
    | `IntAny::_,_ | _,`IntAny::_ -> false
    | `Left _::_, `Left _::_ -> false
    | `Right _::_, `Right _::_ -> false
    | `Left x :: a, `Bounded (y,_) :: _ -> (lt x y) && (disjoint a b)
    | `Bounded (y,_) :: _, `Left x :: b -> (lt x y) && (disjoint a b)
    | `Left x :: _, `Right y :: _ -> lt x y
    | `Right y :: _, `Left x :: _ -> lt x y
    | `Right y :: _, `Bounded (_,x) :: _ -> lt x y
    | `Bounded (_,x) :: _, `Right y :: _ -> lt x y
    | `Bounded (xa,ya) :: a', `Bounded (xb,yb) :: b' ->
        let c = compare xa xb in
        if c = 0 then false
        else
          if c < 0 then (lt ya xb) && (disjoint a' b)
          else (lt yb xa) && (disjoint a b')

let contains n = (* true if n is contain in any element *)
  List.exists (function 
                 | `IntAny -> true
                 | `Left b -> le n b
                 | `Right a -> le a n
                 | `Bounded (a,b) -> (le a n) && (le n b)
              )

let interval2string = function 
     |`IntAny -> "int"
     |`Left a -> string_of_int a
     |`Bounded(a,_) -> string_of_int a
     |`Right b -> string_of_int b
     |_ -> "any" 
let tostring = function [] -> "none" |  a::tl -> interval2string a

let dump ppf t = Custom.dump_list Ast.dump_interval ppf t (* printer *)


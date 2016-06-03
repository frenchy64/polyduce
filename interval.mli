
type t = Ast.interval list
val empty : t
val any : t
val bounded : int -> int -> t
val left : int -> t
val right : int -> t
val atom : int -> t

val neg  : t -> t
val cup  : t -> t -> t
val cap  : t -> t -> t
val diff : t -> t -> t
val is_empty : t -> bool
val disjoint : t -> t -> bool
val contains : int -> t -> bool
val dump : Format.formatter -> t -> unit
val tostring : t -> string

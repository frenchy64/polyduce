open Camlp4.PreCast
open Syntax

let () =
  EXTEND Gram
    expr: LEVEL "top" [
      [ "subtype" ; s = STRING ->
        <:expr< Driver.subtype_of_string ("subtype " ^ $str:s$) >>
      | "def" ; s = STRING ->
        <:expr< Driver.eval_of_string ("def " ^ $str:s$) >>
      | "eval" ; s = STRING ->
        <:expr< Driver.eval_of_string ($str:s$) >>
      | "appl" ; s = STRING ->
        <:expr< Driver.appl_of_string ("appl " ^ $str:s$) >>
      | "match" ; s = STRING ->
        <:expr< Driver.match_of_string ("match " ^ $str:s$) >>
      ]
    ];
  END
;;

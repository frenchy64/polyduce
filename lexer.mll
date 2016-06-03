(* 
   The lexical analyzer: lexer.ml is generated automatically
   from lexer.mll.
   
   The only modification commonly needed here is adding new keywords to the 
   list of reserved words at the top.  
*)

{
open Support.Error
exception Eof

let reservedWords = [
  (* Keywords *)
  ("lambda", fun i -> Parser.LAMBDA i);
  ("mu", fun i -> Parser.MU i);
  ("pi1", fun i -> Parser.PI1 i);
  ("pi2", fun i -> Parser.PI2 i);
  ("let", fun i -> Parser.LET i);
  ("in", fun i -> Parser.IN i);
  (*("unit", fun i -> Parser.UNIT i);
  ("Unit", fun i -> Parser.UUNIT i);*)
  ("nil", fun i -> Parser.NIL i);
  ("true", fun i -> Parser.TRUE i);
  ("false", fun i -> Parser.FALSE i);
  ("Bool", fun i -> Parser.BOOL i);
  ("Nat", fun i -> Parser.NAT i);
  ("Int", fun i -> Parser.INT i);
  ("type", fun i -> Parser.TYPE i);
  ("check", fun i -> Parser.CHECK i);
  ("match", fun i -> Parser.MATCH i);
  ("subtype", fun i -> Parser.SUBTYPE i);
  ("appl", fun i -> Parser.APPL i);
  ("if", fun i -> Parser.IF i);
  ("then", fun i -> Parser.THEN i);
  ("else", fun i -> Parser.ELSE i);
  ("def", fun i -> Parser.DEF i);
  
  (* Symbols *)
  ("v", fun i -> Parser.CUP i);
  ("^", fun i -> Parser.CAP i);
  ("\\", fun i -> Parser.SETMINUS i);
  ("+", fun i -> Parser.ADD i);
  ("-", fun i -> Parser.MINUS i);
  ("/", fun i -> Parser.DIV i);
  ("*", fun i -> Parser.TIMES i);
  ("->", fun i -> Parser.ARROW i);
  ("(", fun i -> Parser.LPAREN i); 
  (")", fun i -> Parser.RPAREN i);
  ("[", fun i -> Parser.LSQUARE i); 
  ("]", fun i -> Parser.RSQUARE i);
  ("--", fun i -> Parser.BOUNDED i);
  (".", fun i -> Parser.DOT i);
  (",", fun i -> Parser.COMMA i);
  (";", fun i -> Parser.SEMI i);
  (":", fun i -> Parser.COLON i);
  ("?", fun i -> Parser.QUES i);
  ("=", fun i -> Parser.EQ i);
  ("==", fun i -> Parser.EQEQ i);
  ("<", fun i -> Parser.LT i);
  (">", fun i -> Parser.GT i);
  ("<:", fun i -> Parser.LE i);
  (">:", fun i -> Parser.GE i);
  ("!=", fun i -> Parser.NEQ i);
  ("%", fun i -> Parser.MOD i);
  ("&&", fun i -> Parser.AND i);
  ("||", fun i -> Parser.OR i);
  ("!", fun i -> Parser.NEG i);

  (* Special compound symbols: *)

]

(* Support functions *)

type buildfun = info -> Parser.token
let (symbolTable : (string,buildfun) Hashtbl.t) = Hashtbl.create 1024
let _ =
  List.iter (fun (str,f) -> Hashtbl.add symbolTable str f) reservedWords

let createID i str =
  try (Hashtbl.find symbolTable str) i
  with _ ->
    if (String.get str 0) >= 'A' && (String.get str 0) <= 'Z' then
       Parser.UCID {i=i;v=str}
    else 
       Parser.LCID {i=i;v=str}

let lineno   = ref 1
and depth    = ref 0
and start    = ref 0

and filename = ref ""
and startLex = ref dummyinfo

(* create a lexbuf from stream (inFile) *)
let create inFile stream =
  if not (Filename.is_implicit inFile) then filename := inFile
  else filename := Filename.concat (Sys.getcwd()) inFile;
  lineno := 1; start := 0; Lexing.from_channel stream

let newline lexbuf = incr lineno; start := (Lexing.lexeme_start lexbuf)

let info lexbuf =
  createInfo (!filename) (!lineno) (Lexing.lexeme_start lexbuf - !start)

let text = Lexing.lexeme

}

(* The main body of the lexical analyzer *)

rule main = parse
  [' ' '\009' '\012']+     { main lexbuf }

| [' ' '\009' '\012']*("\r")?"\n" { newline lexbuf; main lexbuf }

| "*/" { error (info lexbuf) "Unmatched end of comment" }

| "/*" { depth := 1; startLex := info lexbuf; comment lexbuf; main lexbuf }

| ('-'?)['0'-'9']+
    { Parser.INTV{i=info lexbuf; v=int_of_string (text lexbuf)} }

| ['A'-'Z' 'a'-'z' '_']
  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*
    { createID (info lexbuf) (text lexbuf) }

| "->" | "==" | "--" | "<:" | ">:" | "&&" | "||" | "!=" | "\\"
    { createID (info lexbuf) (text lexbuf) }


| ['*' '+' '-' '/' '^' '(' ')' '[' ']' '=' '.' ',' ';' '?' ':' '%' '!' '>' '<']
    { createID (info lexbuf) (text lexbuf) }

| eof { Parser.EOF(info lexbuf) }

| _  { error (info lexbuf) "Illegal character" }

and comment = parse
  "/*"
    { depth := succ !depth; comment lexbuf }
| "*/"
    { depth := pred !depth; if !depth > 0 then comment lexbuf }
| eof
    { error (!startLex) "Comment not terminated" }
| [^ '\n']
    { comment lexbuf }
| "\n"
    { newline lexbuf; comment lexbuf }

(*  *)


open Ast

let valctx = ref [] ;;
let tyctx = ref [] ;;
let kctx = ref 1 ;;

let counter = ref 0

let ordervarbyname t k =
  let vars = SubType.vars t in
  let rec mark vs vsk n = match vs with
    |[] -> (vsk, k+n)
    | a::vs' -> mark vs' ((a,k+n)::vsk) (n+1) 
  in
  let (vm, vl) = mark vars [] 0 in
  let (tt,_,nk) = Core.typerenaming t [] vm vl in
  (tt, nk)

let subtype_of_string s =
  Printf.eprintf " %s %!\n" s;
  let lexbuf = Lexing.from_string s in
  try 
    begin match Parser.topcommand Lexer.main lexbuf with
    | Ast.SubTy(info, t, s) ->
       let (b,v,ns,ps) = SubType.sub t s in
       if b then Format.fprintf Format.std_formatter ">> Subtype %a <: %a\r\n>> False.\n\tA witness is: %a \r\n@?" Ast.dump t Ast.dump s Ast.dump_value_with_constraints v
       else Format.fprintf Format.std_formatter ">> Subtype %a <: %a\r\n>> True \r\n@?" Ast.dump t Ast.dump s
    |_ -> failwith "impossible"
    end
  with Lexer.Eof | Parsing.Parse_error -> Support.Error.error (Lexer.info lexbuf) "Parse error"
;;

let appl_of_string s =
  Printf.eprintf " %s %!\n" s;
  let lexbuf = Lexing.from_string s in
  try 
    begin match Parser.topcommand Lexer.main lexbuf with
    | AppTy(info, t, s) -> 
       let (tt, poly1, k1) = Core.typerenaming t [] [] 1 in
       let (ss, poly2, k2) = Core.typerenaming s [] [] k1 in
        let ts = Core.type_appl [] tt ss in
        Format.fprintf Format.std_formatter ">> Applying %a to %a : %a \r\n@?" Ast.dump tt Ast.dump ss Ast.dump ts;
        let ts' = SubType.simple ts in
        Format.fprintf Format.std_formatter ">> simplifying as : %a \r\n@?"  Ast.dump ts'
    |_ -> failwith "impossible"
    end
  with Lexer.Eof | Parsing.Parse_error -> Support.Error.error (Lexer.info lexbuf) "Parse error"
;;

let eval_of_string s = 
  Printf.eprintf " %s %!\n" s;
  let lexbuf = Lexing.from_string s in
  try 
    begin match Parser.topcommand Lexer.main lexbuf with
    | Eval(info, s, expr) -> 
       let (expr1, k) = Core.termrenaming expr !kctx in
       let e' = Core.eval (!valctx) (!tyctx) expr1 in 
       let ty = Core.typeof [] (!tyctx) expr1 in
       Format.fprintf Format.std_formatter ">> Eval expression : % a \r\n@?" Ast.dump_expr expr1;
       Format.fprintf Format.std_formatter ">> %s : %a = %a \r\n@?" s Ast.dump ty Ast.dump_expr e';
       begin match ty with
          |`Singleton("omega") -> ()
          |_ -> 
            let vals = List.remove_assoc s !valctx in
            let tys = List.remove_assoc s !tyctx in
            let (rety, _, k) = Core.typerenaming ty [] [] !kctx in
            valctx := (s,e')::vals;
            tyctx := (s,ty)::tys; 
            kctx := k; ()
       end
    |_ -> failwith "impossible"
    end
  with Lexer.Eof | Parsing.Parse_error -> Support.Error.error (Lexer.info lexbuf) "Parse error"
;;

let match_of_string s = 
  Printf.eprintf " %s %!\n" s;
  let lexbuf = Lexing.from_string s in
  try 
    begin match Parser.topcommand Lexer.main lexbuf with
    | MatTy(info, s, t) -> 
       let (tt,k1) = ordervarbyname t 1 in
       let (ss,k2) = ordervarbyname s k1 in 
       let ts = (`Cap(ss, `Not(tt))) in
       let (solus) = TypeMatch.norm (ts,[]) in 
       Format.fprintf Format.std_formatter "\n>> Matching %a against %a" Ast.dump tt Ast.dump ss;
       Format.fprintf Format.std_formatter "\n>> Step 1: %a\n" Ast.dump_constrsets solus;
       let solus_satu = TypeMatch.satus [] solus in
       Format.fprintf Format.std_formatter "\n>> Step 2: %a\n" Ast.dump_constrsets solus_satu;
       let substs = TypeMatch.cstrs2tbls solus_satu in
       Format.fprintf Format.std_formatter "\n>> Possible substitution: %a\n@?" Ast.dump_substs substs
    |_ -> failwith "impossible"
    end
  with Lexer.Eof | Parsing.Parse_error -> Support.Error.error (Lexer.info lexbuf) "Parse error"
;;

let processing_one valctx tyctx kctx com = 
    match com with
    | Eval(info, s, expr) -> 
       let (expr1, k) = Core.termrenaming expr !kctx in
       let e' = Core.eval (!valctx) (!tyctx) expr1 in 
       let ty = Core.typeof [] (!tyctx) expr1 in
       Format.fprintf Format.std_formatter ">> Eval expression : % a \r\n@?" Ast.dump_expr expr1;
       Format.fprintf Format.std_formatter ">> %s : %a = %a \r\n@?" s Ast.dump ty Ast.dump_expr e';
       begin match ty with
          |`Singleton("omega") -> ()
          |_ -> 
            let vals = List.remove_assoc s !valctx in
            let tys = List.remove_assoc s !tyctx in
            let (rety, _, k) = Core.typerenaming ty [] [] !kctx in
            valctx := (s,e')::vals;
            tyctx := (s,ty)::tys; 
            kctx := k; ()
       end


    | SubTy(info, t, s) -> 
       let (b,v,ns,ps) = SubType.sub t s in
       if b then Format.fprintf Format.std_formatter ">> Subtype %a <: %a\r\n>> %a \r\n@?" Ast.dump t Ast.dump s Ast.dump_value v
       else Format.fprintf Format.std_formatter ">> Subtype %a <: %a\r\n>> True \r\n@?" Ast.dump t Ast.dump s

    | MatTy(info, s, t) -> 
       let (tt,k1) = ordervarbyname t 1 in
       let (ss,k2) = ordervarbyname s k1 in 
       let ts = (`Cap(ss, `Not(tt))) in
       let (solus) = TypeMatch.norm (ts,[]) in 
       Format.fprintf Format.std_formatter "\n>> Matching %a against %a" Ast.dump tt Ast.dump ss;
       Format.fprintf Format.std_formatter "\n>> Step 1: %a\n" Ast.dump_constrsets solus;
       let solus_satu = TypeMatch.satus [] solus in
       Format.fprintf Format.std_formatter "\n>> Step 2: %a\n" Ast.dump_constrsets solus_satu;
       let substs = TypeMatch.cstrs2tbls solus_satu in
       Format.fprintf Format.std_formatter "\n>> Possible substitution: %a\n@?" Ast.dump_substs substs

    | AppTy(info, t, s) -> 
       let (tt, poly1, k1) = Core.typerenaming t [] [] 1 in
       let (ss, poly2, k2) = Core.typerenaming s [] [] k1 in
        let ts = Core.type_appl [] tt ss in
        Format.fprintf Format.std_formatter ">> Applying %a to %a : %a \r\n@?" Ast.dump tt Ast.dump ss Ast.dump ts;
        let ts' = SubType.simple ts in
        Format.fprintf Format.std_formatter ">> simplifying as : %a \r\n@?"  Ast.dump ts'

    | UnfTy(info, t) -> 
        let vars = SubType.vars t in
        let dump_vars ppf vars = Custom.dump_list Ast.dump ppf vars in
        let (tt,k1) = ordervarbyname t 1 in
        Format.fprintf Format.std_formatter "%a\r\nvars: %a\r\n%a\r\n@?" Ast.dump t dump_vars vars Ast.dump tt 

let rec processing valctx tyctx kctx comlist = 
    match comlist with
     | [] -> () 
     | com::rest -> 
       processing_one valctx tyctx kctx com;
       processing valctx tyctx kctx rest
;;


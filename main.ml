open ExtLib


module Options =
struct
    open OptParse
    (* let debug = StdOpt.store_true () *)

    let options = OptParser.make 
      ~usage: "[options] <filename>"
      ~description:"poly cduce test bench" ()

    open OptParser

(* add options  ~short_name:'d' ~long_name:"debug" ~help:"Debug information" debug; *)
end

let main () = 

  let posargs = OptParse.OptParser.parse_argv Options.options in

  let valctx = ref [] and tyctx = ref [] in
  let kctx = ref 1 in
  let chan = 
    if List.length posargs > 0 then 
      open_in (List.hd posargs) 
    else
      stdin
  in
  List.iter (fun line ->
		let lexbuf = Lexing.from_string line in
		let coms = 
			try Parser.toplevel Lexer.main lexbuf 
			with Lexer.Eof | Parsing.Parse_error -> 
        Support.Error.error (Lexer.info lexbuf) "Parse error"
		in 
    Driver.processing valctx tyctx kctx coms;
    print_newline ();
  ) (Std.input_list chan)
;;

main ();;

open Ocamlbuild_plugin;;
Options.use_ocamlfind := true ;;

open Command ;;

let _ = dispatch begin function
  | After_rules ->
       ocaml_lib ~extern:true ~dir:"_build" "cduce_test"
  | _ -> ()
end;;


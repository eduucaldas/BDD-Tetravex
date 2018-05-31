open PLLib
module Type = CharType
module PL = PropositionalLogic(Type)
module DD = BDD(Type)

let dump () =
  let formule = PL.formule_of_input () in
  let bdd = DD.compress (DD.create_random formule) in
  DD.print bdd;
  exit 0

let valid () =
  let formule = PL.formule_of_input () in
  let bdd = DD.compress (DD.create_random formule) in
  if (DD.validity bdd) then exit 0 else exit (-1)

let satisfiable () =
  let formule = PL.formule_of_input () in
  let bdd = DD.compress (DD.create_random formule) in
  DD.print_satifiability bdd;
  exit 0

let tetravex () =
  exit (-1)

let error_msg () =
  let msg = "This program needs one argument (and only one) that must be among {\"dump\", \"valid\", \"satisfiability\", \"tetravex\"}" in
  Printf.printf "%s\n" msg;
  exit (-1)


let () =
  if(Array.length Sys.argv != 2) then error_msg ()
  else
    let test_type = Sys.argv.(1) in
    match test_type with
    | "dump" -> dump ()
    | "valid" -> valid ()
    | "satisfiable" -> satisfiable ()
    | "tetravex" -> tetravex ()
    | _ -> error_msg ()

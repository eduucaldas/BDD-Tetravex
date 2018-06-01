open PLLib
module Type = CharType
module PL = PropositionalLogic(Type)
module DD = BDD(Type)
include Tetravex

let readTetravex () =
  let rec help i q=
    try
      let lign = read_line () in
      let l = Str.split( Str.regexp " ") lign in
      let a::b::c::d::u = l in
      help (i+1) ((new Tetravex.carre (int_of_string a) (int_of_string b) (int_of_string c) (int_of_string d) i)::q)
    with End_of_file -> q
  in help 0 []

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
  let lig1 = read_line () in
  let lis1 = Str.split (Str.regexp " ") lig1 in
  let n::q = lis1 in let p::q = lis1 in
  let n = int_of_string n in
  let p = int_of_string p in
  let q = readTetravex () in
  let t = new Tetravex.tetravex n p q in
  let solu = t#solve () in
  t#printSolution solu

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

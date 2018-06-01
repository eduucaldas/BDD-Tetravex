open PLLib
open BDT
open VariableInterfaces
module Type = CharType
module PL = PropositionalLogic(Type)
module DT = BDT(Type)
include Tetravex

let readTetravex () =
  let rec help i q=
    try
      let s = read_line () in
      let a, b, c, d = Scanf.sscanf s "%d %d %d %d " (fun a b c d -> (a, b, c, d)) in
      help (i+1) ((new Tetravex.carre a b c d i)::q)
    with End_of_file -> q
  in
  help 0 []

let dump () =
  let formule = PL.formule_of_input () in
  let bdd = DT.compress (DT.create_random formule) in
  DT.print bdd;
  exit 0

let valid () =
  let formule = PL.formule_of_input () in
  let bdd = DT.compress (DT.create_random formule) in
  if (DT.validity bdd) then exit 0 else exit (-1)

let satisfiable () =
  let formule = PL.formule_of_input () in
  let bdd = DT.compress (DT.create_random formule) in
  DT.print_satifiability bdd;
  exit 0

let tetravex () =
  let s = read_line () in
  let n, p = Scanf.sscanf s "%d %d" (fun a b -> (a, b)) in
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

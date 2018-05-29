include Tetravex
  


let readTetravex () =
  let rec help i q=
    try
      let lign = read_line () in
      let list = Str.split( Str.regexp " ") lign in
      let a::b::c::d::u = list in
      help (i+1) ((new Tetravex.domino (int_of_string a) (int_of_string b) (int_of_string c) (int_of_string d) i)::q)
    with End_of_file -> q
  in help 0 []



let () =
  let test_type = Sys.argv.(1) in
  if test_type = "bonjour"
  then
    let s = read_line ()
    in print_string s;
  else if test_type = "dump"
  then
    let s = input_line stdin in
    let bdd = IntBDD.createBDD (ReadFormule.eval s)
    in IntBDD.print bdd
  else if test_type = "valid"
  then 
    let s = input_line stdin in
    let bdd = IntBDD.createBDD (ReadFormule.eval s)
    in
    if  IntBDD.isValid bdd then print_int 0; 
  else if test_type = "satisfiable"
  then
    let s = input_line stdin in
    let bdd = IntBDD.createBDD (ReadFormule.eval s)
    in IntBDD.print_satisfact (IntBDD.satisfact bdd);
  else if test_type = "tetravex"
  then
    let lig1 = read_line () in
    let lis1 = Str.split (Str.regexp " ") lig1 in
    let n::q = lis1 in let p::q = lis1 in
    let n = int_of_string n in
    let p = int_of_string p in
    let q = readTetravex () in
    let t = new Tetravex.tetravex n p q in
    let solu = t#solve () in
    t#printsolu solu 
                                                   

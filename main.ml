include Tetravex
  


let readTetravex () =
  let rec help i q=
    try
      let lign = read_line () in
      let list = Str.split( Str.regexp " ") lign in
      let a::b::c::d::u = list in
      help (i+1) ((new Tetravex.carre (int_of_string a) (int_of_string b) (int_of_string c) (int_of_string d) i)::q)
    with End_of_file -> q
  in help 0 []



let () =
  let test_type = Sys.argv.(1) in
  if test_type = "tetravex"
  then
    let lig1 = read_line () in
    let lis1 = Str.split (Str.regexp " ") lig1 in
    let n::q = lis1 in let p::q = lis1 in
    let n = int_of_string n in
    let p = int_of_string p in
    let q = readTetravex () in
    let t = new Tetravex.tetravex n p q in
    let solu = t#solve () in
    t#printSolution solu 
                                                   

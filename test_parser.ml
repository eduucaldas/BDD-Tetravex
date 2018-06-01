open PLLib
module CPL = PropositionalLogic(CharType)

let () =
  (* Table of truth: OK*)
  let form1 = CPL.formule_of_str ("false && false") in
  assert (CPL.valuation_random form1 [] = false);
  let form2 = CPL.formule_of_str ("false && true") in
  assert (CPL.valuation_random form2 [] = false);
  let form3 = CPL.formule_of_str ("true && false") in
  assert (CPL.valuation_random form3 [] = false);
  let form4 = CPL.formule_of_str ("true && true") in
  assert (CPL.valuation_random form4 [] = true);
  let form5 = CPL.formule_of_str ("false <-> true") in
  assert (CPL.valuation_random form5 [] = false);
  let form6 = CPL.formule_of_str ("false <-> false") in
  assert (CPL.valuation_random form6 [] = true);
  let form7 = CPL.formule_of_str ("true <-> true") in
  assert (CPL.valuation_random form7 [] = true);
  let form8 = CPL.formule_of_str ("true <-> false") in
  assert (CPL.valuation_random form8 [] = false);
  let form9 = CPL.formule_of_str ("false -> true") in
  assert (CPL.valuation_random form9 [] = true);
  let form10 = CPL.formule_of_str ("false -> false") in
  assert (CPL.valuation_random form10 [] = true);
  let form11 = CPL.formule_of_str ("true -> true") in
  assert (CPL.valuation_random form11 [] = true);
  let form12 = CPL.formule_of_str ("true -> false") in
  assert (CPL.valuation_random form12 [] = false);
  let form13 = CPL.formule_of_str ("false || true") in
  assert (CPL.valuation_random form13 [] = true);
  let form14 = CPL.formule_of_str ("false || false") in
  assert (CPL.valuation_random form14 [] = false);
  let form15 = CPL.formule_of_str ("true || true") in
  assert (CPL.valuation_random form15 [] = true);
  let form16 = CPL.formule_of_str ("true || false") in
  assert (CPL.valuation_random form16 [] = true);
  let form17 = CPL.formule_of_str ("~true") in
  assert (CPL.valuation_random form17 [] = false);
  let form18 = CPL.formule_of_str ("~false") in
  assert (CPL.valuation_random form18 [] = true);
  (* Table of truth *)
  (* Parenthesis! *)
  let formP1 = CPL.formule_of_str ("(false && false)||(true && true)") in
  assert (CPL.valuation_random formP1 [] = true);
  let formP2 = CPL.formule_of_str ("(false -> false)&&(true <-> true)") in
  assert (CPL.valuation_random formP2 [] = true);
  let formP3 = CPL.formule_of_str ("(~false) && (false)") in
  assert (CPL.valuation_random formP3 [] = false);
  let formP4 = CPL.formule_of_str ("(~false) && (~(~(~false)))") in
  assert (CPL.valuation_random formP4 [] = true);
  (* Parenthesis! *)
  (* Variables! *)
  let formP1 = CPL.formule_of_str ("(a && false)||(a && true)") in
  assert (CPL.valuation_order formP1 ['a', true] = true);
  assert (CPL.valuation_order formP1 ['a', false] = false);
  let formP2 = CPL.formule_of_str ("(a -> false)&&(b <-> true)") in
  assert ((CPL.valuation_order formP2 ['a', false; 'b', true]) = true);
  let formP3 = CPL.formule_of_str ("(~b) && (c)") in
  assert (CPL.valuation_order formP3 ['b', false; 'c', false] = false);
  let formP4 = CPL.formule_of_str ("(a) || (~(~(~a)))") in
  assert (CPL.valuation_random (CPL.simplify formP4) [true] = true);
  (* Variables! *)

  (* Precedency! *)
  let formComplex1 = CPL.formule_of_str ("a && false||a && true") in
  assert (CPL.valuation_order formComplex1 ['a', true] = true);
  assert (CPL.valuation_order formComplex1 ['a', false] = false);
  let formComplex2 = CPL.formule_of_str ("a -> false&&b <-> true") in
  assert ((CPL.valuation_order formComplex2 ['a', false; 'b', true]) = true);
  let formComplex3 = CPL.formule_of_str ("~b && c") in
  assert (CPL.valuation_order formComplex3 ['b', false; 'c', false] = false);
  let formComplex4 = CPL.formule_of_str ("a || ~~~a") in
  assert (CPL.valuation_random (CPL.simplify formComplex4) [true] = true);
  let formComplex5 = CPL.formule_of_str ("true -> true -> false") in
  assert (CPL.valuation_random (CPL.simplify formComplex5) [] = false);
  let formComplex6 = CPL.formule_of_str ("false <-> false -> true") in
  assert (CPL.valuation_random (CPL.simplify formComplex6) [] = false);
  let formComplex7 = CPL.formule_of_str ("(false <-> false) && ~(false || (true -> true -> (true <-> true && false)))") in
  assert (CPL.valuation_random (CPL.simplify formComplex7) [] = true);



  (* Precedency! *)




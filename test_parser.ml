open PLLib
module CPL = PropositionalLogic(CharType)

let () =
  let form = CPL.formule_of_input ("true && false") in
  assert (CPL.valuation_random form [] = false)


open PLLib
module CPL = PropositionalLogic(CharType)

let () =
  let t = CPL.Boolean true in
  let f = CPL.Boolean false in
  let v = CPL.Variable 'v' in
  let formu_t1 = CPL.Bin_Op (t, CPL.op_or, f) in
  let formu_t2 = CPL.Bin_Op (f, CPL.arrow, v) in


  assert (CPL.valuation formu_t1 []);
  assert (CPL.valuation formu_t2 []);
  assert (CPL.valuation (CPL.Bin_Op (formu_t2, CPL.op_and, formu_t1)) []);
  assert (CPL.valuation (CPL.Bin_Op (v, CPL.op_and, formu_t1)) [true])

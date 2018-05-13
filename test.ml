open PLLib
module CPL = PropositionalLogic(CharType)

let () =
  let t = CPL.Boolean true in
  let f = CPL.Boolean false in
  let v = CPL.Variable 'v' in
  let formu_t1 = CPL.Bin_Op (t, CPL.op_or, f) in
  let formu_t2 = CPL.Bin_Op (f, CPL.arrow, v) in
  let p = CPL.Variable 'p' in
  let q = CPL.Variable 'q' in
  let r = CPL.Variable 'r' in
  let s = CPL.Variable 's' in
  let example = CPL.Bin_Op (CPL.Bin_Op (p, CPL.arrow, q), CPL.op_or, CPL.Bin_Op (r,CPL.op_and,s)) in

  assert (CPL.valuation_random formu_t1 []);
  assert (CPL.valuation_random formu_t2 []);
  assert (CPL.valuation_random (CPL.Bin_Op (formu_t2, CPL.op_and, formu_t1)) []);
  assert (CPL.valuation_random (CPL.Bin_Op (v, CPL.op_and, formu_t1)) [true]);
  assert (CPL.valuation_order example [('p', true);('q', true); ('r', false); ('s', false)])

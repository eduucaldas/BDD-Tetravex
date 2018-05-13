open PLLib
module CPL = PropositionalLogic(CharType)
module CBDD = BDD(CharType)
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
  let same_example = CPL.Bin_Op (CPL.Bin_Op (p, CPL.arrow, q), CPL.op_or, CPL.Bin_Op (r,CPL.op_and,s)) in
  let redundant_example = CPL.Bin_Op (p, CPL.op_or, CPL.Un_op (CPL.neg, p) ) in
  let bddexample = CBDD.compress (CBDD.create_order example ['r';'s';'q';'p']) in
  let bddsameexample = (CBDD.create_order same_example ['r';'s';'q';'p']) in
  let bddredundant_example = CBDD.compress (CBDD.create_random redundant_example ) in

  assert (CPL.valuation_random formu_t1 []);
  (* assert (CPL.valuation_random redundant_example []); *)
  assert (CPL.valuation_random formu_t2 []);
  assert (CPL.valuation_random (CPL.Bin_Op (formu_t2, CPL.op_and, formu_t1)) []);
  assert (CPL.valuation_random (CPL.Bin_Op (v, CPL.op_and, formu_t1)) [true]);
  assert (CPL.valuation_order example [('p', true);('q', true); ('r', false); ('s', false)]);
  assert (CBDD.equal bddsameexample bddexample);
  CBDD.print bddexample;
  assert (CBDD.validity bddredundant_example);
  CBDD.print_satifiability bddexample




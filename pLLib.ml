module type VariableType =
sig
  type t
  val equal : t -> t -> bool
end

module CharType =
struct
  type t = char
  let equal c1 c2 = (c1 = c2)
end


module PropositionalLogic(VT: VariableType) = struct
  type formule =
    | Boolean of bool
    | Variable of VT.t
    | Bin_Op of formule * (formule -> formule -> formule) * formule
    | Un_op of (formule -> formule) * formule

  let rec arrow l r = match (l,r) with
    | (Boolean false, _) -> Boolean true
    | (_, Boolean true) -> Boolean true
    | (Boolean true, Boolean false) -> Boolean false
    | _ -> Bin_Op (l, arrow, r)

  let rec double_arrow l r = match (l,r) with
    | (Boolean l, Boolean r) -> Boolean (l=r)
    | _ -> Bin_Op (l, arrow, r)

  let rec op_and l r = match (l,r) with
    | (Boolean false, _) -> Boolean false
    | (_, Boolean false) -> Boolean false
    | (Boolean true, Boolean true) -> Boolean true
    | _ -> Bin_Op (l, op_and, r)

  let rec op_or l r = match (l,r) with
    | (Boolean true, _) -> Boolean true
    | (_, Boolean true) -> Boolean true
    | (Boolean false, Boolean false) -> Boolean false
    | _ -> Bin_Op (l, op_or, r)

  let rec neg f = match f with
    | Boolean bf -> Boolean (not bf)
    | _ -> Un_op (neg, f)
  (* be cariful with the equality *)
  let eval_one formu var =
    let v = ref var in
    let rec simpl_rec form = match form with
      | Boolean b -> [|Boolean b; Boolean b|]
      | Bin_Op (l, con, r) -> Array.map2 con (simpl_rec l) (simpl_rec r)
      | Un_op (u, f) -> Array.map u (simpl_rec f)
      | Variable p -> match !v with
        | None -> v := Some p; [|Boolean false; Boolean true|]
        | Some vr when (VT.equal vr p) -> [|Boolean false; Boolean true|]
        | Some vr -> [|Variable p; Variable p|]
    in
    let possib = simpl_rec formu in
    (!v, possib.(0), possib.(1))

  let eval_random_v formu = eval_one formu None

  let eval_v formu var = eval_one formu (Some var)

  let rec simplify formu =
    match formu with
    | Bin_Op (l, con, r) -> con (simplify l) (simplify r)
    | Un_op (u, f) -> u (simplify f)
    | Boolean b -> formu
    | Variable p -> formu

  (* Simplifies a formule, using a list of booleans to be assigned to the variables in the order they appear, infix *)
  let eval_list formu l_ev =
    let simplify_step formu b = let (v, form_f, form_t) = eval_random_v formu in
      match b with
      | false -> form_f
      | true -> form_t
    in
    if l_ev = [] then simplify formu else List.fold_left simplify_step formu l_ev

  exception PartialValuation
  (* Perhaps check if we`re giving too many arguments *)
  let valuation formu l_ev =
    let evaluated_formu = eval_list formu l_ev in
    match evaluated_formu with
    | Boolean b -> b
    | _ -> raise PartialValuation

  (* TODO: Module to create formule from input *)


end

module BDD(VT: VariableType) =
struct
  type binary_tree =
    | Leaf of bool
    | Node of binary_tree * VT.t * binary_tree

  module PL = PropositionalLogic(VT)


  let rec create formu =
    match formu with
    | PL.Boolean b -> Leaf b
    | f -> let (v, form_f, form_t) = PL.eval_random_v formu in
      match v with
      | Some vr -> Node (create form_f, vr, create form_t)
      | None -> assert (form_f = form_t); create form_t



end


(* module Boolean =
   struct
   let minus b = not b
   let plus b1 b2 = (b1 || b2)
   let dot b1 b2 = (b1 && b2)
   end
*)

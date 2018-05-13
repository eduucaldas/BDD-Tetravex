
module type OrderedType =
sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
end

module CharType =
struct
  type t = char
  let equal c1 c2 = Char.equal c1 c2
  let compare c1 c2 = Char.compare c1 c2
end


module PropositionalLogic(VT: OrderedType) = struct
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

  let double_arrow l r = match (l,r) with
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

  (* be careful with the equality *)
  let eval_one formu var =
    let v = ref var in
    let rec simpl_rec form = match form with
      | Boolean b -> [|Boolean b; Boolean b|]
      | Bin_Op (l, con, r) -> Array.map2 con (simpl_rec l) (simpl_rec r)
      | Un_op (u, f) -> Array.map u (simpl_rec f)
      | Variable p -> match !v with
        | None -> v := Some p; [|Boolean false; Boolean true|]
        | Some vr when (VT.equal vr p) -> [|Boolean false; Boolean true|]
        | _ -> [|Variable p; Variable p|]
    in
    let possib = simpl_rec formu in
    (!v, possib.(0), possib.(1))

  let eval_random_v formu = eval_one formu None

  let eval_v formu var = eval_one formu (Some var)

  let rec simplify formu =
    match formu with
    | Bin_Op (l, con, r) -> con (simplify l) (simplify r)
    | Un_op (u, f) -> u (simplify f)
    | Boolean _ -> formu
    | Variable _ -> formu

  let choose v_ff_ft b =
    let (_, form_f, form_t) = v_ff_ft in
    match b with
    | false -> form_f
    | true -> form_t

  (* Simplifies a formule, using a list of booleans to be assigned to the variables in the order they appear, infix *)
  let eval_list_random formu l_b =
    let eval_step formul b = choose (eval_random_v formul) b in
    let simple_formu = simplify formu in
    List.fold_left eval_step simple_formu l_b

  (* In this one we especify the order by givin the variables with the booleans *)
  let eval_order formu l_ev =
    let eval_step formul match_var_b =
      let var, b = match_var_b in
      choose (eval_v formul var) b
    in
    let simple_formu = simplify formu in
    List.fold_left eval_step simple_formu l_ev

  exception PartialValuation
  (* Perhaps check if we`re giving too many arguments *)
  let valuation_random formu l_b =
    let evaluated_formu = eval_list_random formu l_b in
    match evaluated_formu with
    | Boolean b -> b
    | _ -> raise PartialValuation

  let valuation_order formu l_ev =
    let evaluated_formu = eval_order formu l_ev in
    match evaluated_formu with
    | Boolean b -> b
    | _ -> raise PartialValuation

  (* TODO: Module to create formule from input *)


end

module BDD(VT: OrderedType) : OrderedType =
struct
  type binary_tree =
    | Leaf of bool
    | Node of binary_tree * VT.t * binary_tree
  type t = binary_tree
  let rec compare bt1 bt2 = match (bt1, bt2) with
    | (Leaf l1, Leaf l2) -> (
        match (l1, l2) with
        | (true, false) -> 1
        | (false, false) -> -1
        | _ -> 0
      )
    | (Leaf _, _) -> -1
    | (_, Leaf _) -> 1
    | (Node (l1, v1, r1), Node (l2, v2, r2)) ->
      match VT.compare v1 v2 with
      | 0 -> (
          match compare l1 l2 with
          | 0 -> compare r1 r2
          | d -> d
        )
      | c -> c
  let equal bt1 bt2 = (compare bt1 bt2 = 0)

  module PL = PropositionalLogic(VT)

  let rec create_random formu =
    match formu with
    | PL.Boolean b -> Leaf b
    | _ -> let (v, form_f, form_t) = PL.eval_random_v formu in
      match v with
      | Some vr -> Node (create_random form_f, vr, create_random form_t)
      | None -> assert (form_f = form_t); create_random form_t

  let of_list l =
    let q = Queue.create () in
    List.iter ((Core.Fn.flip Queue.push) q) l; q

  exception InsufficientEvaluations


  let create_order formu l_v =
    let q = of_list l_v in
    let rec create_rec formul =
      match formul with
      | PL.Boolean b -> Leaf b
      | _ -> if Queue.is_empty q then raise InsufficientEvaluations else
          let (v, form_f, form_t) = PL.eval_v formul (Queue.pop q) in
          match v with
          | Some vr -> Node (create_rec form_f, vr, create_rec form_t)
          | None -> assert (form_f = form_t); create_rec form_t
    in
    create_rec formu


  (* for this we need a hashtbl to check whether the element was found already  *)
  (* let compress dec_tree =
     module found_trees = Set.Make(BDD)
      match decision_tree with
      | Leaf l -> Leaf l
      |  -> expr2 *)

end



(* module Boolean =
   struct
   let minus b = not b
   let plus b1 b2 = (b1 || b2)
   let dot b1 b2 = (b1 && b2)
   end
*)

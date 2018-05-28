
module type OrderedType =
sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
end


module type VariableType =
sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val str : t -> string
end

module CharType =
struct
  type t = char
  let equal c1 c2 = Char.equal c1 c2
  let compare c1 c2 = Char.compare c1 c2
  let str c = Char.escaped c
end


module PropositionalLogic(VT: VariableType) = struct
  (*Fundamental to understand*)
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

  (*Backbone function:
    evaluates the formula with 'var' = true and false and returns the triplet ('var', formula with true, -//- with false)
    If 'var' = None then we just pick the first we find
    In case we don`t find 'var' we simplify the formula and return (None, simple_formu, simple_formu)
  *)
  let eval_one formu var =
    let v = ref var in
    let found = ref false in
    let rec simpl_rec form = match form with
      | Boolean b -> [|Boolean b; Boolean b|]
      | Bin_Op (l, con, r) -> Array.map2 con (simpl_rec l) (simpl_rec r)
      | Un_op (u, f) -> Array.map u (simpl_rec f)
      | Variable p -> match !v with
        | None -> v := Some p; found := true; [|Boolean false; Boolean true|]
        | Some vr when (VT.equal vr p) -> found := true; [|Boolean false; Boolean true|]
        | _ -> [|Variable p; Variable p|]
    in
    let possib = simpl_rec formu in
    ((if !found then (!v) else None), possib.(0), possib.(1))

  let eval_random_v formu = eval_one formu None

  let eval_v formu var = eval_one formu (Some var)

  let rec simplify formu =
    match formu with
    | Bin_Op (l, con, r) -> con (simplify l) (simplify r)
    | Un_op (u, f) -> u (simplify f)
    | Boolean _ -> formu
    | Variable _ -> formu

  (*auxiliary function, don`t bother*)
  let choose v_ff_ft b =
    let (_, form_f, form_t) = v_ff_ft in
    match b with
    | false -> form_f
    | true -> form_t

  (* Evaluates a formule, using a list of booleans to be assigned to the variables in the order they appear, infix *)
  let eval_list_random formu l_b =
    let eval_step formul b = choose (eval_random_v formul) b in
    let simple_formu = simplify formu in
    List.fold_left eval_step simple_formu l_b

  (* Evaluates a formule, using the list of (var, bool), for each var assigns the corresponding bool *)
  let eval_order formu l_vb =
    let eval_step formul match_var_b =
      let var, b = match_var_b in
      choose (eval_v formul var) b
    in
    let simple_formu = simplify formu in
    List.fold_left eval_step simple_formu l_vb

  (*Just ensure that we evaluated stuff completely*)
  exception PartialValuation

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

  (*Function to clean all the spaces and transform the symbols into a one char symbol in order
    to tokenize the original string
    input = string f_string
    output = compact_f_string
    equivalence map 
    original string/tokenized string 
    
    " "/"" , it means we take out all spaces 
    true/t
    false/f
    &&/&
    ||/|
    <->/=
    ->/>
  
    *)
  let compact_input f_string = 
    (*Str.regexp string, gets a string and returns a regexp type corresponding to that string*)
    let regexp_space = Str.regexp " " in
    let regexp_true = Str.regexp "true" in
    let regexp_false = Str.regexp "false" in
    let regexp_AND = Str.regexp "&&" in
    let regexp_OR = Str.regexp "||" in 
    let regexp_equivalence = Str.regexp "<->" in
    let regexp_implication = Str.regexp "->" in
    let step1 = Str.global_replace regexp_space "" f_string in
    let step2 = Str.global_replace regexp_true "t" step1 in
    let step3 = Str.global_replace regexp_false "f" step2 in
    let step4 = Str.global_replace regexp_AND "&" step3 in
    let step5 = Str.global_replace regexp_OR"|" step4 in
    let step6 = Str.global_replace regexp_equivalence "=" step5 in
    Str.global_replace regexp_implication ">" step6

    (*O objetivo no final é criar uma liste de types com o primeiro item tendo a maior priridade. 
      Daí fica mais suave criar a árvore *)

  type grammaire = 
        | Integer of int
        | Parenthese_open
        | Parenthese_close
        | Vrai
        | Faux
        | Neg
        | Et
        | Ou
        | Implique
        | Equivalence
    
  let print = function
        | Integer(x) -> string_of_int x
        | Parenthese_open -> "("
        | Parenthese_close -> ")"
        | Vrai -> "true"
        | Faux -> "false"
        | Neg -> "~"
        | Et -> "&&"
        | Ou -> "||"
        | Implique -> "->"
        | Equivalence -> "<->"

  let create_liste_from_string s =
        let size = String.length s in
        let rec aux i current_number =
            if i = size then
                if current_number != 0 then
                    [Integer(current_number)]
                else
                    []
            else
                let v = (int_of_char s.[i]) - (int_of_char '0') in
                if v >= 0 && v <= 9 then
                    aux (i + 1) (current_number * 10 + v)
                else
                    let a = if current_number != 0 then [Integer(current_number)] else [] in
                    let d =
                    match s.[i] with
                    | '(' -> Parenthese_open
                    | ')' -> Parenthese_close
                    | 't' -> Vrai
                    | 'f' -> Faux
                    | '~' -> Neg
                    | '&' -> Et
                    | '|' -> Ou
                    | '>' -> Implique
                    | '=' -> Equivalence
                    | _ -> Integer(-1) (* ERROR *)
                    in
                    a@(d::(aux (i + 1) 0))
        in
        aux 0 0


  let read_formule_to_liste input_string = create_liste_from_string (compact_input input_string)

end



module BDD(VT: VariableType) =
struct
  type binary_tree =
    | Leaf of bool
    | Node of binary_tree * VT.t * binary_tree

  let rec compare bt1 bt2 = match (bt1, bt2) with
    | (Leaf l1, Leaf l2) -> (
        match (l1, l2) with
        | (true, false) -> 1
        | (false, true) -> -1
        | _ -> 0
      )
    | (Leaf _, _) -> -1
    | (_, Leaf _) -> 1
    | (Node (l1, v1, r1), Node (l2, v2, r2)) ->
      match (VT.compare v1 v2) with
      | 0 -> (
          match (compare l1 l2) with
          | 0 -> (compare r1 r2)
          | d -> d
        )
      | c -> c

  let equal bt1 bt2 = ((compare bt1 bt2) = 0)

  module PL = PropositionalLogic(VT)

  (* Create BDD with no special order *)
  let rec create_random formu =
    match formu with
    | PL.Boolean b -> Leaf b
    | _ -> let (v, form_f, form_t) = PL.eval_random_v formu in
      match v with
      | Some vr -> Node (create_random form_f, vr, create_random form_t)
      | None -> create_random (form_t)

  (* Creates a BDD following the order of var in l_v *)
  exception InsufficientEvaluations

  let rec create_order formu l_v =
    match (PL.simplify formu) with
    | PL.Boolean b -> Leaf b
    | _ -> match l_v with
      | [] -> raise InsufficientEvaluations
      | h::t -> let (v, form_f, form_t) = PL.eval_v formu h in
        match v with
        | Some vr -> let (btf , btt) = (create_order form_f t,create_order form_t t) in (* bt is short for binary tree, f and t are short for false and true *)
          if (equal btt btf) then btf else Node (btf, vr, btt) (*this case the variable was found and evaluated, if btf = btt then this variable changes nothing*)
        | None -> create_order formu t (* in this case the variable we tried to evaluate was redundant or inexistant, then try another *)

  (* compress the BDD, by turning it into a graph, to keep from having the same subtrees over and over *)
  let compress dec_tree =
    let found_trees = Hashtbl.create 54 in
    let f = Leaf false in let t = Leaf true in
    let rec compress_rec dt =
      match dt with
      | Leaf l -> if l then t else f
      | Node (dtf, v, dtt) ->
        let (dtf_zip, dtt_zip) = (compress_rec dtf, compress_rec dtt) in
        let dt_zip = (if (equal dtf_zip dtt_zip) then dtf_zip else Node (dtf_zip, v, dtt_zip)) in
        Hashtbl.add found_trees v dt_zip; dt_zip
    in
    compress_rec dec_tree

  let print dec_tree =
    let tree_id = Hashtbl.create 54 in
    Hashtbl.add tree_id dec_tree "0";
    Hashtbl.add tree_id (Leaf true) "@t";
    Hashtbl.add tree_id (Leaf false) "@f";
    let counter = ref 1 in
    let str dt = Hashtbl.find tree_id dt in
    let discover dt = Hashtbl.add tree_id dt (string_of_int !counter); counter := !counter + 1 in
    let rec print_rec dt =
      match dt with
      | Leaf _ -> ()
      | Node (dtf, v, dtt) -> Printf.printf "%s %s " (str dt) (VT.str v);
        match (Hashtbl.find_opt tree_id dtt, Hashtbl.find_opt tree_id dtf) with
        | None, None -> discover dtt;discover dtf;Printf.printf "%s %s\n" (str dtt) (str dtf); print_rec dtt; print_rec dtf;
        | None, Some s  -> discover dtt; Printf.printf "%s %s\n" (str dtt) s; print_rec dtt;
        | Some s, None  -> discover dtf; Printf.printf "%s %s\n" s (str dtf); print_rec dtf;
        | Some s1, Some s2 -> Printf.printf "%s %s\n" s1 s2;
    in
    print_rec dec_tree

  let rec validity dec_tree =
    match dec_tree with
    | Leaf f -> f
    | Node (dtf, _, dtt) -> (validity dtf) || (validity dtt)

  let rec satisfiability dec_tree =
    match dec_tree with
    | Leaf f -> if f then Some [] else None
    | Node (dtf, v, dtt) -> match (satisfiability dtf,satisfiability dtt)  with
      | None, None -> None
      | Some l, _ -> Some ((v,false)::l)
      | None, Some l -> Some ((v,true)::l)

  let print_satifiability dec_tree =
    let path = satisfiability dec_tree in
    let print_pair vb = let (v, b) = vb in
      match b with
      | true -> Printf.printf "(%s, @t)\n" (VT.str v)
      | false -> Printf.printf "(%s, @f)\n" (VT.str v)
    in
    match path with
    | None -> Printf.printf "Not satisfiable"
    | Some l -> List.iter print_pair l

end

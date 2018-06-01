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
  val to_t : string -> t option
end

module CharType =
struct
  type t = char
  let equal c1 c2 = (c1 = c2) 
  let compare c1 c2 = Char.compare c1 c2
  let str c = Char.escaped c
  let to_t s = match String.length s with
    | 1 -> Some s.[0]
    | _ -> None
end

module IntegerType =
struct
  type t = int
  let equal c1 c2 = (c1 = c2)
  let compare c1 c2 = (c1 - c2)
  let str c = string_of_int c
  let to_t s = int_of_string_opt s
end


module PropositionalLogic(VT: VariableType) = struct
  (*Fundamental to understand*)
  type formule =
    | Boolean of bool
    | Variable of VT.t
    | Bin_Op of formule * (formule -> formule -> formule) * formule
    | Un_op of (formule -> formule) * formule

  let rec neg f = match f with
    | Boolean bf -> Boolean (not bf)
    | Un_op (neg, g) -> g
    | _ -> Un_op (neg, f)

  let rec arrow l r = match (l,r) with
    | (Boolean false, _) | (_, Boolean true) -> Boolean true
    | (Boolean true, k)  -> k
    | (k, Boolean false) -> (neg k)
    | _ -> Bin_Op (l, arrow, r)

  let rec double_arrow l r = match (l,r) with
    | (Boolean true, k) | (k, Boolean true) -> k
    | (Boolean false, k) | (k, Boolean false) -> (neg k)
    | (Un_op (neg, k), _) | (_, Un_op (neg, k)) -> Un_op (neg, double_arrow k r)
    | _ -> Bin_Op (l, double_arrow, r)

  let rec op_and l r = match (l,r) with
    | (Boolean false, _) | (_, Boolean false) -> Boolean false
    | (Boolean true, k) | (k, Boolean true) -> k
    | _ -> Bin_Op (l, op_and, r)

  let rec op_or l r = match (l,r) with
    | (_, Boolean true) | (Boolean true, _) -> Boolean true
    | (Boolean false, k) | (k, Boolean false) -> k
    | _ -> Bin_Op (l, op_or, r)



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

  (* ################### LEXING #####################*)

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
    TEST: OK
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
    let step2 = Str.global_replace regexp_true "T" step1 in
    let step3 = Str.global_replace regexp_false "F" step2 in
    let step4 = Str.global_replace regexp_AND "&" step3 in
    let step5 = Str.global_replace regexp_OR"|" step4 in
    let step6 = Str.global_replace regexp_equivalence "=" step5 in
    Str.global_replace regexp_implication ">" step6

  (* The final objective is to create a list of types, with the first item having the greatest priority *)
  (* Lexic *)
  type token =
    | Var_tok of VT.t
    | Parenthesis_open
    | Parenthesis_close
    | True
    | False
    | Neg
    | And
    | Or
    | Implies
    | Equivalence

  let token2str = function
    | Var_tok (x) -> VT.str x
    | Parenthesis_open -> "( "
    | Parenthesis_close -> " )"
    | True -> "True"
    | False -> "False"
    | Neg -> "not "
    | And -> " A "
    | Or -> " V "
    | Implies -> " => "
    | Equivalence -> " <=> "


  let not_var2token c =
    match c with
    | '(' -> Some Parenthesis_open
    | ')' -> Some Parenthesis_close
    | 'T' -> Some True
    | 'F' -> Some False
    | '~' -> Some Neg
    | '&' -> Some And
    | '|' -> Some Or
    | '>' -> Some Implies
    | '=' -> Some Equivalence
    | _ -> None

  let var2token s =
    match VT.to_t s with
    | Some var -> Some (Var_tok (var))
    | _ -> None

  exception Invalid_variable of string
  exception Invalid_formula of string

  (* turns string into list of tokens *)
  (* Many many things to test, better assume that the input is ok *)
  let tokenize s =
    let size = String.length s in
    let isolate_var begin_var =
      let rec isolate_var_rec end_var =
        if end_var = size then (end_var, String.sub s begin_var (end_var-begin_var)) else
          match s.[end_var] with
          | ')' | '&' | '|' | '>' | '=' -> (end_var, String.sub s begin_var (end_var - begin_var))
          | 'T' | 'F' | '~' | '('  -> raise (Invalid_formula s)
          | _ -> isolate_var_rec (end_var + 1)
      in
      isolate_var_rec (begin_var+1)
    in
    let rec tokenize_rec i =
      if i = size then [] else
        match not_var2token s.[i] with
        | Some tok -> tok::tokenize_rec (i+1)
        | None ->
          let (new_i, var_str) = (isolate_var i) in
          match var2token var_str with
          | Some tok -> tok::tokenize_rec new_i
          | None -> raise (Invalid_variable var_str)
    in
    tokenize_rec 0

  (* string to list of tokes *)
  let tokenize_str input_string = tokenize (compact_input input_string)

  let rec print_tokenized lt = match lt with
    | [] -> Printf.printf "\n"
    | h::t -> Printf.printf "%s" (token2str h); print_tokenized t
  (*#################################################*)
  (* Auxiliary functions*)
  let flip f a b = f b a
  let comp f g x = f (g x)

  (* #####################PARSING##################### *)


  (* Parsing by token *)
  (* We interpret each kind of token in a step, following precedency *)
  (* Expression can be an uninterpreted token or an interpreted formule *)
  type expression =
    | Tok of token
    | Formule of formule

  (* First: interpret atoms!
     atom =
     | Boolean
     | Variable
     | Formule
  *)
  (* if atom then interpret it to formule *)
  let rm_atom atom =
    match atom with
    | Tok True -> Formule (Boolean true)
    | Tok False -> Formule (Boolean false)
    | Tok (Var_tok v) -> Formule (Variable v)
    | _ -> atom

  let interpret_atom l_expr =
    List.map rm_atom l_expr

  (* Second: interpret negations *)
  let rm_neg r =
    match r with
    | Formule f  -> Formule (neg f)
    | _ -> assert false

  let rec interpret_neg l_expr =
    match l_expr with
    | [] -> []
    | h::t -> let l = h::(interpret_neg t) in
      match l with
      | (Tok Neg)::r::tt -> (rm_neg r)::tt
      | _ -> l


  (* Interpreting operators *)
  (* token to corresponding formule constructor *)
  let op2fun op =
    match op with
    | And -> op_and
    | Or -> op_or
    | Implies -> arrow
    | Equivalence -> double_arrow
    | _ -> assert false

  let rm_op op l r =
    match l,r with
    | Formule l, Formule r -> Formule ((op2fun op) l r)
    | _ -> assert false

  (* interprets all operators op in a list of tokens *)
  let interpret_op op l_expr =
    let rec rm_all_op le =
      match le with
      | [] | _::[] | _::_::[] -> le
      | l::c::r::t ->
        match l,c,r with
        | (_, Tok maybe_op, _) when maybe_op = op -> rm_all_op ((rm_op op l r)::t)
        | _ -> l::(rm_all_op (c::r::t))
    in
    rm_all_op l_expr

  (* Same as last but right associative, as the arrow is *)
  let rec interpret_arrow l_expr =
    match l_expr with
    | [] | _::[] -> l_expr
    | l::c::t ->
      let nt = interpret_arrow t in
      match l, c, nt with
      | (_, Tok maybe_op, r::ntt) when maybe_op = Implies ->
        (rm_op Implies l r)::ntt
      | _ -> l::c::nt

  (* Interprets binary operators in order of precedency *)
  let interpret_all_op l_expr =
    let no_and = interpret_op And l_expr in
    let no_or = interpret_op Or no_and in
    let no_arrow = interpret_arrow no_or in
    let no_eq = interpret_op Equivalence no_arrow in
    no_eq

  (* Interpret simple expression, i.e. no parenthesis *)
  let interpret_simple l_expr =
    let no_atom = interpret_atom l_expr in
    let no_neg = interpret_neg no_atom in
    match interpret_all_op no_neg with
    | [f] -> f
    | _ -> assert false

  (* Interpret complex expression, i.e. with parenthesis *)
  let interpret_complex l_tok =
    (* reduce recursively solves all parenthesis returning their corresponding formula *)
    let rec reduce head tail =
      match tail with
      | [] -> List.rev head
      | h::t -> (
          match h with
          | Tok Parenthesis_open -> reduce head (reduce [] t)
          | Tok Parenthesis_close -> (interpret_simple (List.rev head))::t
          | _ -> reduce (h::head) t
        )
    in
    let tok2expr tok = Tok (tok) in
    let l_expr = List.map tok2expr l_tok in
    match interpret_simple (reduce [] l_expr) with
    | Formule f -> f
    | _ -> assert false

  let formule_of_str str = interpret_complex (tokenize_str str)

  let formule_of_input () =
    let raw_str = read_line () in
    formule_of_str raw_str

  (* ############################################### *)
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
    let found_trees = Hashtbl.create 5000 in
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


(*   (* while iterating through list of tokens one could have an operator or an atom (Variable, Boolean)
       To have an elegant algorithm we created an iterator, that iterates from left to right on the list
       And keeps the resulting formula to the present moment:
       It may be a constant iterator, corresponding to a complete formule
       Or an operating one, corresponding to the application of an operation taking the left formule
    *)
       let constIt base a = base
       let idIt form = form
       let get_form iterator = iterator (Boolean true)


       let formule_of_tokens list_tokens =
       let buffer = Queue.create () in
       List.iter ((flip Queue.push) buffer) list_tokens;
       let rec form_of_tok iterator =
        if Queue.is_empty buffer then iterator else
          let curr = Queue.pop buffer in
          if curr = Parenthesis_close then iterator else
            let new_it =
              (match curr with
               | Parenthesis_open -> (comp iterator (form_of_tok idIt))
               | Parenthesis_close -> assert false
               | Var_tok v -> comp iterator (constIt (Variable v))
               | True -> comp iterator (constIt (Boolean true))
               | False -> comp iterator (constIt (Boolean false))
               | Neg -> comp iterator neg
               | And -> op_and (get_form iterator)
               | Or -> op_or (get_form iterator)
               | Implies -> arrow (get_form iterator)
               | Equivalence -> double_arrow (get_form iterator)
              )
            in
            form_of_tok new_it
       in
       get_form (form_of_tok idIt)
*)

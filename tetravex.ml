
module type Variable = sig
    type t
    val equal: t -> t -> bool
    val compare: t -> t -> int
    val hash: t -> int
    val toString: t -> string
end

module StringVar : Variable with type t = string = struct
    type t = string
    let equal x y = (x = y) 
    let compare = Pervasives.compare
    let hash x = int_of_string x
    let toString x = x
end


module GeneralBDDTetravex(VT: Variable) = 
struct

  type bdd = 
    | True
    | False
    | BddNode of int * VT.t * bdd * bdd 

  let getID = function 
    | True -> 1
    | False -> 0
    | BddNode (id, _, _,_) -> id

  let equalBDD bddA bddB = (getID bddA = getID bddB)


(*************************************** BDDNode creation***********************************)

  (*
    We are going to create a HashTable that will save all  bdd's created in one moment in the process
    This will save processement time and will not create bdd's in vain. 
    HashTable: BDDdatabase
    Object Structure to create this Hashtable: HashNodeStructure
    Strutu
  *)
  module HashNodeStructure = struct
        (*Node Type to be entered in the HashTable*)
        type t = VT.t*int*int
        
        let hash (v, g, d) =
            Hashtbl.hash (v,g,d)

        let equal (v1, g1, d1) (v2, g2, d2) =
            v1 = v2 && g1 = g2 && d1 = d2
        
    end
  
  module HTBDDdatabse = Hashtbl.Make(HashNodeStructure)

  (*We ramdonly choose one start id number
    At each Node creation, the counter will go up every time we add a Node in the 
    HashTable. The HashTable also will grow if the number of Nodes grow and overcome 100
  *)
  let currID = ref 2016
  let nodeSet  = HTBDDdatabse.create 100  

  let addNode value bddLeft bddRight = 
    let idL = getID bddLeft in
    let idR = getID bddRight in
    if idL = idR
    then bddLeft
    else
      try
        HTBDDdatabse.find nodeSet (value, idL, idR)
      with Not_found -> (*If the bdd was not created yet, we add him in the HashTable*)
        let newID = !currID
        in currID := newID + 1;
        let newNode = BddNode(newID,value,bddLeft,bddRight)
        in HTBDDdatabse.add nodeSet (value, idL, idR) newNode; 
        newNode

  (******************************Hashtable for relations between BDDs***********************************)

  (*
    We will now create a second type of HashTable intending to save all the results given
    by the operations between two bdd's 
    HashTable: 
    Hashtable Object: RelationbetweenBDDsStructure
    Containers: In order to use the same Hashtable, we are going to create 4 different


  *)


  module RelationbetweenBDDsStructure = struct
    type t = int * int
    
    let hash (a,b) = Hashtbl.hash (a, b)

    let equal (a1,b1) (a2,b2) =
      a1 = a2 && b1 = b2
  end
  (*Containers for each operation*)
  module HTRelationbetweenBDDsDatabase = Hashtbl.Make(RelationbetweenBDDsStructure) 
  let notContainer =  Hashtbl.create 5000
  let andContainer = HTRelationbetweenBDDsDatabase.create 5000
  let orContainer = HTRelationbetweenBDDsDatabase.create 5000

(*********************************Negation/Not relation between BDDs***********************************)
      
    let rec notBDDTetravex bdd =
      match bdd with
      | False -> True
      | True -> False
      | BddNode(id, v, g, d) ->
        try
          Hashtbl.find notContainer id
        with Not_found ->
          let newNode = addNode v (notBDDTetravex g)  (notBDDTetravex d)
          in Hashtbl.add notContainer id newNode;
          newNode

(***************************************AND relation between BDDs***********************************)        
    
      
    let rec andBDDTetravex bdd1 bdd2 =
      match bdd1, bdd2 with
      |True, _ -> bdd2
      |False, _ -> False
      |_, True -> bdd1
      |_, False -> False
      |BddNode(id1, v1, g1, d1), BddNode(id2, v2, g2, d2) ->
         if id1 = id2
         then
           bdd1
         else
           let key = if id1 < id2 then (id1, id2) else (id2, id1)
           in try HTRelationbetweenBDDsDatabase.find andContainer key
               with Not_found ->
                 let newNode =
                   if v1 = v2
                   then
                     addNode v1 (andBDDTetravex g1 g2) (andBDDTetravex d1 d2)
                   else if v1 < v2
                   then
                     addNode v1 (andBDDTetravex g1 bdd2) (andBDDTetravex d1 bdd2)
                   else
                     addNode v2 (andBDDTetravex bdd1 g2) (andBDDTetravex bdd1 d2)
                 in HTRelationbetweenBDDsDatabase.add andContainer key newNode;
                 newNode


(***************************************Or relation between BDDs***********************************)

    
      
    let rec orBDDTetravex bdd1 bdd2 =
      match bdd1, bdd2 with
      |True, _ -> True
      |False, _ -> bdd2
      |_, True -> True
      |_, False -> bdd1
      | BddNode(id1, v1, g1, d1), BddNode(id2, v2, g2, d2) ->
         if id1 = id2
         then
           bdd1
         else
           let key = if id1 < id2 then (id1, id2) else (id2, id1)
           in try HTRelationbetweenBDDsDatabase.find orContainer key 
               with Not_found ->
                 let newNode =
                   if v1 = v2
                   then
                     addNode v1 (orBDDTetravex g1 g2) (orBDDTetravex d1 d2)
                   else if v1 < v2
                   then
                     addNode v1 (orBDDTetravex g1 bdd2) (orBDDTetravex d1 bdd2)
                   else
                     addNode v2 (orBDDTetravex bdd1 g2) (orBDDTetravex bdd1 d2)
                 in HTRelationbetweenBDDsDatabase.add orContainer (id1, id2) newNode;
                 newNode
                   
(***************************************Implies relation between BDDs***********************************)

    let bdd1Impliesbdd2BDD bdd1 bdd2 =
      orBDDTetravex (notBDDTetravex bdd1) bdd2  

    let rec satisfact = function
      | True -> (true, [])
      | False -> (false, [])
      | BddNode(_, var, a, b) -> let (b1, l1) = satisfact a in
        if b1 then (true, (var, true)::l1)
        else let (b2, l2) = satisfact b in (b2, (var, false)::l2)  



end

module BDDTetravex = GeneralBDDTetravex(StringVar)




(*include module with bdd`s ---------------------------------------------------------------------
include Bddtetravex*)

(*Module to wrap the class of carres et tetravex*)
module Tetravex = 
	struct



		(*Carre class
		  Class with the small squares to be put in the larger grid*)
		class carre (up:int) (down:int) (left:int) (right:int) (identity:int) =
		  	object
		  		method id = identity
		  		method get_up = up
		  		method get_down = down
		  		method get_left = left
		  		method get_right= right
		

		  	end

		(*Tetravex puzzle class with 
		 
		*)
	  	class tetravex (n:int) (p:int) (carres_list: carre list) =
	  		object(self)
	  			
	  			val n = n
	  			val p = p
	  			val carres_list = carres_list

	  			(* auxiliary function to print the fields from a carre*)
	  			method printCarre (carre: carre) = 
	  				print_int carre#get_up;
	  				print_string " ";
	  				print_int carre#get_down;
	  				print_string " ";
	  				print_int carre#get_left;
	  				print_string " ";
	  				print_int carre#get_right;
	  				print_string "\n";

	  			(* auxiliary function to find a carre in the position i, j in the grid
				   q is a string list with  ( x, y : id) meaning that in the (x, y) position 
				   of the grid, the carre with identity id is the one in this place
	  			*)
  				
  				method find_carre i j q =
                 let rec aux i j q =
                   match q with
                   |[] -> -1
                   |s::b ->
                     let s = Str.global_replace(Str.regexp ",") ":"  s in
                     let list = Str.split(Str.regexp ":") s in
                     let x::y::id::d = list in
                     if (int_of_string x) = i && (int_of_string y) = j
                     then (int_of_string id)
                     else aux i j b
                 in  aux i j q 

                 (* Method used to find and print the carre with identity id 
				   input : carre's identity id 
                	*)


                method findANDprintcarre id =
                   let rec aux id q = match q with
                   |[] -> ()
                   |a::b -> if a#id = id then
                       self#printCarre a
                     else aux id b
                   in aux id carres_list
                (* Method used 
                 print the solution 
				   input : is a string list with  ( x, y : id) meaning that in the (x, y) position 
				   of the grid, the carre with identity id is the one in this place
				   output: printing in the output method
                	*)

                method printSolution q = 
                	for i = 1 to n   do
                	  for j = 1 to p do
                	    let id = self#find_carre i j q in
                	    self#findANDprintcarre id
                	  done
                	done

                (* Method used to discover what are the possible options at the right of a carre
                	in the grid at a b
				   input : a b 
                	*)


                (*8888888888888888888888888888888888888888888888888888888888888888888888*)
                (* returns the BDD with the value *)

                method formulePlacement dom a b = (*TODO*)
                    BDDTetravex.addNode ((string_of_int b) ^ "," ^ (string_of_int a) ^ ":" ^ (string_of_int dom#id)) False True
                (*
					This method checks the possible carres at the right side of a certain position 

					input carre_analised is the carre to be analised if he is uniquely placed in the position a b
					in the grid
					output
						false if there is no other 
						true (?) list of other carres that could be put at the right side

                *)



                method obligeRightCarre_to_belong a b (carre_analised: carre) (liste: carre list) = 
                    match liste with
                    | [] -> BDDTetravex.False
                    | t::q ->
                        if t#id = carre_analised#id then (*Checks to see if the next carre is not the analised one*)
                            self#obligeRightCarre_to_belong a b carre_analised q
                        else if (t#get_left = carre_analised#get_right) then (*If the next carre cand be put at the right side of the analised one, we add him in the result*)
                            let f = self#formulePlacement t (a + 1) b in (*TODO*)
                            BDDTetravex.orBDDTetravex(f) (self#obligeRightCarre_to_belong a b carre_analised q) (*TODO*)
                        else
                            self#obligeRightCarre_to_belong a b carre_analised q

                method obligeDownCarre_to_belong a b (carre_analised: carre) (liste: carre list) = 
                    match liste with
                    | [] -> BDDTetravex.False
                    | t::q ->
                        if t#id = carre_analised#id then
                            self#obligeDownCarre_to_belong a b carre_analised q
                        else if (t#get_up = carre_analised#get_down) then
                            let f = self#formulePlacement t a (b + 1) in (*TODO*)
                            BDDTetravex.orBDDTetravex f (self#obligeDownCarre_to_belong a b carre_analised q) (*TODO*)
                        else
                            self#obligeDownCarre_to_belong a b carre_analised q 
                (*
					Each carre got in the input can only be used once. 
					This method checks if the carre_analised is uniquely placed in a b. In others words, 
					uniquelyPlacedIn c a b will return true only if c is not also placed in any other
					square in the grid
					input carre_analised is the carre to be analised if he is uniquely placed in the position a b
					in the grid

                *)

                method uniquelyPlacedIn carre_analised a b = (*TODO*)
                    let rec aux u v =
                        if u > n then
                            BDDTetravex.True
                        else if v > p then
                            aux (u + 1) 1
                        else if (u = a && v = b) then
                            aux u (v + 1)
                        else
                            BDDTetravex.andBDDTetravex (BDDTetravex.notBDDTetravex(self#formulePlacement carre_analised u v))( aux u (v + 1)) (*TODO*)
                    in
                    aux 1 1

                (* This method will check if the only carre placed in a certain grid position (a,b) is the carre_analised
					it will search if all others (a, b: c) are false, otherwise it means that we have two carre's in the same 
					square
					input carre_analised is the carre meant to be in the position a,b it will check if it is the only atributed
						a b position of the grid to be analised 
					output 
						true if all others (a, b : id) are false 
						false otherwise 
                *)


                method anyOtherCarreInThisGridPositionButCarreAnalised (carre_analised: carre) a b = 
                    let rec aux = function
                    | [] -> BDDTetravex.True
                    | t::q -> if t#id = carre_analised#id then aux q
                        else
                            BDDTetravex.andBDDTetravex (BDDTetravex.notBDDTetravex(self#formulePlacement t a b)) (aux q) (*TODO*)
                    in
                    aux carres_list

                (* This method will try to place the carre_analised in the a b grid position keeping a possible solution
					input: carre to be analised and position to be inserted a b
					output: boolean = (ccrre_analised placed in a b) => [(obligeRight) && (obligeDown) && (anyOtherCarreInThisGridPositionButCarreAnalised) && (uniquelyPlacedIn)]
                *)

                method conditionsCheckToPlaceAnalisedCarreInAB carre_analised a b = 
                    let row_condition = if a + 1 <= n then self#obligeRightCarre_to_belong a b carre_analised carres_list else BDDTetravex.True in (* If it is in the last *)
                    let column_condition = if b + 1 <= p then self#obligeDownCarre_to_belong a b carre_analised carres_list else BDDTetravex.True in
                    let v = self#formulePlacement carre_analised a b in (*TODO*)
                    let placed_one_time = self#uniquelyPlacedIn carre_analised a b in
                    let unique_in_this_grid_position = self#anyOtherCarreInThisGridPositionButCarreAnalised carre_analised a b in
                    BDDTetravex.bdd1Impliesbdd2BDD v (BDDTetravex.andBDDTetravex(BDDTetravex.andBDDTetravex(BDDTetravex.andBDDTetravex row_condition column_condition) placed_one_time) unique_in_this_grid_position) (*TODO*)

                (* Method used to apply the above method to all the possible grid positions 
                	input: carre_to_be_analised


                *)



                method conditionsCheckToPlaceAnalisedCarreForAllPositions (carre_analised:carre) =  (*TODO*)
                    let rec aux a b =
                        if a > n then
                            BDDTetravex.True
                        else if b > p then
                            aux (a + 1) 1
                        else
                            BDDTetravex.andBDDTetravex(self#conditionsCheckToPlaceAnalisedCarreInAB carre_analised a b) (aux a (b + 1)) (*TODO*)
                    in
                    aux 1 1

                method existenceTetravex =   	
                    let rec exist a b = function
                        | [] -> BDDTetravex.False
                        | t::q -> BDDTetravex.orBDDTetravex(self#formulePlacement t a b)(exist a b q) (*TODO*)
                    in
                    let rec aux a b =
                        if a > n then
                            BDDTetravex.True (*Attention Type*)
                        else if b > p then
                            aux (a + 1) 1
                        else
                            BDDTetravex.andBDDTetravex(exist a b carres_list) (aux a (b +1)) (*TODO*) 
                    in
                    aux 1 1
                
                (*TODO*)
                method toutPlacer = function      
                    | [] -> BDDTetravex.True
                    | t::q -> BDDTetravex.andBDDTetravex (self#conditionsCheckToPlaceAnalisedCarreForAllPositions t) (self#toutPlacer q) (*TODO*) 
                


                (*TODO*)
                method solve () =
                    let allPlaced = self#toutPlacer carres_list in
                    let existenceTetravex = self#existenceTetravex in
                    let bdd = BDDTetravex.andBDDTetravex allPlaced  existenceTetravex in (*TODO*)
                    let (b, l) = BDDTetravex.satisfact bdd in (*TODO*)
                    if b then List.map (fun (x, _) ->  x) (List.filter (fun (_, x) ->not x) l) else []

        end

end

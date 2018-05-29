(*include module with bdd`s*)
include PLLib

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
                (* Method used to print the solution 
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
                    StringBDD.makeNode ((string_of_int b) ^ "," ^ (string_of_int a) ^ ":" ^ (string_of_int dom#id)) False True
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
                    | [] -> False
                    | t::q ->
                        if t#id = carre_analised#id then (*Checks to see if the next carre is not the analised one*)
                            self#obligeRightCarre_to_belong a b carre_analised q
                        else if (t#get_left = carre_analised#get_right) then (*If the next carre cand be put at the right side of the analised one, we add him in the result*)
                            let f = self#formulePlacement t (a + 1) b in (*TODO*)
                            StringBDD.orBDD(f) (self#obligeRightCarre_to_belong a b carre_analised q) (*TODO*)
                        else
                            self#obligeRightCarre_to_belong a b carre_analised q

                method obligeDownCarre_to_belong a b (carre_analised: carre) (liste: carre list) = 
                    match liste with
                    | [] -> False
                    | t::q ->
                        if t#id = carre_analised#id then
                            self#obligeDownCarre_to_belong a b carre_analised q
                        else if (t#get_up = carre_analised#get_down) then
                            let f = self#formulePlacement t a (b + 1) in (*TODO*)
                            StringBDD.orBDD f (self#obligeDownCarre_to_belong a b carre_analised q) (*TODO*)
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
                            True
                        else if v > p then
                            aux (u + 1) 1
                        else if (u = a && v = b) then
                            aux u (v + 1)
                        else
                            StringBDD.andBDD (StringBDD.notBDD(self#formulePlacement carre_analised u v))( aux u (v + 1)) (*TODO*)
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
                    | [] -> True
                    | t::q -> if t#id = dom#id then aux q
                        else
                            StringBDD.andBDD (StringBDD.notBDD(self#formulePlacement t a b)) (aux q) (*TODO*)
                    in
                    aux carres_list

                (* This method will try to place the carre_analised in the a b grid position keeping a possible solution
					input: carre to be analised and position to be inserted a b
					output: boolean = (ccrre_analised placed in a b) => [(obligeRight) && (obligeDown) && (anyOtherCarreInThisGridPositionButCarreAnalised) && (uniquelyPlacedIn)]
                *)

                method conditionsCheckToPlaceAnalisedCarreInAB carre_analised a b = 
                    let row_condition = if a + 1 <= n then self#obligeRightCarre_to_belong a b carre_analised carres_list else True in (* If it is in the last *)
                    let column_condition = if b + 1 <= p then self#obligeDownCarre_to_belong a b carre_analised carres_list else True in
                    let v = self#formulePlacement carre_analised a b in (*TODO*)
                    let placed_one_time = self#uniquelyPlacedIn carre_analised a b in
                    let unique_in_this_grid_position = self#anyOtherCarreInThisGridPositionButCarreAnalised carre_analised a b in
                    StringBDD.implBDD v (StringBDD.andBDD(StringBDD.andBDD(StringBDD.andBDD row_condition column_condition) placed_one_time) unique_in_this_grid_position) (*TODO*)

                (* Method used to apply the above method to all the possible grid positions 
                	input: carre_to_be_analised


                *)



                method conditionsCheckToPlaceAnalisedCarreForAllPositions (carre_analised:carre) =  (*TODO*)
                    let rec aux a b =
                        if a > n then
                            True
                        else if b > p then
                            aux (a + 1) 1
                        else
                            StringBDD.andBDD(self#conditionsCheckToPlaceAnalisedCarreInAB carre_analised a b) (aux a (b + 1)) (*TODO*)
                    in
                    aux 1 1

                method existenceTetravex =   	
                    let rec exist a b = function
                        | [] -> False
                        | t::q -> StringBDD.orBDD(self#formulePlacement t a b)(exist a b q) (*TODO*)
                    in
                    let rec aux a b =
                        if a > n then
                            True (*Attention Type*)
                        else if b > p then
                            aux (a + 1) 1
                        else
                            StringBDD.andBDD(exist a b carres_list) (aux a (b +1)) (*TODO*) 
                    in
                    aux 1 1
                
                (*TODO*)
                method toutPlacer = function      
                    | [] -> True
                    | t::q -> StringBDD.andBDD (self#conditionsCheckToPlaceAnalisedCarreForAllPositions t) (self#toutPlacer q) (*TODO*) 
                


                (*TODO*)
                method solve () =
                    let allPlaced = self#toutPlacer l in
                    let existence = self#existenceTetravex in
                    let bdd = StringBDD.andBDD allPlaced  existenceTetravex in (*TODO*)
                    let (b, l) = StringBDD.satisfact bdd in (*TODO*)
                    if b then List.map (fun (x, _) ->  x) (List.filter (fun (_, x) ->not x) l) else []

end

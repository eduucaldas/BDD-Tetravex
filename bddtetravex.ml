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

end

module BDDTetravex = GeneralBDDTetravex(StringVar)

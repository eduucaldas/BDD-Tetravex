open PLLib
module BDT :
  functor (VT : VariableInterfaces.VariableType) ->
  sig
    type binary_tree =
        Leaf of bool
      | Node of binary_tree * VT.t * binary_tree
    val compare : binary_tree -> binary_tree -> int
    val equal : binary_tree -> binary_tree -> bool

    (** Creates the Binary Decision Tree from formule "f" and the ordering of evaluations *)
    val create_order : PropositionalLogic(VT).formule -> VT.t list -> binary_tree

    (** Creates the Binary Decision Tree from formule "f" by evaluating its variables in no particular order *)
    val create_random : PropositionalLogic(VT).formule -> binary_tree
    exception InsufficientEvaluations

    (** The tree is parsed into subtrees using depth first search and an optimal dictionary is constructed with each index pointingto a distinct subtree. *)
    val compress : binary_tree -> binary_tree

    (** Prints the BDT  *)
    val print : binary_tree -> unit


    val validity : binary_tree -> bool


    val satisfiability : binary_tree -> (VT.t * bool) list option
    val print_satifiability : binary_tree -> unit
  end

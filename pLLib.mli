(** Module for propositional logic expressions, type of variables are specified by VariableType *)
module PropositionalLogic :
  functor (VT : VariableInterfaces.VariableType) ->
  sig
    type formule =
        Boolean of bool
      | Variable of VT.t
      | Bin_Op of formule * (formule -> formule -> formule) * formule
      | Un_op of (formule -> formule) * formule

    (** Gives the two possible valuations of a formule "f" for a varible "v": [ [|f (v<-True), f (v<-False)|] ] *)
    val eval_v : formule -> VT.t -> VT.t option * formule * formule

    (** {b eval_v} for the first variable "v" found through a Infix DFS on "f" *)
    val eval_random_v : formule -> VT.t option * formule * formule

    (** Simplifies the formule using the rules specified in the operators [(formule -> formule -> formule)] and [(formule->formule)] *)
    val simplify : formule -> formule

    (** Given a formule "f" and a list of valuations ("v"<-bool), in the form of tuples, evaluates "f" with this list *)
    val eval_order : formule -> (VT.t * bool) list -> formule

    exception PartialValuation

    (** Applies {b eval_order}, but throws a {b PartialValuation} exn in the case of a partial evaluation, and returns the truth value otherwise *)
    val valuation_order : formule -> (VT.t * bool) list -> bool

    (** Given the string representation of a formule gives in to the its logical representation *)
    val formule_of_str : string -> formule


    (** Picks a string from {i stdin} and gives its logical representation *)
    val formule_of_input : unit -> formule

    (** Format of the string representation of formule:
        {[
          | '(' -> Parenthesis_open
          | ')' -> Parenthesis_close
          | 'true' -> True
          | 'false' -> False
          | '~' -> Neg
          | '&&' -> And
          | '||' -> Or
          | '->' -> Implies
          | '<->' -> Equivalence
          | _ -> Variable
        ]}
    *)

  end

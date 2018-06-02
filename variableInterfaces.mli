module type VariableType =
  sig
    type t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val str : t -> string
    val to_t : string -> t option
  end
module CharType : VariableType
module IntegerType : VariableType
module StringType : VariableType

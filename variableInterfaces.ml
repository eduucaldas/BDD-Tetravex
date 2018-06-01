module type VariableType =
sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val str : t -> string
  val to_t : string -> t option
end

module CharType: VariableType =
struct
  type t = char
  let equal c1 c2 = Char.equal c1 c2
  let compare c1 c2 = Char.compare c1 c2
  let str c = Char.escaped c
  let to_t s = match String.length s with
    | 1 -> Some s.[0]
    | _ -> None
end

module IntegerType: VariableType =
struct
  type t = int
  let equal c1 c2 = (c1 = c2)
  let compare c1 c2 = (c1 - c2)
  let str c = string_of_int c
  let to_t s = int_of_string_opt s
end

module StringType: VariableType =
struct
  type t = string
  let equal c1 c2 = String.equal c1 c2
  let compare c1 c2 = String.compare c1 c2
  let str c = c
  let to_t s = Some s
end

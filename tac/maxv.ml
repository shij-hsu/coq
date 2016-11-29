type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val max_val : __ **)

let max_val =
  __

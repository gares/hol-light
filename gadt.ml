type term = string

type 'a data = { read : 'a -> term ; write : term -> 'a }

type 'a ffi =
  | Arr : 'a data * 'b ffi -> ('a -> 'b) ffi
  | Ret : 'a data -> 'a ffi

type mlcode = ML : ('a ffi * 'a) -> mlcode

let int : int data = { read = string_of_int; write = int_of_string }
let bool : bool data = { read = string_of_bool; write = bool_of_string}

let rec eval : type a. term list -> a ffi -> a -> term =
  fun args ffi f ->
    match args, ffi with
    | [], Ret d -> d.read f
    | x::xs, Arr(d,ffi) -> eval xs ffi (f (d.write x))
    | _ -> "type error"
;;

let run (ML(ffi,f)) l = eval l ffi f

(* ******************** *)

let mytac : int -> bool = fun i -> (i = 42)
let mytac_descr = ML (Arr(int,Ret bool), mytac)

let () =
  Printf.printf "the answer is %s\n"
    (run mytac_descr ["3"])
;;
let () =
  Printf.printf "the answer is %s\n"
    (run mytac_descr [])
;;

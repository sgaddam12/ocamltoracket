(*let rec factorial n z =
match n with | 0|1 -> 1 
| _ -> let x = factorial (n - 1) z in n * x
;;

let fz x y = let fg d = 6 in fg x;;

print_string "hi";;

let x = (3, 5, 6) in
match x with
| (a, b, c) -> a
| _ -> 10
;;

let xx = [3;5] in 
match x with
| h1::h2::[] -> h1
| h1::tl -> h1
| [] -> 2
;;

if (3 < 4) then 10 else if (5 > 7) then 2 else 0;;

print_string "hi"; print_string "hi"; print_string "hi";;

let aa (t, i) (j, k) = t + k;;

let ze = (3, 4);;
let j = let (a, b) = z in a;;

let bb = (fun x y -> x);;

let rec hh f = 
	let rec zz r =
		if (r < 5) then 2 else zz 1
	in
	if (f < 3) then (zz 10) + (-10) else hh (-1)
;;

let xed = let _ = (3, 3) in 2;;

let zed = ();;

let yo () = ();;

let zkz = function
| 3 -> "hi"
| _ -> "no"
;;

(function x -> function
| 3 ->
x + 1);;


type bst_t =  
  | Leaf
  | Node of bst_t * int * bst_t

let ff z = match z with
| Leaf -> 1
| Node (bst1, i, bst2) -> 2
;;

let x = ref "" in x := !x;;

let x =
  assert true;;

true && false || true && not false;;

type bst_t =  
  | Leaf
  | Node of bst_t * int * bst_t

let x = Node (Leaf, 3, Node (Leaf, 2, Leaf));;*)


(*note that curried functions in general will not work under this implementation*)
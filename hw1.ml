type peano = Z | S of peano;;

let rec peano_of_int x = match x with
	if (x == 0) then Z
	else S (peano_of_int (x - 1));;

let rec int_of_peano p = match p with
	Z -> 0
	| S x -> 1 + int_of_peano x;;

let inc x = S x;;

let rec add x y = match y with
	Z -> x
	| S y -> S(add x y);;
	
let rec mul x y = match y with
	Z -> Z
	| S y -> add (mul x y) x;;
	
let rec sub x y = match (x, y) with
	(x, Z) -> x
	| (Z, y) -> Z
	| (S x, S y) -> sub x y;;
	
let rec div x y = match sub (inc x) y with
	Z -> Z
	| _ -> add (S Z) (div (sub x y) y);;
	
let rec power x y = match y with
	Z -> S Z
	| S y -> mul (power x y) x;;
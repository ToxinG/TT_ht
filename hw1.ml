type peano = Z | S of peano;;
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x =
	match x with
	| 0 -> Z
	| x -> S (peano_of_int (x - 1));;

let rec int_of_peano p = 
	match p with
	| Z -> 0
	| S x -> 1 + int_of_peano x;;

let inc x = 
	S x;;

let dec x =
  	match x with
  	| Z -> Z
	| S x -> x;;

let rec add x y = 
	match (x, y) with
	| (x, Z) -> x
	| (Z, y) -> y
	| (x, S y) -> S (add x y);;
	
let rec sub x y = 
	match (x, y) with
	| (x, Z) -> x
	| (Z, y) -> Z
	| (S x, S y) -> sub x y;;
	
let rec mul x y = 
	match (x, y) with
	| (x, Z) -> Z
	| (Z, y) -> Z
	| (x, S y) -> add (mul x y) x;;
	
let rec div x y = 
	match sub (inc x) y with
	| Z -> Z
	| _ -> add (S Z) (div (sub x y) y);;
	
let rec power x y = match y with
	| Z -> S Z
	| S y -> mul (power x y) x;;

let rev l = 
	let rec cut_head head_stack = function
		| [] -> head_stack
		| head :: tail -> cut_head (head :: head_stack) tail in
	cut_head [] l;;
	
let rec merge_sort x = 
	let rec split x =
		match x with
		| [] -> ([], [])
		| [x] -> ([x], [])
		| x :: y :: xs -> let (l, r) = split xs in (x :: l, y :: r)
	and merge x y =
		match (x, y) with
		| ([], y) -> y
		| (x, []) -> x
		| (x :: xs, y :: ys) -> if x < y
			then x :: (merge xs (y :: ys))
			else y :: (merge (x :: xs) ys) in
	match x with
	| [] -> []
	| [x] -> [x]
	| x -> let (l, r) = split x in merge (merge_sort l) (merge_sort r);;

let rec string_of_lambda x =
	let lts = string_of_lambda in
  	match x with
  	| Var x -> x
  	| Abs (x, y) -> "\\" ^ x ^ "." ^ lts y
  	| App (Abs (_, _) as abs, Var y) -> "(" ^ lts abs ^ ") " ^ y
  	| App (Abs (_, _) as abs, y) -> "(" ^ lts abs ^ ") (" ^ lts y ^ ")"
  	| App (x, Var y) -> lts x ^ " " ^ y
  	| App (x, y) -> lts x ^ " (" ^ lts y ^ ")";;

let lambda_of_string input =
	let stream = Stream.of_string (input ^ ";") in
	let tokens = Genlex.make_lexer ["\\"; "."; "("; ")"; ";"] stream in
	let next() = Stream.next tokens in
	let peek() = Stream.peek tokens in
	let check c err = if (next() <> Genlex.Kwd c) then failwith err in
	let check_parenthesis() = check ")" "Parenthesis not closed" in
	let check_dot() = check "." "No dot found" in

	let rec parse_lambda() =
		match next() with
		| Genlex.Kwd "("  -> parse_parentheses()
		| Genlex.Kwd "\\" -> parse_abs()
		| Genlex.Ident v  -> parse_var v
		| _ -> failwith "Unexpected symbol"

	and parse_parentheses() =
		let lambda = parse_lambda() in
		check_parenthesis();
		check_app lambda;

  	and parse_abs() =
	match next() with
		| Genlex.Ident v ->
		  check_dot();
		  let lambda = parse_lambda() in
		  check_app (Abs (v, lambda));
		| _ -> failwith "Unexpected symbol"

  	and parse_var v =
		check_app (Var v);

  	and parse_app lambda token =
		match token with
		| Genlex.Kwd ")"  -> lambda
		| Genlex.Kwd ";"  -> lambda
		| Genlex.Kwd "\\" -> App(lambda, parse_lambda())
		| Genlex.Kwd "("  -> let _ = next() and arg = parse_lambda() in
		  check_parenthesis();
		  check_app (App (lambda, arg));
		| Genlex.Ident v  -> let _ = next() in check_app (App (lambda, Var v))
		| _ -> failwith "Unexpected symbol"

  	and check_app lambda =
		match peek() with
		| None       -> failwith "Unexpected end of string"
		| Some token -> parse_app lambda token
in parse_lambda();;
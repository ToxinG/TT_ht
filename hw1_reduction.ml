open Hw1;;

(** Lambda reference type used for memoization *)
type lambda_ref = Var_ref of string | Abs_ref of (string * lambda_ref ref) | App_ref of (lambda_ref ref * lambda_ref ref);;

module StringSet = Set.Make(String);;
module StringMap = Map.Make(String);;

(* --------------- PRIVATE --------------- *)

(** Generates a new unique variable name *)
let new_name  = Stream.from (fun i -> Some ("name" ^ string_of_int i));;

(** Returns a set of free variables of a lambda expression *)
let rec free_var_set lambda = 
	match lambda with
	| Var v -> StringSet.singleton v
	| Abs (x, y) -> StringSet.remove x (free_var_set y)
	| App (x, y) -> StringSet.union (free_var_set x) (free_var_set y);;
	
(** Returns a list of free variables of a lambda expression *)
let free_var_list lambda = StringSet.elements (free_var_set lambda);;

(** Returns True if variable is free in lambda expression *)
let rec is_free var lambda =
	match lambda with
	| Var v -> v = var
	| Abs (x, y) when x = var -> false
	| Abs (x, y) -> is_free var y
	| App (x, y) -> (is_free var x) || (is_free var y);;
	
(** Returns the result of substitution 
	or throws an error if 'src' is not free for substitution *)
let substitute src expr var =
	let src_free_vars = free_var_set src in
	let no_var_to_replace x = not (is_free var x) in
	let not_bounding x = not (StringSet.mem x src_free_vars) in
	let lts = string_of_lambda in
	let error() = "'" ^ (lts src) ^ "' is not free for substitution in '" ^
				  (lts expr) ^ "' instead of '" ^ var ^ "'" in
	let rec subst_rec expr =
		match expr with
		| Var v -> if (v = var) then src else expr
		| Abs (x, y) when no_var_to_replace expr -> expr
		| Abs (x, y) when not_bounding x -> Abs (x, subst_rec y)
		| App (x, y) -> App (subst_rec x, subst_rec y)
		| _ -> failwith (error())
	in subst_rec expr;;

(** Converts lambda to lambda_ref reference *)
let rec ref_of_lambda lambda =
	match lambda with
	| Var v -> ref (Var_ref v)
	| App (x, y) -> ref (App_ref (ref_of_lambda x, ref_of_lambda y))
	| Abs (x, y) -> ref (Abs_ref (x, ref_of_lambda y));;

(** Converts lambda_ref reference to lambda *)
let rec lambda_of_ref lambda_ref =
	match !lambda_ref with
	| Var_ref v -> Var v
	| App_ref (x, y) -> App (lambda_of_ref x, lambda_of_ref y)
	| Abs_ref (x, y) -> Abs (x, lambda_of_ref y);;

(* --------------- PUBLIC --------------- *)

(** Returns True if first lambda is free for substitution
	to the second instead of given variable *)
let free_to_subst src expr var =
		try
			let _ = substitute src expr var in true
		with _ -> false;;

(** Returns a list of free variables of the lambda expression *)
let free_vars lambda = StringSet.elements (free_var_set lambda);;

(** Returns True, lambda expression is in normal form *)
let rec is_normal_form lambda =
	match lambda with
	| Var _ -> true
	| Abs (x, y) -> is_normal_form y
	| App (Abs (x, y), t) -> not (free_to_subst t y x)
	| App (x, y) -> is_normal_form x && is_normal_form y;;
	
(** Returns True if two lambda expressions are alpha-equivalent *)
let is_alpha_equivalent lambda1 lambda2 =
	let mem = StringMap.mem in
	let find = StringMap.find in
	let add = StringMap.add in
	let check_vars v1 v2 map1 map2 =
		if (mem v1 map1) && (mem v2 map2) && (find v1 map1 = v2) && (find v2 map2 = v1) then true
		else if (not (mem v1 map1)) && (not (mem v2 map2)) && v1 = v2 then true
		else false
	in
	let rec aeq lambda1 lambda2 map1 map2 =
		match (lambda1, lambda2) with
		| (Var v1, Var v2) -> check_vars v1 v2 map1 map2
		| (Abs (x1, y1), Abs (x2, y2)) -> aeq y1 y2 (add x1 x2 map1) (add x2 x1 map2)
		| (App (x1, y1), App (x2, y2)) -> (aeq x1 x2 map1 map2 && aeq y1 y2 map1 map2)
		| _ -> false
	in aeq lambda1 lambda2 StringMap.empty StringMap.empty;;

(** Does one step of beta-reduction for lambda_ref reference *)
let rec reduction_step lambda_ref =
	let mem = StringMap.mem in
	let find = StringMap.find in
	let add = StringMap.add in
	let rec to_aeq lambda_ref map = 
		match !lambda_ref with
		| Var_ref v -> if mem v map then ref (Var_ref (find v map)) else lambda_ref
		| App_ref (x, y) -> ref (App_ref (to_aeq x map, to_aeq y map))
		| Abs_ref (x, y) ->
			let temp = Stream.next new_name in
			ref (Abs_ref (temp, to_aeq y (add x temp map)))
	in
	let rec try_to_subst src expr var =
		match !expr with
		| Var_ref a -> if a = var then expr := !src
		| Abs_ref (a, b) -> if a <> var then try_to_subst src b var
		| App_ref (a, b) ->
			try_to_subst src a var;
			try_to_subst src b var
	in
	let reduction_app a b =
		match !a with
		| Abs_ref (x, y) ->
			let temp = Stream.next new_name  in
			lambda_ref := !(to_aeq y (StringMap.singleton x temp));
			try_to_subst b lambda_ref temp;
			Some lambda_ref
		| _ ->
			match reduction_step a with
			| Some _ -> Some lambda_ref
			| None ->
				match reduction_step b with
				| Some _ -> Some lambda_ref
				| None -> None
	in
	match !lambda_ref with
	| Var_ref a -> None
	| App_ref (a, b) -> reduction_app a b
	| Abs_ref (a, b) ->
		match reduction_step b with
		| Some _ -> Some lambda_ref
		| None -> None;;

(** Does one step of beta-reduction using normal-order reduction *)
let normal_beta_reduction lambda =
	match reduction_step (ref_of_lambda lambda) with
	| Some x -> lambda_of_ref x
	| None -> lambda;;

(** Effectively reduces lambda expression to its normal form *)
let reduce_to_normal_form lambda =
	let rec reduction lambda_ref =
		match reduction_step lambda_ref with
		| Some x -> reduction x
		| None -> lambda_ref
	in
	let result = reduction (ref_of_lambda lambda) in
	lambda_of_ref result;;
	
	
(* --------------- DEPRECATED --------------- *)

(*

(** Returns True if two lambda expressions are alpha-equivalent *)
let is_alpha_equivalent lambda1 lambda2 =
	let rec aeq lambda1 lambda2 =
		match (lambda1, lambda2) with
		| (Var v1, Var v2) -> v1 = v2
		| (Abs (x1, y1), Abs (x2, y2)) ->
			let v = Var (Stream.next new_name  ) in
			aeq (substitute v y1 x1) (substitute v y2 x2)
		| (App (x1, y1), App (x2, y2)) -> (aeq x1 x2 && aeq y1 y2)
		| _ -> false
	in aeq lambda1 lambda2;;
	
*)
	
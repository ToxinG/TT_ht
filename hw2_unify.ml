type algebraic_term = Var of string | Fun of string * (algebraic_term list)

module StringSet = Set.Make (String);;
exception NoSolutionException of string;;

(** Generates a new unique variable name *)
let new_name  = Stream.from (fun i -> Some ("name" ^ string_of_int i));;

(** Returns one equation equivalent to the given system of equations *)
let system_to_equation system =
	let name = Stream.next new_name in
	let (left, right) = List.split system in
	(Fun (name, left), Fun (name, right));;

(** Returns result of substitution *)
let apply_substitution subst_list term =
	let rec apply subst term =
		let (var, new_term) = subst in
		match term with
		| Var v -> if (var = v) then new_term else term
		| Fun (name, args) -> Fun (name, List.map (apply subst) args)
	in
	List.fold_right apply subst_list term;;
	
(** Returns True if the substitution is a solution of the system *)
let check_solution subst_list system = 
	let (left, right) = system_to_equation system in
	let subst = apply_substitution subst_list in
	subst left = subst right;;

(** Returns a solution of the system or None if it has no solution *)
let solve_system system = 
	let error message = raise (NoSolutionException message) in
	let rec contains var term =
		match term with
		| Var v -> v = var
		| Fun (f, args) -> List.exists (contains var) args
	in
	let rec solve system resolved =
		match system with
		| [] -> []
		| _ when StringSet.cardinal resolved = List.length system -> system
		| equation :: tail ->
			match equation with
			| (l, r) when l = r -> solve tail resolved
			| (Var v, term) when contains v term -> error "Error of type x = f(x)"
			| (Var v, term) ->
				let resolved = StringSet.add v resolved in
				let substitute = apply_substitution [(v, term)] in
				let tail = List.map (fun (l, r) -> (substitute l, substitute r)) tail in
				solve (tail @ [equation]) resolved
			| (term, Var v) -> solve (tail @ [(Var v, term)]) resolved
			| (Fun (f, l1), Fun (g, l2)) when f = g && List.length l1= List.length l2 ->
				let new_equations = List.combine l1 l2 in
				solve (tail @ new_equations) resolved
			| (Fun _, Fun _) -> error "Equation has different functions"
	in
	let substitution_of_equation (left, right) =
		match left with
		| Var v -> (v, right)
		| _ -> error "Equation has form different from x = T"
	in
	try
		let resolved_system = solve system StringSet.empty in
		let solution = List.map substitution_of_equation resolved_system in
		Some solution
	with (NoSolutionException e) -> None;;
		
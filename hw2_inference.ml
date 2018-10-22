open Hw1;;
open Hw1_reduction;;
open Hw2_unify;;

(** Simple type: type name or "arrow operation" *)
type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
(** Hindley-Milner lambda: variable, abstraction, application or let *)
type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
(** Hindley-Milner type: type name, arrow or forall quantifier *)
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

module StringMap = Map.Make(String);;
module StringSet = Set.Make(String);;

exception NoSolutionException of string;;

(* --------------- PRIVATE --------------- *)

(** Generates a new unique type name *)
let new_type  = Stream.from (fun i -> Some ("type" ^ string_of_int i));;

(** Generates a new unique variable name *)
let new_var  = Stream.from (fun i -> Some ("var" ^ string_of_int i));;

(** Converts the simple type to an algebraic term using '->' as a function *)
let rec term_of_simp_type t = 
	match t with
	| S_Elem v -> Var v
	| S_Arrow (a, b) -> Fun ("->", [(term_of_simp_type a); (term_of_simp_type b)]);;
	
(** Converts the algebraic term with '->' functions to a simple type *)
let rec simp_type_of_term t =
	match t with
	| Var v -> S_Elem v
	| Fun (f, [l; r]) when f = "->" -> S_Arrow (simp_type_of_term l, simp_type_of_term r)
	| _ -> failwith "Term does not represent a simple type";;
	
(** Converts the pair of types to an algebraic equation *)
let equation_of_types (l, r) = (term_of_simp_type l, term_of_simp_type r);;

(** Converts the Hindley-Milner type to an algebraic term using '->' as a function *)
let rec term_of_hm_type hm_type =
	match hm_type with
	| HM_Elem a -> Var a
	| HM_Arrow (a, b) -> Fun ("->", [(term_of_hm_type a); (term_of_hm_type b)])
	| _ -> failwith "Forall quantifier cannot be represented as a term";;
	
(** Converts the algebraic term with '->' functions to a Hindley-Milner type *)
let rec hm_type_of_term term =
	match term with
	| Var a -> HM_Elem a
	| Fun (f, [l; r]) when f = "->" -> HM_Arrow (hm_type_of_term l, hm_type_of_term r)
	| _ -> failwith "Term is not representing a simple type";;
	
(** Returns a set of free variables in Hindley-Milner lambda *)
let rec hm_free_vars hm_lambda =
	match hm_lambda with
	| HM_Var a -> StringSet.singleton a
	| HM_Abs (a, b) -> StringSet.remove a (hm_free_vars b)
	| HM_App (a, b) -> StringSet.union (hm_free_vars a) (hm_free_vars b)
	| HM_Let (a, b, c) ->
		let hm_free_vars_c = StringSet.remove a (hm_free_vars c) in
		StringSet.union (hm_free_vars b) hm_free_vars_c;;
		
(** Returns a set of free types in Hindley-Milner lambda *)
let rec free_types hm_type =
	match hm_type with
	| HM_Elem a -> StringSet.singleton a
	| HM_Arrow (a, b) -> StringSet.union (free_types a) (free_types b)
	| HM_ForAll (a, b) -> StringSet.remove a (free_types b);;
	
(** Returns the Hindley-Milner type with applied substitution *)
let rec apply_type_subst subst hm_type =
	match hm_type with
	| HM_Elem a when StringMap.mem a subst -> StringMap.find a subst
	| HM_Elem a -> hm_type
	| HM_Arrow (a, b) -> HM_Arrow (apply_type_subst subst a, apply_type_subst subst b)
	| HM_ForAll (a, b) -> HM_ForAll (a, apply_type_subst (StringMap.remove a subst) b);;
	
(** Returns a composition of two substitutions *)
let compose_subst subst1 subst2 =
	let subst2 = StringMap.map (apply_type_subst subst1) subst2 in
	StringMap.merge (fun key v1 v2 ->
		match (v1, v2) with
		| (None, None) -> None
		| (Some v, None) -> Some v
		| (None, Some v) -> Some v
		| (Some v1, Some v2) -> Some v2) subst1 subst2;;

(** Returns a type environment with applied substitution *)
let apply_subst_to_env subst type_env =
	StringMap.map (apply_type_subst subst) type_env;;
	
(** Abstracts a type over all type variables which are free
		in the type but not free in the given type environment *)
let generalize type_env hm_type =
	let add_free_types key value = StringSet.union (free_types value) in
	let free_env_types = StringMap.fold add_free_types type_env StringSet.empty in
	let free_hm_types = free_types hm_type in
	let new_forall_vars = StringSet.diff free_hm_types free_env_types in
	let add_quantifier var hm_type = HM_ForAll (var, hm_type) in
	StringSet.fold add_quantifier new_forall_vars hm_type;;
	
(** Replaces all bound type variables in the type with new type variables *)
let rec instantiate hm_type =
	match hm_type with
	| HM_ForAll (a, b) ->
		let subst = StringMap.singleton a (HM_Elem (Stream.next new_var)) in
		apply_type_subst subst (instantiate b)
	| _ -> hm_type;;
	

(* --------------- PUBLIC --------------- *)

(** Returns the list of variable types and the type of the simple lambda expression *)
let infer_simp_type lambda =
	let n_type() = S_Elem (Stream.next new_type) in
	let add_type_to_map map t = StringMap.add t (n_type()) map in
	let rec get_system lambda types =
		match (lambda : lambda) with
		| Var v -> ([], StringMap.find v types)
		| App (lambda1, lambda2) ->
			let (system1, t1) = get_system lambda1 types in
			let (system2, t2) = get_system lambda2 types in
			(system1 @ system2 @ [(t1, S_Arrow(t2, n_type()))], n_type())
		| Abs (v, l) ->
			let new_map = add_type_to_map types v in
			let (system1, t1) = get_system l new_map in
			(system1, S_Arrow(StringMap.find v new_map, t1))
	in
	let free = free_vars lambda in
	let types = List.fold_left add_type_to_map StringMap.empty free in
	let (system, t) = get_system lambda types in
	match solve_system (List.map equation_of_types system) with
	| None -> None
	| Some solution ->
		let lambda_type_term = apply_substitution solution (term_of_simp_type t) in
		let to_type_list = List.map (fun (a, b) -> (a, simp_type_of_term b)) in
		Some (to_type_list solution, simp_type_of_term lambda_type_term);;

(** Returns the list of variable types and the type of Hindley-Milner lambda *)
let algorithm_w hm_lambda =
	let error message = raise (NoSolutionException message) in
	let rec alg_w_rec type_env hm_lambda =
		match hm_lambda with
		| HM_Var a when StringMap.mem a type_env -> (StringMap.empty, instantiate (StringMap.find a type_env))
		| HM_Var a -> error "Free variable found"
		| HM_App (a, b) ->
			(let (s1, t1) = alg_w_rec type_env a in
			let (s2, t2) = alg_w_rec (apply_subst_to_env s1 type_env) b in
			let n_type = HM_Elem (Stream.next new_var) in
			let left = apply_type_subst s2 t1 in
			let right = HM_Arrow (t2, n_type) in
			let equation = (term_of_hm_type left, term_of_hm_type right) in
			match solve_system [equation] with
			| None -> error "Couldn't solve the system"
			| Some answer ->
				let add_subst (str, term) = StringMap.add str (hm_type_of_term term) in
				let v = List.fold_right add_subst answer StringMap.empty in
				let unifier = compose_subst v (compose_subst s2 s1) in
				(unifier, apply_type_subst unifier n_type))
			| HM_Abs (a, b) ->
				let n_type = HM_Elem (Stream.next new_var) in
				let type_env = StringMap.add a n_type (StringMap.remove a type_env) in
				let (s1, t1) = alg_w_rec type_env b in
				(s1, HM_Arrow (apply_type_subst s1 n_type, t1))
			| HM_Let (a, b, c) ->
				let (s1, t1) = alg_w_rec type_env b in
				let a_type = generalize (apply_subst_to_env s1 type_env) t1 in
				let type_env = apply_subst_to_env s1 (StringMap.remove a type_env) in
				let type_env = StringMap.add a a_type type_env in
				let (s2, t2) = alg_w_rec type_env c in
				(compose_subst s2 s1, t2)
		in
		let free = hm_free_vars hm_lambda in
		let bound_to_unique v = StringMap.add v (HM_Elem (Stream.next new_var)) in
		let type_environment = StringSet.fold bound_to_unique free StringMap.empty in
		try
			let (unifier, hm_type) = alg_w_rec type_environment hm_lambda in
			Some (StringMap.bindings unifier, hm_type)
		with (NoSolutionException e) -> None

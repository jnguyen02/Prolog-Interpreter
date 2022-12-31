let _  = Random.self_init ()

type term =
  | Constant of string
  | Variable of string
  | Function of string * term list

type head = term
type body = term list

type clause = Fact of head | Rule of head * body

type program = clause list

type goal = term list

let rec string_of_f_list f t =
  let _, s = List.fold_left (fun (first, s) t ->
    let prefix = if first then "" else s ^ ", " in
    false, prefix ^ (f t)) (true,"") t
  in
  s

let rec string_of_term t =
  match t with
  | Constant c -> c
  | Variable v -> v
  | Function (f,t) ->
      f ^ "(" ^ (string_of_f_list string_of_term t) ^ ")"

let string_of_term_list fl =
  string_of_f_list string_of_term fl

let string_of_goal g =
  "?- " ^ (string_of_term_list g)

let string_of_clause c =
  match c with
  | Fact f -> string_of_term f ^ "."
  | Rule (h,b) -> string_of_term h ^ " :- " ^ (string_of_term_list b) ^ "."

let string_of_program p =
  let rec func_helper p acc =
    match p with
    | [] -> acc
    | [c] -> acc ^ (string_of_clause c)
    | c::t ->  func_helper t (acc ^ (string_of_clause c) ^ "\n")
  in func_helper p ""

let var v = Variable v
let const c = Constant c
let func f l = Function (f,l)
let fact f = Fact f
let rule h b = Rule (h,b)


(* ################# *)
(* # occurs_check ## *)
(* ################# *)

let rec occurs_check v t =
  match t with
  | Variable _ -> t = v
  | Constant _ -> false
  | Function (_,l) -> List.fold_left (fun acc t' -> acc || occurs_check v t') false l

(* ################# *)
(* ### Problem 1 ### *)
(* ################# *)

module VarSet = Set.Make(struct type t = term let compare = Pervasives.compare end)
(* API Docs for Set : https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html *)


let func_helper funct term =
  List.fold_left (fun acc t -> VarSet.union acc (funct t)) VarSet.empty term

let rec variables_of_term t =
  match t with
  | Constant x -> VarSet.empty
  | Function(x,y) -> func_helper (variables_of_term) y
  | Variable x -> VarSet.singleton t

let variables_of_clause c =
  match c with
  | Fact f -> variables_of_term f
  | Rule(x,y) -> VarSet.union (variables_of_term x) (func_helper (variables_of_term) y)


(* ################# *)
(* ### Problem 2 ### *)
(* ################# *)

module Substitution = Map.Make(struct type t = term let compare = Pervasives.compare end)
(* See API docs for OCaml Map: https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html *)

let string_of_substitution s =
  "{" ^ (
    Substitution.fold (
      fun v t s ->
        match v with
        | Variable v -> s ^ "; " ^ v ^ " -> " ^ (string_of_term t)
        | Constant _ -> assert false (* substitution maps a variable to a term *)
        | Function _ -> assert false (* substitution maps a variable to a term *)
    ) s ""
  ) ^ "}"


let fold_helper func y t =
  List.fold_left(fun acc x -> acc@[func y x]) [] t

let rec substitute_in_term s t =
  match t with
  | Constant x -> t
  | Function(x,y) -> Function (x, fold_helper substitute_in_term s y)
  | Variable x -> let opt = (Substitution.find_opt t s) in 
                if opt = None then t else (Substitution.find t s)

let sub_fact s f = Fact (substitute_in_term s f)

let sub_rule s x y =
  Rule(substitute_in_term s x, fold_helper substitute_in_term s y)

let substitute_in_clause s c =
  match c with
  | Fact f ->  sub_fact s f
  | Rule (x,y) -> sub_rule s x y
  


(* ################# *)
(* ### Problem 3 ### *)
(* ################# *)

exception Not_unifiable

let unify_var v t theta =
  if v = t then theta
  else if occurs_check v t then raise Not_unifiable
  else Substitution.map (substitute_in_term (Substitution.singleton v t)) (Substitution.add v t theta)

let unify_const t1 t2 theta =
  if t1 = t2 then theta else raise Not_unifiable

let unify t1 t2 =
  let rec unify t1 t2 theta =
    let t1 = substitute_in_term theta t1 in
    let t2 = substitute_in_term theta t2 in
    match (t1,t2) with
    |(Variable(x),_) -> unify_var t1 t2 theta
    |(_, Variable(x)) -> unify_var t2 t1 theta
    |(Constant(x), Constant(y)) -> unify_const t1 t2 theta
    |(Function(x,y), Function(x2,y2)) -> List.fold_left2 (fun theta t1 t2 -> unify t1 t2 theta) theta y y2
    | _ -> raise Not_unifiable
  in
  unify t1 t2 Substitution.empty



(* ################# *)
(* ### Problem 4 ### *)
(* ################# *)

let counter = ref 0
let frh () =
  let c = !counter in
  counter := !counter + 1;
  Variable ("_G" ^ string_of_int c)

let frhen c =
  let vars = variables_of_clause c in
  let s = VarSet.fold (fun v s -> Substitution.add v (frh()) s) vars Substitution.empty in
  substitute_in_clause s c

let c = (rule (func "p" [var "X"; var "Y"; const "a"]) [func "q" [var "X"; const "b"; const "a"]])
let _ = (*print_endline*) (string_of_clause c)
let _ = (*print_endline*) (string_of_clause (frhen c))


let substitute_in_list terms substitution =
  List.map (fun term -> substitute_in_term substitution term) terms
  
let nondet_query program goal =
  let solution = goal in
  let rec nondet_query program goal solution =
    let rdm_elem l =
      let index = Random.int (List.length l) in
      List.nth l index
    in
    match solution with
    |[] -> goal
    | solution -> 
    let a = rdm_elem solution in
    let b = rdm_elem program in
    let remove_from_list l element =
      let rec repeat acc = function
        | [] -> acc
        | h::t ->
          if h <> element then repeat (acc @ [h]) t
          else repeat acc t
      in
      repeat [] l
    in
    let rs = remove_from_list solution a in
    let b = frhen b in
    match b with
    |Fact(head) ->
      (match unify head a with
      |exception (Not_unifiable) -> []
      |s ->
      let substitute_in_list l s =
        List.map (fun term -> substitute_in_term s term) l
      in
      let goal' = substitute_in_list goal s in
      let solution' = substitute_in_list rs s in
      nondet_query program goal' solution'
      )
    |Rule(head,body) ->
      (match unify head a with
      |exception (Not_unifiable) -> []
      |s ->
      let goal' = substitute_in_list goal s in
      let solution' = substitute_in_list (rs@body) s in
      nondet_query program goal' solution'
      )
  in
  let rec repeat () =
    let rult = nondet_query program goal solution in
    if rult = [] then repeat ()
    else rult
  in
  repeat ()



(* ################# *)
(* ### Problem 5 ### *)
(* ################# *)



let det_query program goal =
  [goal]


(* psuedocode
let det_query program pgoal =
  let rec rep goal r =
    let selec = List.nth goal (Random.int (List.length goal)) in
    let rand_rule = frhen (List.nth program (Random.int (List.length program))) in
    try
      let substitution = unify selec rand_rule.head in
      let r = List.filter (fun term -> term <> selec) r in
      let r = List.map (fun term -> substitute_in_term substitution term) rand_rule.body.terms in
      let goal = List.map (fun term -> substitute_in_term substitution term) goal in
      rep goal r
    with _ -> r
  in rep pgoal pgoal

*)

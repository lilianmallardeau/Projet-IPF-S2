(* ------------------------------------------------------------------------- *)
(* -------------------------- Arbres de décision --------------------------- *)
(* ------------------------------------------------------------------------- *)

(****** Types definition ******)

type tformula =
  | Value of bool (* ⊥ ou T *)
  | Var of string (* Variable *)
  | Not of tformula (* Negation *)
  | And of tformula * tformula (* Conjonction *)
  | Or of tformula * tformula (* Disjonction *)
  | Implies of tformula * tformula (* Implication *)
  | Equivalent of tformula * tformula;; (* Equivalence *)

type decTree =
  | DecLeaf of bool
  | DecRoot of string * decTree * decTree;;

(* We consider that an environment is "well designed" if it doesn't contain the same variable multiple times *)
type env = (string*bool) list;;

  (****** Question 1 ******)
(*    getVars : tformula -> string list 
 * @brief returns the list of the variables in `formula`
 * @param `formula` the formula to extract variables names from
 * @return a string list of the names of the variables in `formula`
 *)
let getVars (formula : tformula) = 
  let rec aux f = match f with
    | Value(_) -> []
    | Var(a) -> [a]
    | Not(f) -> aux f
    | And(f1, f2) -> (aux f1) @ (aux f2)
    | Or(f1, f2) -> (aux f1) @ (aux f2)
    | Implies(f1, f2) -> (aux f1) @ (aux f2)
    | Equivalent(f1, f2) -> (aux f1) @ (aux f2)
  in List.sort_uniq compare (aux formula);;


  (****** Question 2 ******)

(*    getVarValue : env -> string -> bool
 * @brief gets the value of a variable in a specific environment
 * @param `environment` the environment 
 * @param `variable` the variable to get the value of
 * @pre `environment` is a well designed environment, and contains a value for `variable`
 * @return the value of the variable in `environment`
 *)
let rec getVarValue (environment : env) (variable : string) = match environment with
  | [] -> failwith "variable not found in environment"
  | (var, value) :: t -> if var = variable then value else getVarValue t variable;;

(*    evalFormula : env -> tformula -> bool
 * @brief evaluates a formula in a specific environment
 * @param `environment` the environment to evaluate formula in
 * @param `formula` the formula to evaluate
 * @pre `environment` is a well designed environment, and contains all of the variables in `formula`
 * @return the formula evaluated in the environment `environment`
 *)
let rec evalFormula (environment : env) (formula : tformula) = match formula with
  | Value(a) -> a
  | Var(a) -> getVarValue environment a
  | Not(f) -> not (evalFormula environment f)
  | And(f1, f2) -> (evalFormula environment f1) && (evalFormula environment f2)
  | Or(f1, f2) -> (evalFormula environment f1) || (evalFormula environment f2)
  | Implies(f1, f2) -> (evalFormula environment f2) || not (evalFormula environment f1)
  | Equivalent(f1, f2) -> (evalFormula environment (Implies(f1, f2))) && (evalFormula environment (Implies(f2, f1)));;


  (****** Question 3 ******)
(*    buildDecTree : tformula -> decTree
 * @brief builds the binary decision tree of a formula
 * @param `formula` the formula to build the binary decision tree of
 * @return the binary tree of `formula`
 *)
let rec buildDecTree (formula : tformula) =
  (*    aux : tformula -> env -> string list -> decTree
   * @brief generates the sub decision tree of `formula` for variables `vars`
   * @param `formula` the formula to build the binary decision tree of
   * @param `env` an accumulator for the environment, built with each recursive call
   * @param `vars` the variables not in the environment yet
   * @pre `env` is a well designed environment
   * @pre all the variables in `formula` are ether in the environment `env` or in `vars`
   * @return the sub decision tree of `formula` for the variables `vars`
   *)
  let rec aux (formula : tformula) (env : env) (vars : string list) = match vars with
    | [] -> DecLeaf (evalFormula env formula)
    | h::t -> DecRoot(h, aux formula ((h,true)::env) t, aux formula ((h,false)::env) t)
  in aux formula [] (getVars formula);;



(* ------------------------------------------------------------------------- *)
(* ------------------------ Binary Decision Diagram ------------------------ *)
(* ------------------------------------------------------------------------- *)

(****** Types definition ******)
type bddNode =
  | BddLeaf of int * bool
  | BddNode of int * string * int * int;;

(* We consider a binary decision diagram to be "well designed", or "valid", if :
  - each node has an unique id
  - no node references itself
  - no node references a non-existing node
  - each node is referenced by at least one node
  - there's no loop in the referencement of nodes
  - each path leads to a leaf
*)
type bdd = (int * (bddNode list));; (* un entier pour designer le noeud racine et la liste des noeuds *)


  (****** Question 4 ******)
(*    getBddNodeId : bddNode list -> bddNode -> int
 * @brief checks if a node exists in a list of nodes (set aside its id), and gets its id
 * @param `bddNodeList` the node list to search in
 * @param `node` the node to look for
 * @return the id of the node `node` in `bddNodeList` if `node` is in `bddNodeList`, -1 otherwise
 *)
let rec getBddNodeId (bddNodeList : bddNode list) (node : bddNode) = match bddNodeList with
  | [] -> -1
  | h::t -> match h, node with
    | BddLeaf(i, val1), BddLeaf(_, val2) -> if val1 = val2 then i else getBddNodeId t node
    | BddNode(i, name1, node1_1, node1_2), BddNode(_, name2, node2_1, node2_2) -> if (name1 = name2) && (node1_1 = node2_1) && (node1_2 = node2_2) then i else getBddNodeId t node
    | _ -> getBddNodeId t node;;

(*    getMaxNodeId : bddNode list -> int
 * @brief gets the maximum node id of the nodes in a list
 * @param `bddNodeList` the list of nodes to search the maximum node id of
 * @return the maximum node id of the nodes in `bddNodeList`
 *)
let rec getMaxNodeId (bddNodeList : bddNode list) = match bddNodeList with
  | [] -> 0
  | [BddLeaf(i, _)] -> i
  | [BddNode(i, _, _, _)] -> i
  | h::t -> let m = getMaxNodeId t in
    match h with
      | BddLeaf(i, _) -> if m>i then m else i
      | BddNode(i, _, _, _) -> if m>i then m else i;;

(*    buildBdd : tformula -> bdd
 * @brief builds the binary decision diagram of a formula
 * @param `formula` the formula to build the binary decision diagram of
 * @return the binary decision diagram of `formula`
 *)
let buildBdd (formula : tformula) =
  (*  aux : bddNode list -> tformula -> env -> string list -> int * bddNode list
   * @brief generates the sub binary decision diagram for `formula`,  
   * @param `bddNodeList` an accumulator for the bddNode list
   * @param `formula` the formula to build the bdd of
   * @param `env` an accumulator for the environment, built with each recursive call
   * @param `vars` the variables not in the environment yet
   * @pre bddNodeList is a bddNode list of a valid bdd
   * @pre `env` is a well designed environment
   * @pre all the variables in `formula` are ether in the environment `env` or in `vars`
   * @post returns a well designed bdd
   * @return the sub binary decision diagram for variables `vars`
   *)
  let rec aux bddNodeList formula env vars = match vars with
    | [] ->
      let m = (getMaxNodeId bddNodeList) + 1 in
      let node = BddLeaf(m, evalFormula env formula) in
      let n = getBddNodeId bddNodeList node in
      if n = -1 then (m, node::bddNodeList) else (n, bddNodeList)
    | h::t ->
      let node1, bddNodeList = aux bddNodeList formula ((h,true)::env) t in
      let node2, bddNodeList = aux bddNodeList formula ((h,false)::env) t in
      let m = (getMaxNodeId bddNodeList) + 1 in
      let node = BddNode(m, h, node1, node2) in
      let n = getBddNodeId bddNodeList node in
      if n = -1 then (m, node::bddNodeList) else (n, bddNodeList)
  in aux [] formula [] (getVars formula);;


(* ------------------------------------------------------------------------- *)
(* ----------------------------- BDD simplifié ----------------------------- *)
(* ------------------------------------------------------------------------- *)

  (****** Question 5 ******)
(*    simplifyNode : bddNode list -> int -> int -> bddNode list
 * @brief simplifies the bdd node list by removing the node with id `n` and modifying other nodes pointing to this node
 * @param `bddNodeList` the node list to simplify
 * @param `n` the id of the node to remove
 * @param `p` the node id of the (only) successor of node `n`
 * @return the simplified node list, with Node `n` removed and nodes pointing to node `n` updated to point to node `p`
 *)
let rec simplifyNode (bddNodeList : bddNode list) (n : int) (p : int) = match bddNodeList with
  | [] -> []
  | BddNode(id, _, _, _)::t when (id = n) -> simplifyNode t n p
  | BddNode(id, s, p1, p2)::t -> BddNode(id, s, (if p1=n then p else p1), (if p2=n then p else p2))::(simplifyNode t n p)
  | h::t -> h::(simplifyNode t n p);;

(*    simplifyBDD: bdd -> bdd
 * @brief simplifies a bdd by removing nodes with identical left and right successors
 * @param `bdd` the bdd to simplify
 * @pre `bdd` is a well designed bdd
 * @return the simplified bdd with nodes with identical left and right successors removed and other nodes updated
 *)
let simplifyBDD (bdd : bdd) =
  (*  aux : bdd -> bddNode list -> int * bddNode list
   * @brief simplifies a bdd by removing the nodes in `bddNodeList` which have identical left and right successors
   * @param `bdd` the bdd to simplify
   * @param `bddNodeList` the list of the nodes to browse for possible simplifications
   * @pre `bdd` is a valid bdd
   * @pre for first call, `bddNodeList` is the list of the nodes in `bdd`
   * @return the `bdd` simplified by removing the nodes in bddNodeList which can be simplified
   *)
  let rec aux (bdd : bdd) (bddNodeList : bddNode list) = match bdd, bddNodeList with
    | (m, l), [] -> (m, l)
    | (m, l), BddNode(id, s, p1, p2)::t when (p1=p2 && m=id) -> aux (p1, simplifyNode l id p1) t
    | (m, l), BddNode(id, s, p1, p2)::t when (p1=p2)         -> aux (m, simplifyNode l id p1) t
    | (m, l), h::t -> aux (m, l) t
  in match bdd with
    | (m, l) -> aux bdd l;;



(* ------------------------------------------------------------------------- *)
(* ----------------------- Vérification de formules ------------------------ *)
(* ------------------------------------------------------------------------- *)

  (****** Question 6 ******)
(*    isTautology : tformula -> bool
 * @brief verifies if a formula is a tautology
 * @param `formula` the formula to test
 * @return true if `formula` is a tautology, false otherwise
 *)
let isTautology (formula : tformula) =
  (simplifyBDD (buildBdd formula)) = (1, [BddLeaf (1, true)]);;

  (****** Question 7 ******)
(*    areEquivalent : tformula -> tformula -> bool
 * @brief verifies if two formulas are equivalent
 * @param `formula1` the first formula
 * @param `formula2` the second formula
 * @return true if `formula1` and `formula2` are equivalent, false otherwise
 *)
let areEquivalent (formula1 : tformula) (formula2 : tformula) =
  isTautology (Equivalent(formula1, formula2));;


(* ------------------------------------------------------------------------- *)
(* ------------------ Bonus : Affichage graphique de BDD ------------------- *)
(* ------------------------------------------------------------------------- *)
open Printf;;

  (****** Question 8 ******)
(*    dotBDD : string -> bdd -> unit
 * @brief generates the dot file for a bdd
 * @param `filename` the file in which to save the description of the graph
 * @param `bdd` the bdd to create the graph of
 * @pre `bdd` is a well designed binary decision diagram
 * @post the file `filename` contains the DOT description of the bdd
 *)
let dotBDD (filename : string) (bdd : bdd) =
  let file = open_out filename in
  (*    aux : out_channel -> bddNode list -> unit
   * @brief writes the digraph content description of a bdd in DOT format in a file
   * @param `file` the out_channel of the file in which to write the description of the digraph
   * @param `bddNodeList` the list of nodes of the bdd to graph
   * @pre `file` is a valid out_channel
   * @post the `file` now contains the content description of the digraph representing the bdd
   *)
  let rec aux file bddNodeList = match bddNodeList with
    | [] -> ()
    | BddLeaf(id, value)::t ->
      fprintf file "%d [style = bold, label=\"%B\"];\n" id value;
      aux file t
    | BddNode(id, s, p1, p2)::t ->
      fprintf file "%d [ label=\"%s\"];\n" id s;
      fprintf file "%d -> %d [color=red,style=dashed];\n" id p1;
      fprintf file "%d -> %d;\n" id p2;
      aux file t
  in
  fprintf file "digraph G {\n";
  match bdd with
    | (m, l) -> aux file l;
  fprintf file "}";
  close_out file;;


  (****** Question 9 ******)
(*    dotDec: string -> decTree -> unit
 * @brief generates the dot file for a decTree
 * @param `filename` the file in which to save the description of the graph
 * @param `tree` the decision tree to create the graph of
 * @pre `tree` is a well designed binary decision tree
 * @post the file `filename` contains the DOT description of the decision tree
 *)
let dotDec (filename : string) (tree : decTree) =
  let file = open_out filename in
  (*    aux : out_channel -> int -> decTree -> unit
   * @brief writes the digraph content description of a binary decision tree in DOT format in a file
   * @param `file` the out_channel of the file in which to write the description of the digraph
   * @param `n` the id of the current node to graph
   * @param `tree` the current node to graph
   * @pre `file` is a valid out_channel
   * @post the `file` now contains the content description of the digraph representing the decision tree
   *)
  let rec aux file n tree = match tree with
    | DecLeaf(value) ->
      fprintf file "%d [style = bold, label=\"%B\"];\n" n value;
    | DecRoot(s, l, r) ->
      fprintf file "%d [ label=\"%s\"];\n" n s;
      fprintf file "%d -> %d [color=red,style=dashed];\n" n (10*n+1);
      fprintf file "%d -> %d;\n" n (10*n+2);
      aux file (10*n+1) l;
      aux file (10*n+2) r;
  in
  fprintf file "digraph G {\n";
  aux file 1 tree;
  fprintf file "}";
  close_out file;;

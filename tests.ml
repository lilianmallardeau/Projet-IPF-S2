#use "projet.ml";;

(* ------------------------------------------------------------------------- *)
(* -------------------------- Arbres de décision --------------------------- *)
(* ------------------------------------------------------------------------- *)

  (****** Test Question 1 ******)
let p1 = Var "P1";;
let p2 = Var "P2";;
let q1 = Var "Q1";;
let q2 = Var "Q2";;
let f1 = Equivalent(q1, q2);;
let f2 = Equivalent(p1, p2);;
let ex1 = And(f1 ,f2);;
getVars ex1;;

let a = Var "A";;
let b = Var "B";;
let ex2 = Equivalent(Implies(a, b), Or(b, Not(a)));;

let testFormulas = [ex1; ex2];; (* <------- Enter in this list the formulas to generate the graphs of *)


  (****** Test Question 2 ******)
evalFormula ["P1",false;"P2",false;"Q1",false;"Q2",false] ex1;; (*true*)

  (****** Test Question 3 ******)
buildDecTree ex1;;


(* ------------------------------------------------------------------------- *)
(* ------------------------ Binary Decision Diagram ------------------------ *)
(* ------------------------------------------------------------------------- *)

  (****** test Question 4 ******)
buildBdd ex1;;



(* ------------------------------------------------------------------------- *)
(* ----------------------------- BDD simplifié ----------------------------- *)
(* ------------------------------------------------------------------------- *)

  (****** Test Question 5 ******)
simplifyBDD (buildBdd ex1);;



(* ------------------------------------------------------------------------- *)
(* ----------------------- Vérification de formules ------------------------ *)
(* ------------------------------------------------------------------------- *)

(* tests Questions 6 et 7 *)
let a = Var "A";;
let b = Var "B";;
isTautology (Equivalent(Implies(a, b), Or(b, Not(a))));;
areEquivalent (Implies(a, b)) (Or(b, Not(a)));;
isTautology (Or(a, Not(a)));;


(* ------------------------------------------------------------------------- *)
(* ------------------ Bonus : Affichage graphique de BDD ------------------- *)
(* ------------------------------------------------------------------------- *)

open Printf;;

(* test Question 8 & 9 *)
let rec generateDotFiles n formulas = match formulas with
  | [] -> ()
  | h::t ->
    dotBDD (sprintf "tests/test%d_bdd.dot" n)             (buildBdd h);
    dotBDD (sprintf "tests/test%d_simplified_bdd.dot" n)  (simplifyBDD (buildBdd h));
    dotDec (sprintf "tests/test%d_dectree.dot" n)         (buildDecTree h);
    generateDotFiles (n+1) t;
;;

generateDotFiles 1 testFormulas;;
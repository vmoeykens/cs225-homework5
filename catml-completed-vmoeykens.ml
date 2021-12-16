(*
   Homework 5: Completing the CatML interpreter.
   
   DIRECTIONS: In this OCaml code file you will find the beginning of various functions 
   with COMPLETE ME tags in the comments, that you must complete to obtain a *correct*
   interpreter for the CatML language.
   
   Both the tracer and stepper functions (with pretty printing) have been completed
   for you and can be used for testing examples as you work on the assignment. Example
   expressions for testing can be found in the course github repository. The online
   interpreter at http://ceskalka.w3.uvm.edu/225/catml/catml.php can be used to easily 
   generate ASTs for additional examples. You should submit this file once completed. 
   Your submission must be executable OCaml code.
   
   GRADING: Your code will be graded for correctness (in the sense of Lecture Notes 10, 
   Theorem 1.1), by both direct review of code and evaluation of your function definitions 
   on suites of test cases. The breakdown will be as follows:
   
   100 total points
   40 points for syntax and type correctness with a baseline of effort (i.e., you worked
      on a solution which is valid OCaml code. Note that just handing in this file as given 
      does not count as a baseline of effort).
   6 points for style (formatting, comments, elegance).
   54 points for formal correctness of definitions as measured by test cases: 
     - 10 points for expression closure (closed).
     - 44 points for reduction (redx, subst, isval).
     
   Test cases will be of low to high complexity, from simple arithmetic expressions to recursive 
   function definitions (using both fixpoint combinators and the Fix construct). **Only Graduate 
   Students will be tested on evaluation of structured data, i.e., pairs**. In all cases, evaluation 
   on test cases provided in the CS225-public repo will be a great indicator of your progress.
*) 

(*
   Abstract Syntax
   ---------------
  
   The expr datatype defines the ASTs for CatML. The mapping from CatML concrete syntax
   to abstract syntax is as follows, in full detail. This mapping is implemented by the
   parser in the online tool at http://ceskalka.w3.uvm.edu/225/catml/catml.php.
 
   [[True]] = Bool(true)
   [[False]] = Bool(false)
   [[n]] = Nat(n)           for any natural number n
   [[x]] = Var(Ident("x"))       for any variable x
   [[e1 + e2]] = Plus([[e1]], [[e2]])
   [[e1 - e2]] = Minus([[e1]], [[e2]])
   [[e1 And e2]] = And([[e1]], [[e2]])
   [[e1 Or e2]] = Or([[e1]], [[e2]])
   [[Not e]] = Not([[e]])
   [[(e1, e2)]] = Pair([[e1]], [[e2]])
   [[Fst(e)]] = Fst([[e]])
   [[Snd(e)]] = Snd([[e]])
   [[e1 e2]] = Appl([[e1]], [[e2]])
   [[Let x = e1 in e2]] = Let(Ident("x"), [[e1]], [[e2]])
   [[(Fun x . e)]] = Fun(Ident("x"), [[e]])
   [[(Fix z . x . e)]] = Fix(Ident("z"), Ident("x"), [[e]])
*)

type ident = Ident of string

type expr =
     (* boolean expression forms *)
     Bool of bool | And of expr * expr | Or of expr * expr | Not of expr   
     (* arithmetic expression forms *)
   | Nat of int | Plus of expr * expr | Minus of expr * expr | Equal of expr * expr  
     (* functional expression forms *)
   | Function of ident * expr | Appl of expr * expr | Var of ident
     (* pairs *)
   | Pair of expr * expr | Fst of expr | Snd of expr
     (* other forms *)
   | If of expr * expr * expr | Let of ident * expr * expr | Fix of ident * ident * expr

exception AssignmentIncomplete

(*
   Closed expression check
   ------------------------
   Since reduction is defined only on closed expressions, we need to implement
   a check to ensure that an input expression is closed. Since closure is preserved
   by reduction, this check can be performed once statically on source code,
   as in tracer and stepper below.
   Note: List.mem can be used to check whether a given value occurs in a list.
   
   closed : expr -> ident list -> bool
   in : an expression e and an identifier list ilist
   out : true iff e is closed, assuming every element of ilist is 
         a bound variable
*)
let rec closed e ident_list = match e with
      Bool(_) -> true
    | And(e1, e2) -> closed e1 ident_list && closed e2 ident_list
    | Let(i, e1, e2) -> closed e1 ident_list && closed e2 (i::ident_list)
    | Equal(left, right) -> closed left ident_list && closed right ident_list 
    | Or(left, right) -> closed left ident_list && closed right ident_list
    | Var(var) -> List.mem var ident_list
    | Function(x, e) -> closed e (x::ident_list)
    | Nat(x) -> true
    | Plus(left, right) -> closed left ident_list && closed right ident_list
    | Minus(left, right) -> closed left ident_list && closed right ident_list
    | Not(e) -> closed e ident_list
    | Appl(e3, e4) -> closed e3 ident_list && closed e4 ident_list
    | If(e3, e4, e5) -> closed e3 ident_list && closed e4 ident_list && closed e5 ident_list
    | Fix(z, x, e3) -> closed e3 (x::(z::ident_list))
    | Fst(e3) -> closed e3 ident_list
    | Snd(e3) -> closed e3 ident_list
    | Pair(e3, e4) -> closed e3 ident_list && closed e4 ident_list ;;


(*
   Substitution
   ------------
   We implement substitution as defined symbolically, to obtain a substution-based
   semantics in the interpreter.
  
   subst : expr -> expr -> ident -> expr
   in : expression e1, expression e2, identifier id
   out : e1[e2/id] 
*)
let rec subst e1 e2 id = match e1 with 
      Let(var, e3, e4) -> if var = id then Let(var, (subst e3 e2 id), e4) 
      else Let(var, (subst e3 e2 id), (subst e4 e2 id)) 
    | And(left, right) -> And((subst left e2 id), (subst right e2 id)) 
    | Equal(left, right) -> Equal((subst left e2 id), (subst right e2 id)) 
    | Or(left, right) -> Or((subst left e2 id), (subst right e2 id)) 
    | Var(var) -> if var = id then e2 else e1
    | Function(x, e) -> if x = id  then Function(x, e) else Function(x, subst e e2 id)
    | Nat(x) -> Nat(x)
    | Bool(x) -> Bool(x)
    | Plus(left, right) -> Plus((subst left e2 id), (subst right e2 id))
    | Minus(left, right) -> Minus((subst left e2 id), (subst right e2 id)) 
    | Not(e) -> Not(subst e e2 id)
    | Appl(e3, e4) -> Appl(subst e3 e2 id, subst e4 e2 id)
    | If(e3, e4, e5) -> If(subst e3 e2 id, subst e4 e2 id, subst e5 e2 id)
    | Fix(z, x, e3) -> if x = id then Fix(z, x, e3) else Fix(z, x, subst e3 e2 id)
    | Fst(e3) -> Fst(subst e3 e2 id)
    | Snd(e3) -> Snd(subst e3 e2 id)
    | Pair(e3, e4) -> Pair(subst e3 e2 id, subst e3 e2 id) ;;

(*
   Value predicate
   ---------------
   Checking whether a given expression is a value is critical for the operational 
   semantics. 
   isval : expr -> bool
   in : expression e
   out : true iff e is a value
*)
let rec isval e = match e with 
| Function(_, _) -> true
| Nat(_x) -> true
| Bool(_) -> true
| Fix(_, _, _) -> true
| Pair(e1, e2) -> isval e1 && isval e2 
| _ -> false ;;

exception StuckExpr

(*
   Single step reduction
   ---------------------
   Single (aka small) step reduction is the heart of the operational semantics. Pattern
   matching allows a tight connection with the symbolic definition of the semantics.
   
   redx : expr -> expr
   in : AST [[e]]
   out : AST [[e']] such that e -> e' in the operational semantics
   side effect : exception NotReducible raised if [[e]] isn't reducible in implementation.
*)
let rec redx e = match e with
     Not(Bool(false)) -> Bool(true) 
   | Not(Bool(true)) -> Bool(false)
   | And(Bool(_), Bool(false)) -> Bool(false)
   | And(Bool(true), Bool(true)) -> Bool(true)
   | And(Bool(false), Bool(_)) -> Bool(false)
   | Or(Bool(true), Bool(_)) -> Bool(true)
   | Or(Bool(false), Bool(false)) -> Bool(false)
   | Or(Bool(false), Bool(true)) -> Bool(true)
   | Not(e) -> Not(redx e)
   | And(e1,e2) -> if isval e1 then And(e1, redx e2) else And(redx e1, e2)
   | Or(e1, e2) -> if isval e1 then Or(e1, redx e2) else Or(redx e1, e2)
   | Nat(e1) -> Nat(e1)
   | Plus(Nat(e1), Nat(e2)) -> Nat(e1 + e2)
   | Plus(Nat(e1), e2) -> Plus(Nat(e1), redx e2)
   | Plus(e1, e2) -> Plus(redx e1, e2)
   | Minus(Nat(e1), Nat(e2)) -> Nat(e1 - e2)
   | Minus(Nat(e1), e2) -> Minus(Nat(e1), redx e2)
   | Minus(e1, e2) -> Minus(redx e1, e2)
   | Equal(Nat(e1), Nat(e2)) -> Bool(e1 = e2)
   | Equal(Nat(e1), e2) -> Equal(Nat(e1), redx e2)
   | Equal(e1, e2) -> Equal(redx e1, e2)
   | Bool(v) -> Bool(v)
   | Function(x, e1) -> Function(x, e1)
   | Appl(Function(x, e1), e2) -> if isval e2 then subst e1 e2 x else Appl(Function(x, e1), redx e2)
   | Appl(Fix(z, x, e1), e2) ->  if isval e2 then subst (subst e1 (Fix(z, x, e1)) z) e2 x else Appl(Fix(z, x, e1), redx e2)
   | Appl(e1, e2) -> if isval e1 then Appl(e1, redx e2) else Appl(redx e1, e2)
   | Var(x) -> Var(x)
   | If(Bool(true), e1, e2) -> e1
   | If(Bool(false), e1, e2) -> e2
   | If(e1, e2, e3) -> If(redx e1, e2, e3)
   | Let(x, e1, e2) -> if isval e1 then subst e2 e1 x else Let(x, redx e1, e2)
   | Fix(z, x, e1) -> Fix(z, x, e1) ;;

(*
   Multistep reduction
   -------------------
   redxs : expr -> expr
   in : AST [[e]]
   out : [[v]] such that e ->* v in the operational semantics
*)
let rec redxs e = if isval e then e else redxs (redx e)

open Printf;;

(*
  prettyPrint : expr -> string
  in : An expression AST [[e]].
  out : The concrete expression e in string format.
*)
let rec prettyPrint e = match e with
   | Bool true -> "True"
   | Bool false -> "False"
   | Nat n -> sprintf "%i" n
   | Var(Ident(x)) -> x
   | And (e1, e2) -> "(" ^ (prettyPrint e1) ^ " And " ^ (prettyPrint e2) ^ ")"
   | Or (e1, e2) -> "(" ^ (prettyPrint e1) ^ " Or " ^ (prettyPrint e2) ^ ")"
   | Not e1 -> "(Not " ^ (prettyPrint e1) ^ ")"
   | Plus (e1, e2) -> "(" ^ (prettyPrint e1) ^ " + " ^ (prettyPrint e2) ^ ")"
   | Minus (e1, e2) -> "(" ^ (prettyPrint e1) ^ " - " ^ (prettyPrint e2) ^ ")"
   | Equal (e1, e2) -> "(" ^ (prettyPrint e1) ^ " = " ^ (prettyPrint e2) ^ ")"
   | If(e1, e2, e3) -> "If " ^ (prettyPrint e1) ^ 
                       " Then " ^ (prettyPrint e2) ^
                       " Else " ^ (prettyPrint e3)
   | Function(Ident(x), e) -> "(Fun " ^ x ^ " . " ^ (prettyPrint e) ^ ")"
   | Fix(Ident(z), Ident(x), e) -> "(Fix " ^ z ^ " . " ^ x ^ " . " ^ (prettyPrint e) ^ ")"
   | Let(Ident(x), e1, e2) -> "Let " ^ x ^ " = " ^ (prettyPrint e1) ^ " In\n" ^ (prettyPrint e2)
   | Appl(e1, e2) -> (prettyPrint e1) ^ " " ^ (prettyPrint e2)
   | Pair(e1, e2) -> "(" ^ (prettyPrint e1) ^ ", " ^ (prettyPrint e2) ^ ")"
   | Fst(e1) -> 
      (match e1 with Pair(_) -> "Fst" ^  (prettyPrint e1) 
                  | _ ->  "Fst(" ^  (prettyPrint e1) ^ ")")
   | Snd(e1) -> 
      (match e1 with Pair(_) -> "Snd" ^  (prettyPrint e1) 
                  | _ ->  "Snd(" ^  (prettyPrint e1) ^ ")")


exception NotClosed
(*
  stepper : expr -> expr
  in : AST [[e]]
  out : [[v]] such that e ->* v in the operational semantics
  side effects : Blocks on keystroke between reductions, prints intermediate 
    expressions (aka the reduction trace) during evaluation 
*)
let stepper e = if not (closed e []) then raise NotClosed else
 let rec step e =
   (printf "%s" (prettyPrint e); flush stdout; read_line();
    if isval e then e else (printf "\n->\n"; flush stdout; step (redx e))) in step e
				   
(*
  tracer : expr -> expr
  in : AST [[e]]
  out : [[v]] such that e ->* v in the operational semantics
  side effects : prints intermediate expressions (aka the reduction trace) during evaluation 
*)
let rec tracer e = if not (closed e []) then raise NotClosed else
 let rec trace e =
    (printf "%s" (prettyPrint e); flush stdout;
     if isval e then e else (printf "\n->\n"; flush stdout; trace (redx e))) in trace e


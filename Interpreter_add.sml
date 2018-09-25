(* ____________________________________ Abstrakte Syntax _______________________________________________ *)

datatype con = False | True | IC of int             (* constants/ Konstanten *)
type id = string                                    (* identifiers/ Bezeichner *)
datatype opr = Add | Sub | Mul | Leq | And | Or     (* operators/ Operatoren *)
datatype uopr = Min | Neg | ++ | --                 (* unäre Operatoren (arithmetische Neg. | logische Neg.) *)

datatype ty = Bool | Int | Arrow of ty * ty | PairTy of ty * ty         (* types / Typen *)

datatype exp =                                      (* expressions/ Ausdrücke *)
               Con of con                           (* constants/ Konstanten *)
             | Id of id                             (* identifiers/ Bezeichner *) 
             | Opr of opr * exp * exp               (* operator application/ Operatoranwendung *)
             | UOpr of uopr * exp                   (* unäre Operatoren *)
             | If of exp * exp * exp                (* conditional/ Konditional *)
             | Abs of id * ty * exp                 (* abstraction/ Abstraktion *)
             | App of exp * exp                     (* procedure application/ Prozeduranwendung *)
             | Pair of exp * exp                    (* pair / Paare *)
             | Seq of exp * exp                      (* Sequenzialisierung *)
             | Switch of exp list * exp * exp       (* Switch *)
             | Rfn of id * id * ty * ty * exp       (* Rekursuive Prozedur *)

(* ___________________________________ Statische Semantik (elab) ___________________________________________ *)

type 'a env = id -> 'a                              (* type environment/ Typumgebung *)


exception Unbound of id
exception Error of string

fun empty x = raise Unbound x
fun update env x a = fn y => if y = x then a else env y

fun elabCon True = Bool
  | elabCon False = Bool
  | elabCon (IC _) = Int

fun elabOpr Add Int Int = Int
  | elabOpr Sub Int Int = Int
  | elabOpr Mul Int Int = Int
  | elabOpr Leq Int Int = Bool
  | elabOpr And Bool Bool = Bool
  | elabOpr Or Bool Bool = Bool
  | elabOpr _   _   _   = raise Error ("Unknown operator!")

fun elabUOpr Min Int = Int
  | elabUOpr ++ Int = Int
  | elabUOpr -- Int = Int
  | elabUOpr Neg Bool = Bool
  | elabUOpr _   _    = raise Error ("Unknown operator!")
  

fun elab f (Con c) = elabCon c
  | elab f (Id x)  = f x
  | elab f (Opr (opr, e1, e2)) = elabOpr opr (elab f e1) (elab f e2)
  | elab f (UOpr (uopr, e)) = elabUOpr uopr (elab f e)
  | elab f (Pair (e1, e2)) = PairTy (elab f e1, elab f e2)
  | elab f (If (e1, e2, e3)) = (case (elab f e1, elab f e2, elab f e3) of
                                  (Bool, t1, t2) => if t1=t2 then t1
                                                    else raise Error "Invalid Types! Two types in a conditional has to be equal!"
                                | _ => raise Error "First expression of conditional has to be boolean!")
  | elab f (Abs (x, t, e)) = Arrow (t, elab (update f x t) e)
  | elab f (Rfn (rfn, x, t1, t2, e)) = if (elab (update (update f rfn (Arrow (t1, t2))) x t1) e) = t2 then 
                                          Arrow (t1, t2)
                                       else raise Error "Invalid type of procedure!"
  | elab f (App (e1, e2)) = (case elab f e1 of
                               Arrow (t1, t2) => if t1 = (elab f e2) then t2
                                                 else raise Error "invalid type of procedure argument!"
                             | _ => raise Error "U kidding?! Procedure-application without procedure /).-")
  | elab f (Seq (e1, e2)) = (elab f e1; elab f e2)
  | elab f (Switch (xs, de, e)) = (case (elab f e, elab f de) of
                                    (Int, t) => if (foldl (fn (a,b) => ((elab f a) = t) andalso b) true xs) then t
                                                else raise Error "Invalid switch types."
                                  | _ => raise Error "No int-expression for Switch.")

datatype Elab = T of ty | SE of string

fun elab' f e = T (elab f e) handle                              (* Needed for correct exception message display *)
                    Unbound s => SE ("Unbound identifier: " ^s)
                  | Error m => SE (" Error: " ^m)

(* ___________________________________ Dynamische Semantik (eval) ___________________________________________ *)

datatype value = 
                  IV of int                             (* int values (also for boolean) *)
               |  Pairval of value * value              (* pair values *)
               |  Proc of id * exp * value env          (* procedure values *)
               |  RProc of id * id * exp * value env    (* rekursive Prozedur value *)

fun evalCon False = IV 0
  | evalCon True = IV 1
  | evalCon (IC x) = IV x

fun evalOpr Add (IV x) (IV y) = IV (x+y)
  | evalOpr Sub (IV x) (IV y) = IV (x-y)
  | evalOpr Mul (IV x) (IV y) = IV (x*y)
  | evalOpr Leq (IV x) (IV y) = IV (if x <= y then 1 else 0)
  | evalOpr And (IV 1) (IV 1) = IV 1
  | evalOpr And (IV _) (IV _) = IV 0
  | evalOpr Or (IV 0) (IV 0) = IV 0
  | evalOpr Or (IV _) (IV _) = IV 1
  | evalOpr _   _      _      = raise Error "Unknown operator!"

fun evalUOpr Min (IV x) = IV (x * ~1)
  | evalUOpr ++ (IV x) = IV (x + 1)
  | evalUOpr -- (IV x) = IV (x - 1)
  | evalUOpr Neg (IV 0) = IV 1
  | evalUOpr Neg (IV 1) = IV 0
  | evalUOpr _   _      = raise Error "Unknown operator!"

fun eval f (Con c) = evalCon c
  | eval f (Id x) = f x
  | eval f (Opr (opr, e1, e2)) = evalOpr opr (eval f e1) (eval f e2)
  | eval f (UOpr (uopr, e)) = evalUOpr uopr (eval f e)
  | eval f (Pair (e1, e2)) = Pairval (eval f e1, eval f e2)
  | eval f (If (e1, e2, e3)) = (case (eval f e1) of
                                    IV 1 => eval f e2
                                  | IV 0 => eval f e3
                                  | _ => raise Error "Invalid Type: First expression of conditional has to be bool!")
  | eval f (Abs (x, t, e)) = Proc (x, e, f)
  | eval f (Rfn (rfn, x, t1, t2, e)) = RProc (rfn, x, e, f)
  | eval f (App (e1, e2)) = (case (eval f e1, eval f e2) of
                               (Proc (x, e, venv), v) => eval (update venv x v) e 
                             | (RProc (rfn, x, e, env'), v) => eval (update (update env' rfn (RProc (rfn, x, e, env'))) x v) e
                             | _ => raise Error "Invalid procedure application!")
  | eval f (Seq (e1, e2)) = let 
                                val v1 = eval f e1
                                val v2 = eval f e2
                           in v2
                           end
  | eval f (Switch (xs, de, e)) = (case eval f e of 
                                     IV x => (eval f (List.nth (xs, x-1)) handle Subscript => eval f de)
                                   | _ => raise Error "invalid Switch value.")


datatype Eval = V of value | SE of string

fun eval' f e = V (eval f e) handle                              (* Needed for correct exception message display *)
                    Unbound s => SE ("Unbound identifier: " ^s)
                  | Error m => SE (" Error: " ^m)


(* ____________________________________ Abstrakte Syntax _______________________________________________ *)

datatype con = False | True | IC of int             (* constants/ Konstanten *)
type id = string                                    (* identifiers/ Bezeichner *)
datatype opr = Add | Sub | Mul | Leq                (* operators/ Operatoren *)

datatype ty = Bool | Int | Arrow of ty * ty         (* types / Typen mit Arrow of ty*ty für Prozeduren *)

datatype exp =                                      (* expressions/ Ausdrücke *)
               Con of con                           (* constants/ Konstanten *)
             | Id of id                             (* identifiers/ Bezeichner *) 
             | Opr of opr * exp * exp               (* operator application/ Operatoranwendung *)
             | If of exp * exp * exp                (* conditional/ Konditional *)
             | Abs of id * ty * exp                 (* abstraction/ Abstraktion *)
             | App of exp * exp                     (* procedure application/ Prozeduranwendung *)
             | Sq of exp * exp                      (* Sequenzialisierung *)
             | Rfn of id * id * ty * ty * exp       (* Rekursuive Prozedur *)

(* ___________________________________ Statische Semantik (elab) ___________________________________________ *)

type 'a env = id -> 'a                              (* type environment/ Typumgebung *)


exception Unbound of id
exception Error of string

fun empty x = raise Unbound x
fun update env x a y = if y = x then a else env y

fun elabCon True = Bool
  | elabCon False = Bool
  | elabCon (IC _) = Int

fun elabOpr Add Int Int = Int
  | elabOpr Sub Int Int = Int
  | elabOpr Mul Int Int = Int
  | elabOpr Leq Int Int = Bool
  | elabOpr _   _   _   = raise Error ("Unknown operator!")

fun elab f (Con c) = elabCon c
  | elab f (Id x)  = f x
  | elab f (Opr (opr, e1, e2)) = elabOpr opr (elab f e1) (elab f e2)
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
  | elab f (Sq (e1, e2)) = case (elab f e1, elab f e2) of
                               (t1, t2) => t2

datatype Elab = T of ty | SE of string

fun elab' f e = T (elab f e) handle                              (* Needed for correct exception message display *)
                    Unbound s => SE ("Unbound identifier: " ^s)
                  | Error m => SE (" Error: " ^m)

(* ___________________________________ Dynamische Semantik (eval) ___________________________________________ *)

datatype value = 
                  IV of int                             (* int values (also for boolean) *)
               |  Proc of id * exp * value env          (* procedure values *)
               |  RProc of id * id * exp * value env    (* rekursive Prozedur value *)

fun evalCon False = IV 0
  | evalCon True = IV 1
  | evalCon (IC x) = IV x

fun evalOpr Add (IV x) (IV y) = IV (x+y)
  | evalOpr Sub (IV x) (IV y) = IV (x-y)
  | evalOpr Mul (IV x) (IV y) = IV (x*y)
  | evalOpr Leq (IV x) (IV y) = IV (if x <= y then 1 else 0)
  | evalOpr _   _      _      = raise Error "Unknown operator!"

fun eval f (Con c) = evalCon c
  | eval f (Id x) = f x
  | eval f (Opr (opr, e1, e2)) = evalOpr opr (eval f e1) (eval f e2)
  | eval f (If (e1, e2, e3)) = (case (eval f e1) of
                                    IV 1 => eval f e2
                                  | IV 0 => eval f e3
                                  | _ => raise Error "Invalid Type: First expression of conditional has to be bool!")
  | eval f (Abs (x, t, e)) = Proc (x, e, f)
  | eval f (Rfn (rfn, x, t1, t2, e)) = RProc (rfn, x, e, f)
  | eval f (App (e1, e2)) = (case (eval f e1, eval f e2) of
                               (Proc (x, e, venv), v) => eval (update venv x v) e 
                             | (RProc (rfn, x, e, venv), v) => eval (update (update venv rfn (RProc (rfn, x, e, venv))) x v) e
                             | _ => raise Error "Invalid procedure application!")
  | eval f (Sq (e1, e2)) = let 
                                val v1 = eval f e1
                                val v2 = eval f e2
                           in v2
                           end

datatype Eval = V of value | SE of string

fun eval' f e = V (eval f e) handle                              (* Needed for correct exception message display *)
                    Unbound s => SE ("Unbound identifier: " ^s)
                  | Error m => SE (" Error: " ^m)


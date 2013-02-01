(* mini-ml.fs - Interpreter for a ML inspired language (Ported in 2011 to F#)
* Copyright (C) 1997 Paulo Pinto, Pablo Tavares
*
* This library is free software; you can redistribute it and/or
* modify it under the terms of the GNU Lesser General Public
* License as published by the Free Software Foundation; either
* version 2 of the License, or (at your option) any later version.
*
* This library is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
* Lesser General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public
* License along with this library; if not, write to the
* Free Software Foundation, Inc., 59 Temple Place - Suite 330,
* Boston, MA 02111-1307, USA.
*)


(*
GRAMMAR:
Start ::=  "\n" | "Quit" | "List" | "Let" Id Id "=" Exp | Id | Exp.
Exp ::= MTerm RestExp.
RestExp ::= "+" MTerm RestExp | "-" MTerm RestExp | .
MTerm ::= ETerm RestMTerm.
RestMTerm ::= "*" ETerm RestMTerm | "/" ETerm RestMTerm | .
ETerm ::= STerm ^ ETerm | STerm. 
STerm ::= Real | Id | Id STerm | "(" Exp ")" | "-" Exp | "DERIV" Id STerm |
          "FIX" Id STerm.
*)

(* TOKENS *)
module mini_ml
open System
open System.IO

type Token =
      LParTk
    | RParTk
    | NewLineTk
    | PlusTk
    | MinusTk
    | TimesTk
    | DividesTk
    | PowerTk
    | LetTk
    | AssignTk
    | QuitTk
    | ListTk
    | DerivTk
    | FixTk
    | IncludeTk
    | RealTk of float
    | IdTk of string
    ;;

(* EXPRESSION REPRESENTATION *)
type Exp = 
      UnMinus of Exp
    | Plus of Exp * Exp
    | Minus of Exp * Exp
    | Times of Exp * Exp
    | Divides of Exp * Exp
    | Power of Exp * Exp
    | Real of float 
    | Var of string
    | FunCall of string * Exp
    | Fix of string * Exp
    ;;

(* Used for errors while evaluating user code *)
exception SyntaxError of string;;

(*
   Fuctions to allow coherent error messages and ease its maintainability.
   There are other error messages given as parameter to the SyntaxError constructor,
   however they are relative to unique cases, not like these ones.
*)
let SyntErr () = "Syntax Error.\n";;
let BadId Id ="The " + Id + " identifier is unknown.\n";;
let DuplId () = "Parameter has the same name as the function.\n";;

(* Used for ML compatibility while porting from Camllight *)
let print_float num = printf "%f" num;;
let print_string str = printf "%s" str;;

(* TOKENIZER *)

let first (s:string) = (s.[0]) ;;
let rest (s: string) = s.[ 1 .. (s.Length - 1)] ;;
let split s = (first s, rest s) ;;
let add_ch_end (s:string) (c:char) = s + string(c) ;;
let add_ch_beg (c:char) (s : string) = string(c) + s ;;

let rec get_digits s =
    let (ch, chs) = split s in
        match ch with
            | _ when (ch >= '0' && ch <= '9') ->
                    let (dig2, chs2) = get_digits chs in
                        (add_ch_beg ch dig2, chs2)
            | _ ->  ("", s)
    ;;

let rec get_float_str s =
    let (dig, chs) = get_digits s in
        if (first chs) = '.' then
            let (dig2, chs2) = get_digits (rest chs)
            in (((add_ch_end dig '.') + dig2), chs2)
        else (dig, chs)
    ;;

let rec get_id_str s =
    let (ch, chs) = split s in
        match ch with
            | ch when (ch >= 'A' && ch <= 'Z') ||
                      (ch >= 'a' && ch <= 'z') ->
                    let (id2, chs2) = get_id_str chs in
                        (add_ch_beg ch id2, chs2)
            | _ ->  ("", s)
    ;;

let Keyword_or_Id s = match s with
                       "quit"    -> QuitTk
                     | "list"    -> ListTk
                     | "include" -> IncludeTk
                     | "let"     -> LetTk
                     | "DERIV"   -> DerivTk 
                     | "FIX"     -> FixTk 
                     |    _      -> IdTk s;;

let rec tokenizer s =
    let (ch, chs) = split s in
    match ch with
          ' ' ->    tokenizer chs
        | '(' ->    LParTk:: (tokenizer chs)
        | ')' ->    RParTk:: (tokenizer chs)
        | '+' ->    PlusTk::(tokenizer chs)
        | '-' ->    MinusTk::(tokenizer chs)
        | '*' ->    TimesTk::(tokenizer chs)
        | '^' ->    PowerTk::(tokenizer chs)
        | '/' ->    DividesTk::(tokenizer chs)
        | '=' ->    AssignTk::(tokenizer chs)
        | ch when (ch >= 'A' && ch <= 'Z') ||
                  (ch >= 'a' && ch <= 'z') ->
                    let (id_str, chs) = get_id_str s
                    in (Keyword_or_Id id_str)::(tokenizer chs) 
        | ch when (ch >= '0' && ch <= '9') ->
                    let (fl_str, chs) = get_float_str s
                    in (RealTk (float (fl_str)))::(tokenizer chs)
        | '$' ->    if chs = "" then [] else raise (SyntaxError (""))
        | _ ->      raise (SyntaxError (SyntErr ()))
    ;;

let rec tokens s = if s = "" then [NewLineTk]
                     else tokenizer (add_ch_end s '$') ;;


(* PARSER *)


let rec is_function_name s symTbl  = match symTbl with
                                     |   []           -> false
                                     | ((name, _)::t) -> if s = name then true
                                                         else is_function_name s t;;

(* 
  This code should be placed in the functions area, however it has located originally
  here, due to Camllight lookup rules, as the goal for the F# migration was minimal
  effort, the code was left here.
*)


(* Used to define the functions in the symbol table *)
type FunType = Builtin of (float -> float)
             | UserDef of Exp;;

(*
   Thrown by symbol table lookup rules when symbols are not found.
*)
exception NotFound;;

let rec getFun s symTbl = match symTbl with
                          | []                -> raise NotFound
                          |  ((name, def)::t) -> if s = name then def
                                                 else getFun s t;;

(* Replaces all Var occurences in the expression structure by nexp *)
let  rec Bind def nexp =
          match def with
             Plus  (left, right)   -> Plus  (Bind left nexp, Bind right nexp)

           | Minus (left, right)   -> Minus (Bind left nexp, Bind right nexp)

           | Times (left, right)   -> Times (Bind left nexp, Bind right nexp)

           | Divides (left, right) -> Divides (Bind left nexp, Bind right nexp)

           | Power (left, right)   -> Power (Bind left nexp, Bind right nexp)

           | FunCall (name, value)   -> FunCall (name, Bind value nexp)

           | Fix (name, value)       -> Fix (name, Bind value nexp)

           | UnMinus value           -> UnMinus (Bind value nexp)

           | Real  value             -> Real value

           | Var   name            -> nexp;;




(* Evaluates the derivatives of internal functions *)
let DoDerivBuiltin name = 
         match name with
           | "sin"  -> FunCall ("cos", Var "x")
           | "cos"  -> UnMinus (FunCall ("sin", Var "x"))
           | "log"  -> Divides (Real 1.0, Var "x")
           | "exp"  -> FunCall ("exp", Var "x")
           | "tan"  -> 
                 Divides (Real 1.0, Power (FunCall ("cos", Var "x"),Real 2.0))
           | "asin" -> 
                 Divides (Real 1.0, FunCall ("sqrt", Minus (Real 1.0, Power (Var "x", Real 2.0))))
           | "acos" ->
                 Divides (UnMinus (Real 1.0), FunCall ("sqrt", Minus (Real 1.0, Power (Var "x", Real 2.0))))
           | "atan" -> 
                 Divides (Real 1.0, Plus (Real 1.0, Power (Var "x", Real 2.0)))
           | "sqrt" -> 
                Divides (Real 1.0, Times (Real 2.0, FunCall ("sqrt", Var "x")))
           | _    -> raise (SyntaxError (SyntErr ())) ;;


(* Evaluates the derivative of fdef, where fdef has the Exp type *)
let  rec DoDeriv fdef =
              match fdef with
                 Plus  (left, right)   -> Plus  (DoDeriv left, DoDeriv right)

               | Minus (left, right)   -> Minus (DoDeriv left, DoDeriv right)

               | Times (left, right)   -> Plus (Times (left, DoDeriv right),
                                               Times (DoDeriv left, right))

               | Divides (left, right) -> 
                       Divides (Minus (Times (DoDeriv left, right), 
                                       Times (left, DoDeriv right)), 
                                Power (right, Real 2.0)) 

               | Power (left, right)   ->
                    Plus (Times (Times (Power (left, right), DoDeriv right),
                           FunCall ("log", left)), Times (Times (right, 
                                                           Power (left, Minus (right, Real 1.0))), DoDeriv left))
               | FunCall ("exp", value)   -> 
                    Times (DoDeriv value, FunCall ("exp", value))
               | FunCall ("log", value)   -> Divides (DoDeriv value, value)
               | FunCall ("sin", value)   -> 
                    Times (DoDeriv value, FunCall ("cos", value))
               | FunCall ("cos", value)   -> 
                    Times (UnMinus(DoDeriv value), FunCall ("sin", value))
               | FunCall ("tan", value)   -> 
                   Divides (DoDeriv value, Power ((FunCall ("cos", value)), 
                                                  Real 2.0))
               | FunCall ("asin", value)   -> 
                    Divides (DoDeriv value, 
                     FunCall ("sqrt", Minus (Real 1.0, Power (value, Real 2.0))))
               | FunCall ("acos", value)   -> 
                    Divides (UnMinus (DoDeriv value), 
                     FunCall ("sqrt", Minus (Real 1.0, Power (value, Real 2.0))))
               | FunCall ("atan", value)   -> 
                    Divides (DoDeriv value, 
                     Plus (Real 1.0, Power (value, Real 2.0)))
               | FunCall (_, _)        -> raise (SyntaxError (SyntErr ()))
               | UnMinus value           -> UnMinus (DoDeriv value)

               | Real  value             -> Real 0.0
 
               | Var   name            -> Real 1.0

               | Fix  (fname, def)     -> 
                      raise (SyntaxError "O operador FIX nao e derivavel");;

(* Constructs an expression tree out of token list *)
let rec pExp tks symTbl = 
    let (a, tks2) = pMTerm tks symTbl in
        pRestExp a tks2 symTbl

and  pRestExp x tks symTbl =
                    match tks with
                       PlusTk::tks2 -> let (b, tks3) = pMTerm tks2 symTbl
                                          in pRestExp (Plus (x, b)) tks3 symTbl
                     | MinusTk::tks2 -> let (b, tks3) = pMTerm tks2 symTbl
                                         in pRestExp (Minus (x, b)) tks3 symTbl
                     | _ ->  (x, tks)


and  pMTerm tks symTbl = 
    let (a, tks2) = pETerm tks symTbl in
        pRestMTerm a tks2 symTbl

and  pRestMTerm x tks symTbl =
                match tks with
                    TimesTk::tks2 -> let (b, tks3) = pETerm tks2 symTbl
                                     in pRestMTerm (Times (x, b)) tks3 symTbl
                  | DividesTk::tks2 -> let (b, tks3) = pETerm tks2 symTbl
                                       in pRestExp (Divides (x, b)) tks3 symTbl
                  | _ ->  (x, tks)

and pETerm tks symTbl =
    let (a, tks2) = pSTerm tks symTbl
    in match tks2 with
        PowerTk::tks3 -> 
                let (b, tks4) = pETerm tks3 symTbl
                in (Power (a, b), tks4)
        | _ ->  (a, tks2)

and pSTerm tks symTbl =
    match tks with
          ((RealTk f)::r) ->
                    (Real f, r)
        | (MinusTk::r) ->
                    let (t, r2) = pSTerm r symTbl in
                                ((UnMinus t), r2)
        | (LParTk::r) ->
                    (match pExp r symTbl with
                          (t, RParTk::r2) ->
                                (t, r2)
                        |  _ ->  raise (SyntaxError (SyntErr ())))
        | ((IdTk s)::r) ->
                    if is_function_name s symTbl then
                      match r with
                        |   []  -> 
                                raise (SyntaxError "Function used as value\n")
                        |  _   -> let (t, r2) = pSTerm r symTbl in
                                     (FunCall (s,t), r2)
                    else (Var s, r)
        | (DerivTk::(IdTk fname)::r) -> 
                    (try 
                       let fdef = getFun fname symTbl in
                         let (t, r2) = pSTerm r symTbl in
                           match fdef with
                             Builtin _  -> (Bind (DoDerivBuiltin fname)  t, r2)
                           | UserDef def -> (Bind (DoDeriv def)  t, r2)
                     with
                       NotFound -> raise (SyntaxError (SyntErr ())))
        | (FixTk::(IdTk fname)::r) ->
                    if is_function_name fname symTbl then
                        let (t, r2) = pSTerm r symTbl in
                                (Fix (fname,t), r2)
                    else raise (SyntaxError (BadId fname))
        | _ ->      raise (SyntaxError (SyntErr ()))
    ;;


(* Expression evaluator *)

(* represents calculation results *)
type Result = Const of float
            | UNDEF;;


(* addition *)
let Addop left right =
             match (left, right) with
             |   ((Const x), (Const y)) -> Const (x + y)
             |   ( _ , _ )              -> UNDEF;;

(* subtraction *)
let Minop left right =
             match (left, right) with
             | ((Const x), (Const y)) -> Const (x - y)
             | ( _ , _ )              -> UNDEF;;
             
(* multiplication *)
let Mulop left right =
             match (left, right) with
             |   ((Const x), (Const y)) -> Const (x * y)
             |   ( _ , _ )              -> UNDEF;;

(* division *)
let Divop left right =
             match (left, right) with
             | ((Const x), (Const y)) -> if y <> 0.0 then Const (x / y)
                                         else UNDEF
             |   ( _ , _ )              -> UNDEF;;

(* left to the power of right *)
let Powop left right =
             match (left, right) with
             | ((Const x),  (Const y)) -> if x = 0.0 && y = 0.0 then UNDEF
                                          else Const (x ** y)
             |   ( _ , _ )              -> UNDEF;;

(* unary minus *)
let UMinop arg  =
             match arg with
             | Const x -> Const (- x)
             |  _      -> UNDEF;;



(* evalutates an arithmetic expression *)
let rec EvalExp x symTbl =
  match x with
    Plus  (left, right) -> Addop (EvalExp left symTbl) (EvalExp right symTbl)
  | Minus (left, right) -> Minop (EvalExp left symTbl) (EvalExp right symTbl)
  | Times (left, right) -> Mulop (EvalExp left symTbl) (EvalExp right symTbl)
  | Divides (left, right) -> Divop (EvalExp left symTbl) (EvalExp right symTbl)
  | Power (left, right) -> Powop (EvalExp left symTbl) (EvalExp right symTbl)
  | FunCall (fname, value)-> (let valor = EvalExp value symTbl in
                               match valor with
                                 UNDEF   -> UNDEF
                               | Const y -> let fdef = getFun fname symTbl in
                                              ApplyFun (fname, fdef) y symTbl)

  | Fix (fname, value) -> (let valor = EvalExp value symTbl in
                            match valor with
                             UNDEF   -> UNDEF
                           | Const y -> let fdef = getFun fname symTbl in
                                          DoFix (fname, fdef) y 1000 symTbl)

  | UnMinus value      -> UMinop (EvalExp value symTbl)
  | Real  num        -> Const num
  | Var   name       -> raise (SyntaxError (BadId name))

(* Evaluates the result of value when applied to fdef *)
and ApplyFun def value symTbl =
         match def with
           (fname, Builtin f) -> (match fname with
                                   "asin"
                                 | "acos" -> if value >= -1.0 && value <= 1.0 then
                                               Const (f value)
                                             else
                                               UNDEF
   
                                 | "tan" -> if (cos value) <> 0.0 then
                                               Const (f value)
                                             else
                                               UNDEF

                                 | "log" -> if value > 0.0 then
                                               Const (f value)
                                             else
                                               UNDEF
                                 
                                 | "sqrt" -> if value >= 0.0 then
                                               Const (f value)
                                             else
                                               UNDEF
                                 
                                 |    _  -> Const (f value))

         | (fname, UserDef f) -> EvalExp (Bind f (Real value)) symTbl

(* Calculates the fix point for the function fdef *)
and DoFix fdef value iter symTbl = 
                    let x = ApplyFun fdef value symTbl in
                     match x with
                       UNDEF   -> UNDEF
                     | Const y -> if abs (y - value) < 0.00000000001 then
                                      Const y
                                     else if iter > 0 then
                                            DoFix fdef y (iter - 1) symTbl
                                          else
                                            UNDEF;;



(* Shows the result *)
let PrintResult res =
                match res with 
                  (Const x) -> print_float x
                |     _     -> print_string "UNDEF";;



let  PrintFun s def =
      let rec PrintFun2 def = 
                 match def with
                 Plus  (left, right)   -> PrintFun2 left;
                                          print_string " + ";
                                          PrintFun2 right

               | Minus (left, right)   -> PrintFun2 left;
                                          print_string " - ";
                                          PrintFun2 right

               | Times (left, right)   -> PrintFun3 left;
                                          print_string " * ";
                                          PrintFun3 right

               | Divides (left, right) -> PrintFun3 left;
                                          print_string " / ";
                                          PrintFun3 right

               | Power (left, right)   -> PrintFun3 left;
                                          print_string " ^ ";
                                          PrintFun3 right

               | FunCall (name, value)   -> print_string (" " + name + " ");
                                            PrintFun3 value

               | Fix (name, value)       -> print_string (" FIX " + name + " ");
                                            PrintFun3 value

               | UnMinus value           -> print_string " - ";
                                            PrintFun3 value

               | Real  num             -> print_float num

               | Var   name            -> print_string " x "

(* Helper function to check when parenthesis are required *)
         and PrintFun3 def =
            match def with
                 FunCall (a, b)        -> PrintFun2 def
               | Real  a               -> PrintFun2 def
               | Var   a               -> PrintFun2 def
               |    _                  -> print_string "(";
                                          PrintFun2 def;
                                          print_string ")"
               in print_string ("\n " + s + " x = ");
                  PrintFun2 def;;



(* Dumps to the screen the definition of an existing function in the symbol table *)
let PrintFunDef s symTbl = try
                             let def = getFun s symTbl in
                               match def with
                                Builtin x -> print_string "\n Builtin Function \n"
                              | UserDef x -> PrintFun s x
                           with
                             NotFound -> 
                           print_string ("\nThe function " + s + " is not defined!\n");;

(* Shows all external (not builtin) functions that are currently defined *)
let rec printFunList funcs = 
                     match funcs with
                     |      []                  -> Console.Out.Flush()
                     | ((nome, Builtin f)::t)   -> printFunList t
                     | ((nome, UserDef def)::t) -> printFunList t;
                                                   PrintFun nome def;;

(* Simplifies expressions by performing calculations with constants and simple
   function invocations.
*)
let rec simplify def symTbl =
         match def with
          Plus (left, right) -> (let x = simplify left symTbl in
                                 let y = simplify right symTbl in
                                 match (x, y) with
                                 (Real a, Real b)   -> Real (a + b)
                               | (Real a, Plus (Real b, c)) -> 
                                                  Plus (Real (a + b), c)
                               | (Real a, Plus (b, Real c)) -> 
                                                  Plus (b, Real (a + c))
                               | (Plus (Real a, b), Real c) -> 
                                                  Plus (Real (a + c), b)
                               | (Plus (a, Real b), Real c) -> 
                                                  Plus (a, Real (b + c))
                               | (Real a, Minus (Real b, c)) -> 
                                                  Minus (Real (a + b), c)
                               | (Real a, Minus (b, Real c)) -> 
                                                  Plus (b, Real (a - c))
                               | (Minus (Real a, b), Real c) -> 
                                                  Minus (Real (a + c), b)
                               | (Minus (a, Real b), Real c) -> 
                                                  Plus (a, Real (c - b))
                               | (  _  , Real 0.0)  -> x
                               | (Real 0.0,  _   )  -> y
                               |  ( _, _)           -> Plus (x, y))

        | Minus (left, right) -> (let x = simplify left symTbl in
                                 let y = simplify right symTbl in
                                 match (x, y) with
                                  (Real a, Real b)   -> Real (a - b)
                                | (Minus (Real a, b), Real c) -> 
                                                  Minus (Real (a - c), b)
                                | (Minus (a, Real b), Real c) -> 
                                                  Minus (a, Real (b + c))
                                | (Plus (Real a, b), Real c) -> 
                                                  Plus (Real (a - c), b)
                                | (Plus (a, Real b), Real c) -> 
                                                  Plus (a, Real (b - c))

                                | (  _  , Real 0.0)  -> x
                                | (Real 0.0,  _   )  -> UnMinus y
                                |  ( _, _)           -> Minus (x, y))

        | Times (left, right) -> (let x = simplify left symTbl in
                                 let y = simplify right symTbl in
                                 match (x, y) with
                                 (Real a, Real b)             -> Real (a * b)
                               | (  _  , Real 0.0)            -> Real 0.0
                               | (Real 0.0,   _  )            -> Real 0.0
                               | (_, Real 1.0)                -> x
                               | (Real 1.0, _)                -> y
                               | (_, UnMinus (Real 1.0))      -> UnMinus x
                               | (UnMinus (Real 1.0), _)      -> UnMinus y
                               |  ( _, _)                     -> Times (x, y))

        | Divides (left, right) -> (let x = simplify left symTbl in
                                    let y = simplify right symTbl in
                                    match (x, y) with
                                    (Real a, Real 0.0)           -> 
                                       raise (SyntaxError  (SyntErr ()))
                                  | (Real a, Real b)             -> Real (a / b)
                                  | (Real 0.0, _ )               -> Real 0.0
                                  | ( _ , Real 1.0)              -> x
                                  | ( _ , UnMinus (Real 1.0))    -> UnMinus x
                                  |  ( _, _)                     -> Divides (x, y))

        | Power (left, right) -> (let x = simplify left symTbl in
                                 let y = simplify right symTbl in
                                 match (x, y) with
                                 (Real 0.0, Real 0.0)  ->
                                            raise (SyntaxError  (SyntErr ()))
                               | (Real a, Real b)  -> Real (a ** b)
                               | (Real 0.0, _ )    -> Real 0.0
                               | ( _ , Real 0.0)   -> Real 1.0
                               | (Real 1.0,  _ )   -> Real 1.0
                               | ( _ , Real 1.0)   -> x
                               |  ( _, _)          -> Power (x, y))

        | FunCall (name, param) -> (let x = getFun name symTbl in
                                    match x with
                                        Builtin f -> (let y = simplify param symTbl in
                                                       match y with
                                                         Real z -> 
                                                             (let value = ApplyFun (name, x) z symTbl in
                                                               match value with
                                                                 Const a -> Real a
                                                                | UNDEF  -> 
                                                                      raise (SyntaxError (SyntErr ())))
                                                         |  _   -> FunCall (name, y))
                                      | UserDef y -> simplify (Bind y (simplify param symTbl)) symTbl)

        | Fix (name, param) ->Fix (name, simplify param symTbl)

        | UnMinus a -> (let x = simplify a symTbl in
                        match x with 
                          Real 0.0 -> x
                         |  _      -> UnMinus a)
        |     _     -> def;;
   


(*
  Validates if all occurences of a given Var instance represent the
  same identifier. If not, an exception will be returned.
*)

let rec CheckOcurr def vname =
       match def with
          Plus (left, right) -> CheckOcurr left vname; 
                                CheckOcurr right vname

        | Minus (left, right) -> CheckOcurr left vname; 
                                 CheckOcurr right vname

        | Times (left, right) -> CheckOcurr left vname; 
                                 CheckOcurr right vname

        | Divides (left, right) -> CheckOcurr left vname;
                                   CheckOcurr right vname

        | Power (left, right) -> CheckOcurr left vname;
                                 CheckOcurr right vname

        | FunCall (name, param) -> CheckOcurr param vname

        | Fix (name, param)     -> CheckOcurr param vname  

        | UnMinus a -> CheckOcurr a vname
        | Var name  -> if name <> vname then raise (SyntaxError (BadId name))
                        else ()
        |   _       -> ();;

(*********************************************************************)

(* Used as escape mechanism to exit the application *)
exception Terminate;;

(* Thrown when there is a parse error while reading an included file. This allows
   for a behavior similar to the Pascal language family, which terminate on first error. *)
exception ErrorInFile;;


(*

Parser that evaluates the required math expressions.

EXAMPLES:

#parse "1+2*3^4";;        
- : Exp = Plus (Real 1.0, Times (Real 2.0, Power (Real 3.0, Real 4.0)))
#parse "1^2*3+4";;
- : Exp = Plus (Times (Power (Real 1.0, Real 2.0), Real 3.0), Real 4.0)
#parse "1+2*3";;
- : Exp = Plus (Real 1.0, Times (Real 2.0, Real 3.0))
#parse "(1+2)*3";;
- : Exp = Times (Plus (Real 1.0, Real 2.0), Real 3.0)
#parse "-123.45+x+f 5*3";;
- : Exp =
 Plus
   (UnMinus (Real 123.45),
      Plus (Var "x", Times (FunCall ("f", Real 5.0), Real 3.0)))
*)


let rec parse s symTbl =
  let tks = tokens s in
    match tks with
     | NewLineTk::[] -> symTbl
     | QuitTk::[] -> raise Terminate
     | LetTk::(IdTk f)::(IdTk param)::AssignTk::tks2 ->
                        (try
                          if f <> param then
                           let (t, tks1) = pExp tks2 symTbl in
                           match (t, tks1) with
                             (t, []) ->   CheckOcurr t param;
                                          let x = simplify t symTbl in
                                           PrintFun f x;
                                           print_string "\n";  
                                           (f , UserDef x)::symTbl
                                          
                           |    _    -> raise (SyntaxError (SyntErr ()))
                          else
                           raise (SyntaxError (DuplId ()))
                         with
                           SyntaxError error -> 
                             print_string ("\nError while evaluating " + f + ": " + error);
                             raise ErrorInFile)

     | IncludeTk::(IdTk fname)::[] ->
                   (try
                     let f = File.OpenText fname in
                       let sym = prompt f symTbl in
                         f.Close();
                         sym
                     with
                     | :? FileNotFoundException as a-> print_string "File not found!\n"; symTbl)  
     
     | ListTk::[]      -> printFunList symTbl;
                          print_string "\n"; 
                          symTbl
     | ((IdTk nome)::[]) -> PrintFunDef nome symTbl;
                            print_string "\n";
                            symTbl

     | _ -> let (t, tks1) = pExp tks symTbl in
             match (t, tks1) with
               (t, []) -> PrintResult(EvalExp t symTbl);
                          symTbl
              |  _     -> raise (SyntaxError (SyntErr ()))


(* Interpreter prompt *)
and  prompt (f: TextReader) symTbl =   if f = Console.In then (print_string "#"; Console.Out.Flush());
                                       try
                                         let str = f.ReadLine() in
                                          let sym = parse str symTbl in
                                           if f = Console.In then (print_string "\n"; Console.Out.Flush());
                                         prompt f sym
                                       with
                                          Terminate         -> symTbl 
                                        | SyntaxError ""    -> prompt f symTbl
                                        | SyntaxError error -> 
                                           print_string ("\nError while evaluating expresssion : " + error);
                                           prompt f symTbl
                                        | ErrorInFile       -> if f <> Console.In then symTbl
                                                               else prompt f symTbl
                                        | :? IOException       -> symTbl;;
                                                       

(* Application entry point, using a pre-defined symbol table *)

let main () = print_string "\n\tWelcome to MiniMl.\n\tVersion 0.00002\n";
              let x =
                prompt Console.In [("sin", Builtin sin); ("cos", Builtin cos);
                             ("asin", Builtin asin); ("acos", Builtin acos);
                             ("tan", Builtin tan); ("atan", Builtin atan);
                             ("exp", Builtin exp); ("log", Builtin log);
                             ("sqrt", Builtin sqrt)] in
                print_string "\nBye !!!";;


 main ();;

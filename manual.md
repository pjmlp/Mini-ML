#Mini-ML, an expression evaluator

##Introduction

In this work was intended to create a basic expression evaluator.

This was originally done in [Caml Light](http://caml.inria.fr/caml-light/index.en.html) as a team project. Given F#'s similarity
with the ML language family, I've used it as a way to learn F#.

The name Mini-ML comes from being originally implemented in a ML like language.

Contrary to the ML language this interpreter had to support an
undefined value, something like the absorvent value in mathematics.

##References

In the prompt you may type :

* Math expressions like
    * +, *, -, /, ^, - (unary)
    * exp, log, sqrt, sin, cos, tan, asin, acos, atan
    * User defined functions
    * constants
    * Operator **DERIV**
    * Operator **FIX**

* Function definitions
    * **let** _function\_name_ _variable_ = _math\_expression_

* Funtions names, which result in showing their definition

* **include** _file\_name_, which includes a file in the enviroment

* **quit**, terminates the execution

###DERIV and FIX syntax

**DERIV** function\_name math\_expression

Math expression may be a variable, a constant or a math expression
between braces.

**FIX** function\_name math\_expression

Math expression may be a variable, a constant or a math expression
between braces.

It stops when the modulos of the diference between the function in the
point Xn-1 and Xn be inferior to _0.00000000001_, or when the function has
realized _1000_ iteractions.

#Implementation Considerations
All the internal math operations that need to return a numeric result,
return the following type :

    type Result = const of float
                | UNDEF;;

The internal functions that accept and return the type \emph{Result}
are :

* Addop
* Minop
* Mulop
* Divop
* Powop
* UMinop


There are other functions that indirectly manipulate the type
_Result_, for example : 

* EvalExp
* ApplyFun
* DoFix
* PrintResul

The functions defined by the user and the ones defined by the system
are defined in a symbol table that has the following arrangement :

    (string, FunType)

where FunType is defined by :

    Type FunType = Builtin of float -> float
                 | UserDef of Exp;; 

These definitions allow that the user may redefine the internal
functions if he (or she) wishes so. For example :

    #let f x = 1 + x

    f x = 1 + x

    #let g x = x * f  x

    g x = x * (1 + x)

    #DERIV g 2

    2


The interpreter is case sensitive. Please note the *#* character represents the prompt.

##Grammar


    Start     ::=  "\n" | "Quit" | "List" | "Let" Id Id "=" Exp 
                | Id | Exp.
    Exp       ::= MTerm RestExp.
    RestExp   ::= "+" MTerm RestExp | "-" MTerm RestExp | .
    MTerm     ::= ETerm RestMTerm.
    RestMTerm ::= "*" ETerm RestMTerm | "/" ETerm RestMTerm | .
    ETerm     ::= STerm ^ ETerm | STerm. 
    STerm     ::= Real | Id | Id STerm | "(" Exp ")" | "-" Exp
               |  "DERIV" Id STerm | "FIX" Id STerm.


##Licence

Copyright (C) 1997 Paulo Pinto, Pablo Tavares

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the
Free Software Foundation, Inc., 59 Temple Place - Suite 330,
Boston, MA 02111-1307, USA.

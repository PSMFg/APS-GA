abstract sig Loc { } // An integer variable (X from Loc)

sig DLoc extends Loc { } // Delta Loc (Variables that can be used everywhere)
sig ALoc extends Loc { } // Aux Loc (Variables mainly used in the left-hand side of =. They are forbidden to be used in conditions)
sig XLoc extends Loc { } // Xi Loc (Variables that cannot be changed)

sig State { bind: Loc -> one Int }

sig IState extends State {}
sig FState extends State {}
one sig Example {
  pairs: IState one -> one FState
}


// A generic Command (Statement)
abstract sig Cmd { }
// The Skip statement
lone sig Skip extends Cmd { }
// Assignment statement
sig Assign extends Cmd { lhs: one IntVar, rhs: one AExp }
  { (IntVar<:rhs) != lhs and
    rhs !in IntVal and
    lhs.name !in XLoc
  }
// Arithmetic expressions
abstract sig AExp { }
sig IntVal extends AExp { val: one Int }
sig IntVar extends AExp { name: one Loc }
sig Add extends AExp { op1: one AExp, op2: one AExp }//{ op1 != op2 }//{ op1 in IntVar and op2 in IntVal }
sig Sub extends AExp { op1: one AExp, op2: one AExp }//{ op1 in IntVar and op2 in IntVar and op1.name != op2.name}
sig Mult extends AExp { op1: one AExp, op2: one AExp }//{ op1 in IntVal and op1.val != 0 and op2 in IntVar }
// Sequential composition
sig SComp extends Cmd { cur, next: one Cmd }
// Boolean expressions (Recall that BitTrue = -1 and then -1 needs to be present always!!!)
abstract sig BExp { lhs, rhs: one AExp }
  { /*lhs in IntVar and rhs in IntVar and*/
  	lhs.name != rhs.name and lhs.name !in ALoc and rhs.name !in ALoc
  	and (#BExp =< plus[#While, #CondS])
		/*Se tiver Or e And entao a formula final ficaria
			(#BExp =< plus[#While, plus[#CondS, plus[#And, plus[#Or, 2]]]])
		*/
  }
sig EQ extends BExp {  }
sig NEQ extends BExp {  }
sig LEQ extends BExp {  }
sig GEQ extends BExp {  }
sig GTH extends BExp {  }
// Conditional statement (IF THEN ELSE)
sig CondS extends Cmd { cond: one BExp, then, elsen: one Cmd }{ then != elsen }
// Loop statement
sig While extends Cmd { cond: one BExp, wbody: one (Cmd - While), unfold: set Expansion/*, inv: one BExp*/ }
{ (#unfold >= 2 => (all e1, e2: unfold | e1 != e2 => e1.exp.first.curr.bind != e2.exp.first.curr.bind))
  /*and cond != inv*/ }
sig Expansion { exp: seq StChg }
 { # exp = # exp.elems and (all i: exp.inds | i != exp.lastIdx implies exp[i].next = exp[add[i,1]].curr)}
sig StChg { curr, next: one State }

//sig Max2 extends Cmd { arg1: one Loc, arg2: one Loc, res: one Loc }{ arg1 != arg2 and res !in XLoc }

// Main program
one sig Prog { body: one Cmd }

/*
    //Implementing the Great Common Divisor -- GCD program
    int InLoc1 = 7;
    int InLoc2 = 21;
    int OutLoc = 0;
    while(InLoc1!=InLoc2) {
        if(InLoc1>InLoc2)
            InLoc1=InLoc1-InLoc2;
        else
            InLoc2=InLoc2-InLoc1;
    }
    OutLoc = InLoc1;
    System.out.println("GCD= "+OutLoc);
*/

module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2 extends DLoc {}
one sig OutLoc extends ALoc {}
one sig Assign1, Assign2, Assign3 extends Assign {}
one sig Sub1, Sub2 extends Sub {}
one sig IState1 extends IState {} { bind = {InLoc1 -> 4} + {InLoc2 -> 2} + {OutLoc -> 0}}
one sig FState1 extends FState {} { bind = {InLoc1 -> 2} + {InLoc2 -> 2} + {OutLoc -> 2}}
one sig IState2 extends IState {} { bind = {InLoc1 -> 2} + {InLoc2 -> 3} + {OutLoc -> 0}}
one sig FState2 extends FState {} { bind = {InLoc1 -> 1} + {InLoc2 -> 1} + {OutLoc -> 1}}
one sig Example1 extends Example {} { pairs = IState1 -> FState1 + IState2 -> FState2 }

pred PreC[iSt: one IState] {

	//??=InLoc1-InLoc2
	Assign1.rhs = Sub1
	Sub1.op1.name = InLoc1
	Sub1.op2.name = InLoc2

	//??=InLoc2-InLoc1
	Assign2.rhs = Sub2
	Sub2.op1.name = InLoc2
	Sub2.op2.name = InLoc1

	//?? = InLoc1
	Assign3.rhs.name = InLoc1

}

pred PosC[iSt: one IState, fSt: one FState] {
  	
}

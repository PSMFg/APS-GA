/*
    Trying to sinthesizing the max3 algorithim
    A Java implementation:
    int InLoc1,InLoc2 //XLoc
    int DLoc1=0; //DLoc
    int OutLoc=0; //DLoc
    while(InLoc2>DLoc1)
    {
      OutLoc+=InLoc1;
      DLoc1++;
    }
    printf("The multiplication is %d",OutLoc);
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2 extends XLoc {}
one sig DLoc1, OutLoc extends DLoc {}
one sig Assign1, Assign2 extends Assign {}
one sig Add1, Add2 extends Add {}
one sig SComp1 extends SComp {}
one sig While1 extends While {}
one sig GTH1 extends GTH {}
one sig IState1 extends IState {} { bind = {InLoc1->3} + {InLoc2->2} + {DLoc1->0} + {OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->3} + {InLoc2->2} + {DLoc1->2} + {OutLoc->6}}

one sig Example1 extends Example {} { pairs = IState1->FState1}

pred PreC[iSt: one IState] {

  //?? = OutLoc+InLoc1;
	Assign1.rhs = Add1
	Add1.op1.name = OutLoc
	Add1.op2.name = InLoc1

	//?? = DLoc1+1;
	Assign2.rhs = Add2
	Add2.op1.name = DLoc1
	Add2.op2.val = 1

}

pred PosC[iSt: one IState, fSt: one FState] {  

}

run Synt for 7 but -1..7 Int , 1 IState, 1 FState, 2 Assign, 1 SComp, 1 While, 0 CondS, 2 Add, 1 IntVal, 4 IntVar, 0 Sub, 0 Mult, 1 GTH, 0 EQ, 0 NEQ, 0 LEQ, 0 GEQ
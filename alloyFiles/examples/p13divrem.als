/*
    Trying to sinthesizing the remainder of the division algorithim
    A Java implementation:
		
    int InLoc1; //num
    int InLoc2 //divisor
    int DLoc1=0; //product
    int DLoc2=0; //loop counter
    int OutLoc=0; //DLoc
    while(DLoc1<=InLoc1)
    {
      DLoc2 += 1;
      DLoc1 = InLoc2 * DLoc2
    }
    OutLoc = InLoc2 + InLoc1 - DLoc1
    System.out.Println("The remainder of "+InLoc1+"/"+InLoc2+" is "+OutLoc);
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2 extends XLoc {}
one sig DLoc1, DLoc2, OutLoc extends DLoc {}
one sig IntVal1 extends IntVal {}
one sig Assign1, Assign2, Assign3 extends Assign {}
one sig Add1, Add2 extends Add {}
one sig Sub1 extends Sub {}
one sig Mult1 extends Mult {}
one sig SComp1, SComp2 extends SComp {}
one sig While1 extends While {}
one sig LEQ1 extends LEQ {}
one sig IState1 extends IState {} { bind = {InLoc1->3}+{InLoc2->2}+{DLoc1->0}+{DLoc2->0}+{OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->3}+{InLoc2->2}+{DLoc1->4}+{DLoc2->2}+{OutLoc->1}}

one sig Example1 extends Example {} { pairs = IState1->FState1}

pred PreC[iSt: one IState] {
	
	//?? = DLoc2+1;
	Assign2.rhs = Add1
	Add1.op1.name = DLoc2
	Add1.op2.val = 1

	//?? = InLoc2*DLoc2;
	Assign3.rhs = Mult1
	Mult1.op1.name = InLoc2
	Mult1.op2.name = DLoc2

	//OutLoc = ?? + ?? - DLoc1;
	Assign1.rhs = Add2
	Add2.op1.name = InLoc2
	Add2.op2 = Sub1
	Sub1.op1.name = InLoc1
	Sub1.op2.name = DLoc1

}

pred PosC[iSt: one IState, fSt: one FState] {

}

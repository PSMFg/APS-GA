/*
    Trying to sinthesizing the factorial algorithim
    A Java implementation:  
    Integer InLoc1 = Integer.parseInt(args[1]);
		Integer DLoc1 = 0;
		Integer InLoc2 = Integer.parseInt(args[2]);
		Integer OutLoc = 0;
		
		while(InLoc1 > DLoc1) {
			DLoc1 = DLoc1 + 1;
         InLoc2 = InLoc2 * DLoc1;
		}
		OutLoc = InLoc2;
    System.out.Println("The factorial is "+OutLoc);
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1 extends XLoc {}
one sig DLoc1, InLoc2, OutLoc extends DLoc {}
one sig IntVal1 extends IntVal {}
one sig Assign1, Assign2, Assign3 extends Assign {}
one sig Add1 extends Add {}
one sig Mult1 extends Mult {}
one sig SComp1, SComp2 extends SComp {}
one sig While1 extends While {}
one sig GTH1 extends GTH {}
one sig IState1 extends IState {} { bind = {InLoc1->3}+{InLoc2->1}+{DLoc1->0}+{OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->3}+{InLoc2->6}+{DLoc1->3}+{OutLoc->6}}

one sig Example1 extends Example {} { pairs = IState1->FState1}

pred PreC[iSt: one IState] {

	//?? = DLoc1+1;
	Assign2.rhs = Add1
	Add1.op1.name = DLoc1
	Add1.op2.val = 1

	//?? = InLoc2*InLoc1;
	Assign3.rhs = Mult1
	Mult1.op1.name = InLoc2
	Mult1.op2.name = DLoc1

	//?? = InLoc2;
	Assign1.rhs.name = InLoc2

}

pred PosC[iSt: one IState, fSt: one FState] {  

}

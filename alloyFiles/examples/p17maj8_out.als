/*
  Trying to sinthesizing a simple algorithim
  Java implementation:
	OutLoc = 0;
	InLoc4 = 1; //(or 2)
	InLoc5 = 1; //(or 2)
	...
	InLoc10 = 1; //(or 2)
  InLoc11 = 1; //(or 2)
  OutLoc=InLoc4+InLoc5+InLoc6+InLoc7+InLoc8+InLoc9+InLoc10+InLoc11;
  if(OutLoc >= InLoc3) {
    OutLoc = InLoc2;
  } else {
    OutLoc = InLoc1;
  }
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2, InLoc3, InLoc4, InLoc5, InLoc6, InLoc7, InLoc8, InLoc9, InLoc10, InLoc11 extends XLoc {}
one sig OutLoc extends DLoc {}
one sig GTH1 extends GTH {}
one sig Add1, Add2, Add3, Add4, Add5, Add6, Add7 extends Add {}
one sig Assign1, Assign2, Assign3 extends Assign {}
one sig IState1 extends IState {} {bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->12}+{InLoc4->1}+{InLoc5->1}+{InLoc6->2}+{InLoc7->1}+{InLoc8->1}+{InLoc9->1}+{InLoc10->1}+{InLoc11->1}+{OutLoc->0}}
one sig FState1 extends FState {} {bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->12}+{InLoc4->1}+{InLoc5->1}+{InLoc6->2}+{InLoc7->1}+{InLoc8->1}+{InLoc9->1}+{InLoc10->1}+{InLoc11->1}+{OutLoc->1}}
one sig IState2 extends IState {} {bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->12}+{InLoc4->2}+{InLoc5->2}+{InLoc6->1}+{InLoc7->1}+{InLoc8->1}+{InLoc9->2}+{InLoc10->2}+{InLoc11->2}+{OutLoc->0}}
one sig FState2 extends FState {} {bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->12}+{InLoc4->2}+{InLoc5->2}+{InLoc6->1}+{InLoc7->1}+{InLoc8->1}+{InLoc9->2}+{InLoc10->2}+{InLoc11->2}+{OutLoc->2}}
one sig IState3 extends IState {} {bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->12}+{InLoc4->1}+{InLoc5->2}+{InLoc6->2}+{InLoc7->2}+{InLoc8->2}+{InLoc9->1}+{InLoc10->2}+{InLoc11->1}+{OutLoc->0}}
one sig FState3 extends FState {} {bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->12}+{InLoc4->1}+{InLoc5->2}+{InLoc6->2}+{InLoc7->2}+{InLoc8->2}+{InLoc9->1}+{InLoc10->2}+{InLoc11->1}+{OutLoc->2}}

one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2+IState3->FState3 }

pred PreC[iSt: one IState] {
	
	//?? = InLoc4 + InLoc5 + InLoc6 + InLoc7 + InLoc8 + InLoc9 + InLoc10 + InLoc11
	//Assign1.rhs = Add1
	Add1.op1.name = InLoc4
	Add1.op2 = Add2
	Add2.op1.name = InLoc5
	Add2.op2 = Add3
	Add3.op1.name = InLoc6
	Add3.op2 = Add4
	Add4.op1.name = InLoc7
	Add4.op2 = Add5
	Add5.op1.name = InLoc8
	Add5.op2 = Add6
	Add6.op1.name = InLoc9
	Add6.op2 = Add7
	Add7.op1.name = InLoc10
	Add7.op2.name = InLoc11

	GTH1.lhs.name = OutLoc

	// ??= InLoc1
	Assign3.rhs.name = InLoc1
	//??= InLoc2
	Assign2.rhs.name = InLoc2
	
}

pred PosC[iSt: one IState, fSt: one FState] {
  
}

run Synt for 9 but -1..16 Int , 3 IState, 3 FState, 3 Assign, 1 SComp, 1 CondS, 0 While, 7 Add, 0 IntVal, 12 IntVar, 0 Sub, 0 Mult, 1 GTH, 0 EQ, 0 NEQ, 0 LEQ, 0 GEQ
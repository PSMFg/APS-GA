/*
    Trying to sinthesizing "the sum of squares from 1 to n" algorithm
    A Java implementation:
    InLoc1 = 3;
    OutLoc = 0;
    DLoc1 = 0;
    while(InLoc1>DLoc1 ) {
            DLoc1 = DLoc1 + 1;
            OutLoc += DLoc1 * DLoc1;
            //System.out.println("OutLoc inside loop "+OutLoc);
    }
    System.out.println("The sum of squares from 1 to "+InLoc1+" is "+OutLoc);
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1 extends XLoc {}
one sig DLoc1, OutLoc extends DLoc {}
one sig IntVal1 extends IntVal {}
one sig Assign1, Assign2 extends Assign {}
one sig Add1, Add2 extends Add {}
one sig Mult1 extends Mult {}
one sig SComp1 extends SComp {}
one sig While1 extends While {}
one sig GTH1 extends GTH {}
one sig IState1 extends IState {} { bind = {InLoc1->2}+{DLoc1->0}+{OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->2}+{DLoc1->2}+{OutLoc->5}}

one sig Example1 extends Example {} { pairs = IState1->FState1}

pred PreC[iSt: one IState] {

  //?? = DLoc1+1;
  Assign1.rhs = Add1
  Add1.op1.name = DLoc1
  Add1.op2.val = 1

  //?? = OutLoc + DLoc1 * DLoc1;
  Assign2.rhs = Add2
  Add2.op1.name = OutLoc
  Add2.op2 = Mult1
  Mult1.op1.name = DLoc1
  Mult1.op2.name = DLoc1

}

pred PosC[iSt: one IState, fSt: one FState] {

}

run Synt for 7 but -1..7 Int , 1 IState, 1 FState, 2 Assign, 1 SComp, 1 While, 2 CondS, 1 IntVal, 2 Add, 1 Mult, 3 IntVar, 0 Sub, 1 GTH, 0 EQ, 0 NEQ, 1 LEQ, 0 GEQ
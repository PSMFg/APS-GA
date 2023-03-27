/*
		// A dynamic programming program well-known as Fibonnaci sequency.
    int n = 10; //InLoc1
    int g = 1;  //InLoc2
    int i = 0;  //DLoc3
    int f = 0;  //OutLoc
    while (n > i) {
        i++;
        f = f + g;
        g = f - g;
        System.out.println(f);
    }
    System.out.println("The "+n+"# Fibonacci's sequence value is equal to "+f);
*/

module progFinder

open ../imp[PreC, PosC]

one sig InLoc1, InLoc2, DLoc3, OutLoc extends DLoc {}
one sig Assign1, Assign2, Assign3 extends Assign {}
one sig SComp1, SComp2 extends SComp {}
one sig Add1, Add2 extends Add {}
one sig Sub1 extends Sub {}
one sig While1 extends While {}
one sig GTH1 extends GTH {}
one sig IState1 extends IState {} {bind={InLoc1->3}+{InLoc2->1}+{DLoc3->0}+{OutLoc->0}}
one sig FState1 extends FState {} {bind={InLoc1->3}+{InLoc2->1}+{DLoc3->3}+{OutLoc->2}}
one sig Example1 extends Example {} {pairs=IState1->FState1}

pred PreC[iSt: one IState] {
  
  //?? = DLoc3 + 1
  Assign1.rhs = Add1
  Add1.op1.name = DLoc3
  Add1.op2.val = 1

  //?? = OutLoc + InLoc2
  Assign2.rhs = Add2
  Add2.op1.name = OutLoc
  Add2.op2.name = InLoc2

  //?? = OutLoc - InLoc2
  Assign3.rhs = Sub1
  Sub1.op1.name = OutLoc
  Sub1.op2.name = InLoc2
}

pred PosC[iSt: one IState, fSt: one FState] {

}

run Synt for 8 but -1..4 Int , 1 IState, 1 FState, 3 Assign, 2 SComp, 1 While, 0 CondS, 2 Add, 1 Sub, 1 IntVal, 4 IntVar, 0 Mult, 1 GTH, 0 EQ, 0 NEQ, 0 LEQ, 0 GEQ
/*
    //Implementing the integral SQRT
		//Pre-cond: x>=1
		Post-cond: (i-1)² <= x < i²
      com x = 4 a saída é OutLoc= 2
      com x = 5, 6, 7 ou 8 a saída é OutLoc= 2.
      com x = 9 a saída é OutLoc = 3
      int x=8; // entrada
      int v=1; // var auxiliar
      int i=1; // var auxiliar
      int OutLoc=1; // saída
      while(v<=x) {
          v = v + 2 * i + 1;
          i++;
      }
      OutLoc = i-1;
      System.out.println("A parte inteira da raiz de "+x+" é "+OutLoc+".");
*/

module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1 extends XLoc {}
one sig DLoc1, DLoc2 extends DLoc {}
one sig OutLoc extends ALoc {}
one sig Mult1 extends Mult {}
one sig Sub1 extends Sub {}
one sig Assign1, Assign2, Assign3 extends Assign {}
one sig Add1, Add2, Add3 extends Add {}
one sig IState1 extends IState {} { bind = {InLoc1->6}+{DLoc1->1}+{DLoc2->1}+{OutLoc->1}}
one sig FState1 extends FState {} { bind = {InLoc1->6}+{DLoc1->9}+{DLoc2->3}+{OutLoc->2}}
one sig Example1 extends Example {} { pairs = IState1 -> FState1 }

pred PreC[iSt: one IState] {

  //?? = DLoc2 + 1
  Assign2.rhs = Add3
  Add3.op1.name = DLoc2
  Add3.op2.val = 1

  //?? = DLoc2 - 1
  Assign3.rhs = Sub1
  Sub1.op1.name = DLoc2
  Sub1.op2.val = 1

  //?? = DLoc1 + 2*DLoc2 + 1
  Assign1.rhs = Add1
  Add1.op1.name = DLoc1
  Add1.op2 = Add2
  Add2.op1 = Mult1
  Mult1.op1.val = 2 
  Mult1.op2.name = DLoc2
  Add2.op2.val = 1

}

pred PosC[iSt: one IState, fSt: one FState] {
    
}


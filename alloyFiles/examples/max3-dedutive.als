/*
    Trying to sinthesizing the max3 algorithim
    Here is a c language implementation
    OutLoc = x>y ? (x>z ? x : z) : (y>z ? y : z);
    or a Java implementation:
    if(InLoc1 > InLoc2) {
        if(InLoc3 > InLoc1) {
      	    OutLoc = InLoc3;
        } else {
      	    OutLoc = InLoc1;
        }
    } else {
        if(InLoc2 > InLoc3) {
      	    OutLoc = InLoc2;
        } else {
      	    OutLoc = InLoc3;
        }
    }
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2, InLoc3 extends XLoc {}
one sig OutLoc extends ALoc {}
//one sig IState1 extends IState {} { bind = {InLoc1->3} + {InLoc2->6} + {InLoc3->1} + {OutLoc->0}}
//one sig FState1 extends FState {} { bind = {InLoc1->3} + {InLoc2->6} + {InLoc3->1} + {OutLoc->6}}
one sig IState1 extends IState {} {}
one sig FState1 extends FState {} {}
one sig Example1 extends Example {} { pairs = IState1->FState1}
one sig Assign1, Assign2, Assign3 extends Assign {}

pred PreC[iSt: one IState] {
  iSt.bind[InLoc1] > 0 and 
  iSt.bind[InLoc2] > 0 and 
  iSt.bind[InLoc3] > 0
}

pred PosC[iSt: one IState, fSt: one FState] {

  Assign1.rhs.name = InLoc1
  Assign2.rhs.name = InLoc2
  Assign3.rhs.name = InLoc3

  (fSt.bind[OutLoc] = iSt.bind[InLoc1] or fSt.bind[OutLoc] = iSt.bind[InLoc2] or fSt.bind[OutLoc] = iSt.bind[InLoc3]) and
    fSt.bind[OutLoc] >= iSt.bind[InLoc1] and
    fSt.bind[OutLoc] >= iSt.bind[InLoc2] and
    fSt.bind[OutLoc] >= iSt.bind[InLoc3]

}

//run Synt for 6 but -1..9 Int, 3 Assign, 0 SComp, 3 CondS, 0 While, 0 IntVal, 4 IntVar, 0 Add, 0 Sub, 0 Mult, 0 EQ, 0 NEQ, 1 LEQ, 2 GEQ, 0 GTH

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
one sig IState1 extends IState {} { bind = {InLoc1->3} + {InLoc2->6} + {InLoc3->1} + {OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->3} + {InLoc2->6} + {InLoc3->1} + {OutLoc->6}}
one sig IState2 extends IState {} { bind = {InLoc1->4} + {InLoc2->1} + {InLoc3->2} + {OutLoc->0}}
one sig FState2 extends FState {} { bind = {InLoc1->4} + {InLoc2->1} + {InLoc3->2} + {OutLoc->4}}
one sig IState3 extends IState {} { bind = {InLoc1->2} + {InLoc2->1} + {InLoc3->5} + {OutLoc->0}}
one sig FState3 extends FState {} { bind = {InLoc1->2} + {InLoc2->1} + {InLoc3->5} + {OutLoc->5}}
one sig IState4 extends IState {} { bind = {InLoc1->1} + {InLoc2->6} + {InLoc3->3} + {OutLoc->0}}
one sig FState4 extends FState {} { bind = {InLoc1->1} + {InLoc2->6} + {InLoc3->3} + {OutLoc->6}}
one sig IState5 extends IState {} { bind = {InLoc1->4} + {InLoc2->2} + {InLoc3->1} + {OutLoc->0}}
one sig FState5 extends FState {} { bind = {InLoc1->4} + {InLoc2->2} + {InLoc3->1} + {OutLoc->4}}
one sig IState6 extends IState {} { bind = {InLoc1->1} + {InLoc2->2} + {InLoc3->5} + {OutLoc->0}}
one sig FState6 extends FState {} { bind = {InLoc1->1} + {InLoc2->2} + {InLoc3->5} + {OutLoc->5}}

one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2+IState3->FState3+IState4->FState4+IState5->FState5+IState6->FState6}
one sig Assign1, Assign2, Assign3 extends Assign {}

pred PreC[iSt: one IState] {

  

}

pred PosC[iSt: one IState, fSt: one FState] {

  Assign1.rhs.name = InLoc1
  Assign2.rhs.name = InLoc2
  Assign3.rhs.name = InLoc3

}

run Synt for 6 but -1..9 Int , 6 IState, 6 FState, 3 Assign, 0 SComp, 3 CondS, 0 While, 0 IntVal, 6 IntVar, 0 Add, 0 Sub, 0 Mult, 0 EQ, 0 NEQ, 2 LEQ, 0 GEQ, 1 GTH
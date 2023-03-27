/*
    Trying to sinthesizing the median3 algorithim
    Here is a Java implementation:
    if(InLoc1 > InLoc2) {
        if(InLoc3 > InLoc1) {
      	    OutLoc = InLoc1;
        } else {
      	    OutLoc = InLoc3;
        }
    } else {
        if(InLoc2 > InLoc3) {
      	    OutLoc = InLoc3;
        } else {
      	    OutLoc = InLoc2;
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
one sig FState1 extends FState {} { bind = {InLoc1->3} + {InLoc2->6} + {InLoc3->1} + {OutLoc->3}}
one sig IState2 extends IState {} { bind = {InLoc1->4} + {InLoc2->1} + {InLoc3->2} + {OutLoc->0}}
one sig FState2 extends FState {} { bind = {InLoc1->4} + {InLoc2->1} + {InLoc3->2} + {OutLoc->2}}
one sig IState3 extends IState {} { bind = {InLoc1->2} + {InLoc2->1} + {InLoc3->5} + {OutLoc->0}}
one sig FState3 extends FState {} { bind = {InLoc1->2} + {InLoc2->1} + {InLoc3->5} + {OutLoc->2}}
one sig IState4 extends IState {} { bind = {InLoc1->1} + {InLoc2->6} + {InLoc3->3} + {OutLoc->0}}
one sig FState4 extends FState {} { bind = {InLoc1->1} + {InLoc2->6} + {InLoc3->3} + {OutLoc->3}}
one sig IState5 extends IState {} { bind = {InLoc1->4} + {InLoc2->2} + {InLoc3->1} + {OutLoc->0}}
one sig FState5 extends FState {} { bind = {InLoc1->4} + {InLoc2->2} + {InLoc3->1} + {OutLoc->2}}
one sig IState6 extends IState {} { bind = {InLoc1->1} + {InLoc2->2} + {InLoc3->5} + {OutLoc->0}}
one sig FState6 extends FState {} { bind = {InLoc1->1} + {InLoc2->2} + {InLoc3->5} + {OutLoc->2}}

one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2+IState3->FState3+IState4->FState4+IState5->FState5+IState6->FState6}
one sig Assign1, Assign2, Assign3 extends Assign {}

pred PreC[iSt: one IState] {
  Assign1.rhs.name = InLoc1
  Assign2.rhs.name = InLoc2
  Assign3.rhs.name = InLoc3

}

pred PosC[iSt: one IState, fSt: one FState] {

}

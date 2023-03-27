/*
    Trying to sinthesizing the add3 algorithim
    Java implementation:
    OutLoc = x + y;
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2 extends XLoc {}
one sig OutLoc extends DLoc {}
one sig IState1 extends IState {} { bind = {InLoc1->1} + {InLoc2->3} + {OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->1} + {InLoc2->3} + {OutLoc->4}}
one sig IState2 extends IState {} { bind = {InLoc1->4} + {InLoc2->1} + {OutLoc->0}}
one sig FState2 extends FState {} { bind = {InLoc1->4} + {InLoc2->1} + {OutLoc->5}}
one sig IState3 extends IState {} { bind = {InLoc1->2} + {InLoc2->5} + {OutLoc->0}}
one sig FState3 extends FState {} { bind = {InLoc1->2} + {InLoc2->5} + {OutLoc->7}}

one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2+IState3->FState3}

pred PreC[iSt: one IState] {

}

pred PosC[iSt: one IState, fSt: one FState] {

}


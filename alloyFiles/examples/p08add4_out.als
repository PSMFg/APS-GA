/*
    Trying to sinthesizing the add4 algorithim
    Java implementation:
    OutLoc = x + y + w + z;
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2, InLoc3, InLoc4 extends XLoc {}
one sig Add1, Add2, Add3 extends Add {}
one sig OutLoc extends DLoc {}
one sig IState1 extends IState {} { bind = {InLoc1->0}+{InLoc2->1}+{InLoc3->2}+{InLoc4->3}+{OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->0}+{InLoc2->1}+{InLoc3->2}+{InLoc4->3}+{OutLoc->6}}
one sig IState2 extends IState {} { bind = {InLoc1->2}+{InLoc2->4}+{InLoc3->2}+{InLoc4->1}+{OutLoc->0}}
one sig FState2 extends FState {} { bind = {InLoc1->2}+{InLoc2->4}+{InLoc3->2}+{InLoc4->1}+{OutLoc->9}}
one sig IState3 extends IState {} { bind = {InLoc1->3}+{InLoc2->1}+{InLoc3->0}+{InLoc4->2}+{OutLoc->0}}
one sig FState3 extends FState {} { bind = {InLoc1->3}+{InLoc2->1}+{InLoc3->0}+{InLoc4->2}+{OutLoc->6}}
one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2+IState3->FState3}

pred PreC[iSt: one IState] {

}

pred PosC[iSt: one IState, fSt: one FState] {

}

run Synt for 8 but -1..9 Int , 3 IState, 3 FState, 1 Assign, 0 SComp, 0 CondS, 0 While, 3 Add, 0 IntVal, 5 IntVar, 0 Sub, 0 Mult, 0 EQ, 0 NEQ, 0 LEQ, 0 GEQ, 0 GTH
/*
    Trying to sinthesizing the max2 algorithim
    Here is a c language implementation
    OutLoc = x>y ? x : y;
*/

module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2 extends XLoc {}
one sig OutLoc extends ALoc {}

one sig IState1 extends IState {} { bind = {InLoc1->1}+{InLoc2->2}+{OutLoc->0}}
one sig FState1 extends FState {} { bind = {InLoc1->1}+{InLoc2->2}+{OutLoc->2}}
one sig IState2 extends IState {} { bind = {InLoc1->3}+{InLoc2->2}+{OutLoc->0}}
one sig FState2 extends FState {} { bind = {InLoc1->3}+{InLoc2->2}+{OutLoc->3}}
one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2 }

pred PreC[iSt: one IState] {

}

pred PosC[iSt: one IState, fSt: one FState] {

}

run Synt for 3 but -1..9 Int , 2 IState, 2 FState, 2 Assign, 0 SComp, 1 CondS, 0 While, 0 IntVal, 3 IntVar, 0 Add, 0 Sub, 0 Mult, 0 EQ, 0 NEQ, 0 LEQ, 1 GEQ, 0 GTH
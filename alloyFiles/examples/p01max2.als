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

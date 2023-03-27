/*
    Trying to sinthesizing the swap2 algorithim
    Here is a c language implementation
    read(x, y)
    t=x; x=y; y=t;
    write(x, y)
*/

module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2, InLoc3 extends DLoc {}

one sig IState1 extends IState {} { bind = {InLoc1->1}+{InLoc2->2}+{InLoc3->0}}
one sig FState1 extends FState {} { bind = {InLoc1->2}+{InLoc2->1}+{InLoc3->1}}
one sig IState2 extends IState {} { bind = {InLoc1->4}+{InLoc2->2}+{InLoc3->0}}
one sig FState2 extends FState {} { bind = {InLoc1->2}+{InLoc2->4}+{InLoc3->4}}

one sig Example1 extends Example {} { pairs = IState1->FState1+IState2->FState2 }

pred PreC[iSt: one IState] {

}

pred PosC[iSt: one IState, fSt: one FState] {

}

run Synt for 8 but -1..4 Int
, 0 CondS, 0 While, 0 IntVal, 0 Add, 0 Sub, 0 Mult
, 2 SComp, 3 IntVar, 3 Assign

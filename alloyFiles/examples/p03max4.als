/*
    Trying to sinthesizing the max4 (with no recursion) algorithim
    Here is a Java implementation:
        if(XLoc1 > XLoc2) {
            if(XLoc1 > XLoc3) {
                if(XLoc1 > XLoc4) {
                    Res = XLoc1;
                } else {
                    Res = XLoc4;
                }    
            } else {
                if(XLoc3 > XLoc4) {
                    Res = XLoc3;
                } else {
                    Res = XLoc4;
                }
            }
        } else {
            if(XLoc2 > XLoc3) {
                if(XLoc2 > XLoc4) {
                    Res = XLoc2;
                } else {
                    Res = XLoc4;
                }    
            } else {
                if(XLoc3 > XLoc4) {
                    Res = XLoc3;
                } else {
                    Res = XLoc4;
                }
            }
        }
*/
module progFinder

open ../imp[PreC, PosC]

--------------------------------------------------------------------------------
-- Specification predicate
--------------------------------------------------------------------------------

one sig InLoc1, InLoc2, InLoc3, InLoc4 extends XLoc {}
one sig OutLoc extends ALoc {}
one sig CondS1, CondS2, CondS3, CondS4, CondS5, CondS6 extends CondS {}
one sig Assign1, Assign2, Assign3, Assign4 extends Assign {}
one sig GTH1, GTH2, GTH3, GTH4, GTH5, GTH6 extends GTH {}
one sig IState1 extends IState {} { bind={InLoc1->3}+{InLoc2->6}+{InLoc3->1}+{InLoc4->2}+{OutLoc->0}}
one sig FState1 extends FState {} { bind={InLoc1->3}+{InLoc2->6}+{InLoc3->1}+{InLoc4->2}+{OutLoc->6}}
one sig IState2 extends IState {} { bind={InLoc1->3}+{InLoc2->1}+{InLoc3->5}+{InLoc4->2}+{OutLoc->0}}
one sig FState2 extends FState {} { bind={InLoc1->3}+{InLoc2->1}+{InLoc3->5}+{InLoc4->2}+{OutLoc->5}}
one sig IState3 extends IState {} { bind={InLoc1->3}+{InLoc2->2}+{InLoc3->1}+{InLoc4->4}+{OutLoc->0}}
one sig FState3 extends FState {} { bind={InLoc1->3}+{InLoc2->2}+{InLoc3->1}+{InLoc4->4}+{OutLoc->4}}
one sig IState4 extends IState {} { bind={InLoc1->5}+{InLoc2->1}+{InLoc3->3}+{InLoc4->2}+{OutLoc->0}}
one sig FState4 extends FState {} { bind={InLoc1->5}+{InLoc2->1}+{InLoc3->3}+{InLoc4->2}+{OutLoc->5}}


one sig Example1 extends Example {} { pairs=IState1->FState1+IState2->FState2+IState3->FState3+IState4->FState4}

pred PreC[iSt: one IState] {

  //Relational expressions such as (x > y), (x > z), (x > w), etc.
  GTH1.lhs.name = InLoc1
  GTH1.rhs.name = InLoc2

  GTH2.lhs.name = InLoc1
  GTH2.rhs.name = InLoc3

  GTH3.lhs.name = InLoc1
  GTH3.rhs.name = InLoc4

  GTH4.lhs.name = InLoc2
  GTH4.rhs.name = InLoc3

  GTH5.lhs.name = InLoc2
  GTH5.rhs.name = InLoc4

  GTH6.lhs.name = InLoc3
  GTH6.rhs.name = InLoc4

  //Assigns such as (?? = x), (?? = y), (?? = z) and (??=w).
  Assign1.rhs.name = InLoc1
  Assign3.rhs.name = InLoc3
  Assign4.rhs.name = InLoc4
  Assign2.rhs.name = InLoc2

}

pred PosC[iSt: one IState, fSt: one FState] {

}

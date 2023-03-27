// A Program Synthesizer Alloy* Prototype for the Glynn Winskel's IMP language
module imp<PreC, PosC>

open util/integer as i
// Syntax
open impMs/syntax
// Well-formedness rules
open impMs/wellF
// Semantics
open impMs/semantics

--------------------------------------------------------------------------------
-- Synthesis predicate
--------------------------------------------------------------------------------

pred Synt[p: Prog] {
  all iSt: IState, evalC: Cmd -> (State -> lone State), evalB: BExp -> State -> Bit,
           evalA: AExp -> State -> Int when {
        PreC[iSt]
        Semantics[evalC, evalB, evalA]
      }{
        PosC[iSt, Example.pairs[iSt]]
      }
}

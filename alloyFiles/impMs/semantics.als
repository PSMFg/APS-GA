open syntax
open wellF

//pred PreMax2[iSt: one State] { }
/*
pred PostMax2[c: Max2, iSt: one State, fSt: one State] {
    fSt.bind[c.res] = max[iSt.bind[c.arg1] + iSt.bind[c.arg2]]
    fSt.bind[c.arg1] = iSt.bind[c.arg1]
    fSt.bind[c.arg2] = iSt.bind[c.arg2]
    fSt.bind[c.res] >= iSt.bind[c.arg1] and fSt.bind[c.res] >= iSt.bind[c.arg2] and
    (fSt.bind[c.res] = iSt.bind[c.arg1] or fSt.bind[c.res] = iSt.bind[c.arg2])
}*/

pred Semantics[evalC: Cmd -> (State -> State),
                      evalB: BExp -> (State -> Bit), evalA: AExp -> (State -> Int)] {
// Examples must belong to evaluations
  Example.pairs in evalC[Prog.body]
//  all s: State | (some p: Prog | s in evalP[p].univ or s in univ.(evalP[p])) or (some c: Cmd | s in evalC[c].univ or s in univ.(evalC[c]))
  all c: Cmd | evalC[c].univ in State and univ.(evalC[c]) in State
//  all c: Cmd, s: State | lone evalC[c][s]
  all sc: StChg | sc.curr in State and sc.next in State
  all a: AExp, s: State  | one evalA[a][s] and evalA[a][s] in Int
  all b: BExp, s: State | one evalB[b][s] and evalB[b][s] in Bit
// Evaluating boolean expressions
  all b: GEQ, s: State |  evalA[b.lhs][s] >= evalA[b.rhs][s] implies evalB[b][s] = BitTrue else evalB[b][s] = BitFalse
  all b: EQ, s: State |  evalA[b.lhs][s] = evalA[b.rhs][s] implies evalB[b][s] = BitTrue else evalB[b][s] = BitFalse
  all b: NEQ, s: State |  evalA[b.lhs][s] != evalA[b.rhs][s] implies evalB[b][s] = BitTrue else evalB[b][s] = BitFalse
  all b: LEQ, s: State |  evalA[b.lhs][s] <= evalA[b.rhs][s] implies evalB[b][s] = BitTrue else evalB[b][s] = BitFalse
  all b: GTH, s: State |  evalA[b.lhs][s] > evalA[b.rhs][s] implies evalB[b][s] = BitTrue else evalB[b][s] = BitFalse
// Evaluating arithmetic expressions
  all a: Add | some c: Assign | (a in c.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))) and (all s: evalC[c].univ | evalA[a][s] = bvadd[evalA[a.op1][s], evalA[a.op2][s]])
  all a: Sub | some c: Assign | (a in c.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))) and (all s: evalC[c].univ | evalA[a][s] = bvsub[evalA[a.op1][s], evalA[a.op2][s]])
  all a: Mult | (some c: Assign | (a in c.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))) and (all s: evalC[c].univ | evalA[a][s] = bvmul[evalA[a.op1][s], evalA[a.op2][s]])) or
     some b: BExp | (a in b.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))) and (all s: evalB[b].univ | evalA[a][s] = bvmul[evalA[a.op1][s], evalA[a.op2][s]])
  all a: IntVar, s: State | evalA[a][s] = s.bind[a.name]
  all a: IntVal, s: State | evalA[a][s] = (IntVal <: a).val
// Evaluating programs and commands
//  all c: Max2, iSt: evalC[c].univ | /*PreMax2[iSt] =>*/ //PostMax2[c, iSt, evalC[c][iSt]]
//	evalC[c][iSt].bind = iSt.bind ++ { c.res -> max[iSt.bind[c.arg1] + iSt.bind[c.arg2]] }

  evalC[Skip] in iden

  all c: Assign, iSt: evalC[c].univ | evalC[c][iSt].bind = iSt.bind ++ { c.lhs.name -> evalA[c.rhs, iSt] }

  all c: SComp | evalC[c] = (evalC[c.cur]) . (evalC[c.next])

  all c: CondS, iSt: evalC[c].univ | //evalC[c].univ = evalC[c.then].univ and evalC[c].univ = evalC[c.elsen].univ and
          (evalB[c.cond][iSt] = BitTrue => evalC[c.then][iSt] = evalC[c][iSt] else evalC[c.elsen][iSt] = evalC[c][iSt])

  all c: While, iSt: evalC[c].univ | 
          /*evalB[c.inv][iSt] = BitTrue and evalB[c.inv][evalC[c][iSt]] = BitTrue and*/
          (((evalB[c.cond][iSt] = BitFalse =>
                    evalC[c][iSt] = iSt //and (no st: c.unfold | iSt = st.exp.first.curr)
           else
                    /*evalB[c.inv][iSt] = BitTrue and*/
                    (one st: c.unfold | st.exp.first.curr = iSt and evalC[c][iSt] = st.exp.last.next and
                        (all ic: st.exp.elems | evalC[c.wbody][ic.curr] = ic.next and /*evalB[c.inv][ic.curr] = BitTrue and
                                                    evalB[c.inv][ic.next] = BitTrue and*/ evalB[c.cond][ic.curr] = BitTrue and
                                                    (ic = st.exp.last => evalB[c.cond][ic.next] = BitFalse else evalB[c.cond][ic.next] = BitTrue)))))
                    and (all st: c.unfold.exp.first.curr | evalB[c.cond][st] = BitTrue))
}

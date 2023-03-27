open syntax

fact {
  some IntVar => (all v: Loc, s: State | v in s.bind.univ) and (all v: Loc | v in IntVar.name)
  all disj s1, s2: State | /*s1 != s2 <=>*/ s1.bind != s2.bind
  all c: Cmd | c in (Prog.body) or c in (Prog.body).*(cur + next + then + elsen + wbody)
  all c: GEQ | (some cs: CondS | c = cs.cond) or (some wc: While | c = wc.cond)
  all c: LEQ | (some cs: CondS | c = cs.cond) or (some wc: While | c = wc.cond)
  all c: EQ | (some cs: CondS | c = cs.cond) or (some wc: While | c = wc.cond /*or c = wc.inv*/)
  all c: NEQ | (some cs: CondS | c = cs.cond) or (some wc: While | c = wc.cond)
  all c: GTH | (some cs: CondS | c = cs.cond) or (some wc: While | c = wc.cond)

  all i: IntVal | (some a: Add | i = (IntVal <: a.op1) or i = (IntVal <: a.op2)) or
                    (some a: Sub | i = (IntVal <: a.op1) or i = (IntVal <: a.op2)) or
                    (some a: Mult | i = (IntVal <: a.op1) or i = (IntVal <: a.op2))
/*  all i: IntVar | (some c: Assign | i = c.lhs or i in c.rhs.(*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2)))) or
          (some b: BExp | b.lhs = i or b.rhs = i)*/
  all o: Add | some c: Assign | o in c.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))
  all o: Sub | some c: Assign | o in c.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))
  all o: Mult | (some c: Assign | o in c.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))) or
          some b: BExp | o in b.rhs.*((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))
  all c: CondS | some b: BExp | c.cond = b
  all c: While | some b: BExp | (c.cond = b /*or c.inv = b*/)
  all c: SComp | some c_: Cmd - c | c.cur = c_ or c.next = c_

  all s: StChg | some e: Expansion | s in e.exp.elems
  all e: Expansion | some w: While | e in w.unfold
  all e: Expansion | some sc: StChg | sc in e.exp.elems
  no c: Cmd | c in c.^(cur + next + then + elsen + wbody)
  no a: AExp | a in a.^((Add <: op1) + (Add <: op2) + (Sub <: op1) + (Sub <: op2) + (Mult <: op1) + (Mult <: op2))
}

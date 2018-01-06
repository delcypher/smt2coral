; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(DEQ(DVAR(ID_0),DCONST(Infinity)),DEQ(DVAR(ID_0),DCONST(-Infinity)))
(declare-const a Float64)
(assert (fp.isInfinite a))

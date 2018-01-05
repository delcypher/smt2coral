; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: DEQ(DCONST(Infinity),DVAR(ID_0))
(declare-const a Float64)
(assert (fp.eq (_ +oo  11 53) a))

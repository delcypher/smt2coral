; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: DEQ(MUL(DVAR(ID_0),DVAR(ID_1)),DVAR(ID_0))
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.eq (fp.mul RNE a b) a))

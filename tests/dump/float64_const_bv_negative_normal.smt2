; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: DEQ(DCONST(-0x1.0000000000001p-1022),DVAR(ID_0))
(declare-const a Float64)
(assert (fp.eq (fp #b1 #b00000000001 #x0000000000001) a))

; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FEQ(FCONST(0x1.000001p-126),FVAR(ID_0))
(declare-const a Float32)
(assert (fp.eq (fp #b0 #b00000001 #b00000000000000000000001) a))

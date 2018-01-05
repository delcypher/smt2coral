; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FEQ(FCONST(-0.0),FVAR(ID_0))
(declare-const a Float32)
(assert (fp.eq (fp #b1 #b00000000 #b00000000000000000000000) a))

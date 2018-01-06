; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FEQ(FVAR(ID_0),FCONST(0.0))
(declare-const a Float32)
(assert (fp.isZero a))

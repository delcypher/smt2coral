; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FEQ(MUL(FVAR(ID_0),FVAR(ID_1)),FVAR(ID_0))
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq (fp.mul RNE a b) a))

; RUN: %smt2coral-dump %s | %FileCheck %s
; CHECK: FEQ(FVAR(ID_0),FVAR(ID_1))
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq a b))

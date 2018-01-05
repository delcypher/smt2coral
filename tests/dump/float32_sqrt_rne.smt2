; RUN: %smt2coral-dump %s | %FileCheck %s
; CHECK: FEQ(FVAR(ID_0),SQRT_(FVAR(ID_1)))
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq a (fp.sqrt RNE b)))

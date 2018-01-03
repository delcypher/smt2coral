; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FLE(FVAR(ID_0),FVAR(ID_1))
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.leq a b))

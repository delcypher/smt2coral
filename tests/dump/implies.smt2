; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(BNOT(FEQ(FVAR(ID_0),FVAR(ID_1))),FEQ(FVAR(ID_1),FVAR(ID_0)))
(declare-const a Float32)
(declare-const b Float32)
(assert (=> (fp.eq a b) (fp.eq b a)))

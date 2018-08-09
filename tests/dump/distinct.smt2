; RUN: %smt2coral-dump %s | %FileCheck %s
(declare-const a Float32)
(declare-const b Float32)
(assert (distinct a b))
(check-sat)
; CHECK: BNOT(BOR(BAND(FNE(FVAR(ID_0),FVAR(ID_0)),FNE(FVAR(ID_1),FVAR(ID_1))),FEQ(FVAR(ID_0),FVAR(ID_1))))

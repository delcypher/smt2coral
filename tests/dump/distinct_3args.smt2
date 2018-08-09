; RUN: %smt2coral-dump %s | %FileCheck %s
(declare-const a Float32)
(declare-const b Float32)
(declare-const c Float32)
(assert (distinct a b c))
(check-sat)
; CHECK: BAND(BAND(BAND(BCONST(TRUE),BNOT(BOR(BAND(FNE(FVAR(ID_0),FVAR(ID_0)),FNE(FVAR(ID_1),FVAR(ID_1))),FEQ(FVAR(ID_0),FVAR(ID_1))))),BNOT(BOR(BAND(FNE(FVAR(ID_2),FVAR(ID_2)),FNE(FVAR(ID_1),FVAR(ID_1))),FEQ(FVAR(ID_2),FVAR(ID_1))))),BNOT(BOR(BAND(FNE(FVAR(ID_2),FVAR(ID_2)),FNE(FVAR(ID_0),FVAR(ID_0))),FEQ(FVAR(ID_2),FVAR(ID_0)))))


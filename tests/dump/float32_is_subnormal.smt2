; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(BAND(FLT(FVAR(ID_0),FCONST(0x1.000000p-126)),FGT(FVAR(ID_0),FCONST(0.0))),BAND(FGT(FVAR(ID_0),FCONST(-0x1.000000p-126)),FLT(FVAR(ID_0),FCONST(-0.0))))
(declare-const a Float32)
(assert (fp.isSubnormal a))

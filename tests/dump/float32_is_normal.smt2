; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(BAND(FGE(FVAR(ID_0),FCONST(0x1.000000p-126)),FLT(FVAR(ID_0),FCONST(Infinity))),BAND(FLE(FVAR(ID_0),FCONST(-0x1.000000p-126)),FGT(FVAR(ID_0),FCONST(-Infinity))))
(declare-const a Float32)
(assert (fp.isNormal a))

; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(BAND(DGE(DVAR(ID_0),DCONST(0x1.0000000000000p-1022)),DLT(DVAR(ID_0),DCONST(Infinity))),BAND(DLE(DVAR(ID_0),DCONST(-0x1.0000000000000p-1022)),DGT(DVAR(ID_0),DCONST(-Infinity))))
(declare-const a Float64)
(assert (fp.isNormal a))

; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(FEQ(FVAR(ID_0),FCONST(Infinity)),FEQ(FVAR(ID_0),FCONST(-Infinity)))
(declare-const a Float32)
(assert (fp.isInfinite a))

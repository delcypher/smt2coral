; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FEQ(FCONST(NaN),FVAR(ID_0))
(declare-const a Float32)
(assert (fp.eq (_ NaN  8 24) a))

; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FNE(FVAR(ID_0),FVAR(ID_0))
(declare-const a Float32)
(assert (fp.isNaN a))

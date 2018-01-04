; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: DNE(DVAR(ID_0),DVAR(ID_0))
(declare-const a Float64)
(assert (fp.isNaN a))

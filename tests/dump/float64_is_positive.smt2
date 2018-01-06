; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; FIXME: Not sound
; CHECK: DGT(DVAR(ID_0),DCONST(0.0))
(declare-const a Float64)
(assert (fp.isPositive a))

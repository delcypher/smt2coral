; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: DGE(DVAR(ID_0),DVAR(ID_1))
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.geq a b))

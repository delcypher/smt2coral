; RUN: %smt2coral-dump %s | %FileCheck %s
; CHECK: DEQ(DVAR(ID_0),SUB(DCONST(0.0),DVAR(ID_1)))
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.eq a (fp.neg b)))

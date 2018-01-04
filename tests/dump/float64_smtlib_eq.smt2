; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: BOR(BAND(DNE(DVAR(ID_0),DVAR(ID_0)),DNE(DVAR(ID_1),DVAR(ID_1))),DEQ(DVAR(ID_0),DVAR(ID_1)))
(declare-const a Float64)
(declare-const b Float64)
(assert (= a b))


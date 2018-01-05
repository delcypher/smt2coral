; RUN: %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: FEQ(MOD(FVAR(ID_0),FVAR(ID_1)),FVAR(ID_0))
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq (fp.rem a b) a))

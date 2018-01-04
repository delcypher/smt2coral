; RUN: %smt2coral-dump  %s | %FileCheck %s
; CHECK: BNOT(BXOR(BCONST(TRUE),BCONST(FALSE)))
(assert (= true false))

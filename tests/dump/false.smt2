; RUN: %smt2coral-dump %s | %FileCheck %s
; CHECK: BCONST(FALSE)
(assert false)

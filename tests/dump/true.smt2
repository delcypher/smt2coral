; RUN: %smt2coral-dump  %s | %FileCheck %s
; CHECK: BCONST(TRUE)
(assert true)

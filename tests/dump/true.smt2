; RUN: %smt2coral-dump --query-file %s | %FileCheck %s
; CHECK: BCONST(TRUE)
(assert true)

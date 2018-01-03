; RUN: %smt2coral-dump --query-file %s | %FileCheck %s
; CHECK: BCONST(FALSE)
(assert false)

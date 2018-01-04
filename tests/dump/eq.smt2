; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: Unsupported operation =
(declare-const a Float32)
(declare-const b Float32)
(assert (= a b))

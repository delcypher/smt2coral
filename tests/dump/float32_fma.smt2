; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedOperation: fp.fma
(declare-const a Float32)
(declare-const b Float32)
(declare-const c Float32)
(assert (fp.eq a (fp.fma RNE a b c)))

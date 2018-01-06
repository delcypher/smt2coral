; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedOperation: Converting FPSort(8, 24) to FPSort(11, 53)
(declare-const a Float32)
(declare-const b Float64)
(assert (fp.eq ((_ to_fp 11 53) RNE a) b))

; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedOperation: Converting FPSort(11, 53) to FPSort(8, 24)
(declare-const a Float32)
(declare-const b Float64)
(assert (fp.eq ((_ to_fp 8 24) RNE b) a))

; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedSort: FPSort(15, 113)
(declare-const a Float128)
(declare-const b Float128)
(assert (fp.eq a b))

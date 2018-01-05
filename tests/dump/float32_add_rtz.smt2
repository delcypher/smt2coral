; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedRoundingMode: roundTowardZero
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq (fp.add RTZ a b) a))

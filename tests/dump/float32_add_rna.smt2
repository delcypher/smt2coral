; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedRoundingMode: roundNearestTiesToAway
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq (fp.add RNA a b) a))

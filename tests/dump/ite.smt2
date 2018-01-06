; RUN: %not %smt2coral-dump %s 2>&1 | %FileCheck %s
; CHECK: CoralPrinterUnsupportedOperation: ite
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq (ite (fp.gt a b) a b) a))

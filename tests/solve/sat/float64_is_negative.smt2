; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(assert (fp.isNegative a))
(check-sat)

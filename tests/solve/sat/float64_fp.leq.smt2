; RUN: %coral %s | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.leq a b))
(check-sat)

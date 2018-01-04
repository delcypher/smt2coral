; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.gt a b))
(check-sat)

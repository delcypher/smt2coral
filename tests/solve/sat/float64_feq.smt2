; RUN: %coral %s | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.eq a b))

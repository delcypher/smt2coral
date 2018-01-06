; FIXME: Coral crashes on this using random, AVL, and PSO
; XFAIL: *
; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(assert (fp.isInfinite a))
(check-sat)

; FIXME: Coral crashes on this
; XFAIL: *
; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float32)
(assert (fp.isSubnormal a))
(check-sat)

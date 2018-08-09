; FIXME: Coral crashes and I can't figure out how to avoid this.
; XFAIL: *
; RUN: %coral %s | %FileCheck %s
(declare-const a Float32)
(declare-const b Float32)
(assert (distinct a b))
(check-sat)
; CHECK: {{^sat}}

; FIXME: Coral can't solve this
; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^unknown}}
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.eq (fp.div RNE a b) a))
(check-sat)

; RUN: %coral %s | %FileCheck %s
; CHECK: {{^unknown}}
(assert false)
(check-sat)

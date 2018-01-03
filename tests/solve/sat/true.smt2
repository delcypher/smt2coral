; RUN: %coral %s | %FileCheck %s
; CHECK: {{^sat}}
(assert true)
(check-sat)

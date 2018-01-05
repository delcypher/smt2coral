; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(assert (fp.isNaN (_ NaN 8 24)))
(check-sat)

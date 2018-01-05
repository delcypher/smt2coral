; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(assert (fp.isNaN (_ NaN 11 53)))
(check-sat)

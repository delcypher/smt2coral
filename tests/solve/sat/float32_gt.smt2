; HACK --pcCanonicalization=false is required to prevent coral from crashing
; RUN: %coral --pcCanonicalization=false %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.gt a b))
(check-sat)

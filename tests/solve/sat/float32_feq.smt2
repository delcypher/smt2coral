; HACK --pcCanonicalization=false is required to prevent coral from crashing
; RUN: %coral --pcCanonicalization=false %s | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq a b))

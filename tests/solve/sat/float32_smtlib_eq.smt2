; HACK: Default PSO solver crashes, use random instead
; HACK --pcCanonicalization=false is required to prevent coral from crashing
; RUN: %coral --solver=RANDOM --pcCanonicalization=false %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float32)
(declare-const b Float32)
(assert (= a b))
(check-sat)

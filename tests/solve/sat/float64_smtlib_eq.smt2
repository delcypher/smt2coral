; HACK: Default PSO solver crashes, use random instead
; RUN: %coral --solver=RANDOM %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(declare-const b Float64)
(assert (= a b))
(check-sat)

; HACK: Need --removeSimpleEqualities=false to prevent coral for crashing
; RUN: %coral --removeSimpleEqualities=false %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float64)
(declare-const b Float64)
(assert (fp.eq (fp.rem a b) a))
(check-sat)

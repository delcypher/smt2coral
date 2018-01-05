; FIXME: Coral can't solve this
; HACK --pcCanonicalization=false is required to prevent coral from crashing
; RUN: %coral --pcCanonicalization=false %s 2>&1 | %FileCheck %s
; CHECK: {{^unknown}}
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq (fp.div RNE a b) a))
(check-sat)

; FIXME: Bug in coral causes it to crash
; XFAIL: *
; HACK --pcCanonicalization=false is required to prevent canonicalizer from crashing
; RUN: %coral --pcCanonicalization=false %s | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.eq a (fp.sqrt RNE b)))
(check-sat)

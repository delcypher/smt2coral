; XFAIL: *
; FIXME: coral crashes on this
; RUN: %coral %s 2>&1 | %FileCheck %s
; CHECK: {{^sat}}
(declare-const a Float32)
(declare-const b Float32)
(assert (=> (fp.eq a b) (fp.eq b a)))

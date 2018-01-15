; FIXME: This test is a hack that depends on internal implementation details.
; NOTE: Have to strip the query because in debug mode this file gets dumped verbatim
; which would cause the FileCheck stderr check to always match.
; RUN: sed -e '/^;/d' %s > %t.stripped_query.smt2

; RUN: %coral -ldebug --seed=99 --seed-iter=4 %t.stripped_query.smt2 > %t.stdout 2> %t.stderr
; RUN sed %s '/^CHECK/d'
; RUN: %FileCheck -check-prefix=CHECK-STDOUT %s < %t.stdout
; RUN: %FileCheck -check-prefix=CHECK-STDERR %s < %t.stderr
; CHECK-STDOUT: {{^unknown}}
; CHECK-STDERR: '--seed=99'
; CHECK-STDERR: '--seed=100'
; CHECK-STDERR: '--seed=101'
; CHECK-STDERR: '--seed=102'
; CHECK-STDERR-NOT: '--seed={{.*}}'
(assert false)
(check-sat)

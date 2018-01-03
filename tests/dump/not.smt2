; RUN: %smt2coral-dump %s | %FileCheck %s
; FIXME: Coral crashes on boolean variables, so there isn't a test for this right now
; CHECK: BNOT(BVAR(ID_0))
(declare-const a Bool)
(assert (not a))

; RUN: %smt2coral-dump %s | %FileCheck %s
; FIXME: Coral crashes on boolean variables, so there isn't a test for this right now
; CHECK: BOR(BVAR(ID_0),BVAR(ID_1))
(declare-const a Bool)
(declare-const b Bool)
(assert (or a b))

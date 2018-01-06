; RUN: %smt2coral-dump %s | %FileCheck %s
; FIXME: Coral crashes on boolean variables, so there isn't a test for this right now
; CHECK: BOR(BCONST(TRUE),BAND(BVAR(ID_0),BAND(BVAR(ID_1),BVAR(ID_2))))
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (or true (and a b c)))

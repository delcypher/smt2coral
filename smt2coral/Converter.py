# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import io
import logging
import z3
from . import Util

_logger = logging.getLogger(__name__)

class CoralPrinterException(Exception):
    def __init__(self, msg):
        self.msg = msg

class CoralPrinter(Util.Z3ExprDispatcher):
    def __init__(self):
        super().__init__()
        self.sio = io.StringIO('')

    def print_constraints(self, constraints):
        assert isinstance(constraints, list)
        sio = io.StringIO('')
        for index, constraint in enumerate(constraints):
            self.print_constraint(constraint)
            if index < (len(constraints) -1):
                self.sio.write(';')
        final_str = self.sio.getvalue()
        return final_str

    def reset(self):
        self.sio.close()
        self.sio = io.StringIO('')

    def print_constraint(self, constraint):
        self.visit(constraint)

    # Visitors
    def visit_true(self, e):
        self.sio.write('BCONST(TRUE)')

    def visit_false(self, e):
        self.sio.write('BCONST(FALSE)')


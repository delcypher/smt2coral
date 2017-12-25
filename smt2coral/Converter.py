# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import io
import logging
import z3

_logger = logging.getLogger(__name__)

class CoralPrinterException(Exception):
    def __init__(self, msg):
        self.msg = msg

class CoralPrinter:
    def __init__(self):
        self.sio = io.StringIO('')
    
    def print_constraints(self, constraints):
        assert isinstance(constraints, list)
        sio = io.StringIO('')
        for constraint in constraints:
            self.print_constraint(constraint)
            self.sio.write(';')
        final_str = self.sio.getvalue()
        return final_str

    def reset(self):
        self.sio.close()
        self.sio = io.StringIO('')

    def print_constraint(self, constraint):
        # TODO
        self.sio.write('')


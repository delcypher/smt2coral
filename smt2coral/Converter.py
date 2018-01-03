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
        self.symbol_table = dict()

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
        self.symbol_table = dict()

    def print_constraint(self, constraint):
        self.visit(constraint)

    # Visitors
    def visit_true(self, e):
        self.sio.write('BCONST(TRUE)')

    def visit_false(self, e):
        self.sio.write('BCONST(FALSE)')

    def _is_supported_fp_sort(self, sort):
        # TODO
        return False

    def _is_supported_bv_sort(self, sort):
        # TODO
        return False

    def escape_variable_name(self, name):
        sym = None
        try:
            sym = self.symbol_table[name]
        except KeyError:
            sym = 'ID_{}'.format(len(self.symbol_table))
            self.symbol_table[name] = sym
        assert sym is not None
        return sym

    def visit_variable(self, e):
        sort = e.sort()
        if sort.kind() == z3.Z3_BOOL_SORT:
            decl = e.decl()
            name = decl.name()
            escaped_name = self.escape_variable_name(name)
            # FIXME: This doesn't really work. Coral doesn't document
            # this in its grammar but its parser does accept it. However
            # the rest of Coral's code seems to crash on this.
            _logger.warning('Emitting BVAR, coral will likely crash on this')
            self.sio.write('BVAR({})'.format(escaped_name))
        elif sort.kind() == z3.Z3_BV_SORT:
            if not self._is_supported_bv_sort(sort):
                raise CoralPrinterException(
                    'BitVector sort {} not supported'.format(sort))
            raise NotImplementedError('BitVector variable')
        elif sort.kind() == z3.Z3_FLOATING_POINT_SORT:
            if not self._is_supported_fp_sort(sort):
                raise CoralPrinterException(
                    'Floating point sort {} not supported'.format(sort))
            raise NotImplementedError('Float Variable')
        else:
            raise CoralPrinterException('Unsupported sort: {}'.format(sort))

    def _visit_binary_op(self, e, name):
        assert e.num_args() == 2
        self.sio.write(name + '(')
        self.visit(e.arg(0))
        self.sio.write(',')
        self.visit(e.arg(1))
        self.sio.write(')')

    def visit_and(self, e):
        self._visit_binary_op(e, 'BAND')

    def visit_or(self, e):
        self._visit_binary_op(e, 'BOR')

    def visit_xor(self, e):
        self._visit_binary_op(e, 'BXOR')

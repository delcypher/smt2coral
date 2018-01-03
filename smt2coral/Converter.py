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

    def _expr_is_supported_fp_sort(self, e):
        return self._is_supported_fp_sort(e.sort())

    def _is_supported_fp_sort(self, sort):
        if sort.kind() != z3.Z3_FLOATING_POINT_SORT:
            return False
        return self._is_float32_sort(sort) or self._is_float64_sort(sort)

    def _is_float32_sort(self, sort):
        assert sort.kind() == z3.Z3_FLOATING_POINT_SORT
        return sort.ebits() == 8 and sort.sbits() == 24

    def _is_float64_sort(self, sort):
        assert sort.kind() == z3.Z3_FLOATING_POINT_SORT
        return sort.ebits() == 11 and sort.sbits() == 53

    def _is_supported_bv_sort(self, sort):
        if sort.kind() != z3.Z3_BV_SORT:
            return False
        # TODO
        return False

    def _expr_is_supported_bv_sort(self, e):
        return self._is_supported_bv_sort(e.sort())

    def _check_fp_sort(self, e):
        if not self._expr_is_supported_fp_sort(e):
            raise CoralPrinterException(
            'Unsupported floating point sort: {}'.format(e.sort()))

    def _check_bv_sort(self, e):
        if not self._expr_is_supported_bv_sort(e):
            raise CoralPrinterException(
            'Unsupported bitvector sort: {}'.format(e.sort()))

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
        decl = e.decl()
        name = decl.name()
        escaped_name = self.escape_variable_name(name)
        if sort.kind() == z3.Z3_BOOL_SORT:
            # FIXME: This doesn't really work. Coral doesn't document
            # this in its grammar but its parser does accept it. However
            # the rest of Coral's code seems to crash on this.
            _logger.warning('Emitting BVAR, coral will likely crash on this')
            self.sio.write('BVAR({})'.format(escaped_name))
        elif sort.kind() == z3.Z3_BV_SORT:
            self._check_bv_sort(e)
            raise NotImplementedError('BitVector variable')
        elif sort.kind() == z3.Z3_FLOATING_POINT_SORT:
            self._check_fp_sort(e)
            if self._is_float32_sort(sort):
                self.sio.write('FVAR({})'.format(escaped_name))
            elif self._is_float64_sort(sort):
                self.sio.write('DVAR({})'.format(escaped_name))
            else:
                raise CoralPrinterException('Unsupported sort')
        else:
            raise CoralPrinterException('Unsupported sort: {}'.format(sort))

    def _visit_binary_op(self, e, name):
        assert e.num_args() == 2
        self.sio.write(name + '(')
        self.visit(e.arg(0))
        self.sio.write(',')
        self.visit(e.arg(1))
        self.sio.write(')')

    def _visit_unary_op(self, e, name):
        assert e.num_args() == 1
        self.sio.write(name + '(')
        self.visit(e.arg(0))
        self.sio.write(')')

    def visit_and(self, e):
        self._visit_binary_op(e, 'BAND')

    def visit_or(self, e):
        self._visit_binary_op(e, 'BOR')

    def visit_xor(self, e):
        self._visit_binary_op(e, 'BXOR')

    def visit_not(self, e):
        self._visit_unary_op(e, 'BNOT')

    def visit_float_eq(self, e):
        assert e.num_args() == 2
        self._check_fp_sort(e.arg(0))
        arg_sort = e.arg(0).sort()
        if self._is_float32_sort(arg_sort):
            self._visit_binary_op(e, 'FEQ')
        elif self._is_float64_sort(arg_sort):
            self._visit_binary_op(e, 'DEQ')
        else:
            raise CoralPrinterException('Unhandled float eq case')


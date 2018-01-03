# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import io
import logging
import z3
from collections import deque

_logger = logging.getLogger(__name__)

def parse(query_file):
    assert isinstance(query_file, io.TextIOWrapper)
    # Load query_file as string
    query_str = ""
    for l in query_file.readlines():
        query_str += str(l)
    _logger.debug('query:\n{}'.format(query_str))
    try:
        constraint = z3.parse_smt2_string(query_str)
    except z3.z3types.Z3Exception as e:
        msg = 'Parsing failed: {}'.format(e)
        return (None, msg)
    return (constraint, None)

def split_bool_and(constraint):
    """
        Recursively split boolean and into separate constraints
    """
    final_constraints = []
    work_list = deque([constraint])
    while len(work_list) > 0:
        item = work_list.popleft()
        if not z3.is_and(item):
            final_constraints.append(item)
            continue
        # Have and And node, append children to the work list
        # right to left so args get processed left to right.
        assert item.num_args() >= 2
        indices = list(range(0, item.num_args()))
        indices.reverse()
        for i in indices:
            work_list.appendleft(item.arg(i))

    return final_constraints

class Z3ExprDispatcherException(Exception):
    def __init__(self, msg):
        self.msg = msg

class Z3ExprDispatcher:
    def __init__(self, throw_except_on_no_override=True):
        self.throw_except_on_no_override = throw_except_on_no_override
        self._init_dispatcher()

    def _init_dispatcher(self):
        self._z3_app_dispatcher_map = dict()
        # Map function application id to handler function

        # Boolean constants
        self._z3_app_dispatcher_map[z3.Z3_OP_TRUE] = self.visit_true
        self._z3_app_dispatcher_map[z3.Z3_OP_FALSE] = self.visit_false
        self._z3_app_dispatcher_map[z3.Z3_OP_UNINTERPRETED] = self.visit_uninterpreted_function

        # Boolean operations
        self._z3_app_dispatcher_map[z3.Z3_OP_AND] = self.visit_and
        self._z3_app_dispatcher_map[z3.Z3_OP_OR] = self.visit_or
        self._z3_app_dispatcher_map[z3.Z3_OP_XOR] = self.visit_xor
        self._z3_app_dispatcher_map[z3.Z3_OP_NOT] = self.visit_not

        # Float relations
        self._z3_app_dispatcher_map[z3.Z3_OP_FPA_EQ] = self.visit_float_eq

    def default_handler(self, e):
        msg = "No handler implemented for Z3 expr {}".format(
            e.sexpr())
        if self.throw_except_on_no_override:
            raise NotImplementedError(msg)
        else:
            _logger.warning(msg)

    def visit(self, e):
        assert z3.is_ast(e)
        if not z3.is_app(e):
            raise Z3ExprDispatcherException('expr was not an application')

        # Call the appropriate function application handler
        app_kind = e.decl().kind()

        if app_kind == z3.Z3_OP_UNINTERPRETED and e.num_args() == 0:
            self.visit_variable(e)
            return

        try:
            handler = self._z3_app_dispatcher_map[app_kind]
            handler(e)
        except KeyError as e:
            msg ='Handler for {} is missing from dispatch dictionary'.format(app_kind)
            raise NotImplementedError(msg)

    # Visitors
    def visit_true(self, e):
        self.default_handler(e)

    def visit_false(self, e):
        self.default_handler(e)

    def visit_variable(self, e):
        self.default_handler(e)

    def visit_uninterpreted_function(self, e):
        self.default_handler(e)

    def visit_and(self, e):
        assert e.get_num_args() == 2
        self.default_handler(e)

    def visit_or(self, e):
        assert e.get_num_args() == 2
        self.default_handler(e)

    def visit_xor(self, e):
        assert e.get_num_args() == 2
        self.default_handler(e)

    def visit_not(self, e):
        assert e.get_num_args() == 1
        self.default_handler(e)

    def visit_float_eq(self, e):
        assert e.get_num_args() == 2
        self.default_handler(e)

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

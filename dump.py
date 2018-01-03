#!/usr/bin/env python
"""
  Read SMT-LIBv2 query file and dump constraints
  in Coral's native format.
"""
# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import argparse
import logging
import sys
import z3
from smt2coral import Converter
from smt2coral import DriverUtil
from smt2coral import Util

_logger = logging.getLogger(__name__)

def main(args):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query-file",
        dest='query_file',
        type=argparse.FileType('r'),
        default=sys.stdin,
    )
    parser.add_argument("--output",
        type=argparse.FileType('w'),
        default=sys.stdout,
    )

    DriverUtil.parserAddLoggerArg(parser)

    pargs = parser.parse_args(args)
    DriverUtil.handleLoggerArgs(pargs, parser)

    # Parse using Z3
    constraint, err = Util.parse(pargs.query_file)
    if err is not None:
        # Parser failure
        return 1
    constraints = Util.split_bool_and(constraint)

    # Do conversion and write
    printer = Converter.CoralPrinter()
    pargs.output.write(printer.print_constraints(constraints))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))


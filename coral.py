#!/usr/bin/env python
"""
  Read SMT-LIBv2 query file and dump constraints
  in Coral's native format.
"""
# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import argparse
import os
import pprint
import logging
import subprocess
import sys
import tempfile
import z3
from smt2coral import Converter
from smt2coral import DriverUtil
from smt2coral import Util

_logger = logging.getLogger(__name__)

def main(args):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query_file",
        nargs='?',
        type=argparse.FileType('r'),
        default=sys.stdin,
    )
    parser.add_argument("--output",
        type=argparse.FileType('w'),
        default=sys.stdout,
    )
    parser.add_argument("--dump-output",
        dest='dump_output',
        default=False,
        action='store_true',
    )
    DriverUtil.parserAddLoggerArg(parser)

    # Do partial argument passing so we can pass the rest to coral
    pargs, unhandled_args = parser.parse_known_args(args)
    DriverUtil.handleLoggerArgs(pargs, parser)

    try:
        # Parse using Z3
        constraint, err = Util.parse(pargs.query_file)
        if err is not None:
            # Parser failure
            _logger.error('Parser failure: {}'.format(err))
            return 1
        constraints = Util.split_bool_and(constraint)

        # Do conversion from SMT-LIBv2 to Coral syntax
        printer = Converter.CoralPrinter()
        constraints = printer.print_constraints(constraints)

        # Invoke coral
        coral_jar = os.path.join(os.path.dirname(__file__), 'coral.jar')
        if not os.path.exists(coral_jar):
            _logger.error('Cannot find "{}"'.format(coral_jar))
            return 1

        cmd_line = [
            'java',
            '-jar',
            coral_jar
        ]
        # Add unhandled arguments
        cmd_line.extend(unhandled_args)

        # Now add the constraint
        cmd_line.extend([
            '--inputCONS',
            constraints
        ])

        _logger.debug('Invoking: {}'.format(pprint.pformat(cmd_line)))

        # Write stdout to tempfile so we can parse its output
        with tempfile.TemporaryFile() as stdout:
            proc = subprocess.Popen(args=cmd_line, stdout=stdout)
            try:
                exit_code = proc.wait()
            except KeyboardInterrupt as e:
                proc.kill()
                raise e
            response = parse_coral_output(stdout, pargs.dump_output)
            if response is True:
                pargs.output.write('sat\n')
            elif response is False:
                pargs.output.write('unsat\n')
            else:
                pargs.output.write('unknown\n')
        return exit_code
    except KeyboardInterrupt:
        pargs.output.write('unknown\n')
        return 1

def parse_coral_output(stdout, dump_output):
    # Convert stdout to string
    # Move to beginning of stream
    stdout.seek(0)
    lines = []
    for l in stdout.readlines():
        line_as_str = l.decode()
        lines.append(line_as_str)
    if dump_output:
        _logger.info('Coral output:\n{}'.format(pprint.pformat(lines)))

    # Walk past parameter dump and get satisfiability response
    num_eq_encounter = 0
    line_to_parse = None
    for l in lines:
        if num_eq_encounter < 2:
            if l.startswith('==='):
                num_eq_encounter += 1
            continue
        assert num_eq_encounter == 2
        line_to_parse = l
        break

    assert line_to_parse is not None
    _logger.debug('Line to parse is \"{}\"'.format(line_to_parse))
    if line_to_parse.startswith('SOLVED'):
        # Satisfiable
        return True
    elif line_to_parse.startswith('NOT SOLVED'):
        # Unsat?
        # Not sure, for now just pretend like it's unknown
        return None
    else:
        # Unknown
        _logger.error('Unrecognised response from coral: \"{}\"'.format(line_to_parse))
        return None
    return None

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))


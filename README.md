# smt2coral

`smt2coral` is a small python module and set of command line tools that take
constraints in the [SMT-LIBv2 format](http://smtlib.cs.uiowa.edu/) and convert
them into the [constraint language](http://pan.cin.ufpe.br/coral/InputLanguage.html) understood by the
[Coral](http://pan.cin.ufpe.br/coral/index.html) constraint solver.

## Tools

## `dump.py`

This tool parses SMT-LIBv2 constraints and then dumps the converted constraints
as text. This is useful for debugging/testing.

## `coral.py`

This is a wrapper for Coral that parses constraints, invokes coral and responds
in a "mostly" SMT-LIBv2 compliant manner.

Note you need to place `coral.jar` in the same directory as `coral.py`. `coral.jar`
is available at http://pan.cin.ufpe.br/coral/Download.html .

Note that the `coral.py` script will ignore command line arguments it doesn't recognise
and will pass them directly to Coral.

# Dependencies

* Coral
* Java (to run coral)
* Z3 and python bindings

For testing

* lit
* FileCheck

## Testing

Run

```
lit -vs tests/
```

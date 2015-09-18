foreignfd: clpfd-like Prolog interface for external solvers.
============================================================

This library mimicks the API of the library(clpfd) to provide an
interface to external solvers.

At the time of writing, the library is written for SWI-Prolog and
the only solver that is supported is JaCoP.

The JaCoP interface is written in Java 1.8 and Maven is used for
downloading the JaCoP dependencies and building the JAR file.

`make` should build the JaCoP interface in `classes/jacop.jar` and
run some tests in SWI-Prolog.

In order to use the foreignfd library, jacop.jar must be in the
CLASSPATH.  You may run the swipl top-level like this:

    $ CLASSPATH="classes/jacop.jar${CLASSPATH:+:}$CLASSPATH" swipl
    ?- use_module(foreignfd).

The solver is initialized automatically the first time a variable is
declared, but it may take some time.  You may want to initialize
the solver before running some benchmarks by executing the goal
`solver(_).`.

At the time of writing, the following constraints are supported:
* arithmetic constraints.  Notes:
  - only non-negative constant powers are supported with `^`.
  - rem and mod are undifferentiated.
* reification.
* `all_different`, `all_distinct`, `sum`, `scalar_product`.

Labeling is performed by the solver.  Notes:
* `step` and `enum` are undifferentiated.

Reflection via `fd_var`, `fd_inf`, `fd_sup`, `fd_size` and `fd_dom` is
supported.
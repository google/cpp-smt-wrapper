# cpp-smt-wrapper
## C++ Wrappers for SMT Solvers

This library provides the ability to interact with one or more
[SMT Solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
implementations using C++.

It provides:

1) An abstraction that allows users to avoid relying directly on a specific
SMT Solver implementation, which allows programs to switch out underlying
solvers when performance or correctness needs are identified.

1) An opinionated C++ API, based on SMT-Lib, that attempts to comply with
[Google's C++ Style Guide](https://google.github.io/styleguide/cppguide.html).
In particular, this library ensures that regardless of the underlying SMT Solver
implementation's error handling, a program using this library can use
`absl::Status` [error handling](https://abseil.io/docs/cpp/guides/status).

3) An implementation of this wrapper interface for Z3 (Other solver wrappers --
e.g. CVC4/CVC5 -- are planned.)

# Building this library

This library uses [Bazel](https://bazel.build/) to both build and test.

You should be able to build the entire library and its dependencies via:
```
bazel build //...
```

This will automatically download and build all of this library's dependencies,
including Z3. The first time this is run, it may take several minutes.
However, subsequent builds should be very fast due to caching of intermediates.

You should be able to run all of the tests in the library via:
```
bazel test //...
```

# Using this library

The primary interface for interacting with an underlying SMT solver is in
`src/smt/smt.h`. You can aquire a Z3 backed concrete implementation via
the Z3 Solver Factory defined in `src/smt/z3_smt_solver_factory.h`.

The "Printing SMT Solver" interface you can create from
`src/smt/printing_smt_solver_factory.h` provides a way to get SMT-Lib-esque
output from your application, while also calling into an underlying solver
interactively.  This can be quite helpful for debugging, although we do not
guarantee this can be provided directly to another solver as text input
at the moment.

At the moment, we would recommend consuming this library via Bazel's http_archive
[method of consuming dependencies](https://bazel.build/external/overview#workspace-system).
We may update this guidance to support other build systems, or bzlmod in the
future -- if that's desired, please consider creating a GitHub issue.

## Avoid unit tests on specific outputs
A common problem when using SMT solvers is to write unit tests
asserting that the SMT solvers output a specific model or sequence of models.
This is a form of golden testing and is brittle. SMT solvers do
not guarantee the same output between versions, and this library does not either.

# Contributing

See CONTRIBUTING.md

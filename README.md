portgraph
=========

[![build_status][]](https://github.com/CQCL/portgraph/actions)
[![crates][]](https://crates.io/crates/portgraph)
[![msrv][]](https://github.com/CQCL/portgraph)
[![codecov][]](https://codecov.io/gh/CQCL/portgraph)
[![bencher][]](https://bencher.dev/perf/portgraph)

Data structure library for directed graphs with first-level ports. Includes
secondary data structures for node and port weights, and node hierarchies.

Please read the [API documentation here][].

## Features

-   `pyo3`: Enable Python bindings via pyo3.
-   `serde`: Enable serialization and deserialization via serde.
-   `petgraph`: Enable petgraph interoperability by implementing the
    `petgraph::visit` traits for `PortGraph` and `MultiPortGraph`.

## Recent Changes

See [CHANGELOG][] for a list of changes. The minimum supported rust
version will only change on major releases.

## Development

See [DEVELOPMENT.md](DEVELOPMENT.md) for instructions on setting up the development environment.

## License

This project is licensed under Apache License, Version 2.0 ([LICENSE][] or http://www.apache.org/licenses/LICENSE-2.0).

  [API documentation here]: https://docs.rs/portgraph/
  [build_status]: https://github.com/CQCL/portgraph/actions/workflows/ci.yml/badge.svg
  [crates]: https://img.shields.io/crates/v/portgraph
  [LICENSE]: LICENCE
  [msrv]: https://img.shields.io/badge/rust-1.75.0%2B-blue.svg?maxAge=3600
  [codecov]: https://img.shields.io/codecov/c/gh/CQCL/portgraph?logo=codecov
  [bencher]: https://img.shields.io/badge/bencher-.dev-blue.svg?logo=data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAMAAABEpIrGAAAAtFBMVEVHcEwEBAT+/v4AAADi4uKenp7u7/ABAQEAAAAAAAAAAAAwMDAAAAAAAAAAAACGh4e2tLJfX18AAAAAAAD///++wMEAAABoaGiRkZEAAABucXMAAAAAAAB1dXUxMTHMzMzh4eH/0rRJSUmsrKz29vb////+q3v8bQD9+PP/8+kZGhp9fn/8dAD/3cXk4OT/tIL9p2z8ZwD+vI+UlJTPmnn/5tT/xqH/2cD9k1D9kkL8ijj8fhszkVn/AAAAJXRSTlMA4fgz7ePq/o3zRv0hfcfb7dJoVubyDvvpqfjTt+Dl+tTz3uPjxce2cgAAAaJJREFUOI2lklmTqjAQhcMSOpFFQHB3nJl7O2wii46z/f//daOOJYkvU3XPA6Q4X53udEPIbxWv1+x2ZsF6ovsLd05n/PJ5wmd07jLVj7mDaFKwCPE4NREdrmbwEOu+MOerKQnmZtHXGBpDfwp28dV9YgKWxf/iZ/dV2OV0CLjO227X1cgnE451t9u9Oa43jChtCWQ9vsbxK/aZBOxS6cFI848sE7jx/Q2KLPvIU6UHwiJszsCYsfEZaDBS72nxJO/uQJcn3FIHEVBsuxvQtUgDbZIj1ym+BUZBEKH4Lhx3pM+aUzy1GBlGhO0JqaH7ZARy2Dc58BBAGDzfgWdguu+7gwAZoW/T4jYqsrUiK4qa1DanpQw4VObVM6uDjCiHy4pnJqYA1RWoAFI0Z/HwChW+HwEOV+AAcHzHiilA3TbH8FY/PDZtrQD+8kWIppBecXk0Qrws/QHglfZJ/oeIuRC5fNX9SW2SGBTPRo77/c9hrG7D4uml+l7qctNQ/x9GsEnuU0qWj9vyFvwp3NpS2z9PsPB0/1zGDziUJfCV/7js/9A/nA48HxVN/KwAAAAASUVORK5CYII=
  [CHANGELOG]: CHANGELOG.md
portgraph
=========

[![build_status][]](https://github.com/CQCL/portgraph/actions)
[![crates][]](https://crates.io/crates/portgraph)
[![msrv][]](https://github.com/CQCL/portgraph)
[![codecov][]](https://codecov.io/gh/CQCL/portgraph)
[![codspeed][]](https://codspeed.io/CQCL/portgraph)

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
  [codspeed]: https://img.shields.io/endpoint?url=https://codspeed.io/badge.json
  [CHANGELOG]: CHANGELOG.md
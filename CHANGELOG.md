# Changelog


## [0.15.2](https://github.com/CQCL/portgraph/compare/v0.15.1...v0.15.2) - 2025-08-05

### Bug Fixes

- Handle multiports in TopoSort ([#236](https://github.com/CQCL/portgraph/pull/236))

### New Features

- New ConvexChecker algorithm for Circuit-like graphs ([#240](https://github.com/CQCL/portgraph/pull/240))
- Add LineConvexChecker::nodes_in_interval ([#241](https://github.com/CQCL/portgraph/pull/241))
- Add LineConvexChecker::lines_at_port ([#242](https://github.com/CQCL/portgraph/pull/242))
# Changelog

## [0.15.1](https://github.com/CQCL/portgraph/compare/v0.15.0...v0.15.1) - 2025-07-19

### Bug Fixes

- Serialise/Deserialise for indices is backwards compatible ([#234](https://github.com/CQCL/portgraph/pull/234))

## [0.15.0](https://github.com/CQCL/portgraph/compare/v0.14.1...v0.15.0) - 2025-07-18

### New Features

- added DynamicTopoConvexChecker ([#212](https://github.com/CQCL/portgraph/pull/212))
- [**breaking**] convert `PortOffset` in to struct with private fields ([#218](https://github.com/CQCL/portgraph/pull/218))
- [**breaking**] Make PortGraph generic on node and port types ([#230](https://github.com/CQCL/portgraph/pull/230))

### Performance

- Avoid double graph traversals in insert_graph ([#206](https://github.com/CQCL/portgraph/pull/206))

### Refactor

- [**breaking**] Add MaybeNodeIndex/PortIndex for performance ([#232](https://github.com/CQCL/portgraph/pull/232))

### New contributors

- @gluonhiggs

## [0.14.1](https://github.com/CQCL/portgraph/compare/v0.14.0...v0.14.1) - 2025-04-28

### New Features

- Implement petgraph traits on adaptors ([#195](https://github.com/CQCL/portgraph/pull/195))
- FlatRegions that do not include their root node ([#200](https://github.com/CQCL/portgraph/pull/200))
- Node style attributes in render options ([#199](https://github.com/CQCL/portgraph/pull/199))
- Allow the FlatRegion to own its hierarchy ([#201](https://github.com/CQCL/portgraph/pull/201))

## [0.14.0](https://github.com/CQCL/portgraph/compare/v0.13.3...v0.14.0) - 2025-04-08

### Others

- [**breaking**] Bumped the public `petgraph` dependency to `0.8.1` ([#193](https://github.com/CQCL/portgraph/pull/193))

## [0.13.3](https://github.com/CQCL/portgraph/compare/v0.13.2...v0.13.3) - 2025-03-04

### Bug Fixes

- Fix panic when removing InPorts in MultiPortGraph::set_num_ports ([#191](https://github.com/CQCL/portgraph/pull/191))

## [0.13.2](https://github.com/CQCL/portgraph/compare/v0.13.1...v0.13.2) - 2025-02-24

### Documentation

- cleanups, clarify (+test) connected components (#180)

### New Features

- add Subgraph::copy_in_parent (#182)

### Refactor

- Simplify PortGraph::port_links (#188)

## [0.13.1](https://github.com/CQCL/portgraph/compare/v0.13.0...v0.13.1) - 2025-01-20

### Bug Fixes

- Mermaid render of graph views was empty (#175)
- Hierarchy descendants return root siblings (#178)

## [0.13.0](https://github.com/CQCL/portgraph/compare/v0.12.3...v0.13.0) - 2025-01-17

This release has been focused on performance improvements.
Subgraphs and region filters now avoid unnecessary full-graph traversals
by using specialized implementation.

We also added a `Boundary` definition used for `Subgraph`s that can compute
the partial order between its inputs and outputs.

### New Features

- [**breaking**] Use RPITIT for graph traits (#156)
- [**breaking**] Added a `Boundary` definition and port partial-order computation (#164)

### Performance

- [**breaking**] Fix O(n) complexity in `Subgraph` (#157)
- [**breaking**] Manual impl of `Region`/`FlatRegion` for improved perf (#162)

## [0.12.3](https://github.com/CQCL/portgraph/compare/v0.12.2...v0.12.3) - 2024-11-13

### New Features

- Fastpath for `is_node_convex` on a single node ([#153](https://github.com/CQCL/portgraph/pull/153))

## [0.12.2](https://github.com/CQCL/portgraph/compare/v0.12.1...v0.12.2) - 2024-07-05

### Bug Fixes
- Intergraph edges in mermaid rendering ([#139](https://github.com/CQCL/portgraph/pull/139))

### New Features
- Add PortOffset::opposite ([#136](https://github.com/CQCL/portgraph/pull/136))
- Efficient LCA algorithm for the hierarchy ([#138](https://github.com/CQCL/portgraph/pull/138))

### Testing
- Use `insta` for mermaid/dot render tests ([#137](https://github.com/CQCL/portgraph/pull/137))

## [0.12.1](https://github.com/CQCL/portgraph/compare/v0.12.0...v0.12.1) - 2024-06-03

### Bug Fixes
- Link and neighbour iterators counting self-loops twice ([#132](https://github.com/CQCL/portgraph/pull/132))

## 0.12.0 (2024-03-01)

### Features

- Proptest for Multiportgraph
- (Multi)Portgraph implement Arbitrary
- [**breaking**] Mermaid rendering ([#125](https://github.com/CQCL/portgraph/pull/125))

### Miscellaneous Tasks

- [**breaking**] Hike MSRV to 1.75

## 0.11.0 (2023-12-14)

### Features

- [**breaking**] Make the ConvexChecker into a trait ([#121](https://github.com/CQCL/portgraph/pull/121))

## 0.10.0 (2023-10-20)

### Features

- Simpler convex checker, no longer requires `&mut` ([#114](https://github.com/CQCL/portgraph/pull/114))

### Miscellaneous Tasks

- [**breaking**] Update pyo3 requirement from 0.19 to 0.20 ([#110](https://github.com/CQCL/portgraph/pull/110))

### Doc

- Add DEVELOPMENT.md

## v0.9.0 (2023-09-05)

### Features

- Require Clone instead of Copy in ConvexChecker, add `Copy` to filters ([#104](https://github.com/CQCL/portgraph/issues/104))
- Allow non-references in the portgraph wrappers ([#105](https://github.com/CQCL/portgraph/issues/105))

## v0.8.0 (2023-08-08)

### Added

- `view::FilteredGraph` for filtering both nodes and links of a graph ([#100][])
- `view::SubGraph` for views into non-hierarchical subgraphs ([#100][])

### Changed

- `view::NodeFiltered` is now a specialized version of `view::FilteredGraph`.
  Its constructor has been renamed to `NodeFiltered::new_node_filtered`. ([#100][])

  [#100]: https://github.com/CQCL/portgraph/issues/100

## v0.7.2 (2023-07-31)

### Added

- `algorithms::ConvexChecker` to check convexity property of subgraphs of `LinkView`s ([#97][])

### Changed

- References to `PortView`s and `LinkView`s also implement the traits ([#94][])
- `Toposort` now works with any `LinkView` object ([#96][])

  [#94]: https://github.com/CQCL/portgraph/issues/94
  [#96]: https://github.com/CQCL/portgraph/issues/96
  [#97]: https://github.com/CQCL/portgraph/issues/97

## v0.7.1 (2023-07-13)

### Fixed

- Only yield output neighbours in petgraph's IntoNeighbors trait implementation ([#88][])
- Fix incorrect dot rendering of the hierarchy for flat filtered regions ([#91][])

  [#88]: https://github.com/CQCL/portgraph/issues/88
  [#91]: https://github.com/CQCL/portgraph/issues/91

## v0.7.0 (2023-06-28)

### Added

- `LinkMut::insert_graph` to insert a full graph into an existing graph ([#80][])
- `PortMut::swap_nodes` to swap node indices ([#83][])
- `Hierarchy::swap_nodes` to swap node indices ([#87][])
- `Debug` and `Default` implementation for multiple iterators ([#81][])

### Removed

- Removed the `substitute` module ([#82][])

  [#80]: https://github.com/CQCL/portgraph/issues/80
  [#81]: https://github.com/CQCL/portgraph/issues/81
  [#82]: https://github.com/CQCL/portgraph/issues/82
  [#83]: https://github.com/CQCL/portgraph/issues/83
  [#87]: https://github.com/CQCL/portgraph/issues/87

## v0.6.0 (2023-06-21)

### Added

- `NodeFiltered`, `Region`, and `FlatRegion` graph wrappers ([#77][])
- Implemented the petgraph visit traits for the graph wrappers ([#78][])
- Benchmarks for the `toposort` algorithm ([#75][])

### Changed

- Split the `PortView`, `LinkView`, and `MultiView` traits into separate `*View` and `*Mut` traits ([#76][])
- Replaced `NonZeroU16` in `PortOffset::Incoming` with `u16` ([#73][])

### Fixed

- Fix dot formatter not hiding "Hidden" ports ([#74][])

  [#73]: https://github.com/CQCL/portgraph/issues/73
  [#74]: https://github.com/CQCL/portgraph/issues/74
  [#75]: https://github.com/CQCL/portgraph/issues/75
  [#76]: https://github.com/CQCL/portgraph/issues/76
  [#77]: https://github.com/CQCL/portgraph/issues/77
  [#78]: https://github.com/CQCL/portgraph/issues/78

## v0.5.0 (2023-06-14)

### Added

- Added a MultiPortGraph structure that supports multiple connections to the same port ([#67][])
- Added new traits `PortView`, `LinkView`, and `MultiView` to unify the
  `PortGraph` and `MultiPortGraph` interfaces ([#68][])
- Added a `petgraph` feature that implements petgraph's `visit` traits for interoperability ([#70][])
- Added missing `Debug` implementations for iterators ([#65][])

### Changed

- Reworked the dot formatter API ([#69][])
- The serialized format for NodeIndex and PortIndex now uses the user-facing
  indices instead of the off-by-one values used internally ([#64][])
- Simplified PortGraph debug information by showing the ports of a node as a range ([#66][])

  [#64]: https://github.com/CQCL/portgraph/issues/64
  [#65]: https://github.com/CQCL/portgraph/issues/65
  [#66]: https://github.com/CQCL/portgraph/issues/66
  [#67]: https://github.com/CQCL/portgraph/issues/67
  [#68]: https://github.com/CQCL/portgraph/issues/68
  [#69]: https://github.com/CQCL/portgraph/issues/69
  [#70]: https://github.com/CQCL/portgraph/issues/70

## v0.4.0 (2023-06-06)

### Added

- `SecondaryMap::remove` method to drop stored ([#59][])
- `PortGraph::link_offsets`  ([#58][])
- Implemented `SecondaryMap` for `HashSet`s to efficiently store sparse flags for nodes and ports ([#62][])
- Generalized the `Iterator` impl of `TopoSort` to any `SecondaryMap` ([#63][])

### Changed

- Changed the `PortGraph::set_num_ports` callback to give more information using a new `PortOperation` ([#57][])
- Allows `PortGraph::link_ports` to connect ports in any order, as long as the directions are compatible ([#58][])

  [#57]: https://github.com/CQCL/portgraph/issues/57
  [#58]: https://github.com/CQCL/portgraph/issues/58
  [#59]: https://github.com/CQCL/portgraph/issues/59
  [#62]: https://github.com/CQCL/portgraph/issues/62
  [#63]: https://github.com/CQCL/portgraph/issues/63

## v0.3.0 (2023-05-31)

### Breaking changes

- Renamed `SecondaryMap` to `UnmanagedDenseMap` ([#51][])

### New features

- Added a `SecondaryMap` generic trait, implemented by `UnmanagedDenseMap` and `BitVec` ([#51][])
- Added a generic `Map : SecondaryMap` type parameter to the dominators and toposort algorithms,
  allowing more efficient executions on partially explored graphs ([#51][])

### Fixes

- Fix incorrect port count update when resizing ports in-place ([#53][])

  [#51]: https://github.com/CQCL/portgraph/issues/51
  [#53]: https://github.com/CQCL/portgraph/issues/53

## v0.2.4 (2023-05-25)

- Add `as_range` methods to `NodePorts` and `NodePortOffsets` ([#49][], [#50][])
- Fix equality comparison between secondary maps with different capacity ([#48][])

  [#48]: https://github.com/CQCL/portgraph/issues/48
  [#49]: https://github.com/CQCL/portgraph/issues/49
  [#50]: https://github.com/CQCL/portgraph/issues/50

## v0.2.3 (2023-05-17)

- Add a `rekey` method to `SecondaryMap` ([#44][])
- Fix `set_num_ports` deleting links ([#43][])

  [#43]: https://github.com/CQCL/portgraph/issues/43
  [#44]: https://github.com/CQCL/portgraph/issues/44

## v0.2.2 (2023-05-11)

This is a bugfix release that fixes a panic when growing the number of ports in an empty node.

- Fix a panic on `set_num_ports` ([#40][])

  [#40]: https://github.com/CQCL/portgraph/issues/40

## v0.2.1 (2023-05-10)

- Implemented serialization on Weights and PortOffset ([#36][])
- Added port capacity to the nodes, and an overallocation factor when increasing
  the number of ports. ([#37][])

  [#36]: https://github.com/CQCL/portgraph/issues/36
  [#37]: https://github.com/CQCL/portgraph/issues/37

## v0.2.0 (2023-05-03)

- Initial release with support for directed graphs with first-level ports.

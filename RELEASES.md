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
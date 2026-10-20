# Disjoint-ball Maxwell partition adapter

Source: `lean/DisjointBallPartition.lean`.

SHA256: `1C58E1D521D90E85AF43B297F4F00A2E63936F7D9DEE529B03EAA82E4BBFD06E`.

Author final compiler exit 0; importable object 73688 bytes; both selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/disjoint-ball-partition-check.log`.

The constructor fills every geometric field of the actual Maxwell partition using literal separated inclusion interiors and their proved connected common exterior. Assumptions are finite indexing, positive radii, strict pair separation, positive material values and actual AE coefficient agreement on those cells. A seed is constructed outside any prescribed support radius. There is no assumed partition, connectivity or PDE propagation conclusion.

Status: root independent full-source audit and compiler PASS. Frozen unchanged at the hash above. Independent output: `lean/logs/DisjointBallPartition-independent-root.log`.

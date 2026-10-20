# Sphere angular symmetry

Author verification for `lean/SphereAngularSymmetry.lean`.

- Source SHA256: `02E77892AF649EA05DF627779F7CE91406BF9E3D72175A5DA7B05C0A40736340`.
- Pinned Lean 4.19.0, `lake env lean -o .lake/build/lib/lean/SphereAngularSymmetry.olean SphereAngularSymmetry.lean`: exit 0.
- Log: `lean/SphereAngularSymmetry.final.log`; SHA256 `E294DA4B4D93109DE8CCD1929080F02945E04F0804B2B69CC5C11A6B43168A89`.
- Four printed declarations, each using only `propext`, `Classical.choice`, `Quot.sound`; no compiler warnings.

The sphere homeomorphism is the restriction of an actual Euclidean linear isometry equivalence. The cone preimage is proved by explicit forward and inverse scaling witnesses. The actual `angularMeasure` is defined from volume; its defining cone formula and volume preservation prove its invariance. The real integral identity follows from this proved measure-preserving homeomorphism, without a symmetry premise.

Object emitted: 184576 bytes. Independent root full-source mathematical audit and pinned compiler recheck PASS at the exact source hash above, all four standard-only reports. Source frozen.

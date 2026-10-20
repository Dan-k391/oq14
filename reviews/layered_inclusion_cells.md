# Finite radial layers around separated inclusions

Source: `lean/LayeredInclusionCells.lean`.

SHA256: `64D2E5DE5A9A7284A6291EC43D4D67D6B840899AD9E753032153E4C6B3AA06DF`.

Author final compiler exit 0; importable object 307056 bytes. All ten selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/layered-inclusion-cells-check.log`.

The literal cells are indexed by `ι ⊕ Fin (n+2)`. Inclusion cells are their actual open balls. Radial cell zero is replaced by the proved connected cavity inside the innermost radius; every other radial cell is the existing literal radial cell. Actual openness, preconnectedness, AE volume cover, adjacent bridges, all-cell reachability, and an exterior seed outside any given radius are derived.

The first radial bridge uses the actual cavity-to-shell bridge. If there is only one cut, its annular target is enlarged to the actual exterior. Later bridges reuse the frozen finite radial construction. The AE cover uses the genuine radial and inclusion covers. There is no assumed partition, connectivity, PDE propagation, or uniqueness conclusion.

The material partition constructor takes positive material values and their actual AE agreement with the supplied dielectric on these literal cells. Geometry is fully discharged by the preceding proofs.

Independent reviewer continuation_review_sol read the complete source,
the complete CavityBallGeometry and CavityBallBridges sources, the actual
DisjointBallCells cover, and the reused finite radial geometry interfaces.
An independent pinned Lean 4.19 compiler run completed with exit 0 at the
exact hash above; all ten reports are standard-only. The final hash was
checked again after compilation. No frozen proof source was edited.

The geometry is genuine: the cavity is the core ball outside all closed
inclusion balls, its paths are constructed by actual clamping and radial
pushes, and its bridge balls have actual overlap points and exclude only
null interface spheres. Inclusion-to-cavity edges and the cavity-to-first
radial layer connect to the actual finite chain of higher radial layers.
This includes the one-cut case and permits an empty inclusion index type.
The proof assumes strict inclusion separation and strict core containment,
not the resulting connectivity or any PDE uniqueness conclusion.

Scope: finitely many positive-radius separated spherical inclusions strictly
inside the first positive concentric cut, with any finite number of later
strictly ordered positive cuts. This does not cover touching inclusions,
inclusions crossing a radial interface, or arbitrary piecewise geometry.
Independent mathematical and compiler audit: PASS.

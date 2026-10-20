# Actual finite radial partition verification

Author: continuation_review_sol. Date: 2026-10-20.

Source: `lean/FiniteRadialPartition.lean`.
SHA256: `4C972A4BF6DB508C28794052CE9C4931308FB8DDE810533319F1A6CB25362863`.

Pinned Lean 4.19 targeted compilation and importable olean emission passed
with exit 0. All twelve selected dependency reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Independent reviewer fredholm_sol read
the complete source and reran the pinned compiler at this exact hash:
exit 0, no warnings, and all twelve reports standard-only. Its log is
`lean/FiniteRadialPartition.independent-fredholm.log`. Independent mathematical
and compiler audit: PASS.

Given n+1 strictly ordered positive radii, the actual cells are indexed by
Fin(n+2). Membership requires the point's norm to be above every radius
whose index is lower than the cell index and below every remaining radius.
The first cell is proved equal to the literal open inner ball, every middle
cell to the literal open annulus between adjacent radii, and the final cell
to the literal exterior. Openness and preconnectedness invoke the actual
three-dimensional geometry theorems in RadialMaterialCells.

For a point not on any interface sphere, the smallest cut above its norm,
when present, identifies its cell. Minimality gives all lower inequalities;
strict ordering gives all upper inequalities. If no such cut exists, the
point is in the exterior. Each actual interface sphere has zero volume,
and the finite AE conjunction therefore proves a genuine full-space AE
cover. No coverage hypothesis is assumed.

Each adjacent pair invokes the actual inner/exterior, inner/annulus,
annulus/exterior, or annulus/annulus bridge theorem, with the strict gap
and positivity inequalities derived from the radii. This handles n=0 as
well as multiple cuts. Natural induction constructs a finite adjacent path
from the inner cell to every cell; bridge symmetry gives every-to-every
reachability. No abstract PDE propagation conclusion is assumed.

An explicit point on the coordinate axis at radius max(R,lastCut)+1 belongs
to the exterior cell and lies outside any prescribed support ball. This
discharges the geometric exterior-seed existence needed by the Maxwell
volume uniqueness theorem.

The final partition constructor accepts the actual dielectric epsilon,
positive cell material values, and their literal AE constancy on these
fixed radial cells. All openness, connectedness, cover, and reachability
fields are proved by the preceding geometry. Material constancy is the
only coefficient-identification input, not a uniqueness or connectivity
premise. This supports arbitrary finite concentric piecewise-constant
positive material profiles; it is not a construction for arbitrary
nonradial piecewise geometries or arbitrary variable coefficients.

The source contains no standalone custom axiom/constant declarations or
proof-hole tokens. Targeted compiler verification: PASS.

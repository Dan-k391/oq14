# Actual plane-separated source kernel verification

Author: continuation_review_sol. Date: 2026-10-20.

Source: `lean/PlaneSourceKernel.lean`.
SHA256: `45849CC859734C56ABFBC94ED49689E9530F29CF78AC1E822911B13ABFF6DEB0`.

Pinned Lean 4.19 targeted compilation and importable olean emission passed
with exit 0. All twenty-one selected dependency reports use only `propext`,
`Classical.choice`, and `Quot.sound`. Independent source and compiler review
is requested before registration.

Admissible sources are literal vector functions with componentwise L1
integrability, support in a fixed radius-R ball, and actual nonzero source
values at vertical distance at least d from the observation plane. The
source region is the compact intersection of that ball with |y2|>=d.
The actual plane embedding gives norm(planePoint(q)-y)>=|y2|>=d. For d>0
the electric dyadic and magnetic gradient kernels therefore avoid their
singularity on each compact observation-disk/source-region product.

Continuity of the actual kernel norm-sum on that product supplies a positive
finite bound, depending only on k,R,d and the observation radius. No kernel
bound is postulated. Actual Bochner integrability follows by domination
with this constant times the actual source norm. Dominated convergence
proves continuity of every actual response on the entire observation plane.

Actual electric component bounds on a disk are C*sourceMass; magnetic
component bounds are 2*abs(k)*C*sourceMass, with the same uniform compact
kernel constant. The actual electric and magnetic plane fields and their
bilinear complex normal cross product are continuous. These are ordinary
integral representatives separated from source support, not arbitrary
distributional traces.

Subtraction preserves source admissibility. The actual source L1 mass
obeys its triangle bound. Integral subtraction is justified using actual
integrable kernel products, yielding electric and magnetic source
subtraction and the exact bilinear flux difference identity. No abstract
linear-operator or flux-continuity conclusion is assumed as an input.

The three checkpoint errors were syntactic Pi-subtraction rewrite shapes;
the final source supplies those actual shapes explicitly. Full targeted
compiler verification: PASS. The frozen PlaneInverseCube and
MaxwellPlaneTail dependencies were not modified.

## Independent root verification on resumption

Full source reviewed and pinned Lean compiler returned exit0. All 21 selected reports use only the standard foundations. Source SHA256 `45849cc859734c56abfbc94ed49689e9530f29cf78ac1e822911b13abff6deb0`. Independent log: `lean/logs/PlaneSourceKernel-independent-root.log`. Actual definitions and hypotheses were checked; this result does not close the outstanding full Maxwell/OQ14 constructions.

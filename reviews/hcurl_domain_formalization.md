# Open-region weak curl: formal scope and independent review

The source is `lean/HCurlDomain.lean`, namespace `OQ14.DomainCurl`, on the
same actual Euclidean three-space as `Maxwell.lean`. The pinned Lean and
mathlib dependencies are unchanged. This review records the twelve checked
exports; it does not claim a full Maxwell scattering formalization.

Scalar fields are `Lp Complex 2 (volume.restrict region)`, hence are actual
almost-everywhere equivalence classes for restricted Lebesgue measure.
Vector fields consist of three such coordinates. Tests are globally C1
complex functions with compact support contained in the region. Their
derivatives are continuous and compactly supported, and define bounded L2
test functionals. Equality with the actual restricted integral and the
required integrability are both proved.

The curl graph is the intersection of kernels of the explicit continuous
linear residuals for those test identities. Closedness supplies completeness
of its inherited Banach norm: the maximum of the field and curl coordinate
L2 norms. This is not a modal energy norm and no inner-product structure is
claimed for the maximum norm.

On an open region, the actual open-set fundamental lemma for compact smooth
tests proves separation of the L2 classes, by applying it to the difference
of two locally integrable representatives. Complex tests include the real
tests used by that lemma. Weak curl is consequently unique and the field
projection of its graph is injective. Simultaneous L2 convergence of field
and curl preserves graph membership.

For globally C1 classical fields whose field and classical curl are L2 only
on the region, the weak law follows from the already checked whole-space
integration-by-parts theorem: the test and its derivatives vanish outside
the region. There is no hidden global L2 condition and no zero boundary
condition. This bridge does not prove that every locally C1 field on an
arbitrary open set has a global C1 extension.

The final theorem `weak_divergence_curl` applies to arbitrary weak L2 fields.
It differentiates a compact C2 test, obtains three valid C1 curl tests, and
cancels the resulting mixed derivatives using the checked Schwarz identity
`Maxwell.partial_comm`. Neither the original field nor its curl is assumed
differentiable. Its C2 test class contains all compact smooth distribution
tests, so it proves distributional divergence zero. This does not identify
pointwise derivatives of a nonsmooth field.

The independent counterexample/formalization agent reviewed the complete
source after successful compilation and found no substantive defect. Its
review explicitly checked signs, support of derivative tests, the openness
premise for uniqueness, and the lack of field regularity premises in the
last theorem. All twelve exports report only `propext`, `Classical.choice`,
and `Quot.sound`. No admitted proof or project-specific axiom is used.

The combined research build checked fifty-one exports in four modules. Its
raw output and provenance are retained under `lean/HCurlDomain/`; the clean
release build, when present, is recorded under `output/lean/`. The research
record identifies its dirty source state explicitly. Boundary traces,
interface transmission, radiation, weak-field existence and complete
continuum OQ14 proofs remain separate obligations.

# Lean verification of operator estimates and Maxwell foundations

The formal sources are `OQ14.lean`, `Maxwell.lean`, `HCurl.lean`,
`HCurlDomain.lean`, `HCurlCutoff.lean`, `WeakPoynting.lean`, and
`WeakPoynting/Green.lean`, `WeakPoynting/Poynting.lean`,
`WeakPoynting/Local.lean`, `WeakPoynting/Conservation.lean`,
`WeakPoynting/Slices.lean`, `WeakPoynting/Representative.lean`,
`WeakPoynting/Weighted.lean`, `ModalAlgebra.lean`, `ModalWronskian.lean`,
`RadialGreen.lean`, `StaticVolume.lean`, and `LongitudinalProjection.lean`.
Also registered are `WeakPoynting/Polarization.lean`, `FourierL2.lean`,
`ModalRational.lean`, `GreenKernel.lean`, `VectorFourier.lean`,
`GradientProjection.lean`, `HelmholtzProjection.lean`, `StaticCoefficient.lean`,
`DyadicKernel.lean`, `ModalAlgebraicity.lean`, `ModalExistence.lean`,
`ModalAsymptotics.lean`, `WeakPoynting/Lipschitz.lean`, and
`WeakPoynting/Aperture.lean`, `WeakPoynting/Axial.lean`,
`WeakPoynting/LipschitzBoundary.lean`, `ModalMatching.lean`, and
`KernelIntegrability.lean`, `HeatFourier.lean`, `NewtonFourier.lean`,
`NewtonHessian.lean`, `DynamicIntegrability.lean`, `KernelEstimates.lean`,
`ModalDipole.lean`, `ModalInterface.lean`, `WeakPoynting/Energy.lean`, and
`WeakPoynting/EnergyLocalization.lean`. The continuation adds `PointSingularity.lean`, `RealKernelBounds.lean`, `KernelGradient.lean`, `KernelSource.lean`, `DynamicSource.lean`, `NewtonConvolution.lean`, `NewtonL2.lean`, `NewtonL1L2.lean`, `StaticNewton.lean`, `ModalOrigin.lean`, `WeakPoynting/DivCurl.lean`, `WeakPoynting/DivCurlCompact.lean`, `WeakPoynting/DivCurlRegularity.lean`, `WeakPoynting/LocalRegularity.lean`, and `WeakPoynting/RegularityBounds.lean`. The spatial-source, volume, spherical-assembly and compactness modules described below are also registered. One thousand eight hundred thirty-five exported
theorems compile with Lean 4.19.0
and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`
(the `v4.19.0` tag). `lake-manifest.json` pins every transitive dependency.

## Reproduce

Install the [official Lean 4.19.0 release](https://github.com/leanprover/lean4/releases/tag/v4.19.0)
or use an existing installation selected by `lean-toolchain`. From this
directory, prepare dependencies using the supplied lockfile (keep
`lake-manifest.json` unchanged):

```text
lake exe cache get Mathlib.Analysis.NormedSpace.OperatorNorm.Basic Mathlib.Analysis.Normed.Operator.LinearIsometry Mathlib.Analysis.InnerProductSpace.Basic Mathlib.LinearAlgebra.FiniteDimensional.Defs Mathlib.LinearAlgebra.Dimension.Finrank Mathlib.MeasureTheory.Integral.Bochner.Basic Mathlib.Data.Real.Sqrt Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
lake exe cache get Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.Calculus.FDeriv.Mul Mathlib.Analysis.Calculus.FDeriv.Symmetric Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.LinearAlgebra.CrossProduct Mathlib.Tactic.FinCases Mathlib.Tactic.LinearCombination
lake exe cache get Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Function.LpSpace.Indicator Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
lake exe cache get Mathlib.Analysis.Convolution Mathlib.Analysis.Calculus.BumpFunction.Convolution Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
lake exe cache get Mathlib.Geometry.Manifold.PartitionOfUnity
lake exe cache get Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace Mathlib.Analysis.InnerProductSpace.Positive Mathlib.Analysis.Calculus.Deriv.ZPow
lake exe cache get Mathlib.Analysis.Distribution.FourierSchwartz Mathlib.Analysis.Calculus.Rademacher Mathlib.Topology.MetricSpace.Contracting Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv Mathlib.RingTheory.Algebraic.Integral
lake exe cache get Mathlib.MeasureTheory.Constructions.HaarToSphere
```

Then run the portable clean source build and axiom audit:

```text
python build.py
```

For a portable compiler outside PATH, use
`python build.py --lake /absolute/path/to/lake` (or `lake.exe` on Windows).
The local Windows compiler, when present, is automatically found under
`../.tools/lean/lean-4.19.0-windows/bin`. No global installation is required.
`build.ps1` delegates to the same Python audit; its `-Python` option selects
the interpreter. There is no separate weaker PowerShell verification path.
Use `--log-dir /absolute/output/directory` to preserve the tracked evidence
files during a new clean-checkout build. Git is used read-only to verify
every installed dependency HEAD against the manifest and reject changed
tracked dependency files; `--git /absolute/path/to/git` selects it explicitly.
The output also records the source repository commit and dirty flag.

The build removes **only this package's** `.lake/build`, verifies the pinned
compiler and mathlib revision, builds all one hundred fifty-two registered modules, and audits all 1835
`#print axioms` reports. It retains compiled dependency artifacts, as a
normal clean project build does. The raw successful compiler output is
`logs/clean-build.txt`; exact source and manifest SHA256 hashes, compiler,
and theorem names are in `logs/provenance.json`. Large downloaded tools,
dependency checkouts and compiled caches are excluded from the deliverable.
Do not run `lake update` for a locked reproduction: it is a dependency-update
operation. Lake fetches missing packages for the cache/build command using
the supplied manifest. A clean source checkout may reuse the existing
`.lake/packages` directory (for example with a local directory junction)
while retaining its own freshly rebuilt `.lake/build`.

If the official ProofWidgets release download encounters a transient
network failure during setup, retry `lake build proofwidgets:release`,
then repeat the cache command. This repair does not change the proof source
or dependency revisions.

## Formal theorem coverage

All names below have namespace prefix `OQ14.`.

| Declaration | Verified statement |
|---|---|
| `approximation_kernel_trivial` | A strict operator error below a uniform amplitude lower bound excludes nonzero kernel vectors. |
| `approximation_injective` | The approximating operator is injective. |
| `finiteDimensional_of_approximation` | Finite-dimensional approximation range forces actual finite dimensionality of the domain. |
| `finite_rank_channel_bound` | The resulting dimension is at most the approximation rank bound. |
| `finite_rank_power_channel_bound` | The power formulation uses exactly the strict error threshold `sqrt(tau)` and returns finite dimensionality and dimension at most M. |
| `isometry_perturbation_lower_bound` | Error at most e from an isometry yields amplitude at least `(1-e)` times input norm for every input. |
| `isometry_perturbation_power_threshold` | The strict margin `e < 1-sqrt(tau)` yields power above tau for every nonzero input. |
| `compression_power_threshold` | A contractive output compression satisfying that certificate yields the same lower bound on full output power. |
| `quadratic_flux_norm_bound` | Absolute real quadratic flux is bounded by operator norm times squared input norm. |
| `absolute_bypass_certificate` | Integrating the operator norm gives the coherent absolute-bypass bound, with integrability explicitly assumed. |

The first group formalizes the elementary dimension reduction in the
channel section. The second group covers the unitary/isometry compression
certificate in `cx:compression`. The final group proves the analytic
integration step underlying `cx:absolute-bypass`, in a complex inner
product space over an arbitrary measure space.

## Actual differential and weak Maxwell proofs

The following names have prefix `OQ14.Maxwell.`. The domain is actual
Euclidean three-space. Partial derivatives use the real Fréchet derivative;
the fields, curls, divergence and Lebesgue integrals are concretely defined.

| Declaration | Verified statement |
|---|---|
| `divergence_cross` | Differential cross-product identity from the product rule. |
| `curl_conj` | Curl commutes with complex conjugation. |
| `complex_poynting_identity` | Complex local Poynting identity from Maxwell curl equations. |
| `real_poynting_divergence_zero` | Zero real divergence for lossless local coefficients. |
| `curl_gradient` | Curl of an actual C2 gradient vanishes. |
| `divergence_curl` | Divergence of an actual C2 curl vanishes. |
| `maxwell_superposition` | Coherent linear combinations solve the same Maxwell equations. |
| `maxwell_curl_curl` | The homogeneous second-order electric equation follows from the two curl equations. |
| `partial_integration_by_parts` | Coordinate integration by parts for compactly supported C1 tests. |
| `curl_integration_by_parts` | The actual distributional curl pairing. |
| `classical_maxwell_weak_form` | Every C1 Maxwell solution satisfies the compact-test weak equations. |
| `vacuum_plane_wave` | An explicit nonzero propagating solution at positive frequency. |
| `evanescent_wave` | Explicit growing and decaying Maxwell waves. |
| `paired_evanescent_maxwell` | Their coherent pair is a Maxwell solution everywhere. |
| `evanescent_zero_normal_power` | One wave has zero normal power at the origin. |
| `paired_evanescent_positive_power` | The pair has power 3/4 at the origin. |
| `evanescent_zero_normal_power_everywhere` | One wave has zero normal power everywhere. |
| `paired_evanescent_power_everywhere` | The pair has constant power 3/4 everywhere. |

All differentiability hypotheses are explicit. Compact support proves the
integrability needed in integration by parts. The weak theorem concerns
classical fields tested against compact functions; it is not an existence
theorem for arbitrary weak fields. The evanescent witnesses grow in space
and have infinite transverse extent; no finite-power physical excitation
or unrestricted channel counterexample follows from them.

The source hashes and research checks are in `Maxwell/`, `HCurl/`,
`HCurlDomain/`, `HCurlCutoff/`, and `WeakPoynting/`. The
combined clean release build is recorded under `../output/lean/`.

Every audited theorem's reported axioms are exactly `propext`, `Classical.choice`,
and `Quot.sound`, the standard Lean/mathlib foundations. There are no
project-specific axioms, admitted proofs, or assumed Maxwell conclusions.

## Weak curl on all space and open regions

`HCurl.lean`, namespace `OQ14.WeakCurl`, constructs the genuine L2 weak-curl
graph on Euclidean three-space. `HCurlDomain.lean`, namespace
`OQ14.DomainCurl`, uses L2 classes for Lebesgue measure restricted to a region
and tests compactly supported inside it. Fields in the second space need
not be globally square integrable. No zero boundary condition is imposed.

Each module proves these eleven exported results:

| Declaration | Verified statement |
|---|---|
| `testPair_integrable` | The products defining test pairings are integrable. |
| `testPair_integral` | A bounded L2 test functional equals the actual integral. |
| `hasWeakCurl_iff_integral` | The graph condition is exactly the weak curl equation. |
| `graph_closed` | The graph is a closed complex subspace. |
| `hcurl_complete` | Its inherited graph norm is complete. |
| `graph_norm` | The norm is the maximum field/curl coordinate L2 norm. |
| `weakCurl_limit` | Simultaneous L2 limits preserve the weak equation. |
| `tests_separate` | Admissible compact tests separate scalar L2 classes. |
| `weakCurl_unique` | The distributional curl is uniquely determined. |
| `field_projection_injective` | No unconstrained curl data enter the graph. |
| `classical_hasWeakCurl` | A C1 field with L2 field and curl belongs to the graph. |

The domain separation and uniqueness results require the region to be open.
The domain classical bridge assumes a globally C1 field but requires L2 only
on the region. Both norms are Banach graph norms, not mode energy norms.

The twelfth domain export, `weak_divergence_curl`, proves that the weak curl
has zero distributional divergence. It tests against compact C2 functions,
which include the usual smooth distribution tests, and derives cancellation
from actual mixed derivatives. The field and curl need no differentiability.

## Interior cutoff and localization

`HCurlCutoff.lean`, namespace `OQ14.CurlCutoff`, proves multiplication by
an actual compact C1 scalar and the weak product rule
`curl(chi E) = chi curl E + grad chi cross E`. No differentiability of E
is assumed. Supremum bounds A on the multiplier and B on each coordinate
derivative give graph norm at most `(A + 2 B) norm E`. The source also
constructs the isometric zero extension of restricted L2 classes, proves
its integral pairing identity, and proves that the product-rule curl
extends correctly after a cutoff supported inside the open region.

Its eleven audited exports are `multiplier_memLp`, `mulL2_ae`,
`mulL2_norm_le`, `testPair_mulL2`, `derivativePair_product`,
`weakCurl_multiply`, `cutoff_norm_le`, `extendScalar_ae`,
`extendScalar_norm`, `extendScalar_pair`, and `weakCurl_cutoff_extend`.
Unrestricted zero extension across a boundary is not claimed.

## Smooth approximation and weak Green identity

The sixteen audited exports of `WeakPoynting.lean` prove actual
convolution smoothness, commutation with weak curl, strong continuity of
L2 translations, and strong convergence of normalized bump averages.
Absolute product-space integrability justifies Fubini and identifies
the Bochner L2 average with the pointwise smooth convolution. Explicit
shrinking bumps therefore produce smooth representatives converging to
every whole-space H(curl) field in its graph norm. No density assumption
is used.

The six audited exports of `WeakPoynting/Green.lean` prove bounded bilinear
L2 pairings equal the actual integrals, and derive the local Green identity
for two arbitrary whole-space H(curl) fields:

`integral chi (curl E dot F - E dot curl F) + grad chi dot (E cross F) = 0`.

The test chi is any compact C1 scalar. The proof first tests weak curl
against chi times a smooth field, then passes to the proved graph-norm
approximation. Neither nonsmooth field is differentiated classically.
These two modules require global L2 field and curl. The following three
modules prove the separate local-domain bridge.

## Local weak power conservation

`WeakPoynting/Poynting.lean` has five exports: weak curl commutes with
conjugation, weighted conjugate products are integrable, the actual
complex Poynting density is integrable, its integral agrees with the
Green functional, and its integral is zero for arbitrary whole-space
H(curl) fields.

`WeakPoynting/Local.lean` has six exports. A smooth interior cutoff equal
to one near the compact test support is constructed, not assumed.
Cutoff zero extension preserves the field and curl there, giving both
integrability and the complex Poynting law on any open region. No global
L2 condition or boundary condition is imposed on the original fields.

`WeakPoynting/Conservation.lean` has six exports. Its `WeakMaxwell`
predicate is exactly the two almost-everywhere equations for the actual
regional weak curls. Real variable coefficients make the reactive term
purely imaginary. Consequently the actual real time-averaged Poynting
vector has zero distributional divergence against every real compact C1
test. No differentiability of fields or coefficients is assumed. This
formalizes the distributional conservation step of `ch:fluxlemma`, not
its remaining plane-slice representatives or trace evaluations.

## Plane slices and exact modal/radial algebra

The sixteen exports of `WeakPoynting/Slices.lean` prove the actual
volume-preserving Euclidean-three-space coordinates `(z, x, y)`, Fubini,
L1 slice integrability, and the compact tensor-test calculation. Applied
to the actual weak Maxwell Poynting vector, they give the one-dimensional
weak derivative of the plane-integrated aperture flux, including its
transverse-gradient term. The zero extension is of an integrable flux;
its divergence law is only asserted inside the original open region.
Slices initially are a.e. integral functions. The thirteen exports of
`WeakPoynting/Representative.lean` derive their continuous representatives
from genuine weak derivatives: convolution proves the zero-derivative
constancy lemma, Fubini proves the actual integral primitive's test
identity, and smooth localization gives the interval increment law.
Continuity and a.e. equality determine endpoint values uniquely on every
nondegenerate interval. The eight exports of `WeakPoynting/Weighted.lean`
then prove the distributional product rule and weighted endpoint identity,
and turn it into the actual three-dimensional slab integral of gradient
cutoff dotted with real power. Both axial and transverse terms are kept.
These are canonical scalar flux values for compact C1 apertures and
cutoffs; general tangential H(curl) traces are not asserted.

The twenty-eight exports of `WeakPoynting/Polarization.lean` prove actual
regional weak Maxwell closure under complex combinations and the physical
Hermitian cross-input flux formula, sesquilinearity, diagonal agreement,
and conjugate symmetry. Integrable complex conservation yields actual
complex plane slices, continuous canonical values, exact increments and
the full weighted volume formula. Hermitian symmetry holds at every
canonical plane value, including endpoints. Cutoffs still have C1 scope.

The twenty-five exports of `ModalAlgebra.lean` define the exact finite
Riccati-Hankel Laurent expressions and prove their complex derivatives,
the TM determinant's exponential factorization, rational pole equation,
and the derivative condition forced by a hypothetical multiple pole.
The degree-one Wronskian and matching-coefficient nonvanishing are proved
directly. The twenty-six exports of `ModalWronskian.lean` derive the
factorial coefficient recurrence, actual radial ODE, and Wronskian -2i in
every degree. Its normalization follows from an entire polynomial in the
inverse coordinate, with no asymptotic or normalization premise. Matching
coefficients cannot vanish together; the rational multiple-pole conditions
therefore have their nonvanishing hypotheses discharged in every degree.
Transcendence and identification with Fredholm multiplicity remain separate
obligations; actual determinant-zero existence is proved below.

The seventeen exports of `ModalRational.lean` represent the actual matching
coefficients by finite inverse-coordinate polynomials. Explicit nonzero
polynomial obstructions prove that the multiple nonzero zeros at each
fixed degree form a finite set, and that the common nonzero zeros of each
distinct degree pair form a finite set, for n outside 0,+1,-1. Neither
emptiness nor avoidance of the countable union is inferred.

The twenty-four exports of `RadialGreen.lean` prove the exact complex
outgoing continuation and source coefficient for a real determinant-one
transfer, including minus its imaginary part equals squared core gain.
The source-load Wronskian cancellation and denominator lower bound are
proved. Actual radial ODEs imply the load/state derivative identities
and closed-interval barrier monotonicity, without a monotonicity premise.
The complete spherical expansion and all-order Green limit are not yet
formalized by these algebraic and differential results.

The ten exports of `StaticVolume.lean` construct the actual Hilbert-space
block `1 + S† P S` and prove its inverse norm at most one for positive P.
An actual orthogonal projection is shown positive. A perturbation Q of
norm below one gives invertibility, inverse bound `1/(1-norm Q)`, and an
error bound from the actual polarization residual. Identification of P
with the physical longitudinal Newton/Fourier operator is not assumed or
claimed to have been proved in this module. The twenty-two exports of
`LongitudinalProjection.lean` construct the actual frequency symbol
xi xi-transpose / |xi|^2, zero at xi=0, and its genuine vector-valued L2
multiplier. Coordinate formula, measurability, contraction, idempotence,
self-adjointness and positivity are proved. Physical-space Fourier
conjugation and spatial Newton identification are proved in the later modules below.

The twenty-three exports of `FourierL2.lean` prove actual scalar Euclidean
Plancherel. Fourier-integral Fubini and Schwartz inversion give Parseval;
compact smooth test annihilation proves density. The norm-preserving
extension is proved onto by inversion and closed isometric range.
Agreement with the actual Fourier integral on Schwartz functions and
uniqueness are checked. Its convention is exp(-2 pi i inner(x,xi)).
Vector lifting and identification with the physical Newton kernel are
not conclusions of the scalar module.

The seventeen exports of `GreenKernel.lean` prove actual radial and
Euclidean first/second derivatives of exp(i k |x|)/(4 pi |x|), smoothness
away from zero, the three-dimensional Helmholtz equation there, and the
radial Sommerfeld radiation limit for real k. Its distributional source
at the origin is proved below; full convolution/radiation solvability remains separate.

## Physical projection, material multiplication and kernel remainder

The 31 exports of `VectorFourier.lean` construct actual vector Plancherel
from the scalar theorem and volume-preserving coordinate maps. Its
component integral formula identifies the Fourier transform on Schwartz
fields. Conjugating the actual longitudinal multiplier gives a positive,
self-adjoint contractive projection on physical vector L2.

The 15 exports of `GradientProjection.lean` prove Fourier differentiation
with the correct 2 pi i factor for actual Maxwell coordinate derivatives.
The projection fixes Schwartz gradients, kills divergence-free Schwartz
fields and curls, and supplies the corresponding weak orthogonality laws.
The 16 exports of `HelmholtzProjection.lean` prove that its kernel is
exactly the annihilator of Schwartz gradients, using actual inverse Fourier
tests and a locally integrable spectral divergence. Consequently it is
exactly the orthogonal projection onto the closed span of those gradients.
Its range and variational uniqueness are proved, without a density premise.

The 20 exports of `StaticCoefficient.lean` construct bounded multiplication
by the square root of an actual measurable nonnegative susceptibility.
Self-adjointness and its square identity give the concrete positive block
I+sqrt(chi) P sqrt(chi), its inverse bound one, and norm-small perturbation
and residual estimates. The perturbation remains explicit abstract data;
its identification with a dynamic Maxwell integral operator is not assumed.

The nine exports of `DyadicKernel.lean` identify the actual dyadic Hessian
and its exact difference from the static Hessian. Cancellation of constant
and linear terms gives the pointwise component bound 14 k^2/(4 pi |x|)
when x is nonzero and |k||x|<=1. Local integrability, the distributional
source term and the Newton-convolution identification remain separate.

## Actual modal zeros and Lipschitz flux tests

The 24 exports of `ModalAlgebraicity.lean` prove algebraicity of any
exceptional multiple or shared nonzero determinant root for algebraic n,
by lifting the explicit matching polynomials into the actual algebraic
closure of Q in C. Such a root would give a nonzero algebraic number with
algebraic exponential. No full transcendence theorem is assumed or proved.

The eight exports of `ModalExistence.lean` construct actual arbitrarily
large determinant zeros by an inverse-coordinate contraction and complex
exponential periodicity. The proved finite exceptional set gives simple
zeros avoiding any prescribed finite point set. The eleven exports of
`ModalAsymptotics.lean` shrink the displacement to any positive tolerance,
compute actual exponential centers, and prove for real n>1 simple zeros
with negative imaginary part and arbitrarily large Re(z)/(-2 Im(z)).
Their imaginary parts approach -log((n+1)/(n-1))/(2n). Infinite-degree
separation and identification with full Maxwell operator poles remain open.

The 16 exports of `WeakPoynting/Lipschitz.lean` extend the actual real and
Hermitian weak Maxwell conservation identities to arbitrary compact
Lipschitz scalar tests supported inside the region. Rademacher integration
by parts proves derivative commutation with mollification; support control,
uniform bounds and a.e. convergence justify the L1 limit. No test-density
assertion is inserted as a hypothesis. The eleven exports of
`WeakPoynting/Aperture.lean` construct actual derivatives and tensor tests
for compact Lipschitz plane apertures, then derive integrable slice
functions, their weak derivative, continuous canonical flux and exact
interval increments. Eight exports of `WeakPoynting/Axial.lean` prove
the actual one-dimensional Lipschitz weak-test extension, product rule
and weighted endpoint identity. Fourteen exports of
`WeakPoynting/LipschitzBoundary.lean` combine the two: actual regional
Maxwell fields have canonical Hermitian flux values and a finite-slab
formula integrating the actual a.e. gradient of the tensor cutoff. Both
aperture and axial functions may be compact globally Lipschitz functions.
General tangential field traces and the identification of arbitrary
bundled W1-infinity classes with Lipschitz representatives remain separate.

Sixteen exports of `ModalMatching.lean` construct the actual two-amplitude
matching map from the factorial-series entries, prove its inverse and
determinant-zero kernel equivalence, and derive the actual punctured
inverse-residue limit. The nonzero residue has explicitly one-dimensional
image. The high-quality matching-pole existence theorem discharges the
root and simplicity hypotheses using the preceding construction. Full
vector Maxwell trace and operator identification remain separate.

Ten exports of `KernelIntegrability.lean` use actual Haar polar coordinates
to prove integrability of inverse distance and inverse squared distance
on every finite ball in Euclidean three-space. Compact-set containment
gives local integrability. The actual real-frequency scalar outgoing
kernel is measurable, locally integrable, and locally L2, including the
origin as a null set. No source distribution or convolution identity is
supplied as a hypothesis or asserted by this module.

Twenty-six exports of `HeatFourier.lean` prove the actual L1 convolution
Fourier identity, Gaussian normalization and Fourier transform, and both
Newton Gaussian scale representations. Eleven of `NewtonFourier.lean`
prove the absolute scale-space integrability and the actual scalar Newton
Fourier identity on Schwartz tests. Ten of `NewtonHessian.lean` derive the
full distributional Hessian symbol, its equality with the negative
longitudinal matrix, and the exact source identity `ΔN = -δ`. These include
the contact term; they do not replace the distributional Hessian by its
pointwise expression. The spatial convolution identification is proved below.

Five exports of `DynamicIntegrability.lean` prove actual local L1 and L2
membership of each dynamic dyadic remainder entry when `|k|R≤1`. Four of
`KernelEstimates.lean` prove the exact inverse-distance and inverse-square
ball integrals and the resulting quadratic local L1 mass bound for each
remainder entry. An operator-norm bound is not asserted by these modules.

Fourteen exports of `ModalDipole.lean` construct actual complex-frequency
dipole fields and verify their coordinate curls from the proved Riccati
ODE. Twenty-three of `ModalInterface.lean` identify the actual all-sphere
electric and magnetic tangential transmission conditions with the matching
matrix, prove both amplitudes and some exterior trace are nonzero, and
construct matching Maxwell fields at arbitrarily high quality factor.
The regular extension at the center is proved in ModalOrigin below; global weak
spherical assembly and the full outgoing resolvent remain separate.

Ten exports of `WeakPoynting/Energy.lean` derive the imaginary Poynting
identity and a genuine Caccioppoli estimate for regional weak Maxwell
fields with real nonzero frequency, permeability one, and `ε≥m>0`.
Weighted electric energy integrability is proved, rather than assumed.
Four exports of `WeakPoynting/EnergyLocalization.lean` give the actual
inner-set estimate with coefficient `2+4d²/(ω²m)` against magnetic energy
on the cutoff support. These results use a compact C1 cutoff and require
no derivative or upper bound of ε; they do not yet give magnetic H1
regularity or compactness.

## Spatial kernels, center regularity and magnetic weak derivatives

Nine exports of `PointSingularity.lean` prove genuine integration by parts
across a point in R3 using coordinate Fubini and one-dimensional integration
by parts. Seven in `RealKernelBounds.lean` extend the actual remainder
bound to every real frequency and radius, deriving local L1 membership.
Six in `KernelGradient.lean` give actual gradient bounds, local L1 and
the scalar kernel's first weak derivative. Thirteen in `KernelSource.lean`
derive the weak Hessian of phi_k-N, the complete outgoing Hessian
decomposition and `(Delta+k²)phi_k=-delta_0`. Seven in `DynamicSource.lean`
use actual derivatives of compact smooth tests to derive the full dyadic
static/dynamic decomposition and `(curl curl-k²)K=k² I delta_0`.
The singular Newton contribution is retained throughout.

Eleven exports of `NewtonConvolution.lean` prove actual spatial weak
convolution Fourier identities for every L1 source. Twenty-one in
`NewtonL2.lean` identify this response with the negative longitudinal
projection on Schwartz sources, prove genuine density and uniqueness,
and obtain its bounded L2 extension with norm at most one. Eleven in
`NewtonL1L2.lean` prove ordinary/Plancherel Fourier agreement for all
L1-intersection-L2 sources and their literal spatial response identity.
Nine in `StaticNewton.lean` apply it to compact material sources and
identify the actual weighted static volume block with the coercive
block, transferring its inverse bound one. The subsequent modules derive dynamic convolution bounds, a small-volume
inverse and actual compact-smooth-test Maxwell equations.

Forty-four exports of `ModalOrigin.lean` construct the entire regular
dipole radial profile from repeated divided differences of the
exponential. The actual center values and derivatives satisfy Maxwell's
equations, so the high-quality transmission field now has no excluded
center point. The spherical weak assembly and full resolvent pole
identification are not asserted by this module.

Six exports of `WeakPoynting/DivCurl.lean` prove the actual Schwartz
div-curl energy identity. Seven in `DivCurlCompact.lean` give genuine
compact representatives, reflected convolution and graph approximation.
Eight in `DivCurlRegularity.lean` construct all nine weak L2 derivatives
by completeness and derive their exact energy sum. Nine in
`LocalRegularity.lean` apply this to regional weak Maxwell fields with
nonzero real frequency and permeability one: the magnetic field is
divergence-free and has actual weak H1 representatives near every
compact interior set. Four in `RegularityBounds.lean` give the cutoff
derivative bound in terms of field norms, frequency, cutoff bounds
and an upper bound for the real permittivity. No derivative of that
coefficient is needed. Compact embedding is established in the subsequent modules. General
boundary traces remain separate.

## Actual source fields, material equations, spherical assembly and compactness

Sixteen exports of `L1Convolution.lean` construct the actual L1-kernel
convolution as a bounded L2 operator and prove its spatial identification.
Thirteen in `DynamicConvolution.lean` apply this to the actual truncated
dyadic remainder. Fourteen in `DynamicVolume.lean` remove that truncation
exactly on the material support, derive the weighted operator norm, and
prove an inverse, a unique volume unknown and its bound. Two in
`DynamicVolumeConstants.lean` simplify the sufficient smallness bound to
`252 * chi_max * k² * R² < 1`.

Five exports of `NewtonWeak.lean` prove the actual Newton response has zero
weak curl. Six in `KernelConvolution.lean` establish absolute compact-source
Fubini pairings and actual translated tests. Three in `WaveResponse.lean`
convolve the full dyadic source equation. Five in `FieldResponse.lean`
identify the actual spatial electric field and its curl-curl equation.
Ten in `MagneticResponse.lean` construct H from actual outgoing-gradient
integrals and prove curl E = ikH and curl H = -ik(E+rho).
These source identities use compact smooth tests and retain the singular
Newton contribution; they do not assume the response solves Maxwell.

Seven exports of `LocalVolumeResponse.lean` prove the actual electric field
is locally L2 using an exact cutoff on every observation ball. Seven in
`MaterialField.lean` derive rho = chi E from the volume equation without
dividing by possibly zero contrast. Seven in `MaterialMaxwell.lean` combine
this identity with the actual source equations to prove the dielectric
Maxwell equations on compact smooth tests. Five in
`IncidentLocalization.lean` construct the weighted L2 datum from the
incident field's local L2 restriction to the material ball. No global
L2 assumption is imposed on the incoming field. The subsequent modules
prove the regional C1-test upgrade and actual outgoing radiation.

Eleven exports of `SphereRemovable.lean` prove actual integration by parts
across a sphere using finite coordinate-line intersections. Twenty-three
in `RadialInterface.lean` instantiate it for genuine radial profiles and
coordinate-weighted potentials, with local derivative integrability proved.
Thirty-four in `ModalProfiles.lean` construct the actual continuous
potential and axial decomposition of the spherical electric field.
Twenty-one in `ModalWeak.lean` prove the global distributional Maxwell
equations on compact C2 tests, with the normal electric jump handled by
the weak gradient. Its high-Q existence result gives actual nonzero fields,
real positive material bounds and the exact outgoing Hankel exterior.
It does not identify an isolated pole of the full Maxwell resolvent.

Nine exports of `WeakPoynting/PartialSmoothing.lean` prove genuine derivative
approximation and compact-C1 test transfer. Seven in `Translations.lean`
derive translation and mollification bounds from actual weak L2 derivatives.
Ten in `Compactness.lean` prove compact closure of the supported weak H1
ball, using actual smoothing, Arzela-Ascoli and finite-cover transfer.
Six in `MagneticCompactness.lean` apply this to bounded regional Maxwell
families. Eight in `ElectricControl.lean` derive actual electric L2 control
by magnetic cutoff energy. Eleven in `MaxwellCompactness.lean` apply the
bound to differences to obtain full local E/H compactness and a strong
L2 subsequence for one fixed positive bounded permittivity. A common open
neighborhood and actual a.e. agreement are part of the conclusions.
These results do not assert compactness uniformly over varying coefficients.

## Actual radiation, regional fields and meromorphic shell response

Five exports of `LocalConvolution.lean` and three of `MagneticLocal.lean`
prove actual local L2 magnetic fields. Eight of
`WeakPoynting/InteriorTestDensity.lean` and four of `RegionalCurlUpgrade.lean`
approximate actual compact C1 tests inside the open region and pass the
weak-curl identity. Six of `SmallVolumeMaxwell.lean`, eight of
`MaterialHCurl.lean` and four of `MaterialPower.lean` construct actual
small-volume material fields, their regional H(curl) graphs and physical
local power conservation. Eight of `WeakPoynting/MaterialCaccioppoli.lean`
control magnetic and electric-curl energy by outer electric energy.

Seven exports of `NewtonExterior.lean` and fifteen of
`NewtonExteriorResponse.lean` identify the actual exterior electric field
with the ordinary dyadic integral. Nine of `ExteriorContinuity.lean` and
nine of `ExteriorMaterial.lean` construct continuous representatives on
the whole exterior. Thirteen of `ScalarRadiation.lean`, eight of
`DyadicRadiation.lean` and fourteen of `MaxwellRadiation.lean` give explicit
inverse-square radiation-defect bounds and the actual Silver--Müller
limit at spatial infinity. Three of `OutgoingMaterial.lean` combine the
volume inverse, local equations, regional H(curl), continuous exterior
representatives and outgoing condition for one small-volume solution.
This is existence under the explicit sufficient smallness bound; uniqueness
among all outgoing PDE solutions and arbitrary-size solvability are separate.

Ten exports of `ScalarExterior.lean`, eleven of `ScalarExteriorSecond.lean`
and six of `ScalarExteriorRegularity.lean` differentiate the actual source
integrals, prove the exterior scalar Helmholtz equation and establish C2
regularity. Fourteen of `L2KernelCompact.lean` prove compactness of the
actual L2-kernel convolution after a bounded input map with common compact
support. Ten of `DynamicVolumeCompact.lean` apply this to the actual
weighted dyadic remainder for every finite support radius, without smallness.

Twelve exports of `ModalLocal.lean` and fourteen of `ModalHCurl.lean`
give local integrability and genuine nonzero regional H(curl) modal fields.
Nine of `ModalShell.lean` construct the actual electric/magnetic pair in
shell L2. Thirteen of `ModalFieldResidue.lean` prove the operator-norm
residue and its nonzero field image. Seventeen of `ModalShellAnalytic.lean`
prove Banach-valued analyticity of the actual shell field. Fourteen of
`ModalFieldPole.lean` construct its analytic regularization and prove
standard meromorphic order minus one at the constructed high-Q zeros.
The response here maps two spherical matching data to actual shell fields;
identification with a pole of the full Maxwell resolvent is still required.

## Actual far-field power and analytic volume family

The continuation adds 348 audited declarations in 24 modules. The compact
operator alternative is proved in `CompactPerturbation` (6 exports) and
`CompactAlternative` (7); `VolumeFredholm` (7) applies the actual static
preconditioner and compact remainder, and `VolumeAlternative` (8) derives
arbitrary-data solvability conditional on homogeneous volume uniqueness.
That remaining uniqueness premise is explicit.

`ExteriorSmooth` (9) and `ExteriorClassical` (18) prove actual exterior
smoothness and classical Maxwell/Gauss equations. `ScalarFarField` (8),
`MaxwellFarField` (15) and `FarFieldPower` (9) prove actual compact-source
far-field limits, transversality and the directional power formula.
`AngularPower` (17) derives a uniform angular bound and the actual spherical
power limit by dominated convergence. Its nonnegative limit is the integral
of half the squared electric amplitude. `SphereMeasure` (3) proves that the
ordinary angular measure is positive on every nonempty open patch.

`ComplexGreenKernel` (15) and `ComplexDynamicKernel` (14) construct the actual
complex-frequency kernel and local L1/L2 cancellation bounds. `L2Parametric`
(2) proves Banach L2 differentiation by dominated convergence of squared
difference quotients. `ComplexKernelAnalytic` (18) applies it to the actual
truncated remainder. `L1KernelOperator` (18) constructs bounded linear
dependence of L2 convolution on its L1 kernel and the finite-support L2-to-L1
map. `ComplexConvolutionAnalytic` (37) assembles the genuine entire compact
volume pencil, its exact real-frequency restriction, static factorization
and invertible value at zero. The subsequent meromorphic-inverse construction
and isolated noninvertible values are now proved below.

`KernelReciprocity` (29) and `NewtonReciprocity` (16) prove non-Hermitian
bilinear reciprocity of the actual weighted volume block and actual
untruncated compact-source electric fields. The singular Newton source term
is retained. These results do not yet identify the reciprocal resonance norm.

`ModalPoleMode` (9), `ModalOutgoing` (22) and `ModalPoleRadiation` (7) tie the
same nonzero shell residue to global weak Maxwell fields and the actual
complex-frequency radiation condition. `ModalScaling` (24) gives prescribed
positive real frequency and arbitrary quality factor by actual spatial
dilation. `ModalScaledPole` (30) proves exact meromorphic order minus one and
the residue factor 1/s for the scaled physical shell response. Its shell
measure pushes forward to ordinary spatial volume, and its residue is the
same dilated actual field. This is a spherical matching response; full
resolvent isolation across all angular degrees remains unproved in Lean.

## Zero outgoing power and the meromorphic volume inverse

A further 175 declarations in 18 modules close two analytic bridges.
`PolarIntegration` (5), `RadialPowerTest` (27), `RadialWeight` (19), and
`RadialFlux` (9) derive zero far-field power from actual weak Maxwell
conservation, using a genuine compact radial test, exact Euclidean polar
integration, and a nonnegative radial weight with strictly positive mass.
The zero-power conclusion is not assumed. `AngularPowerZero` (6) upgrades
zero power to both amplitudes vanishing in every unit direction.
`HomogeneousVolumePower` (11) derives all these hypotheses from any actual
homogeneous volume solution, without support smallness. `AngularEnergy`
(8) proves actual unphased surface-energy limits. `ExteriorHelmholtz` (8)
derives the actual component Helmholtz equations from exterior Maxwell and
Gauss equations. Exterior Rellich and material continuation remain separate.

`HilbertFiniteRank` (3) constructs finite-dimensional approximations from
compact image nets and orthogonal projection. `FiniteRankSchur` (11)
proves the exact typed Schur criterion and Woodbury inverse.
`FiniteDimensionalDeterminant` (3) proves actual determinant analyticity and
its invertibility criterion. `LocalDichotomy` (3) proves connectedness
propagation. `LocalFredholmReduction` (16) combines these with a locally
invertible regular factor to prove punctured invertibility of an anchored
entire compact pencil at every center. `FiniteMeromorphicInverse` (14)
constructs the actual analytic adjugate and meromorphic finite inverse.
`MeromorphicOperator` (2) and `AnalyticCompactInverse` (2) transfer it through
the actual Woodbury formula. `VolumeAnalyticAlternative` (12) applies this
to the actual volume operator: its exceptional frequencies form a closed
discrete set, finite in bounded sets, its inverse is meromorphic, and actual
noninvertible values are genuine poles. Finite-rank principal Laurent
coefficients and real-frequency homogeneous uniqueness remain further work.

`ModalMatchingNorm` (16) proves the genuine derivative pairing and normalized
rank-one residue for the finite matching pencil. This is not yet the
reciprocal physical-volume resonance norm or full modal multiplicity.

## Explicitly outside the formalization

This is **not complete formal verification of OQ14**. Maxwell derivatives
and weak-test identities, complete weak-curl graphs and weak divergence of
curl are represented. The source does not yet construct H(curl) trace theory,
general boundary traces, arbitrary-size outgoing solvability, the conical spectrum,
Runge approximation, rounding, finite-rank principal Laurent coefficients, or
the reciprocal physical resonance norm. The complete written modal theorem is not yet a Lean
theorem. The written unrestricted channel counterexample is likewise not
yet a Lean theorem. No hypothesis or custom axiom stands in for either
missing formal conclusion. The exact remaining library development is
listed in `../reviews/maxwell_formalization.md`.

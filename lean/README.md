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
`WeakPoynting/EnergyLocalization.lean`. The continuation adds `PointSingularity.lean`, `RealKernelBounds.lean`, `KernelGradient.lean`, `KernelSource.lean`, `DynamicSource.lean`, `NewtonConvolution.lean`, `NewtonL2.lean`, `NewtonL1L2.lean`, `StaticNewton.lean`, `ModalOrigin.lean`, `WeakPoynting/DivCurl.lean`, `WeakPoynting/DivCurlCompact.lean`, `WeakPoynting/DivCurlRegularity.lean`, `WeakPoynting/LocalRegularity.lean`, and `WeakPoynting/RegularityBounds.lean`. The spatial-source, volume, spherical-assembly and compactness modules described below are also registered. 5238 exported
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
compiler and mathlib revision, builds all 627 registered modules, and audits all 5238
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
noninvertible values are genuine poles. The finite-rank Laurent coefficients
are proved in the continuation below; global homogeneous uniqueness for explicit material-cell geometry is
proved in the continuation below.

`ModalMatchingNorm` (16) proves the genuine derivative pairing and normalized
rank-one residue for the finite matching pencil. This is not yet the
reciprocal physical-volume resonance norm or full modal multiplicity.

## Exterior Rellich and finite-rank Laurent coefficients

A further 198 declarations in 24 modules derive actual exterior uniqueness
and complete the finite-rank principal-part construction.
`FiniteRankAnalyticJets` (6), `CompactLaurent` (1), and `VolumeLaurent` (1)
give convergent Laurent expansions for the actual inverse modulo an analytic
regular part, with finite-rank coefficients from a fixed finite-dimensional
Schur factor. `ComplexVolumeReciprocity` (9) proves actual complex-frequency
bilateral reciprocity and reciprocity of the operator derivative.

`SpherePolynomial` (5), `HarmonicPolynomial` (21), and
`FischerDecomposition` (11) prove actual polynomial differentiation,
Euler's formula, finite Fischer decomposition, and uniform density of the
homogeneous harmonic restrictions. `HarmonicMomentSeparation` (3) proves
pointwise separation using the actual angular measure.

`HelmholtzTestCalculus` (7), `ExteriorGreen` (11), `RadialNormTest` (8),
and `ComplexPolarIntegration` (8) give actual spatial test derivatives,
local integration by parts, compact annular tests, and the complex polar
identity. `SphericalMomentEquation` (9) derives the actual weak radial
equation from the spatial Helmholtz equation. `RadialMoment` (17),
`RadialMomentRegularity` (4), `RadialMomentWeights` (9),
`OneDimensionalGreen` (11), and `RadialMomentClassical` (4) establish its
actual derivatives and classical radial flux equation. `RadialRellich` (20)
and `RadialMomentODE` (4) prove the radial nondecay and uniqueness argument.

`ScalarExteriorRellich` (3) consequently proves pointwise exterior
vanishing from the actual positive-frequency Helmholtz equation and
vanishing surface mass. `ComponentAngularEnergy` (9) and
`MaxwellExteriorRellich` (5) apply this to the actual electric and magnetic
volume fields: every homogeneous volume solution has both fields zero
outside the material support, without a support-smallness premise.
The next continuation supplies interior propagation and global uniqueness
for explicit material-cell geometry.
`SpatialKernelAnalytic` (12) exposes actual kernel analyticity away from
the source; it does not assert analyticity of arbitrary PDE solutions.

## Weak continuation and material-cell global uniqueness

A further 150 declarations in 22 modules derive actual scalar continuation
and global Maxwell volume uniqueness for explicitly specified material-cell
geometry. `AnnularMoment` (15), `AnnularMomentClassical` (2), and
`AnnularMomentEquation` (3) prove actual finite-annulus moment calculus and
the radial equation from actual spatial Helmholtz tests.
`RadialIntervalUniqueness` (5) and `RadialIntervalFlux` (4) give genuine
finite-interval ODE uniqueness. `HelmholtzBallContinuation` (4) combines it
with actual harmonic density to prove whole-ball zero from a zero germ.
`HelmholtzTranslation` (11), `LocalZeroPropagation` (4), and
`HelmholtzUniqueContinuation` (3) prove smooth connected-domain continuation.

`LocalHelmholtzRepresentation` (10) proves the actual compact and local
Green representation. `WeakHelmholtzRegularity` (7), `HelmholtzMollifiers`
(5), and `HelmholtzMollifierZero` (5) prove actual convolution derivatives,
shrinking support, eventual classical PDE and zero germs, and genuine AE
convergence. `LocalAEZeroPropagation` (6) proves the countable-cover step;
`WeakHelmholtzContinuation` (4) gives actual weak connected-domain
continuation. A smooth representative or solution analyticity is not assumed.

`RegionalMaxwellHelmholtz` (22) derives Gauss and scalar weak Helmholtz from
literal regional Maxwell tests, including the actual H(curl) interface.
`RegionalMaxwellLocalization` (10) derives those regional equations from
global variable-material Maxwell tests whenever the material-weighted field
agrees with a constant material. `RegionalMaxwellContinuation` (6) uses
actual PDE continuation to carry electric zero across an open interface
bridge covered almost everywhere by two cells. `MaterialCellGraph` (7)
proves geometric reachability and AE cover globalization.

`HomogeneousVolumeUniqueness` (7) gives actual component local integrability
and proves that electric AE zero forces the original homogeneous volume
unknown to vanish. `PiecewiseMaxwellUniqueness` (5) combines exterior
Rellich, interface propagation, cell reachability and the actual Fredholm
alternative. It proves global uniqueness and invertibility with no support
smallness, for an explicit geometric partition: positive constant material
on open preconnected cells, AE coverage, actual bridge reachability, and an
exterior seed point. The PDE propagation and zero-kernel conclusion are
proved, not supplied as premises. Concrete construction geometries still
need instances of this partition data. `MaxwellZeroField` (5) derives
magnetic AE zero from electric AE zero using actual global weak Maxwell
and the fundamental lemma.

## Concrete radial geometry, scattering and positive-real regularity

A further 51 declarations in five modules instantiate actual finite-layer
geometry and assemble its scattering fields. `RadialMaterialCells` (18)
proves ball, annulus and exterior connectivity, sphere-null interfaces and
explicit interface bridges. `FiniteRadialPartition` (12) proves the actual
finite ordered-radius cover, every adjacent bridge, reachability and an
exterior seed. `RadialMaxwellUniqueness` (6) consequently proves actual
global homogeneous zero, an invertible volume operator and unique volume
solutions for any finite number of concentric positive-material layers,
without a smallness condition or assumed geometric certificate.

`PiecewiseScattering` (7) constructs actual global weak Maxwell fields from
the unique volume solution for the geometric-partition class. It proves
local square integrability, material self-consistency, exterior continuity
and the actual inverse-square Silver--Mueller defect bound and radiation
limit. This proves existence of physical fields and uniqueness of the
volume unknown; equivalence with every possible outgoing PDE solution
has not been established. `PiecewiseRealSpectrum` (8) proves that the actual
complex volume pencil has no positive-real exceptional frequencies under
the partition hypotheses. Its inverse is analytic in genuine complex
neighborhoods of every such frequency, and its fixed-source evaluation
agrees with the actual real-frequency solution. This is not full modal
isolation or the final hotspot theorem.

## Angular estimates, concrete inclusion geometry and plane tails

A further 156 declarations in 14 modules extend actual continuum estimates.
`SphereAngularSymmetry` (4) derives angular-measure invariance from Euclidean
volume and orthogonal maps. `ConicalAngularTrial` (23) proves the literal
cap-weighted coordinate trial has weighted mean zero, positive denominator
and Rayleigh quotient below 2. Its tangent vector represents the actual
coordinate derivative. Eigenfunction attainment is not inferred from this
trial alone.

`HankelEnergy` (14) derives the actual all-degree outgoing energy identity,
its limit 2 and low-angular-range bounds. `HankelRealBasis` (15) identifies
the real basis and determinant 1, and bounds the actual forward/inverse
states. `HankelCoefficientBounds` (16) proves reversed factorial coefficient
estimates and actual Hankel/derivative exponential bounds.
`HankelIntermediateBounds` (6) derives uniform intermediate-range estimates.
High-barrier estimates and the complete all-order Green limit remain open
within this formalization.

`DisjointBallGeometry` (18), `DisjointBallCells` (8), and
`DisjointBallPartition` (2) construct actual paths outside finitely many
strictly separated balls, sphere-null coverage, interface bridges and the
Maxwell partition. `CavityBallGeometry` (13) proves actual paths in a bounded
cavity via a continuous radial clamp and finite radial pushes.
`CavityBallBridges` (3) and `ShellInclusionCells` (6) add actual interfaces,
coverage and reachability for inclusions inside a single enclosing shell.
These are geometric constructions, with no supplied connectivity conclusion.

`PlaneInverseCube` (10) proves genuine two-dimensional tail integrability
and its inverse-radius integral. `MaxwellPlaneTail` (18) proves cancellation
of the leading normal flux of actual compact outgoing Maxwell sources on
the plane. It obtains an inverse-cube bound and integrable tails for both
ordinary power and cross-source flux. Constants retain source-radius
dependence. Whole-plane source continuity and uniform remote-stack limits
are subsequent work; these tail bounds do not by themselves close the
unrestricted channel construction.

## Actual angular profiles, device coefficients and outgoing load

A further 205 declarations in 12 modules derive actual constructions.
`CapLegendreSeries` (45) proves convergent series, their derivatives and
Legendre equations, parameter continuity and exact endpoint identities.
`CapAngularShooting` (17) obtains an actual matching root with angular
exponent in (0,1). `CapSturmLiouville` (30) constructs the literal odd
piecewise profile, identifies its derivative away from interfaces, proves
three-interval integration by parts and the weighted weak equation, and
normalizes its genuine positive weighted mass. These are one-dimensional
results. The subsequent sphere H1 section supplies the actual angular
lifting. The finite-frequency Maxwell conical coefficient remains unfinished.

`PlaneSourceKernel` (21) derives actual compact kernel bounds and source
subtraction. `MaxwellPlaneL1` (8) proves whole-plane flux integrability and
L1 continuity under source L1 convergence. A fixed source radius and a
positive plane gap are required; the constants need not remain bounded
when either varies.

`LayeredInclusionCells` (10) constructs finite shell/inclusion partitions;
`LayeredInclusionScattering` (11) applies actual Maxwell solvability.
`LayeredInclusionCoefficient` (18) constructs the literal indicator-sum
susceptibility, its common bound, exact cell values and compact support.
`LayeredDeviceScattering` (11) obtains the actual volume solution, physical
fields and positive-frequency inverse regularity for this coefficient.
The final scattering theorem no longer takes partition, support or cell
material agreement as supplied conclusions.

`DynamicSupportVolume` (13) bounds the actual dynamic remainder by the
square root of material volume, at fixed enclosing radius. It includes
finite-ball volume bounds and a quantitative inverse estimate. This is
not the sharper two-thirds volume power used elsewhere in the paper.

`HankelPolynomial` (14) derives a third-order polynomial identity for the
actual finite outgoing/incoming product, its coefficient recurrence,
degree bound and coefficient nonnegativity. `HankelPositive` (7) identifies
that product with the actual squared outgoing norm and proves the outgoing
radial load is nonpositive in every degree at every positive radius.
The subsequent section adds regular barrier estimates and actual stack
propagation. All-order Green convergence and complete counted-space flux
identities remain work in progress.

## Constructed radial sources, angular measure and material response

A further 209 declarations in 18 modules are independently audited.
`AxialCoordinates` (13) proves the actual Jacobian, injectivity and volume
change of variables outside a null plane. `SphereAxialMeasure` (20)
derives the sphere surface measure by cones, the latitude/azimuth integral
formula and zero measure of every latitude. The subsequent sphere H1
section supplies arbitrary-test angular weak lifting.

`RiccatiRaising` (9), `RiccatiSeriesCoefficients` (11),
`RiccatiOriginSeries` (16), and `RiccatiOriginLimits` (14) derive the
entire regular series, its identification with the actual Hankel-defined
solution off zero, and both normalized origin limits. The entire series
is the extension at zero; the Laurent definition is not substituted there.
`RiccatiBarrier` (9) proves positivity of the regular solution and its
derivative. `RiccatiLogDerivative` (9) proves both logarithmic-derivative
bounds by a weighted Wronskian. The subsequent section supplies the
Gaussian lower bound and actual all-derivative scalar high-degree tails.

`RadialLayer` (7) constructs homogeneous bases, actual solutions and
endpoint transfers. `RadialPropagation` (10) proves energy and barrier
estimates from those ODEs. `RadialStack` (17) derives estimates for exact
shared-radius chains, common material bounds and conserved imaginary
load. `RadialSource` (16) constructs outgoing core coefficients, a nonzero
denominator, negative imaginary reaction, low-order bound, core ODE,
normalized boundary matching and scalar Green branch-derivative jump.
`RadialLoadBounds` (8) derives the barrier reaction bound and both
normalized core source bounds. Full spatial Maxwell Green reconstruction
and all-order convergence are not already formalized by these results.

`SphereReactionKernel` (12) defines the literal sphere-integral parity
reaction and derives its bounds. `BoundedMaterialKernel` (17) constructs
the weighted L2 integral operator with its material-volume bound.
`ParityReactionVolume` (7) and `SmallParityInclusions` (5) derive uniform
invertibility for gain b/a and small finite balls. `ParityMaterialField`
(9) derives the unique inverse solution, norm estimates and actual
material relation for this explicit kernel. Identification with the
finite physical stack and final shrinking-gap whole-plane estimates remain
separate. Exact static sphere polarization is established below.

## Actual sphere H1, scalar stack limits and spherical inclusion response

A further 358 declarations in 36 modules have complete-source and independent
pinned-compiler audits. The new aggregate revision still needs its own clean
combined build. The completed clean 2804 release is preserved separately.

`CapSturmEndpointTest`, `CapProfileFirstOrder`, `SphereAxialTests`,
`SphereCapWeak`, `SphereAxialSurface`, `SphereSurfaceTests` and
`SphereSurfaceFubini` derive the actual spherical weak identities for
arbitrary ambient C1 tests, including integrable pole behavior, periodic
azimuth cancellation and the curvature term in all three tangential
gradient components. `SphereCapH1` proves L2 membership, actual weak
tangential differentiation, a nonzero L2 class, positive mass and a normalized
H1 eigenfunction from the actual shooting root, with exponent in (0,1).
Its H1 definition explicitly states these distribution identities; no
equivalence with an abstract manifold Sobolev library is claimed.
`ConicalCapField` constructs literal spatial potential and electric
candidate, proves global Borel representatives, local L2 membership,
continuity of the potential at the origin and a nonzero angular electric
factor. Its spatial weak-gradient and transmission equations, and the
finite-frequency Maxwell correction, are still subsequent work.

`RiccatiBarrierNormalization` and `RiccatiGaussianBound` prove the actual
Gaussian regular lower bound. `RadialHighOrderBound`, `RadialHighOrderTail`
and `RadialStackHighTail` derive actual high-degree reaction estimates,
absolute weighted summability and decay faster than every fixed inverse
power of the radius for common bounded-index chains.
`RadialReactionKernel` and `RadialReactionTail` identify the literal scalar
Green reaction and its first mixed derivatives. `RiccatiCompactDerivatives`,
`RadialEntireReaction` and `RadialEntireTail` extend these scalar results to
every fixed derivative order on compact complex disks, including the
analytic origin. Constants and larger comparison disks are independent of
degree and radius. `RadialIntermediateBound` supplies an actual exponential
bound in the complementary degree window. Summing that window and the full
spatial dyadic reconstruction remain separate requirements.

`RadialGluing` proves literal radial matching. `RadialReference` constructs
the exact constant-coefficient sine/cosine transfer and quarter-wave powers.
`RadialApproximation` derives the actual radial/reference error of order
R^-2 for fixed layer width and degree. `RadialFiniteLimit` constructs
physical shared-radius lists and proves their forward finite-stack limit.
`RadialBackwardLimit` proves inverse transfer identities, the backward
finite-stack limit and equality with the existing actual traversal.
These are fixed-degree, fixed-finite-stack results. The outgoing coefficient
parity limit and spatial Green identification are not supplied as premises
or inferred from those results alone.

`StaticBallPotential`, `StaticBallHessian`, `StaticBallL2`,
`StaticBallSchwartz`, `StaticBallFourier`, `StaticBallSymbol` and
`StaticBallNewton` derive the genuine uniform-ball potential, weak Hessian,
Schwartz identities, Fourier symbol and its identification with the existing
Newton operator. The interior action is actually -P/3.
`StaticSpherePolarization` proves the exact isolated-sphere response.
`StaticBallTranslation` and `StaticBallCentered` establish it at any center
through actual measure-preserving translation and translated weak pairings.
`StaticSphereMaterial` proves the exact weighted block and inverse action;
the weighted trial is 3 sqrt(chi)/(chi+3) E and its physical polarization is
3 chi/(chi+3) E, including chi=0. Quantitative varying-field, multiple-ball,
finite-frequency and shrinking-gap source estimates remain subsequent work.

## Actual static cone, complete scalar stack sum and finite sphere asymptotics

A further 242 declarations in 40 modules have complete-source and independent
pinned-compiler audits. Registered totals are 3404 reports, 323 modules and
295 libraries. The new aggregate revision needs its own clean combined build;
the completed clean 3162 release is preserved separately.

`RadialPhaseLimit`, `RadialParityLimit` and `RadialPairedFamily` derive the
actual outgoing coefficient limit along a common sequence of physical
finite radial stacks, for both polarizations and common material bounds.
`RiccatiFactorialTail`, `RadialMiddleTail`, `RadialLowTail` and
`RadialFullMajorant` combine the actual low, intermediate and high degree
estimates into a fixed summable majorant. `RadialScalarSeries`,
`RadialScalarUniform`, `RadialPairedScalar` and
`RadialScalarDifferentiation` prove convergence of the entire scalar sum
and its actual mixed derivatives, uniformly on compact complex disk
products and with each fixed degree weight. These are actual derivatives
of the sum, rather than merely convergent formal differentiated series.
The spatial dyadic Maxwell reconstruction remains a separate requirement.

The conical radial, angular and spatial test modules prove the actual weak
gradient, zero weak curl and zero weighted divergence of the literal
singular static field. `ConicalStaticField` assembles existence from the
actual shooting root, with exponent in (0,1), finite local energy, common
positive permittivity bounds and uniform blowup on an open cone of positive
measure. The singular field is static. Preserving its nonzero coefficient
under a positive-frequency Maxwell correction remains unfinished.

The static sphere residual, forcing, scale and small-error modules derive
the actual inverse error from incident variation. The finite sphere modules
extend this to multiple separated balls, including moving centers, with
actual cross-Newton interactions and derived perturbation smallness.
`FiniteSphereAsymptotics` proves the actual weighted and physical L2 errors
of order a*sqrt(a), and coordinate L1 error of order a^3, under explicit
incident derivative and center-amplitude bounds of order 1/a. It uses the
actual parity limiting kernel; its identification with finite physical
stacks remains a separate step. `StaticBallDipole` proves the actual source
moment and exact exterior Newton point-dipole identity.

`DebyeCalculus` and `DebyeMaxwell` derive genuine local vector Maxwell
equations for both Debye polarizations from an actual smooth scalar
Helmholtz solution. `LocalRadialHarmonic` derives the spatial scalar equation
from an actual radial ODE and a homogeneous harmonic polynomial.
`EntireFactorialSeries` proves actual differentiation of factorially bounded
entire series. These bridges do not by themselves supply the normalized
spherical basis, its addition identities or full spatial Green series.

## Actual conical Maxwell continuation, normalized harmonics and plane bounds

A further 513 declarations in 70 modules have complete-source and independent
pinned-compiler audits. That revision contained 3917 reports, 393 modules and
365 libraries. Its clean aggregate, diagnostics and matching paper passed;
the complete 3917 release remains preserved separately.

Actual all-degree regular scalar and TE/TM Maxwell waves now include the
origin; outgoing waves satisfy the equations on punctured space. Riccati
profiles agree with the physical radial layer transfer states. Tangential
E/H and normal D/B match at adjacent interfaces with the correct TE/TM
material factors. Global interface gluing, radiation identification and
the full spatial dyadic Green reconstruction still require assembly.

The actual polynomial harmonic spaces have finite orthonormal bases and
dense union. Their rotation action yields the diagonal addition identity
and evaluation bounds; the rank has a proved cubic upper bound. Literal
three-coordinate Lagrange interpolation derives polynomial-times-exponential
coefficient bounds for the actual normalized representatives, and hence
all-order compact spatial derivative bounds, including the origin.
Cross-degree orthogonality and the full vector angular basis are separate.

The conical static field is localized using an actual vector potential
whose weak curl is its dielectric displacement. The resulting annular source
is compact and L2. Actual Schwartz gradient/divergence identities prove its
static volume equation and exact inverse identity. The actual positive-
frequency inverse, with frequency-dependent annular forcing, converges to
this field in L2; its weighted error is O(k^2). The spatial Green fields
satisfy both Maxwell curl equations in the inner conical region. Their
regional H(curl) fields and Gauss law are proved. Genuine H1 annular angular
tests have the literal polar gradient and same-support smooth approximation.
A general actual scalar-potential decomposition has a continuous correction
bounded by k^2 times the source norm. The remaining conical step is to derive
the singular projection system and retain its nonzero coefficient, followed
by Runge approximation and rounding. L2 convergence alone does not prove
that coefficient remains nonzero.

The actual finite-sphere inverse has derived reaction and gain errors.
Continuous Newton representatives identify exact exterior point dipoles on
the plane without restricting an ambient almost-everywhere identity to a
null set. Their whole-plane static dipole error is O(a^2). Genuine plane
inverse-distance integrals give a gap-independent local dynamic bound;
inverse-square integrals give the magnetic logarithm. Actual finite-sum
electric/magnetic disk L1 bounds and source-difference estimates follow.
Whole-plane coherent flux for the actual Herglotz family and finite-stack
identification remain essential.

## Actual Green coefficients, conical projection and whole-plane errors

A further 474 declarations in 76 modules have complete-source and independent
pinned-compiler audits. That revision contained 4391 reports, 469 modules
and 441 libraries. Its clean aggregate, diagnostics and matching paper
passed; the complete 4391 release remains preserved separately. The
following description records the scope at that revision.

Actual cross-degree orthogonality gives the complete scalar complex harmonic
basis. Actual vector harmonic normalization, tangency and orthonormality are
proved; completeness of the vector family is separate. The literal outgoing
scalar Green kernel has its actual radial moment equation, regular interior
and outgoing exterior selection. Smooth compact tests derive continuity and
the exact source jump. Wronskians fix the physical coefficient, including the
sign relating it to the reduced radial Green function. The resulting angular
L2 expansion is proved for the actual kernel. Spatial derivative convergence,
the dyadic normalization and full finite-stack identification remain.

Actual finite-chain TM electric fields have only normal jumps. An explicit
normal primitive and integration by parts through countably many spheres
prove their weak curl. Actual magnetic profiles have locally integrable
partials and a global weak curl. Both Maxwell equations therefore hold through
all interfaces for compact tests inside the layer annulus. The clipped core
is excluded from this result; full core/exterior assembly remains.

For the actual conical Maxwell field, the scalar Green potential and continuous
O(k^2) correction yield literal angular moments. Actual Hdiv testing, polar
integration, AE transfer and finite-energy estimates derive the two weak radial
equations. Smooth-test weak derivatives have genuine continuous representatives
on open real sets, exact integral increments and classical derivatives for
continuous forcing. This constructs the actual classical conical system on its
finite inner interval. Wronskian classification and actual L2 radial energy
remove the negative power, leaving c r^nu plus the literal particular solution.
The coefficient c is not yet proved nonzero at positive frequency. Retention,
Runge approximation, rounding and the full normalized modal statement remain.

Literal sphere-integral electric and magnetic parity columns, and their finite
sums, satisfy both global vacuum Maxwell equations. Actual volume-response
coherent flux against these finite illuminations is integrable on the whole
plane, with proved local singular estimates and an inverse-cubic tail.
For a gap gamma*a, source error O(a^3) and coefficient mass O(1/a), the actual
coherent L1 error tends to zero. The finite-ball material inverse supplies
the source error and geometric support conditions. Incident coefficient
construction, complete physical-stack identification and final all-vector
channel assembly remain.

## Actual vector kernel, separated excitation and complete plane flux

The continuation adds 847 independently audited reports in 158
modules. Registration now contains 5238 selected reports, 627
modules and 599 libraries. Exact source and independent compiler
hashes are in `../reviews/audited_constructions_5238.json`. The matching clean aggregate is recorded in
release provenance; individual audits alone do not certify that build.

The actual transverse harmonic family is complete, with derived complex
expansion and literal plane-wave coefficients. The genuine spherical
reaction integral has its normalized regular Maxwell dyad expansion.
Exact regular source moments, outgoing ray amplitudes and free-source
coefficients fix all signs and constants. Actual all-layer TM/TE fields
satisfy both weak Maxwell equations and outgoing radiation away from the
point source. The source-state core is singular, not a regular origin.

The normalized paired vector series converges, together with every fixed
finite derivative order, uniformly on compact core regions to the explicit
central-inversion gain kernel. Origins and coincident points are included;
the required radius depends on the derivative order. Genuine half-turn
covariance supplies the plane-wall formula on the specified invariant
sector. Full outgoing dyadic identification, summation through interfaces
and the perturbed finite-stack response still need assembly.

Actual conical fields now retain a nonzero singular coefficient at every
sufficiently small positive frequency. This includes separated sources
vanishing on the whole material ball: actual Maxwell equations, weak
potential, gradient graph, projected radial system, finite energy and a
nonzero static annular pairing derive the coefficient. Genuine vacuum
Runge density, finite transverse plane-wave approximation and material
inverse transfer are proved. Explicit rounded families preserve high
positive-volume superlevel sets under strong convergence. Assembly of
these ingredients into final finite-illumination rounded devices remains.

For literal finite parity-column illuminations, the actual inverse total
plane flux converges in whole-plane L1 to the exact static dipole flux.
Both coherent and quadratic self terms are controlled with actual source
mass, error and moving-gap bounds. Symmetric scalar Helmholtz waves,
their Debye fields, scalar edge-jet interpolation and angular jet integrals
are derived. Restricted finite even-degree/even-azimuthal TE interpolation,
physical input power and Gram balancing remain essential; arbitrary
finite point columns do not supply that sector by themselves.

Actual reciprocal modal residue normalization, infinite-degree pole
isolation and simultaneous three-dimensional modal maxima in the
prescribed plane patch are still required. Neither final OQ14 construction
is yet a complete Lean theorem.

## Explicitly outside the formalization

This is **not complete formal verification of OQ14**. Maxwell derivatives
and weak-test identities, complete weak-curl graphs and weak divergence of
curl are represented. The source does not yet construct H(curl) trace theory,
general boundary traces, full geometric instances and physical scattering
assembly for the final constructions, the final rounded finite-illumination
device and prescribed modal maxima, or the reciprocal physical resonance norm. The complete written modal theorem is not yet a Lean
theorem. The written unrestricted channel counterexample is likewise not
yet a Lean theorem. No hypothesis or custom axiom stands in for either
missing formal conclusion. The exact remaining library development is
listed in `../reviews/maxwell_formalization.md`.

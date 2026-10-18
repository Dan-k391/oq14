# Maxwell formalization audit

Status: genuine continuum Maxwell calculus and an actual whole-space L2 weak-curl graph are implemented; the complete OQ14 theorems are **not formally verified**.

The new source is `lean/Maxwell.lean`, in namespace `OQ14.Maxwell`. Its spatial domain is `EuclideanSpace ℝ (Fin 3)`, its fields have complex coordinate values, and every coordinate derivative is mathlib's real Fréchet derivative evaluated on a coordinate basis vector. Curl, divergence, the complex cross product, and the integrals are actual mathematical operations. `MaxwellAt` is the explicit pair of curl equations for the `exp(-i omega t)` convention. It does not package power conservation or a realization theorem as an axiom.

## Checked scope

The formal calculations cover:

- The differential identity `div(E cross H) = H dot curl E - E dot curl H`, including the real derivative of complex conjugation.
- The complex Poynting identity and zero real divergence for real local coefficients and differentiable fields satisfying Maxwell's equations.
- Mixed partial symmetry, `curl(grad f) = 0`, and `div(curl F) = 0`, proved for actual C2 functions using mathlib's Schwarz theorem.
- Linearity of curl and Maxwell superposition, with differentiability hypotheses stated explicitly.
- The second-order electric curl-curl equation derived from both first-order equations.
- Integration by parts against compactly supported C1 scalar test functions on Euclidean three-space. Continuity and compact support establish integrability in the proof, rather than supplying an integral identity as a hypothesis.
- The classical-to-weak implication: C1 Maxwell fields satisfy the distributional curl equations against every such test. Each of the three components is proved, so arbitrary vector tests follow componentwise. This is not an existence or regularity theorem for weak fields.
- Explicit exact propagating and evanescent exponential Maxwell solutions in vacuum at normalized positive frequency one. The exponential is differentiated in the proof. For the evanescent fields the transverse wave number is 5/4 and the real growth/decay rate is 3/4.
- A coherent pair of exact evanescent fields. Each separate wave has zero real normal power everywhere, while the pair has constant normal power 3/4 everywhere. These fields have exponential growth and infinite transverse extent. They are not finite-power incident scattering solutions or an OQ14 counterexample.

All classical results state the regularity they use. The `fderiv` operator is total in Lean, so these differentiability conditions matter: they prevent interpreting its default value at a nondifferentiable point as a physical derivative.

The exported axiom-audit declarations, all prefixed `OQ14.Maxwell.`, are:

| Declaration | Scope |
|---|---|
| `divergence_cross` | Differential cross-product identity |
| `curl_conj` | Curl commutes with conjugation |
| `complex_poynting_identity` | Complex local conservation identity |
| `real_poynting_divergence_zero` | Real local power conservation |
| `curl_gradient` | Curl of a C2 gradient vanishes |
| `divergence_curl` | Divergence of a C2 curl vanishes |
| `maxwell_superposition` | Coherent linear superposition |
| `maxwell_curl_curl` | Second-order electric equation |
| `partial_integration_by_parts` | Compact-test coordinate integration by parts |
| `curl_integration_by_parts` | Distributional curl pairing |
| `classical_maxwell_weak_form` | Classical Maxwell implies weak curl equations |
| `vacuum_plane_wave` | Explicit exact propagating wave |
| `evanescent_wave` | Explicit exact growing or decaying wave |
| `paired_evanescent_maxwell` | Exact coherent pair solves Maxwell everywhere |
| `evanescent_zero_normal_power` | Single-wave zero normal power at origin |
| `paired_evanescent_positive_power` | Pair power 3/4 at origin |
| `evanescent_zero_normal_power_everywhere` | Single-wave zero normal power everywhere |
| `paired_evanescent_power_everywhere` | Pair power 3/4 everywhere |

The origin statements are retained as explicit simple regression witnesses; they are special cases of the stronger everywhere statements, not additional independent physical mechanisms.

## Pinned foundations and audit criteria

The existing project uses Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. No package source, dependency revision, or global toolchain setting was changed for this extension. The added imports use the pinned library's Fréchet calculus, symmetric second derivatives, complex exponential derivative, cross product, and integration by parts for line derivatives.

The successful exported declarations must report only `propext`, `Classical.choice`, and `Quot.sound`. Any occurrence of `sorryAx`, an error, or an extra project axiom invalidates the claimed check. The final source hash and raw compiler output are recorded under `lean/Maxwell/`; the root build also audits both Lean modules. The proof source contains no `sorry`, `admit`, or project `axiom` declaration.

The standalone check completed with exit code zero at `2026-10-18T04:12:51Z`, for source SHA256 `5ebb3c27d3dfd95f139125f1aafaf75cfbad6f1b284fc37ae785f4e6c74104c4`. All eighteen exported axiom reports contain exactly the three standard axioms above. The source hash was checked before and after compilation and remained unchanged. `Maxwell.lean` was then frozen for the root's combined clean build.

The weak pairing's signs were separately checked against `curl F = (d1 F2 - d2 F1, d2 F0 - d0 F2, d0 F1 - d1 F0)`: moving each derivative onto the compact test gives exactly the implemented pairing. Complex tests use the bilinear distribution convention. This is equivalent to using conjugated tests, since conjugation preserves the test class. Compact C1 tests include the usual compact smooth tests. No `WeakMaxwell` structure with an assumed conclusion was introduced.

A read-only review of the extended `build.py` confirmed that it builds both modules, hashes all current root and Maxwell-subtree Lean sources, verifies installed dependency revisions and clean tracked dependency files, and audits every declared axiom report. The root was notified that the older PowerShell entry point and README needed corresponding updates, because the earlier versions still described only the ten operator lemmas.

## Foundations available in the pinned library

Read-only source inspection found genuine tools for Fréchet and line derivatives, continuous linear maps, Schwarz's theorem, finite-dimensional Euclidean spaces, complex calculus, Bochner integration, compact-support integration by parts, box divergence theorems, Fourier transforms, distributions, and Sobolev inequalities. These are useful building blocks; their presence does not establish Maxwell scattering theory.

Representative library sources are:

- `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `Mathlib/Analysis/Distribution/`

Targeted searches of the pinned analysis and geometry sources did not find an existing Maxwell curl operator, H(curl) trace theory, Silver-Müller outgoing condition, dielectric Maxwell resolvent, Maxwell Runge theorem, or corner/cone transmission theory. This is a report of the inspected library, not a theorem that no equivalent infrastructure exists anywhere.

## Missing steps for the complete research claims

1. Domain weak-curl graphs, interior cutoff/zero extension, whole-space smooth graph-norm approximation, general-open-region weak Poynting localization, and weak real power conservation are implemented. Canonical scalar plane-slice representatives are proved for C1 and compact Lipschitz apertures. General tangential field traces and boundary theory remain separate obligations. Whole-space smoothing and Lipschitz test approximation are proved through actual convolution, not supplied as density assumptions.
2. Establish tangential traces and interface transmission, including integration by parts on bounded Lipschitz domains and the correct normal physical flux. The present compact-test theorem has no boundary trace.
3. Construct the outgoing homogeneous Maxwell fundamental solution as a distribution, including its singular local term. Prove the volume operator mapping estimates, its small-contrast inverse, uniqueness, far-field representation, and the scattering/incident normalization identities.
4. Prove total-field Maxwell Runge approximation from source reciprocity and unique continuation. Abstract density or compactness alone would not discharge this step.
5. Formalize the angular conical eigenproblem, its weighted spectral theory, the regularized Poincaré decomposition, radial forcing identities and estimates, nonzero singular coefficient, and interface regularity.
6. Prove stability under rounding and smooth-interface uniform convergence, followed by the finite peak construction and its unit incident-power normalization.
7. For modal claims, build analytic Fredholm/resonance continuation, a genuine outgoing resonant-state normalization, and its nonvanishing and rounding continuity. Neither abstract operator perturbation nor local coefficient continuation supplies these global statements by itself.
8. For the channel counterexample, formalize the actual physical input/output spaces and flux forms, finite-band jet interpolation and Gram balancing, all-order radial source Green convergence, self-consistent small-inclusion estimate, and uniform whole-plane flux convergence in the written uc:counterexample proof. Its fixed delta>eta scope and full scattering output must be retained. The formal local evanescent example does not meet those global conditions.

Replacing these steps by hypotheses named after the desired conclusions would verify only a conditional algebraic statement. No such replacement is presented here as verification of OQ14.

## Independent analytic review of the new modal coefficient continuation

The read-only review of `manuscript/sections/modal_next.tex` found the constant-forcing cancellation correct: `B0 = lambda(lambda+1) A0` makes the particular solution exactly `-r A0`. Subtracting `W(0)` leaves a Hölder remainder whose radial integrals converge uniformly near `lambda = 1`. The limiting coefficient `sqrt(4 pi/3) E(0) dot axis` has the correct normalization. This removes the apparent local pole at contrast zero.

Two precision requests were sent to the owning author: explicitly specify H(curl)_loc in the weak-field hypothesis (or prove the local graph regularity being used), and explain higher-norm holomorphy using locally uniform estimates plus weak holomorphy. The audit found no substantive local coefficient sign or convergence defect. Global resonance and normalization are separate obligations that the local calculation alone does not settle.

The subsequent read-only review of `modal_spectral.tex` found no new defect in its written completion of those global obligations. The compact/static decomposition and static inverse have the stated signs; strong convergence followed by composition with the compact remainder yields the claimed norm convergence; the reciprocal derivative pairing gives the displayed Green residue; and spatial scaling gives the `s^3` mode norm factor. For algebraic refractive index, the rational-function pole equation and the nonzero algebraic-exponent transcendence theorem rule out multiple poles and shared different-degree poles as claimed. The `1/z` term separates equal-parity angular degrees. Axisymmetry removes the irrelevant azimuthal multiplicity in the chosen sector and permits rotation of a magnitude maximum into the specified plane. These mathematical reviews are not Lean proofs of the spectral construction.

## H(curl) extension

The new source `lean/HCurl.lean`, namespace `OQ14.WeakCurl`, keeps `Maxwell.lean` frozen. Its scalar fields are mathlib's `Lp ℂ 2 volume` on the same Euclidean three-space; vector fields are three such a.e. equivalence classes. A test consists of an actual complex C1 function with compact support.

For every compact continuous function `f`, `testPair f` is constructed as the L2 inner product against the L2 class of `conj f`. The source proves both that `u*f` is integrable and that the bounded linear functional equals `integral u*f`. Thus continuity is obtained from the actual L2 inner product, with the Cauchy-Schwarz machinery already proved in mathlib. No distributional continuity is postulated.

The weak curl constraint is the componentwise identity
`integral C_j*phi = integral E_next*d_previous(phi) - integral E_previous*d_next(phi)`.
The derivative test functions are continuous and compactly supported, so they too define bounded L2 functionals. The graph is the intersection of the kernels of these explicit continuous linear residual maps. This proves it is a closed complex subspace of the product of two three-component L2 spaces. Its inherited norm is `max(norm E, norm C)`, where the coordinate vector norm is the maximum of the three scalar L2 norms. This is a Banach graph norm; it is not a positive-energy normalization of a Maxwell mode.

The complete-space instance is derived from closedness and completeness of L2. Simultaneous L2 limits preserve the weak relation. The fundamental lemma for locally integrable functions, applied to compact smooth real tests embedded into the complex test class, proves that these pairings separate scalar L2 classes. Consequently the weak curl is unique, and projection of the graph onto its field component is injective: the graph cannot carry arbitrary extra curl data.

Finally, for a classical C1 field whose field and actual curl components lie in L2, `classical_hasWeakCurl` proves graph membership by the previously checked curl integration-by-parts theorem and the a.e. identities for `MemLp.toLp`. The weak law is not included among that theorem's hypotheses.

| Exported declaration, prefix `OQ14.WeakCurl.` | Verified content |
|---|---|
| `testPair_integrable` | Products defining compact-test L2 pairings are integrable |
| `testPair_integral` | Bounded test functional equals the actual integral |
| `hasWeakCurl_iff_integral` | Graph predicate is exactly distributional curl |
| `graph_closed` | Distributional graph is a closed subspace |
| `hcurl_complete` | The graph is a complete normed space |
| `graph_norm` | Its norm is the maximum field/curl coordinate L2 norm |
| `weakCurl_limit` | Weak curl is preserved under simultaneous L2 limits |
| `classical_hasWeakCurl` | C1 fields with field and curl in L2 belong to the graph |
| `tests_separate` | Compact smooth tests separate scalar L2 classes |
| `weakCurl_unique` | The weak curl is uniquely determined |
| `field_projection_injective` | The graph representation has no spurious curl data |

This space is over all of R3. A radiating scattering field generally does not belong to global L2. Local H(curl), bounded-domain spaces, tangential traces, radiation conditions, material jumps, and resolvent estimates are still distinct formal obligations. The new space does not claim any of those results.

The standalone HCurl check completed with exit code zero at `2026-10-18T05:02:49Z`. Source SHA256 is `b69399a56774c646b2fb74a5f017df3dd7e77670be207a96a01bcaba7b0ec926`; it was checked unchanged before and after compilation. All eleven exported reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The imported Maxwell source remains at its recorded frozen hash. Raw output and provenance are `lean/HCurl/verification.txt` and `lean/HCurl/provenance.json`.

## Smooth approximation and genuine weak Green identity

`WeakPoynting.lean` proves actual convolution commutation with weak curl,
strong continuity of L2 translations, norm-contracting Bochner bump
averages, and their L2 convergence. A product-space Cauchy-Schwarz bound
establishes absolute Fubini integrability. Compact-test separation then
identifies the average with the smooth pointwise convolution. An explicit
shrinking bump sequence proves smooth approximation in the existing
whole-space graph norm. The root independently reviewed all definitions,
quantifiers, Fubini hypotheses and the final graph convergence theorem.

`WeakPoynting/Green.lean` derives the compact-test bilinear Green identity
for two arbitrary whole-space weak-curl graph elements. It first tests the
weak equation against a compact scalar times a smooth field, then uses
the proved approximation and continuity of actual L2 product pairings.
The root independently checked the sign, integral identification, compact
product tests, and limiting argument. No classical derivative of a weak
field or assumed Green identity enters the proof.

The frozen sources have 16 and 6 audited exports respectively, with
successful direct compiler checks and only the standard three axioms.
Their hashes and raw output are in `lean/WeakPoynting/`. These are
whole-space graph theorems; a general scattering field still needs a
local-domain bridge. They do not prove outgoing existence, interface
regularity, conical spectra or modal continuation.

## Local weak Poynting and real power conservation

Root read every definition and proof in the frozen Poynting, Local, and
Conservation modules. Conjugation is the actual real-linear isometry on
complex L2, and the compact derivative pairing uses the proved conjugate
derivative identity. Every complex Poynting term is an integrable L2
product, and the combined integral is identified with the already proved
bilinear Green functional.

The localization constructs a smooth cutoff equal to one on a neighborhood
of the test's compact support, with support inside the open region. Actual
cutoff/product-curl zero extensions agree almost everywhere with the
regional field and curl there. Outside that support both the test and its
derivatives vanish. This proves the restricted integral identity and
integrability without an assumed trace theorem or global L2 hypothesis.

The real conservation module defines WeakMaxwell by the two actual weak
curl equations almost everywhere. For real variable coefficients the
reactive density is imaginary pointwise; projection of the proved complex
integral gives the conventional half-scaled real Poynting law. No
coefficient differentiability or separate integrability of each reactive
energy term is needed: integrability of the combined density was already
proved from regional L2 fields and curls. Its conclusion is distributional
divergence zero, not the later W1,1 slice-representative conclusion.

The three frozen hashes are respectively
`c419f2a94d9cb0d303ad7f5642b821047e06d596a765cc4df7955c6aa0bb6a78`,
`b15e9b8de4108e3ce597c1e228690300d2396ac13dbbb50cb0a00e106b9806dc`,
and `e788c2c43bae08e130810338facad3a92cadb8bd7871e1dbab5318695ccea75f`.
Their 5+6+6 direct compiler reports use only the standard three axioms.
No substantive defect was found in this independent review.

## Plane slices and exact radial/modal formulas

Root independently read all of `WeakPoynting/Slices.lean`. The Euclidean
coordinate equivalence preserves actual volume. Tensor compactness and
the aperture-collar support condition are proved, as are the three
coordinate derivatives. Fubini identifies the resulting integrals with
the defined plane slices. The zero extension is of the L1 real flux,
and its divergence law is tested only inside the original open region.
The final theorem starts with actual regional weak Maxwell fields and
gives two genuine L1 slice functions with the correct derivative sign.
It does not assume a continuous representative or every-plane trace.
No substantive issue was found in the sixteen exports.

Root independently read all of `ModalAlgebra.lean`. Factorial Laurent
coefficients, actual complex derivatives, the nonzero exponential
prefactor, pole equivalence, multiple-zero derivative condition and
degree-one Wronskian/matching nonvanishing agree with the manuscript.
The latter conclusion does not assume the coefficient nonvanishing that
it is intended to prove. The general-degree and transcendence obligations
remain explicit. All twenty-five qualified exports were built locally.

Root independently read all of `RadialGreen.lean`. Real determinant-one
transfer data produce the exact complex outgoing coefficients; the
denominator positivity and imaginary part have the right signs. Load
cancellation uses the actual Wronskian convention. Complex derivatives
of the radial ODE imply nonnegative load derivative and, after the
endpoint argument, nonincreasing squared magnitudes on a closed
interval. The hypotheses are the ODEs, continuity and nonnegative
coefficients, not the intended monotonicity conclusion. All twenty-four
exports have appropriate analytic/algebraic scope, without assuming
the complete source Green convergence theorem.

## Continuous flux, weighted slabs and two exact analytic constructions

Root independently read all of Representative.lean and Weighted.lean.
The zero-distribution-derivative theorem is proved using actual smooth
convolutions and their a.e. convergence, with a common full-measure point
fixing the constant. The primitive is the actual integral over Iic x;
Fubini applies to an explicitly integrable triangular kernel and gives
the compact-test integration-by-parts identity with the correct sign.
Smooth localization proves the local increment law. Equality of continuous
representatives on the open interval extends to both endpoints when a<b.
The weighted identity follows by a proved distributional product rule and
this uniqueness; neither a classical derivative of the L1 slice nor an
endpoint evaluation is assumed. Slab Fubini uses the actual half-open slab
a<z<=b and retains the transverse derivative term. Regional Maxwell fields
give all integrability and weak-derivative hypotheses. This supplies scalar
flux values for C1 apertures; it does not assert general field traces.
No substantive defect was found in the 13+8 exports. Frozen source hashes:
`bade5cb79e3c7f085d9d73141d9fc1ed97d0dfc1f89805a48625b8857b9a237c`
and `ddfeb07dbf433fbd38a1a6bb1918e8855d9e9381af9de33e7101aca1e82f7783`.

Root independently read LongitudinalProjection.lean. The actual singleton
orthogonal projection gives the stated frequency symbol, including zero;
the symbol is measurable and dominated by the input norm. Lp construction
and a.e. representatives supply a genuine bounded linear multiplier.
Idempotence and self-adjointness imply positivity by an actual inner-product
identity. No Fourier equivalence or Newton-kernel conclusion is assumed.
No substantive defect was found in its 22 exports. Source hash:
`fb11b48e57152f5d72ce9324cd3b490d82599aef4fbd4905ffe3c63980dc1a63`.

Root independently read ModalWronskian.lean. Adjacent factorial coefficients
give the finite-sum radial ODE with its last term canceled explicitly.
Complex differentiation gives the zero derivative of the actual Wronskian.
Its inverse-coordinate polynomial is entire, including the separately
proved derivative at zero. Global constancy and its value at zero give
the normalization -2i for every degree. Nonvanishing arguments apply at
both z and n*z with their hypotheses checked. No transcendence, pole
existence or Fredholm identification is inferred. No substantive defect
was found in the 26 exports. Source hash:
`fc553bf203757c505cad71ed013c05d872b1fac683ab24c036e4903bbbfdab54`.

## Fourier completion, rational spectral obstructions and cross flux

Root independently read FourierL2.lean in full, in addition to the hotspot
agent's independent audit. Fourier conjugation and Fubini have the correct
sign convention. Schwartz inversion supplies Parseval. Compact smooth
functions are actually constructed as Schwartz functions, with bounded
weighted derivatives, and the test annihilator theorem proves dense L2
range. The Fourier map on that range preserves its inherited L2 norm.
Continuous extension, dense-image inversion and closed isometric range
prove an onto scalar L2 isometry; integral agreement and uniqueness are
proved. There is no assumed Plancherel equivalence or density premise.
The 23-export scope is scalar Euclidean L2. Vector lifting and physical
Newton-kernel identification are still separate. No defect found.

Root independently read ModalRational.lean. The explicit inverse-coordinate
polynomials represent the matching coefficients with nonzero arguments.
Differentiating the exact rational identity yields a polynomial obstruction
for multiple zeros. Its value at zero is nonzero for n outside 0,+1,-1.
The cross-degree separation polynomial is nonzero by its constant and first
derivative coefficients, with l(l+1) distinct for distinct natural degrees.
Finite polynomial root sets give the stated finite exceptional sets. This
does not imply that the sets are empty, or that the countable union over
all degrees avoids a chosen pole. All 17 exports preserve that distinction.
No defect found.

Root independently read Polarization.lean in full. Actual Lp representative
identities prove weak Maxwell closure under complex combinations. The
physical Hermitian cross product, its 1/4 normalization and +i polarization
sign agree with linearity in the first input. Real/imaginary conservation
and integrability give a genuine complex compact-test identity. Fubini
decompositions are asserted a.e. where required. Component representative
theorems give complex continuous scalar plane values, increments and the
complete weighted volume identity. Uniqueness extends conjugate symmetry
to canonical endpoint values. No arbitrary boundary trace or Lipschitz-test
extension is asserted. No defect found in the 28 selected exports.

Hashes: FourierL2
`05d8ddafe4a06231e854a6d816f4b1156ff9fdcb9ee7c9a1e37c1de4af3759e7`;
ModalRational
`a048238309504620781a29a8ecf9aacf437ff04ff29d0f13164d4019b54fd0a9`;
Polarization
`39d9449e74baeabaa657601913ccbbc2e17bcd5aa49e9e927bb90ea79ef63740`.
The separately reviewed scalar outgoing kernel is described in
`green_kernel.md`; its distributional source term is not yet formalized.

## Actual physical projection, spectral zeros and Lipschitz tests

Root independently read VectorFourier.lean, GradientProjection.lean,
HelmholtzProjection.lean and StaticCoefficient.lean in full. The actual
volume-preserving coordinate maps and finite coordinate L2 decomposition
give vector Plancherel, including agreement with the Fourier integral.
Conjugation produces the actual longitudinal projection. Schwartz
coordinate derivatives agree with Maxwell's real Frechet derivatives;
Fourier differentiation has the positive 2 pi i sign. The gradient and
curl consequences therefore concern actual spatial fields.

For the closed-gradient characterization, the spectral divergence is
proved locally integrable from scalar L2 components. Inverse Fourier
transforms of actual compact smooth scalar tests convert annihilation of
gradients into vanishing of that distribution. This proves the exact
kernel, closed span, orthogonal projection and variational uniqueness,
without an assumed Helmholtz decomposition. The coefficient multiplier
uses the actual pointwise square root; its self-adjointness, square and
norm bound instantiate the positive inverse theorem for actual chi and P.
The dynamic perturbation Q is still explicitly abstract norm-small data.
No Newton-convolution identity is inferred. These 31+15+16+20 exports
passed independent source review and targeted builds.

Root independently read ModalAlgebraicity.lean, ModalExistence.lean and
ModalAsymptotics.lean in full. Actual algebraic coefficient lifting and
restriction of scalars prove the exceptional roots' algebraicity and
the nonzero algebraic-exponential obstruction. No full transcendence
principle is a hypothesis. The inverse-coordinate map sends a small
closed disk to itself and is a contraction by an explicit denominator
lower bound. A local analytic logarithm of the actual matching quotient
gives exact determinant zeros near periodic exponential centers.
Shrinking that neighborhood proves arbitrarily small displacement.
Center real/imaginary formulas have the correct signs. Finite multiple
roots are avoided by a modulus bound, and for real n>1 the lower-half-plane
zeros have arbitrarily large positive frequency-to-decay ratio.
These 24+8+11 exports neither infer avoidance of a countable union of
shared-root sets nor identify determinant zeros with full operator poles.
The last ModalExistence docstring's word "poles" is shorthand for its
precisely stated determinant zeros; the review and theorem scope make the
remaining operator step explicit. No substantive defect was found.

Root independently read Lipschitz.lean and Aperture.lean in full.
Rademacher integration by parts cancels the reflection sign in the
mollifier identity. Uniform derivative bounds, a.e. convergence and compact
support retention justify dominated convergence against every L1 flux.
Actual a.e. Frechet gradients give the real and Hermitian Maxwell laws.
For a plane aperture, the a.e. differentiability set pulls back through
the volume-preserving coordinate decomposition. Tensor derivatives and
weighted Fubini retain both the axial and transverse terms with their
correct signs. The existing representative theorem then gives exact
continuous scalar flux increments. No nonsmooth chain rule at every point
or boundary trace is assumed. The 16+11 exports passed review and targeted
builds. The axial weighted endpoint extension is separate active work.

Root's DyadicKernel.lean was independently read by the channel agent.
The actual Hessian linkage, static subtraction and exact two-numerator
formula are correct. Exponential Taylor cancellation bounds the transverse
and radial numerators by 4 and 10 times |ikr| squared. Unit coordinate
products and |exp(ikr)|=1 give the component bound 14 k squared/(4 pi r).
This is pointwise for real k, nonzero x and |k||x|<=1, including k=0.
The nine exports do not assume or assert local integrability or a source
distribution. No defect was found. All 161 new selected theorem reports
contain exactly the standard three axioms, with no proof placeholders.

## Lipschitz endpoints, matching residue and singular integrability

Root independently read Axial.lean and LipschitzBoundary.lean in full.
The one-dimensional mollification uses the actual line derivative, and
both derivative and function convergence are justified against L1 data.
The product test is genuinely compact Lipschitz; its actual a.e.
derivative gives the distributional product rule. Continuous representative
uniqueness proves the weighted endpoint identity. Both tensor factors are
differentiable on a common full-measure subset under the coordinate map,
and their Frechet derivatives give the complete three-dimensional gradient.
The real/imaginary decomposition, finite-slab Fubini and endpoint signs
are consistent. The main theorem has actual regional Maxwell states and
Lipschitz cutoffs as its data; the slice values and gradient integral are
conclusions. It does not assert a general boundary field trace. No defect
was found in the 8+14 exports. The identifier-only rename of the two
Lipschitz constants preserves every mathematical statement and lets the
strict unproved-declaration source scan remain unchanged.

Root independently read ModalMatching.lean. The matching matrix and
signed adjugate multiply in both orders to the exact determinant. The
outgoing Wronskian guarantees a nonzero column. The actual derivative
slope limit proves the reciprocal determinant residue and punctured
nonvanishing, and the continuous adjugate gives the inverse limit.
Explicit factors prove the residue has nonzero line image. The final
existence theorem uses the previously constructed high-quality simple
zeros, rather than assuming one. Its scope is the actual two-amplitude
matching system, not the full vector Maxwell resolvent. No defect found
in the 16 selected exports.

KernelIntegrability.lean was independently reviewed by the channel agent;
the details are in kernel_integrability.md. Actual polar measure transfer
proves inverse-distance and inverse-square local integrability. The actual
real-frequency outgoing scalar kernel is measurable and locally L1 and
L2. The origin is restored only through the null-singleton identity.
All ten exports compiled cleanly with standard axioms only. These results
do not assert the missing source distribution or convolution identity.

## Newton distribution, actual dipole interfaces, and energy estimates

Root independently read NewtonFourier and NewtonHessian in full. The actual
inverse-radius estimates justify both absolute scale-space integrals before
Fubini. Gaussian Fourier constants and the inverse-transform derivative sign
give the full Hessian multiplier -xi_i xi_j/|xi|^2. Summing it gives the exact
source identity Delta N=-delta, with the origin removed only from an
almost-everywhere frequency identity. The physical projection statement is
correctly limited to its frequency multiplier. The spatial weak convolution
identity is still separate. HeatFourier and these two modules also passed
independent cross-agent audits. Their 26+11+10 exports compile with standard
axioms only.

Root independently read ModalDipole and ModalInterface in full. Actual
Frechet curls and the actual Riccati ODE give the complex-frequency Maxwell
equations. The a/n interior normalization matches the determinant convention.
The all-sphere cross-product traces give the matching equations, and the
reverse implication is obtained at a genuine equatorial point. Wronskians
prove both amplitudes and some exterior trace are nonzero. The final high-Q
field construction uses the proved root-existence theorem. Center
removability is explicitly excluded from these statements. Both modules
also passed an independent channel-agent audit; 14+23 exports compiled.

Root independently read Energy and EnergyLocalization in full. Weighted
electric energy integrability is derived from the imaginary weak Poynting
identity and actual L2 products. The exact complex cross-product inequality
and squared compact C1 cutoff give Caccioppoli, with the sign of the real
nonzero frequency correctly disappearing in its square. The unit-cutoff
inner-set integral and actual support magnetic integral yield
2+4d^2/(omega^2 m). The measures are consistently restricted to the open
region; the theorem does not silently assert that an arbitrary K lies
inside that region. No derivative or upper bound on epsilon is assumed.
The 10+4 selected exports compiled cleanly.

DynamicIntegrability5 and KernelEstimates4 also compiled and passed separate
independent audits. The additional 107 checked exports bring the registered
source total to 646 in 45 modules. Their complete aggregate clean-checkout
rebuild is a separate provenance step; the preserved 539-declaration release
remains the latest complete clean-build package until that step is recorded.

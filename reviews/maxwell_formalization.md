# Maxwell formalization audit

Status: a genuine continuum Maxwell foundation is implemented; the complete OQ14 theorems are **not formally verified**.

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

1. Define local weak derivatives and the H(curl) graph space over domains, with a.e. equivalence, distributional curl, completeness, density, restriction, and cutoff operations. The present integration-by-parts theorem is a starting lemma, not that entire theory.
2. Establish tangential traces and interface transmission, including integration by parts on bounded Lipschitz domains and the correct normal physical flux. The present compact-test theorem has no boundary trace.
3. Construct the outgoing homogeneous Maxwell fundamental solution as a distribution, including its singular local term. Prove the volume operator mapping estimates, its small-contrast inverse, uniqueness, far-field representation, and the scattering/incident normalization identities.
4. Prove total-field Maxwell Runge approximation from source reciprocity and unique continuation. Abstract density or compactness alone would not discharge this step.
5. Formalize the angular conical eigenproblem, its weighted spectral theory, the regularized Poincaré decomposition, radial forcing identities and estimates, nonzero singular coefficient, and interface regularity.
6. Prove stability under rounding and smooth-interface uniform convergence, followed by the finite peak construction and its unit incident-power normalization.
7. For modal claims, build analytic Fredholm/resonance continuation, a genuine outgoing resonant-state normalization, and its nonvanishing and rounding continuity. Neither abstract operator perturbation nor local coefficient continuation supplies these global statements by itself.
8. For the channel claim, identify the actual physical input/output spaces and flux forms, prove the absolute bypass condition for every coherent vector, and prove either a uniform approximation bound or a globally realizable counterexample with the prescribed fixed section. The formal local evanescent example does not meet those global conditions.

Replacing these steps by hypotheses named after the desired conclusions would verify only a conditional algebraic statement. No such replacement is presented here as verification of OQ14.

## Independent analytic review of the new modal coefficient continuation

The read-only review of `manuscript/sections/modal_next.tex` found the constant-forcing cancellation correct: `B0 = lambda(lambda+1) A0` makes the particular solution exactly `-r A0`. Subtracting `W(0)` leaves a Hölder remainder whose radial integrals converge uniformly near `lambda = 1`. The limiting coefficient `sqrt(4 pi/3) E(0) dot axis` has the correct normalization. This removes the apparent local pole at contrast zero.

Two precision requests were sent to the owning author: explicitly specify H(curl)_loc in the weak-field hypothesis (or prove the local graph regularity being used), and explain higher-norm holomorphy using locally uniform estimates plus weak holomorphy. The audit found no substantive local coefficient sign or convergence defect. Global resonance and normalization are separate obligations that the local calculation alone does not settle.

The subsequent read-only review of `modal_spectral.tex` found no new defect in its written completion of those global obligations. The compact/static decomposition and static inverse have the stated signs; strong convergence followed by composition with the compact remainder yields the claimed norm convergence; the reciprocal derivative pairing gives the displayed Green residue; and spatial scaling gives the `s^3` mode norm factor. For algebraic refractive index, the rational-function pole equation and the nonzero algebraic-exponent transcendence theorem rule out multiple poles and shared different-degree poles as claimed. The `1/z` term separates equal-parity angular degrees. Axisymmetry removes the irrelevant azimuthal multiplicity in the chosen sector and permits rotation of a magnitude maximum into the specified plane. These mathematical reviews are not Lean proofs of the spectral construction.

# Lean verification of operator estimates and Maxwell foundations

The formal sources are `OQ14.lean`, `Maxwell.lean`, `HCurl.lean`,
`HCurlDomain.lean`, and `HCurlCutoff.lean`. Sixty-two exported
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
compiler and mathlib revision, builds all five registered modules, and audits all 62
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
`HCurlDomain/`, and `HCurlCutoff/`. The
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

## Explicitly outside the formalization

This is **not complete formal verification of OQ14**. Maxwell derivatives
and weak-test identities, complete weak-curl graphs and weak divergence of
curl are represented. The source does not yet construct H(curl) trace theory,
density theory, outgoing scattering, the conical spectrum,
Runge approximation, rounding, the analytic Fredholm resonance pencil or
its reciprocal norm. The complete written modal theorem is not yet a Lean
theorem. The unrestricted channel claim additionally still lacks a written
proof or physical counterexample. No hypothesis or custom axiom stands in
for either missing conclusion. The exact remaining library development is
listed in `../reviews/maxwell_formalization.md`.

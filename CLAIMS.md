# Claim ledger

Status labels refer to exact statements. PROVED means an explicit mathematical
proof in the manuscript; formal verification is a separate column or mapping.
No restricted theorem resolves the original full conjectures by relabeling.

| Canonical labels | Statement and hypotheses | Dependencies | Status / relation to OQ14 |
|---|---|---|---|
| `pr:channel-target` | Fixed positive material bounds, frequency, physical D, power threshold and all-vector passage/bypass; unrestricted support and fine structure | Full global Maxwell scattering class | OPEN |
| `hs:angular`, `hs:coefficient` | Checkerboard exponent and continuous finite-k local singular projection | Positive binary contrast; scalar Hz reduction; H1 solutions | PROVED local mechanism |
| `hs:local-excitation` | Nonzero coefficient at prescribed positive frequency in a small disk | Coercive Dirichlet perturbation | PROVED |
| `hs:wellposed`, `hs:runge` | Outgoing scalar-TM scattering and density of total fields | Finite polygon partition, vacuum exterior, connected complement; DtN/Rellich/edge UCP | PROVED within stated class |
| `hs:simultaneous` | One smooth normalized incoming field excites all N coefficients | Continuous nonzero functionals and finite union of kernels | PROVED |
| `hs:rounding-convergence`, `hs:packing` | Arbitrarily many rounded peaks in any patch under one unit-power-per-length input | Above lemmas, fixed-geometry local regularity and rounding | PROVED driven invariant 2D version only |
| `hs:regional-ratio` | Bounded-region energy/peak tends to zero | Strong H1 rounding convergence | PROVED; not modal volume |
| `hs:open3d` | Limits of the extrusion argument | Finite-height control is not imported | Scope remark; direct 3D construction follows |
| `hs:three-angular`, `hs:three-coefficient` | Conical exponent below one; intrinsic L2-continuous Maxwell coefficient | Angular Rayleigh trial, regularized curl lifting, exact radial projection | PROVED local 3D mechanism |
| `hs:three-local-excitation`, `hs:three-volume`, `hs:three-runge` | Positive-frequency coefficient, uniform small-contrast scattering inverse, total-field density | Weighted PEC correction, dyadic Neumann inverse, reciprocity/Rellich/interface UCP | PROVED for stated class |
| `hs:three-rounding`, `hs:three-packing` | N finite 3D driven peaks under one unit-power illumination | Fixed small contrast, smooth rounded finite inclusions, patch projection constraint, one-sided maxima | PROVED; not an exact common-plane-maxima or modal theorem |
| `hs:three-no-real-mode`, `hs:three-modal-gap` | No nonzero real-frequency finite-energy mode of stated compact finite-piece class; QNM packing still requires normalization and one-pole persistence | Exterior spherical waves and interface UCP; missing resonance bridges | PROVED diagnostic / OPEN modal target |
| `ch:ranklemma`, `ch:factorization` | Finite-rank obstruction and factorization with every factor norm retained | Hilbert-space linear operators, fixed positive norm threshold | PROVED operator implications |
| `ch:fluxlemma`, `ch:magneticHone`, `ch:caccioppoli` | Legitimate weak flux, magnetic H1, flux domination | Real positive bounded material, local H(curl), constant mu, specified cutoffs | PROVED full-vector local results |
| `ch:resourcecount`, `ch:average` | Channel count and N^(5/3) summed field-resource cost | All-vector positive weighted flux; local field norm | PROVED; earlier report rederived and credited |
| `ch:outerwindow` | Sharp D passage survives an outer smooth window up to absolute bypass | Trace compatibility, psi=1 on unchanged D | PROVED bridge; coercivity needs delta<eta*tau |
| `ch:fulloutput` | Finite-rank approximation to complete T after feedback | Passage/bypass, trace compatibility, local resource B_* | PROVED with explicit resources; not unconditional |
| `ch:spectralcor`, `ch:arearesource` | Uniform spectral count and explicit area scaling | Common B_*, material ratio, collar, shape and thresholds | CONDITIONAL family bound |
| `ch:essential` | Essential norm <=sqrt(delta/eta); compact when delta=0 | Same full-output hypotheses and finite resource | PROVED per-device statement; no family uniformity |
| `ch:anisotropy` | Local extension to real symmetric positive tensor epsilon | Common tensor ellipticity, constant scalar mu | PROVED local extension |
| `ch:algebraaudit` | Passivity/individual compactness/ratio-monotonicity shortcuts fail | Exact algebraic examples | DISPROVED shortcuts; no physical counterexample |
| `cx:bragg`, `cx:bragg-scope` | Unbounded unit-input local fields for any eps_plus>1 | Fixed core, growing radial support, exact Maxwell matching | PROVED obstruction; zero net spherical transmission |
| `cx:evanescent` | Infinite positive local flux index, coherent sidewall zero flux | Homogeneous local collar, paired evanescent solutions | PROVED local obstruction, not global device |
| `cx:mirror-network` | Arbitrarily weak lossless links resonantly match | Reciprocal unitary network algebra | PROVED model diagnostic |
| `cx:pair-solution`, `cx:pair-sensitivity`, `cx:n-model` | Exact matching, energy, linewidth and weighted perturbation bounds | Stated energy-normalized coupled-mode equations | PROVED in model only |
| `cx:compression`, `cx:absolute-bypass` | Full-subspace transmission and bypass certificates | Actual physical isometries, pointwise flux traces and operator bounds | PROVED sufficient criteria; physical data unconstructed |
| `cx:coherent-failure` | Basis-only and signed-flux tests fail | Explicit Hermitian matrices | DISPROVED inference rules |
| `cx:angular-obstruction` | High-order regular radial solution cannot have zero value or derivative in too-small ball | Radial scalar dielectric; strict centrifugal inequality | PROVED restricted obstruction |
| `cx:missing-bridge` | Bounded-index Maxwell synthesis of arbitrary N matched directions through D | Common frequency, power ports, relative errors, all-vector bypass | OPEN |
| `ca:powerbudget` | eta*tau <= 1+delta necessary for a nonzero counted space | Full-plane integrability, physical radiation normalization and hemisphere conservation | PROVED; closes only empty threshold regime |
| `ca:localpackets`, `ca:packetresource` | Arbitrary local positive-flux dimension with whole-plane coherent bypass bound | Bandlimited sinc packets and exact Maxwell Cauchy evolution; finite but growing field norm | PROVED local obstruction; no physical input map |
| `ca:outgoingfailure`, `ca:compactcompletion` | No exact outgoing-vacuum or finite compact-exterior reproduction of the full-slab packet fields | Evanescent support, unique continuation, radiation convention | PROVED exact noncompletion; approximate synthesis remains OPEN |
| `ver:lean` | Ten compiled operator and integral declarations | Lean 4.19.0, pinned mathlib; propext, Classical.choice, Quot.sound only | LEAN VERIFIED; continuum Maxwell bridges excluded |

The prior ENZ/shape-varying result is not recertified here as a complete theorem;
its differing quantifiers are audited. Full formal scope is documented in
`lean/` and the manuscript verification section. No continuum bridge may be
inserted as an axiom and reported as full OQ14 formalization.

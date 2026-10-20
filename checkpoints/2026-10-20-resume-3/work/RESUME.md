# OQ14 resume checkpoint — October 20, 2026 (third pause)

**PAUSED at the user's explicit request: "alright, stop with a checkpoint".**
All three 6.1 Sol agents stopped and confirmed no active owned sessions.
Root stopped clean aggregate session21965 (interrupted EXIT1). The Gronwall
dependency build had already completed EXIT0; the RadialReference draft
compiler had already completed EXIT1. No proof work should resume until the
user asks. The complete requested Maxwell formalization remains unfinished.

## Start here

Checkpoint tag: `oq14-resume-2026-10-20-3`.
Read `checkpoints/2026-10-20-resume-3/manifest.json`, its exact work snapshots,
and `evidence/handoff.md`. Original working files remain in place. Never
restore over later work. User preference: 6.1 Sol subagents; Astra for the
important proof design, integration and audits.

1. Independently audit the frozen `SphereCapWeak` (12 reports). Seven other
   unregistered frozen modules already have full-source/compiler audits.
   The eight frozen sources total104 reports (92 independently audited).
2. Finalize the three targeted-compiling drafts: `CapProfileFirstOrder`,
   `RadialHighOrderBound`, `RadialHighOrderTail`. Preserve their actual
   mathematics; finish reports, objects, reviews and independent audits.
3. Repair the three unfinished drafts: `SphereAxialSurface`, `StaticBallL2`,
   `RadialReference`. Exact failures and next proof steps are below.
4. Register only fully audited sources. All14 current new Lean files remain
   unregistered. Do not run a root aggregate that globs unfinished drafts.
5. Resume a genuinely clean aggregate in the independent checkout after
   freezing the intended source commit. Never clean the root Lean build
   while agents are active. No clean2804 aggregate PASS exists.

## Exact verification and delivery state

Registered source commit `bc37efda5d633e3dd3bf8b16161907d8ee5e8fba`:
**2804 declarations /247 modules /219 libraries**. Its new files passed
targeted compilation and independent full-source audits. Its clean combined
build was interrupted by this stop request; it is NOT certified as a whole.
The separate checkout `tmp/clean-checkout` remains at that exact commit.
Its output/lean provenance and clean-build log still identify the completed
2390 build, and must not be labeled2804. The interrupted process buffered
its output, so no complete2804 compilation log was produced.

At the clean2804 commit, all15 diagnostic groups passed. The110-page PDF
passed reference/citation/overfull-box checks; rendered pages106 and109 were
visually inspected without clipping. PDF SHA256:
`6ed23ce3c113b57a16742166d2228901b3770f06fada0f3b570b956c492aa34c`.
The checkpoint preserves these scoped PDF/diagnostic artifacts and renders.
They are not a coherent2804 proof release.

The latest completed clean proof build AND coherent packaged release is
`oq14-maxwell-foundations-2390`, commit
`2f1ca342b33687c154226129f8417487dad3a175`.
2390 reports,15 diagnostics and110-page PDF passed; pages106 and109 inspected.
Its14 matching artifacts remain in
`output/checkpoints/oq14-maxwell-foundations-2390/` and at top-level output.
Delivery5002464bytes, SHA256
`011b8e9ed5767c25d8ae5ecf1f14b8a25731fa7910a794dfdc74ff0320cacf4e`.
PDF SHA256
`b05d9298e67fe66d8b0ac863b9a66b9cc95843a82ddc0113a135d3e080a0f92c`.
This checkpoint saves its clean proof provenance/log and release hashes too.
All earlier immutable checkpoints and releases remain intact.

## What the registered continuation added

2595 constructed actual cap Legendre shooting with a root in(0,2), actual
three-piece profile and interval weak equation; whole-plane L1 flux
continuity for a fixed compact source region and positive gap; literal
finite-layer/inclusion geometry, material coefficients and physical
scattering inverse; dynamic support-volume estimates; and actual all-degree
Hankel polynomial positivity/outgoing-load sign.

2804 constructed actual homogeneous radial ODE solutions, layer/stack
propagation and energy estimates, outgoing/core source coefficients, scalar
Green jump, load and barrier bounds; regular Riccati series identification,
origin limits and positive barriers; genuine axial coordinate Jacobian and
geometric sphere measure; explicit parity-reaction volume operators and
unique literal small-inclusion material fields. Read the exact reviews
`actual_constructions_2595.md` and `actual_constructions_2804.md`.

New frozen work constructs continuous radial gluing across all interfaces;
sharp regular-solution Gaussian bounds; genuine cap endpoint and latitude
test identities and the actual sphere weak equation; exact ball potential,
global weak Hessian and weak Poisson source. None of these alone is full
physical Green convergence, H1 lifting, or Newton projection identification.

## Radial and channel continuation — root and modal_sol

`RadialGluing`18 is independently audited. Actual Chain endpoint matching,
including zero widths, continuous positive-radius gluing of outgoing and
normalized core branches, and actual off-interface ODEs are proved. Spatial
Maxwell Green reconstruction is not yet proved.

`RiccatiBarrierNormalization`14 and `RiccatiGaussianBound`15 are audited.
Actual normalized regular v and y=x psi'/psi extend continuously to zero.
The weighted deficit derivative gives the sharp actual Gaussian lower
bound, not an assumed comparison. Raw ModalAlgebra.psi is NOT the continuous
extension at zero (e.g. psi1(0)=-1); use the actual origin-series extension.

`RadialHighOrderBound`9 compiled and emitted an object before final prints
were appended. Its exact current final-report run was interrupted. Do not
treat that old object as certification of the current source. Tail12 passed
a target compile with one redundant congr1 warning but has no prints,
object or review. Complete both final audits before registration.
Their route uses actual RadialLoadBounds, l>=2R, and g.q^2*g.b^2<=l(l+1).
Then gamma_*>=l/2, prefactor<=4, Gaussian exponent<=R/2, and exact factorial
product1/(2l+1) give the actual coefficient envelope. For R>=max(1,e*s),
split(s/R)^(2l) into e^-l and2^-l, yielding a geometric weighted tail with
decay faster than every inverse power of R. No all-order convergence premise.
Next prove Chain implies eachg.b<=X; specialize q_g<=q, X<=2R,q>=1 and
l>=2qR to the actual barrier. Lower degrees fit the existing intermediate
window; check no gap at the cutoff. Physical full Green summation remains.

`RadialReference` is a failed draft. Actual proposed constant-coefficient
transfer matrix is [cos(qt),(sigma/q)sin(qt);-(q/sigma)sin(qt),cos(qt)].
Failures: matrix derivative algebra around45; missing parentheses around
the second HasDerivAt derivative product near58; quarter-wave simplification
near73 and pair-diagonal algebra near87-91. Exact log preserved. Do not
claim its7 proposed lemmas compile. The pinned mathlib Gronwall dependency
build succeeded (1887/1887); no dependency revision was changed.
After repair, compare the actual translated layer ODE to this reference:
error'=A0*error+(0,l(l+1)/(sigma*x^2)*actualu). Use proved energy bounds and
Gronwall to derive actual fixed-width O(R^-2) transfer convergence, then
finite quarter-wave pairs and common-stack limits. Follow with spatial
Green reconstruction and uniform all-order/whole-plane estimates.

## Angular continuation — fredholm_sol

`CapSturmEndpointTest`2 and `SphereAxialTests`15 have root source/compiler
PASS. The latter audit is already complete (session48962), despite the
agent's final handoff still calling it pending. `SphereCapWeak`12 has author
target/object PASS with all standard-only reports and no warnings; root
independent audit remains pending. Its sphere_weak_identity derives actual
geometric sphere integrals for every ambient C1 test by genuine coarea,
Fubini, integrability and the per-azimuth cap equation. Full H1 is not claimed.

`CapProfileFirstOrder` has4 proofs and target EXIT0/no warnings, but no
prints/object/review. It proves actual right derivatives through interfaces
using value continuity and genuine first-order interval IBP. Finalize it.
`SphereAxialSurface` is an unfinished7-lemma coordinate draft. Fix curvature
linear_combination signs near62/64 to positive cos(theta)/sin(theta) times
transverse_sq. Solve9 tangent-decomposition coordinate polynomial identities
using transverse_sq and cos^2+sin^2=1; avoid field_simp no-progress failure.

Then derive actual profile IBP for
v(z)=axialTangent_i(z,theta)*psi(latitude(z,theta)), whose pole flux vanishes,
and periodic theta IBP for azimuthCoefficient_i*psi. Use
A'_i+B'_i=-2n_i and P_i=A_i*sigma_z+B_i*sigma_theta, endpoint majorants and
Fubini to prove all3 genuine weak surface gradient identities:
integral G_i psi = -integral phi [Dpsi(e_i-n_i*n)-2n_i*psi].
Prove phi,G inL2 from the bounded actual three-piece slope and tangent.
Any custom H1 notion must explicitly use these distribution identities plus
L2; AE pointwise slopes alone are insufficient. Combine with shooting root
and sphere weak equation, then actual conical Maxwell coefficient lifting.

## Static ball continuation — continuation_review_sol

`StaticBallPotential`14 and `StaticBallHessian`14 are independently audited.
Actual Psi=R^2/2-r^2/6 inside andR^3/(3r) outside is globallyC1. The actual
weak Hessian follows from existing RadialInterface.weak_partial (anyR),
with no surface delta, and trace gives the actual global weak Poisson source.
Do not recreate the removed duplicate SphereWeakPartial draft.

`StaticBallL2` latest target EXIT1 (session68484), no object. One remaining
error near131: unknown ModalDipole.coordinate in hessian_measurable.
Replace its two uses with explicit continuous complex coordinate maps,
e.g. Complex.continuous_ofReal.comp of the actual PiLp projection continuity.
First8 dependency reports are standard-only; last3 use compiler error
recovery and are NOT accepted. Recheck the entire source after repair.
Then derive actual L2 weak derivatives, genuine Fourier weak-derivative
identification (e.g. Schwartz IBP with the proved decays/integrability),
and combine symmetry/trace to identify the actual Newton/projection operator
on the constant-ball source. Only then derive the exact -P/3 response.
That operator identification is not yet proved.

## Remaining full scope and scientific limits

Full physical all-order Green convergence, self-consistent inclusion
asymptotics, moving-gap coherent whole-plane flux, counted-space power
identities, conical Maxwell coefficient lifting, Runge approximation,
rounding, physical reciprocal residue normalization, infinite-degree pole
isolation and final simultaneous modal maxima still require construction.
Do not insert those conclusions as hypotheses or report full closure.

The written channel disproof fixes delta>eta>0, full scattering output,
common ordinary bounds/frequency and unrestricted finite support. It does
not close delta<=eta, receiving-only, sole-connection or uniformly bounded
support variants. The written modal theorem uses a reciprocal-residue-
normalized high-Q QNM, fixed real frequency/common bounds, arbitrarily many
actual3D maxima in a prescribed plane patch, and N-dependent insertion
contrast. Preserve this scope. `reviews/original_scope_2026_10_20.md` records
that the original Downloads manual is currently absent; its historical hash
does not certify an exact present-day manual comparison.

## Environment and safe resumption

Workspace D:/oq14; PowerShell. Python:
`C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Lake `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`.
Tectonic `D:/oq14/.tools/tectonic/tectonic.exe`.
Lean4.19.0, mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, nine locked deps.
Use Python -X utf8, TECTONIC_CACHE_DIR=D:/oq14/tmp/tectonic-cache,
MATHLIB_CACHE_DIR=D:/oq14/.tools/lean/cache.
Target check/object: lake env lean -o .lake/build/lib/lean/Module.olean Module.lean.
Clean aggregate only in the independent checkout using lean/build.py.
Run scripts/verify.py and scripts/build.py --cached for diagnostics/PDF.
Package only matching clean-commit proof/PDF/diagnostic evidence.
Only propext, Classical.choice and Quot.sound are permitted foundation axioms;
no project axioms, sorry or admit. Error-recovery reports are not proofs.

Integration scripts1058,1312,1660,1835,2033,2183,2234,2390,2595,2804 and all
previous checkpoint/preservation scripts have executed and are nonidempotent.
Do not rerun them, including this checkpoint's creation script.
Unrelated untracked sites/ belongs to the user; do not touch or package it.
No external paper/site/repository publication or scheduled continuation.

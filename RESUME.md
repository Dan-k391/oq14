# OQ14 checkpoint — October 22, 2026

**PAUSED at the user's explicit request: "stop and make a checkpoint after
the current stage".** Current-stage checks finished. All three 6.1 Sol
agents and all owned compiler jobs stopped. Resume only when the user asks.
Full requested OQ14 Lean closure remains incomplete.

Checkpoint: `checkpoints/2026-10-22-resume/`.
Local checkpoint tag: `oq14-resume-2026-10-22`.
Read its `manifest.json`, immutable `work/RESUME.md`, and the saved agent
handoffs. Original working files remain in place. Restore only missing
files with the checkpoint's non-overwriting restore script. User preference:
6.1 Sol subagents; Astra for critical mathematics, design and integration.

## Completed clean milestone

`oq14-maxwell-foundations-4391` at
`c597c535c9a751fccbf3e9a0d644721326ceda26`:
4391 audited reports /469 modules /441 libraries. Clean aggregate exit0,
nine dependency pins verified, all 15 diagnostic groups passed. Matching
113-page PDF passed reference/citation/overfull checks; pages106–113 rendered
and visually inspected. All14 matching artifacts are preserved under
`output/checkpoints/oq14-maxwell-foundations-4391/` and top-level `output/`.

PDF SHA256:
`8c29cdc3b31ee277cdb7e0b9efc3a54669eb69b85e46d38af052a0b060ad22ce`.
Delivery9365092bytes, SHA256:
`89f16629977b6477345ca0732357fc0bf468ee32def7d0570fec75ec4eafe0c3`.
See `reviews/clean_release_4391.md`. Clean build47048 finished and was
consumed; clone `tmp/clean-checkout` remains at this clean release commit.
Root build caches were not cleaned. Older coherent3917/3404/3162/2804/2390
releases and earlier immutable resume checkpoints remain preserved.

## New unregistered source state

69 new Lean sources are preserved, with361 selected source directives:

- 58 modules /277 reports independently reviewed and compiled.
- 10 modules /74 reports have clean author-final compiles and objects;
  independent audits remain pending.
- One10-report draft, `ConicalRoundedHCurl`, has never compiled and has no
  object. Its statements are not verified results.

The68 checked new modules contain351 reports; these are targeted results,
not a new clean combined release. Do not add them to4391 as an aggregate
claim. No new module has been registered in `OQ14.lean`/`lakefile.lean`.
Do not run a root aggregate that includes the unfinished draft.

Independent pending modules:
`ConicalRoundedMaxwell`, `DensityCurl`, `DensityDerivatives`, `DensityWeak`,
`HarmonicRadiationFactors`, `HarmonicVectorDecomposition`,
`ParityDensityMaxwell`, `PolynomialVectorCalculus`, `SourceTERadiation`,
`SphereParityDifferential`.

Exact source/log hashes, report counts and statuses are in the checkpoint
manifest and saved evidence. `tmp/audited_after_4391.json` records the58
independent checks and is preserved in checkpoint evidence. The two record
scripts are incremental and reject changed frozen receipts. Old one-time
integration/preservation/checkpoint scripts must not be rerun blindly.

## Root source Maxwell/radiation work

Actual normalized source fields now satisfy both weak Maxwell equations
on all punctured space, including core, every layer and exterior, for both
TM and TE and every prescribed positive frequency. This is actual source
assembly, not a regular-origin solution. `SourceRadialSystem.Data` has NO
dispersion field: TM uses explicit layer q²=sigma; TE uses sigma=1, and
the general constitutive coefficient is actual q²/sigma. Do not restore the
obsolete pre-refactor Data or earlier audit logs.

SourceRadialSystem14, SourceElectricProfiles11, RadialToroidalCurl1,
SourceMagneticProfiles8, SourceUnclippedMaxwell6, SourceGeneralMaxwell8,
SourceDielectricMaxwell4 and PuncturedMaxwellScaling5 are independently
audited. Tests must have support avoiding the origin. Frequency fields are
literal E(k*x), H(k*x), with coefficient a(k*norm(x)). Origin source
distribution normalization is not proved by these statements.

HarmonicRadiationGeometry4 and SourceRadiation4 are independently audited.
The actual all-degree TM weighted defect equals outgoing amplitude times
phase times pD(r) times the normalized toroidal factor. The uniform angular
bound proves convergence for every path with norm tending to infinity.
HarmonicRadiationFactors8 and SourceTERadiation4 are author-final PASS,
awaiting independent audit. TE has actual pD*poloidal and p/r*radial terms.
Final TE compiler49373 completed exit0; earlier failed logs are obsolete.
Next: audit these two, apply the already genuine spatial dilation to both
radiation defects, and bundle actual Maxwell/radiation source families.
Full origin distribution and spatial dyadic Green identification remain.

## Scalar Green and vector completeness — modal_sol

Physical reaction coefficients are **-(gamma+I)**, not gamma alone. Actual
joint spatial derivative majorants, summability and compact C-norm Tannery
limits are proved, including the origin in the regular reaction series.
The radius condition depends on the chosen finite derivative order:
R>=exp(1)*B and B>=degreeScale(order,ball). Do not claim all orders at a
fixed insufficient radius.

Actual free scalar Green modes are uniformly summable on angular sphere
pairs for0<r<s. Genuine jump/Wronskian coefficients plus actual angular L2
expansion and full-support injectivity identify the continuous sum with
Phi. ScalarGreenSpatial gives literal polynomial-coordinate HasSum for
nonzero x,y with unequal norms, either radial order. These are independently
audited. Equal-radius/diagonal issues and the vector dyadic are separate.

PolynomialVectorCalculus12 and HarmonicVectorDecomposition9 are author-final
PASS, awaiting independent audit. Actual positive-degree three-sector
harmonic vector decomposition is proved; tor(Q)=Q cross x. Next: degree-zero
case, representative polynomial span/injectivity, actual vector sphere
density and transverse completeness, then normalized TE/TM dyadic assembly.
No completeness draft was started. See their author reviews.

## Conical coefficient, cutoff and peaks — fredholm_sol

The actual annular coefficient functional has positive static normalization
and is retained nonzero at small positive frequency. The genuine projected
expansion with0<nu<1 proves the actual electric field essentially unbounded
in every tip ball. ConicalDynamicHotspot removes data-existence premises for
every prescribed positive cap contrast and genuine cap geometry.

Actual bounded-AE material convergence gives strong sqrt-multiplier, volume
block and inverse-response convergence with a common small-frequency
radius. L2 convergence preserves positive-volume superlevel sets above
every fixed threshold. Exact physical-coordinate pullback connects this
to the actual conical field. These results and ConicalTipRounding14 and
ConicalRoundedPeaks8 are independently audited.

The explicit smooth radial gate is zero for norm<=1/(n+1), one for
norm>=2/(n+1). The coefficient shares contrast and outer support and
converges AE to the sharp cone. This is smooth removal of material at the
tip; it does not assert globally smooth interfaces or finite maxima.

ConicalRoundedMaxwell14 author-final PASS constructs genuine compact-source
Green E/H, identifies the L2 volume response AE, proves actual material
self-consistency and both inner weak Maxwell equations. Root independent
audit is pending. Its log is `lean/ConicalRoundedMaxwell.final.log` (outside
lean/logs). ConicalRoundedHCurl10 is the sole uncompiled draft; compile/fix
it first when resuming this track. Then transfer peaks to literal electric
representatives through field_ae and bundle actual Hcurl rounded families.
Actual illumination Runge remains essential: the present excitation is an
annular source. Test-function density is not solution-space Runge density.
No fixed-point/plane maxima follow from L2 convergence alone.
Exact handoff: `reviews/conical_rounding_stop_handoff.md`.

## Complete plane flux and density Maxwell — continuation_review_sol

Actual finite illumination bounds derive the source massO(a²), source
errorO(a³), genuine moving gap and inverse smallness. The exact complete
parity total plane flux contains four reaction terms; their whole-plane
L1 remainder tends to zero in the pure electric-wall finite-incident regime.
FiniteSpherePlaneLimit compares the constructed actual inverse total flux
to the actual static trial incident+free flux. Finite coefficient-mass
control and geometric hypotheses remain explicit. These modules are
independently audited; no final flux limit or mass/error premise is assumed.

Five latest density modules (27 reports) have author-final PASS and await
root independent audit. Actual density differentiation/curl interchange
proves both global vacuum equations and the genuine magnetic partner of
the material reaction. DensityWeak gives the genuine weak-test upgrade.
No unfinished draft in this track. See
`reviews/continuation_stop_2026_10_22.md` and its sources JSON.

Next: instantiate density weak curl pairs and assemble the actual full
material TestMaxwell pair through the derived modified incident datum;
then specialize to finite balls and the legitimate continuous strip/plane
representative. A three-dimensional AE identity cannot simply be restricted
to a plane. Later derive whole-plane static trial/dipole comparison, actual
Gram interpolation/incoming-power normalization and physical finite-stack
identification. Do not infer whole-plane convergence from local convergence.

## Remaining final scope

Still essential: actual full spatial dyadic/source normalization,
physical finite-stack/channel identification and Gram/power construction,
illumination Runge, final rounded driven realization, actual reciprocal
modal residue normalization, infinite-degree pole isolation and simultaneous
three-dimensional modal maxima in the prescribed plane patch.

The written unrestricted-channel disproof fixes delta>eta>0 and complete
scattering output with common frequency/material bounds and unrestricted
finite support. Delta<=eta, receiving-only, sole-connection and uniformly
bounded-support variants are separate. The written modal theorem uses actual
reciprocal-residue normalization, arbitrarily high Q, fixed real frequency,
common bounds and N-dependent insertion contrast. Preserve the scope.
The original Downloads manual was absent at the last recorded comparison;
see reviews/original_scope_2026_10_20.md. No current exact comparison claimed.

## Safe resumption

Workspace D:/oq14, PowerShell. Python:
`C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Lake: `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`.
Lean4.19.0, mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, nine pinned deps.
Use Python -X utf8 or explicit UTF-8 file encoding. Some compiler logs have
UTF16 BOM; decode accordingly. Compile in cwd `lean`, never project root.
Do not compile a dependent file while its imported object is being rebuilt.
Never clean root lean/.lake/build. Use the separate clone for clean releases.
Only propext, Classical.choice and Quot.sound are accepted. Error recovery
reports are not proofs. Complete remaining audits before registration.
Unrelated untracked `sites/` must not be touched, staged or packaged.
No external publication or scheduled continuation. Work is stopped.

# Stage 65 — STOPPED checkpoint: actual complex outgoing and Debye fields

Date: October 28, 2026. Parent: `506a5393d80de5a2b5be8afb5293e97270a0a030`.
The user explicitly requested checkpoint and stop. All three Terra agents stopped;
no compiler sessions remain. Do not resume proof work without a new user request.

The accepted incremental ledger is 495 modules / 3632 standard-only reports,
adding 22 modules / 57 reports after stage 64. Every source/log hash and report
list was checked, and all previous 473 records remain unchanged. These are
targeted checks against existing dependency objects, not a clean aggregate build.
Clean aggregate release 5238 is unchanged. Full OQ14 closure remains unfinished.

Checked mathematical progress:

- AnalyticOutgoingSelection eliminates the incoming radial component of the
  ACTUAL exterior electric response at every nonzero complex frequency, using
  entire radial L2 dual determinants and the true Wronskian. OutgoingModeGluing
  gives one amplitude throughout each whole observation annulus. No invalid
  lower-half-plane inference from a scaled far-field limit is used.
- WeakDebyeScalar derives the weak Helmholtz equation for x dot E from actual
  component equations and divergence. DebyeScalarL2 constructs its actual L2
  datum. ComplexKernelDebye discharges every premise for genuine sphere-kernel
  vectors and proves r^2 times the actual radial electric coefficient is one
  regular Riccati mode throughout the interior, for every harmonic degree.
- General positive-degree radial/poloidal weak moment coupling is derived from
  actual compact tests, angular L2 slices and justified radial integrability.
  WeakDerivativeIdentification supplies the classical/weak derivative uniqueness
  tool needed to turn this into an explicit tangential coefficient formula.
- The actual complex magnetic field is constructed as a locally L2 gradient-
  source integral. Its localized L2 operator is entire. ComplexMagneticMaxwell
  proves BOTH first-order Maxwell equations with the actual electric response
  and true source, including interface-crossing tests.
- Actual magnetic difference quotients and their weak curl equations, the flat
  inverse-weight commutation, lower energy coercivity, a weak Green identity,
  and an explicit local magnetic quotient bound are checked. These do not yet
  give the uniform differentiated-curl or one-sided interface sup estimate.

Exact accepted source/log/exit bytes are in stage65-raw-evidence.zip; metadata is
audit-metadata/stage65.json and audited_after_5238-stage65.json.

Pending work is separately preserved in stage65-pending-drafts.zip, with exact
byte hashes and statuses in audit-metadata/stage65-pending-drafts.json. It is NOT
part of the accepted ledger and must be independently audited before promotion.
The working copies remain in lean/. The archive also preserves author logs and
reviews. It includes later magnetic regional Maxwell/Helmholtz/Debye/parity
modules, localized/nested cutoff-forcing modules and these unfinished drafts:

- KernelRadialMomentBridge: passed a draft check, no final object/freeze/review.
  KernelBridgeProbe is diagnostic only. Finalize the bridge, substitute the
  actual regular radial mode into HarmonicMomentIntegrability's weak relation,
  then use WeakDerivativeIdentification for the tangential coefficient.
- MonopoleFlux: failed author2 check at a cast-of-one simplification. Resume by
  resolving that error, then prove the degree-zero coefficient vanishes using
  weak flux conservation and the nonzero-frequency regular radial equation.
- GlobalToRegionalCurl: the added restrict_weakMaxwell theorem is uncompiled.
  Finish this only after resume, then establish a genuine uniform flat-patch
  differentiated-curl estimate by nested localization and energy absorption.

Modal next: audit pending magnetic modules, prove actual magnetic axial rotation
covariance and combine with reflection-odd x dot H to eliminate the TE scalar in
the electric sector. Derive vector coupling, weak interface matching, all-degree
kernel classification, selected-sector rank-one simple residue, then the modal
perturbation/exact-plane construction. Scalar harmonic degrees are not TM degrees.
Hotspot next: close the uniform flat estimate, extend to the fixed curved collar,
prove one-sided continuous representatives and compact attainment. The maximum
may lie on a material interface; use the manuscript's one-sided E_* convention.

Do not edit accepted/frozen source or evidence bytes. Do not register abandoned
ModalDrivenFarB or diagnostic KernelBridgeProbe. Do not touch unrelated sites/.
Do not rerun the old 5238 integration script. Use the pinned Lean 4.19.0 toolchain.

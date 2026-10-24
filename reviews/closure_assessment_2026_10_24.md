# OQ14 closure assessment — October 24, 2026 (root)

Purpose: state exactly how far the Lean formalization is from closing the
OQ14 statement after the October 24 continuation, branch by branch, with the
blocking obligations named. Nothing here is a claim of closure. Release 5238 is
unchanged; the incremental ledger holds the independently audited additions
(counts in RESUME.md).

## Target recalled

Three pieces together constitute "full OQ14 closure" as recorded in CLAIMS.md
and the October 23 stop notes: (A) the unrestricted counted-channel theorem
(delta > eta > 0, arbitrary finite N, fixed frequency, common positive
dielectric bounds, unrestricted finite device support, complete scattering
output); (B) the fixed finite-power hotspot theorem (one unit-power input,
arbitrarily many rounded peaks, arbitrary N, unrestricted finite support); (C)
the modal theorem (arbitrarily high Q, fixed real pole frequency, common
bounds, N-dependent insertion contrast, simultaneous genuine three-dimensional
maxima in the prescribed plane, residue normalization). Only the written
manuscript proves (C) (CLAIMS.md `ms:modal-packing`, "not yet Lean-formalized").

## (B) Hotspot: formal status

Proved in Lean and audited: for every sufficiently small positive frequency,
one nonzero finite angular input with unit limiting inward half-field power is
fixed before the rounding level, radius, coordinate and threshold; the rounded
total fields satisfy the weak Maxwell system with regional H(curl)
representatives, converge on the ball, have a nonzero singular coefficient with
the projected-graph identity, and exceed every threshold on sets of positive
measure (ConicalNormalizedInputCoefficient, ConicalNormalizedInputHCurl). The
incident is identified exactly with the finite mixed Debye field
(FiniteMixedHerglotz).

Remaining: the input is chosen per frequency, not uniformly in k; "unit power"
is the limit of the inward half-field Poynting integral, not the total-field
power (the total-field sphere flux vanishes almost everywhere for the global
weak class, LosslessSphereFluxConstancy, so a total-field normalization must go
through the incoming/outgoing split); peaks are per-coordinate superlevel sets,
not counted separated maxima; no plane-maximum statement. These are
quantitative sharpenings, not missing mechanisms.

## (A) Channel: formal status

Proved and audited: the explicit parity device's whole-plane L1 flux
convergence to exact finite-ball dipole flux, uniform over the physical-power
unit ball of a finite orthonormal input space (RestrictedTEUnitSphere), with
passage/bypass transfer under uniform L1 error (RestrictedTEPassageTransfer);
the parity block is a named shell block of the shell-inclusion algebra
(RestrictedTEParitySandwich). The finite-shell source reduction is formalized
end to end: combined paired-shell-plus-inclusion block = shell block plus an
effective inclusion block whose operator equals the clamped paired-core operator
for large shell index, with operator-norm convergence to the central-inversion
limit, inverse stability, and automatic smallness below an explicit inclusion
radius (SourcePairedReduction, SourcePairedSmallInclusion). On the
proper-half-turn-invariant source sector the limiting effective block IS the
parity device block with B = q^n, and the paired-shell effective solutions
converge to the parity solution (SourcePairedWallKernel,
SourcePairedParityLimit).

Done since the first draft of this note: the half-turn equivariance of the
parity block (HalfTurnVectorAction, HalfTurnParityEquivariance, including the
physical Fourier projection) and the closure theorem
`SourcePairedParityClosure.paired_shell_solutions_tendsto_parity_of_small`:
for a symmetric inclusion and half-turn-fixed data, the paired-shell effective
inclusion solutions converge to the explicit parity-device solution, all
hypotheses discharged by explicit smallness. Single-mode exterior plane flux
density bound (SourceRemotePlaneFlux).

Also done: dipole-flux concentration, plane jets and the counted-channel
inequality for the explicit parity device with arbitrarily many channels
(RestrictedTEPlaneJets.explicit_parity_device_counting,
RestrictedTEConcreteDevice.concrete_counting), and the single-mode exterior
plane flux tails (SourceRemotePlaneTail).

Done in the third continuation: finite-band sums (SourceRemotePlaneBand),
annulus layers (SourceAnnulusStateBounds, SourceAnnulusPlaneFlux), all-degree
radial state bounds (BarrierSourceStateBounds, BarrierAnnulusStateBounds),
exterior constants uniform in the shell index (SourceRemotePlaneUniform:
the absolute finite-band plane flux outside the core vanishes with the shell
index); the partner-ball device with half-turn-fixed data for every TE input.
Done since: the all-degree remote return flux (series step, degree-summable
constants, all-degree flux outside the core: stages 18, 20, 22); the closure
theorem instantiated for the partner device (stage 19); unit throughput of the
complete lossless field and of the actual device, with the isometric scattering
map (stages 23, 26); the counted-subspace statement for the actual device
through one fixed square, for every N and every window, with the dielectric in
[1, eps_plus], modulo a whole-plane L1 interface (stages 27, 29, 31, 34), now
reduced to field estimates (stages 35, 36); the plane fields of the paired
shells converging on compacts to the parity device, electric and magnetic
(stages 21, 24, 28, 33, 35, 40); the background lift (stages 25, 30, 32, 39,
42); the radiated field majorant in the growing core (stages 37, 41) and its
mode series beyond the stack radius and on the annulus (stages 38, 43); the
assembly with the n-dependent parity phase (stage 42); and the final theorem
`RestrictedTEActualDevice.actual_counted_subspaces_device` (stage 44): the
counted-subspace statement for the actual paired dielectric with no field
hypotheses, depending only on the three standard axioms. The piecewise device
fields whose flux it counts are the physical L2 fields almost everywhere in
space off null sets (stages 38, 40, 42, 43), and the consolidated statement
`PhysicalFieldIdentification.physical_identification` (stage 45) identifies the
L2 total electric field, its continuous exterior representative and the
pointwise total magnetic field of the combined solution with the space
versions of the piecewise fields, region by region, with no hypothesis on the
annulus; the literal corollary for the final theorem's radiated plane fields
(zero on the inner circle and below the threshold index) is in progress. Remaining caveats: unit frequency, finite even-degree
TE inputs, the open square up to parametrization, eventual statements without
rates. Then, in the original list:
(2) tying the parity-device inputs to half-turn-fixed data
and the parity plane flux to the paired-shell total-field flux, so that the
parity count transfers to the actual finite dielectric; (3) unit throughput /
`ca:powerbudget` (needs a Riemann-Lebesgue cross-term step absent from the
tree); (4) the named even-m basis is not in the tree (the even sector is
intrinsic), and the interpolation geometry is narrower than the manuscript
arbitrary plane points.

## (C) Modal: formal status

Proved: sphere-interface residue normalization and derivative pairing, fixed
real-frequency arbitrary-Q shell poles with nonzero residue, meromorphy of the
volume inverse with discrete exceptional set, finite-rank Laurent structure,
the abstract rank-one residue form (SimplePoleResidueForm) and the geometric
plane-maximizer lemma (AxisymmetricPlaneMaximizer).

Blocking: `weighted_mode_in_volume_kernel` needs a complex-frequency radiation
representation formula that is not in the tree; all-degree pole separation and
simplicity need Hermite–Lindemann (transcendence of exp of a nonzero algebraic
number), which Mathlib at the pinned revision does not contain and which the
project's no-axiom rule forbids assuming; the modal coefficient continuation,
modal rounding convergence and the finite assembly are large. The modal
theorem therefore cannot be closed in Lean in this session without either
importing an axiom (forbidden) or formalizing Hermite–Lindemann.

## Verdict

The Lean formalization now covers every mechanism of (A) up to the remote-flux
bridge and the transfer of the parity-device count to the actual dielectric
(the physical symmetry bridge is closed on the invariant sector and the count
is proved for the explicit parity device), and every mechanism of (B) up to quantitative
sharpenings, with all additions independently audited. (C) is proved in the
manuscript only and is blocked in Lean by a missing transcendence theorem. Full
OQ14 closure must not be claimed.

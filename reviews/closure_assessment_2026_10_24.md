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
annulus; and `PhysicalDeviceFields.device_fields_physical` (stage 46) shows
that the exact fields counted by the final theorem are these space versions at
every plane point off the inner circle and almost everywhere on the plane. The
field-identification chain is complete. Stage 49
(`RestrictedTEFrequencyScaling.counted_subspaces_at_frequency`, standard axioms
only) removes the unit-frequency caveat in the following exact sense: for every
k > 0 the unit-frequency device of half-side k L, with its coefficient dilated
by 1/k (`scaleCoeff k`, dielectric still in [1, eps_plus]) and its fields
dilated with amplitude factor k (`scaleField k`, `scaleMap k`), has dilated
physical fields that are a weak Maxwell pair at frequency k with the dilated
dielectric (`TestMaxwell k`, stage 48, with the stage-45 identification
transported), dilated finite TE inputs that are vacuum weak Maxwell pairs at
frequency k with limiting inward power `physicalPower` (stage 47), and the span
of the same orthonormal family is a counted subspace through the square of
half-side L with the same scattering map, power and thresholds. Not asserted:
that the dilated fields are the volume solution
`MaterialField.total (scaleCoeff k c) k …` of a dilated L2 datum (no dilation
of the L2 machinery and no uniqueness theorem at frequency k are in the tree;
reviews/frequency_scaling_design.md, section 5). What the Lean development
still does not contain is any rate in n or r and the manuscript's own
parametrization of the square. Remaining caveats: finite even-degree TE
inputs, the open square up to parametrization, eventual statements without
rates, and the frequency-k fields being dilations rather than re-solved volume
equations. Then, in the original list:
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

## Addendum (fourth continuation, same day)

Stages 47-49 extend (A) to every frequency k > 0 in the dilation sense stated
in the channel section (scale invariance of the frozen weak system, of the
plane flux through the dilated square, of the inward power and of the far
amplitude; the k-frequency device is the unit-frequency device dilated by 1/k).
This changes nothing for (B) and (C); full OQ14 closure is still not claimed.

## Addendum (fifth continuation, 2026-10-25)

Stage 50 (`CountedSubspacesManuscript`) states (A) in the manuscript's literal
form: for every frequency k > 0, eps_plus > 1, side L, 0 < tau < 1 and
0 < eta < delta fixed before N, every N has a single finite device with explicit
gain and shell indices, dielectric in [1, eps_plus], an N-dimensional counted
subspace of finite TE inputs through (-L/2, L/2)^2 and unit throughput of the
scattering map; its docstring lists what is not asserted (finite TE inputs,
dilation sense of k, identification in space, no rates). The constructive
identification of the dilated fields with the frequency-k volume solution is in
progress. (B) and (C) are unchanged; full OQ14 closure is still not claimed.

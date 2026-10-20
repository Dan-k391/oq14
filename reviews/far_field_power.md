# Actual far fields and radial outgoing power

Status: targeted compilations and independent source audits passed; these new
modules are outside the coherent 1312-export package.

## ScalarFarField — 8 exports

SHA256: `517928a052a3efa0711a6edbfcdfeb4ce3ede7c3c308facfa214167680483cb9`.

The exact compact-source integral is multiplied by `r exp(-ikr)` on a unit
ray. A rationalized distance identity proves the phase limit. A uniform
source-support bound justifies dominated convergence. The limit is the actual
Fourier integral with the outgoing Green normalization `1/(4π)`.

Root full-source review passed. Independent modal Sol review and pinned
recompilation passed. Only standard foundational dependencies were printed.

## MaxwellFarField — 15 exports

SHA256: `3c0373832ac8fd4621f21bfdc41346f88a4013ab2a6795ed8dacc9192d8b7de9`.

The actual electric dyadic response and magnetic curl response are compared
with their leading transverse fields using the previously proved uniform
inverse-square error. Their scaled limits are `k²(I-nnᵀ)A` and `k² n×A`.
The latter equals `n×E∞`, and `n·E∞=0`. These are actual vector limits, not
limits of an unspecified almost-everywhere representative.

Root full-source compilation and review passed. Independent modal Sol source
audit, normalization/sign check and pinned recompilation passed. All fifteen
reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## FarFieldPower — 9 exports

SHA256: `0d510b5c7cb24df54d91acac1275e524c4d4e1f685d958e015e1d9c61310ec05`.

The actual time-average radial power is `Re(n·(E×conj H))/2`. A proved
complex-vector triple-product identity, the real unit direction, and
transversality identify the amplitude power with `energy(E∞)/2`.
Common complex scaling multiplies power by the squared scalar norm.
Continuity and the two actual vector limits therefore give the pointwise
directional limit of `r²` times the actual radial power.

Root compilation and full-source audit passed. Reciprocity Sol independently
read and recompiled the exact file: exit zero, nine standard-only dependency
reports. The independent log is `lean/FarFieldPower.independent-sol.log`.

## Scope

Frequency is real. The sources are compactly supported componentwise L1.
No nonzero amplitude is assumed or concluded. These three modules establish
fixed-ray limits; spherical integration is separate ongoing work in
AngularPower. Neither arbitrary-size outgoing uniqueness nor the complete
channel or modal-hotspot theorem follows from these modules alone.

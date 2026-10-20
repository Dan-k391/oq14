# Actual compact-source Maxwell plane-tail verification

Author: continuation_review_sol. Date: 2026-10-20.

Source: `lean/MaxwellPlaneTail.lean`.
SHA256: `7C186CC4EA54D5967F89FCDA0760E44181CEEA93B57202DE241E4C5E5F2423BB`.

Pinned Lean 4.19 targeted compilation and importable olean emission passed
with exit 0. All eighteen selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Root independently read
the complete source and reran the pinned compiler at this exact hash:
exit 0 and all eighteen reports standard-only. Independent mathematical
and compiler audit: PASS.

The fields are the literal exterior dyadic electric integrals and actual
magnetic curl response of integrable compactly supported vector sources.
The source radius R is nonnegative. The actual leading fields from
MaxwellRadiation obey component bounds of order sourceMass/norm(x), and
the proved actual field-minus-leading errors obey order sourceMass/norm(x)^2.
Their constants are explicit functions of real frequency and R.

On the actual plane x2=0, the complex normal cross product of a leading
electric field and the conjugated leading magnetic field vanishes exactly.
This is proved for two different sources, using the actual radiation
identity and actual real radial direction. It does not rely on an angular
average, signed-flux cancellation between regions, or a same-source energy
identity. Expanding the actual cross product around its two leading fields
therefore leaves an inverse-cube bound. The inverse-fourth-order product
is absorbed using norm(x)>=2. All source masses are actual L1 component
norm sums, not assumed field amplitudes.

For any two sources rho and sigma supported in the same radius-R ball,
the actual complex normal cross product is bounded by
tailConstant(k,R)*sourceMass(rho)*sourceMass(sigma)/norm(x)^3 outside both
radius 2R and radius 2. The ordinary real time-averaged normal power is
the real part of this expression divided by two, yielding the corresponding
diagonal bound. Bilinearity means these estimates control coherent source
cross terms as well as individual source responses.

The actual plane embedding from Euclidean 2-space into Euclidean 3-space
preserves the norm and is continuous. The actual exterior responses are
continuous there outside the source ball, so their normal cross product
is AE strongly measurable on every sufficiently distant exterior disk.
PlaneInverseCube supplies genuine two-dimensional integration, proving
actual complex bilinear-flux integrability and an absolute tail integral
bounded by tailConstant*mass(rho)*mass(sigma)*diskConstant/T. The ordinary
physical normal-power tail has the extra factor one-half.

Precise scope: tails outside disks with T>=2 and T>=2R for actual outgoing
compact-source responses in homogeneous vacuum. No global-plane local
trace regularity through source support is asserted here. Incident regular
waves, the incoming part of reaction fields, uniform remote-stack bounds,
all-angular-order Green convergence, and the complete physical channel
construction remain separate obligations. No part of the latter conclusions
is hidden in the final theorem's premises.

The source contains no standalone custom axiom/constant declarations or
proof-hole tokens. Targeted compiler verification: PASS.

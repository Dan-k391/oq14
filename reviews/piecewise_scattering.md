# PiecewiseScattering — actual physical scattering without small-support premises

Source: `lean/PiecewiseScattering.lean`

SHA256: `3CE78ABE7488BF4FC618A4AD290D97D01EA313CA14FA5C9522CE3050452AA16C`

Evidence: `lean/logs/piecewise-scattering-check.log`. Final compile exited
zero without warnings, created an importable object (262840 bytes), and
emitted seven selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The physical incident datum is the existing actual compact material
square-root-weighted incident electric field. Only local component L2
regularity on closed balls and actual vacuum Maxwell tests are imposed on
the incident fields. The scattered electric field uses the existing
continuous exterior representative; the magnetic field is the existing
actual outgoing source convolution.

For any actual solution of that literal volume equation, the new
PhysicalFields conclusion derives both dielectric Maxwell test equations,
all-ball local component L2 regularity, exterior continuity of the
scattered electric field, and actual polarization rho=chi Etotal. None
of these field equations is an assumption. The helper uses existing
local response estimates whose signatures contain no smallness premise.

The actual scattered Silver–Müller defect is identified with the actual
ordinary exterior source defect outside the support radius. Its uniform
inverse-square bound and radius-weighted zero limit along every escaping
path follow from the proved compact-source radiation theorem. A separate
literal equality identifies this defect with the total electric and
magnetic fields minus their incident fields.

The main existence theorem applies the actual geometric Partition-based
volumeBlock_isUnit theorem. Its witness is exactly the existing
MaterialField.solution, namely the actual Ring.inverse applied to the
literal incident datum. It proves that volume equation, uniqueness of the
volume unknown, the actual inverse operator norm bound, and all the above
physical field conclusions. A classical C1 vacuum-incident wrapper proves
the incident local L2 and test hypotheses from actual classical Maxwell.

Scope: support size is unrestricted for materials satisfying the explicit
Partition geometry and positive real frequency. There is no old numerical
smallness premise. This is not an extension to arbitrary measurable
material geometry. The inverse bound is its actual operator norm, not a
uniform numerical Neumann bound. Uniqueness here concerns the actual
volume unknown; no equivalence with every arbitrary outgoing weak PDE
solution or resulting broader PDE uniqueness is asserted.

Self-review checked actual datum construction, inverse cancellation,
volume unknown uniqueness, polarization transfer to the exterior
representative, both Maxwell signs, local response assumptions,
total-minus-incident identities, support-radius restrictions, and the
arbitrary-filter radiation limit.

Root independently read the complete final source and independently
recompiled all seven exports at the recorded hash. Source frozen.

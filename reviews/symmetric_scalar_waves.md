# Literal symmetric scalar plane waves and actual TE Maxwell fields

Frozen source: lean/SymmetricScalarWaves.lean.
SHA256: AD7F8022E9E4F35377620C652D52105C08E7EF709E87FD8F7A3BB3A13A3A301A.
Author final pinned compiler/object PASS: exit 0, no warnings, eleven reports
using standard foundations only. Log: lean/logs/SymmetricScalarWaves-final.log.
Independent audit pending.

The scalar is literally cos(a*x0+b*x1)*cos(c*x2). Genuine first and second
Frechet coordinate derivatives establish the actual scalar Helmholtz equation
when a^2+b^2+c^2=k^2. It is invariant under equatorial reflection and the
half-turn about the vertical axis. For a^2+b^2<=k^2, the actual real square root
c=sqrt(k^2-a^2-b^2) discharges dispersion, and the literal Debye TE fields
satisfy both vacuum Maxwell equations globally. No PDE is an input to that
final theorem.

These waves are an intermediate point-angular-measure family in the manuscript
ct:jets argument. Neither finite physical incoming power, finite harmonic-band
membership, nor jet surjectivity is claimed. Smooth angular approximation and
actual restricted-band realization still require construction; this module
does not replace the restricted TE sector by general electric-wall J/K fields.

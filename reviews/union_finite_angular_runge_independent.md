# UnionFiniteAngularRunge — independent root audit

PASS, 2026-10-28. Full source and mathematical scope reviewed independently. Source SHA256 `722274446F3789F3C3359E749BFD280B91E030DC04546ACD5CCA1BA241ED7CC3`.

Fresh pinned source check completed with exit 0. Audit log: `lean/logs/UnionFiniteAngularRunge-root-audit.log`, SHA256 `0FACE98CA4B0AA2361B36F82903C5FE518F3D9F4EF7877F4531CA1F338FD4D5F`. Exit receipt: `lean/logs/UnionFiniteAngularRunge-root-audit.exit.log` = 0. All 6 reports use only standard axioms; no errors, warnings or proof placeholders. The check uses existing dependency objects, not a clean dependency rebuild.

The actual finite plane-wave approximation on the union is replaced by one finite-support transverse vector spherical-harmonic Herglotz input. The proof uses uniform approximation on the enclosing ball solely for the entire plane-wave sum; it does not apply centered-ball Runge to the source response. An explicit finite-measure vector L2 bound and a positive error budget yield the final union-domain error. Input normalization, common material response, nonzero local coefficients and rounded maxima are not claimed here.

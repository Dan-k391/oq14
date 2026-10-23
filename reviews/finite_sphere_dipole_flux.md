# Exact static finite-sphere dipole flux

Frozen source: lean/FiniteSphereDipoleFlux.lean.
SHA256: 67FC438C3C395A2D24CC208BB5A3DD3D970FAF52D30AB1F6839F25D087EBEED0.
Author final pinned compiler/object PASS: exit 0, no warnings, two reports
using standard foundations only. Log: lean/logs/FiniteSphereDipoleFlux-final.log.
Independent audit pending.

The literal indicator source of finitely many uniformly polarized balls has
an exact static plane response equal to the genuine volume-weighted dipole
sum. Pairing that actual field with the literal finite electric-wall magnetic
illumination yields exactly the stated dipole Poynting cross term. The proof
invokes the already constructed Newton/ball exterior identity; it supplies
neither a dipole approximation nor a field identity as a premise. Actual
positive ball radii and plane gap are explicit.

# Actual inverse residual and physical source errors for the sphere trial

Source: `lean/StaticSphereResidual.lean`.
SHA256: `ECDCBB2EE94A379451E53EF3DCEE6AFFC0FBCDA3810E0ED3FAE63993EE7A2323`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all six reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticSphereResidual-final.log`. Root independent full-source
mathematical and pinned compiler review PASS, no warnings and all six reports
standard-only. Log: `lean/logs/StaticSphereResidual-root-audit.log`.

The actual explicit parity-kernel inverse controls the error of any trial
by twice its actual block residual when the already derived perturbation
bound is at most one half. For a genuine static trial the residual separates
into actual forcing variation and actual perturbation applied to the trial.
The isolated sphere instantiation discharges its static equation using the
previously proved existing weightedBlock identity; the static trial equation
is not left as an assumption in that sphere theorem.

The physical polarization L2 error is then bounded by sqrt(chi) times the
material-weighted error. The actual coordinatewise L1 error against the
constant-ball physical polarization is bounded by the same quantity times
sqrt(actual support volume). Its proof uses actual source subtraction and
the already proved compact-support Cauchy-Schwarz estimate.

These are quantitative residual bounds for actual operators, with explicit
forcing difference and genuine kernel-derived perturbation bound. They do
not yet claim powers of the inclusion radius, actual finite-stack Green
identification, or several interacting spheres. Incident derivative/variation
estimates and geometry must still discharge those remaining quantitative
inputs before a small-inclusion asymptotic theorem is asserted.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 6 reports using only standard foundations. Final source SHA256 `ecdcbb2ee94a379451e53ef3dcee6affc0fbcda3810e0ed3fae63993ee7a2323`. Independent log: `lean/logs/StaticSphereResidual-root-audit.log`; log SHA256 `15469c77ab78370bdf11bc6eec44e7e26b7176a9342e99159fe4110f218cf7fa`. This certifies the stated scope, not either complete OQ14 construction.

# Exact actual parity plane flux

Frozen source: lean/HerglotzParityPlane.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/HerglotzParityPlane-final.log.
Independent audit pending.

The actual electric reaction and its proved magnetic reaction have exact
plane selectors: the normal complex flux equals the literal J/K regular
flux precisely for electric=false and magnetic=true, and vanishes in the
other three cases. This follows from the actual reflected component
formulas and complex conjugation, with no field/parity assumption.

The actual parity flux therefore inherits the genuine inverse-cube tail
and full-plane integrability with a uniform L1 bound for source centers in
a fixed ball. There is no positive plane-gap or integrable-density premise.
This is a literal sphere-kernel result; physical finite-stack Green
identification and finite-sum/coherent-limit assembly remain further work.
SHA256: 441D9B3883E861FD7048E031257BC3007D83FC5678F4DA39DC60329E15A461FB

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `441d9b3883e861fd7048e031257bc3007d83fc5678f4da39dc60329e15a461fb`. Independent log `lean/logs/HerglotzParityPlane-root-audit.log`, SHA256 `4735b955c9a4a30bca20bb1f8187fe9e804819998d38f96eedad6e0b316da314`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

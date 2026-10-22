# Actual point Herglotz whole-plane flux

Frozen source: lean/HerglotzPointTail.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/HerglotzPointTail-final.log.
Independent audit pending.

The literal actual J/K point columns are expanded using their proved
incoming/outgoing dyadic identities. All four actual mixed-frequency flux
terms have the genuine inverse-cube plane tail from PointMaxwellTail.
Their constants are even in frequency, so the actual J/K flux obeys the
same explicit tail constant, uniformly for two source centers in a fixed
ball and all column indices.

Actual J/K continuity and their uniform sphere-integral entry bounds give
a bounded local disk envelope. Combined with the actual inverse-cube tail,
this constructs a genuine integrable whole-plane envelope, uniform in the
two centers. The actual full-plane L1 norm is bounded by its actual integral;
the tail L1 norm is bounded by tailConstant*diskConstant/T.

Only k nonzero, a nonnegative enclosing radius and actual point-center
membership are required. No positive point-plane gap, compact-density
surrogate, field identification, tail or integrability conclusion is
assumed. Finite parity-center assembly and physical finite-stack Green
identification remain separate constructions.
SHA256: D666BA65A6588E087C0409492BD97D3AC04ACB362C63C5060282F70B45A37CF1

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `d666ba65a6588e087c0409492bd97d3ac04acb362c63c5060282f70b45a37cf1`. Independent log `lean/logs/HerglotzPointTail-root-audit.log`, SHA256 `fe685826113dba7c161f8e9de816a3275ee2527923fba95188109c06e365ec69`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

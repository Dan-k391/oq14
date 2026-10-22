# Actual finite-source parity Herglotz Maxwell fields

Frozen source: lean/FiniteSphereMaxwell.lean.
SHA256: 09AC3F5F9521C527BB925DD3C98D3F538F12D9362970E8023F55A259B4296847.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all three reports standard-only. Log: lean/logs/FiniteSphereMaxwell-final.log.
Independent audit pending.

The fields are exactly FiniteHerglotzFlux.electric/magnetic, with arbitrary
finite centers, column choices, parity choices and complex coefficients.
Actual Frechet differentiability follows from that of the derived literal
parity point fields. Real Frechet finite-sum differentiation derives curl
linearity; the actual point Maxwell identities prove both global vacuum
Maxwell equations for these literal finite fields. No pointwise PDE,
smoothness or finite-field reconstruction conclusion is assumed.

Every spatial point and real frequency is covered. Physical incoming
power normalization, finite interpolation/Gram nondegeneracy and physical
finite-stack Green identification remain separate work.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 3 reports use only standard foundations. Final source SHA256 `09ac3f5f9521c527bb925dd3c98d3f538f12d9362970e8023f55a259b4296847`. Independent log `lean/logs/FiniteSphereMaxwell-root-audit.log`, SHA256 `a2a44f7359e46f3e5c8f07636fb558277855b00189a7250d41bce7046dacf703`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

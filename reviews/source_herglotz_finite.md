# Actual volume-response and finite parity incident coherent flux

Frozen source: lean/SourceHerglotzFinite.lean.
SHA256: 59737C77DF320227415CB65B3BD2F9630447144176848838FD8E277293D3491B.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/SourceHerglotzFinite-final.log.
Independent audit pending.

The literal actual volume response is paired with the actual finite
parity incident electric or magnetic field from FiniteHerglotzFlux.
Exact plane parity and finite-sum algebra derive the actual coherent
flux expansion with the correct coefficient conjugation and parity signs.
The genuine point/source whole-plane bounds yield actual whole-plane
integrability and L1 bounds proportional to sourceMass times the actual
sum of incident coefficient norms. The electric constant grows as 1/d;
the magnetic constant grows only logarithmically for d <= T+R.

Actual source subtraction gives these same bounds for genuine finite-
incident coherent flux differences, with sourceMass(rho-sigma). No finite
incident replacement, source-to-field identity, tail or flux convergence
conclusion is assumed. Source gap and support and enclosing incident point
geometry are actual premises. Moving-gap finite-family convergence and
physical finite-stack Green identification remain further work.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `59737c77df320227415cb65b3bd2f9630447144176848838fd8e277293d3491b`. Independent log `lean/logs/SourceHerglotzFinite-root-audit.log`, SHA256 `fa7981a5a7d019edfaa710128073bdb5b291755c523265336e89abb5fb71bf41`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

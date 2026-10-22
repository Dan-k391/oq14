# Moving-gap coherent errors for actual finite parity illuminations

Frozen source: lean/SourceHerglotzFiniteMoving.lean.
SHA256: BABC8946D6989EE0F33A6539DCB119418EC067ACEFF21B8BE4FE3DDBEAA5F922.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/SourceHerglotzFiniteMoving-final.log.
Independent audit pending.

The literal finite parity Maxwell fields may have arbitrary varying centers,
columns, parity flags and coefficients. The centers remain in a fixed ball
and the actual sum of coefficient norms is bounded by A0/a. Genuine compact
volume sources have fixed enclosing radius and gap gamma*a from the plane.
An actual source L1 difference at most C*a^3 yields whole-plane mixed coherent
flux error bounded by C*A0 times the explicit electric or magnetic plane
constant times a^2. Previously proved scalar limits give convergence to zero.
No field or coherent flux convergence conclusion is assumed.

This result concerns the mixed coherent terms involving a finite incident
field and a volume response. It does not establish Gram interpolation,
coefficient control for a constructed channel, the quadratic scattered term,
or identification with the physical finite-stack Green field.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `babc8946d6989ee0f33a6539dcb119418ec067aceff21b8be4fe3ddbeaa5f922`. Independent log `lean/logs/SourceHerglotzFiniteMoving-root-audit.log`, SHA256 `b6d3aa4e92810f8f065eb3df20aecad9ab82ac171d826c3b3590853a8e8942d1`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

# Actual whole-plane volume-response/Herglotz coherent bounds

Frozen source: lean/SourceHerglotzWhole.lean.
SHA256: CF76378A9CBB1BCEBE6951330A6BD594A8BB540A13BFD91E2D6D8A4BA5FC5A3E.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/SourceHerglotzWhole-final.log.
Independent audit pending.

The genuine local disk and actual density-integrated tails are assembled
by the actual disk/complement partition of the full plane. Both literal
E_volume cross conjugate K_point and J_point cross conjugate H_volume are
integrable on the whole plane. Explicit L1 constants are the proved local
constant plus the actual inverse-cube tail mass. Electric dependence is
proportional to 1/d plus a gap-independent tail; magnetic dependence is
logarithmic plus a gap-independent tail (d <= T+R).

Actual source subtraction gives whole-plane coherent flux differences
bounded by these same explicit constants times the genuine coordinate L1
source difference. No field convergence, whole-plane integrability, tail,
source-to-field or trace identity is supplied as a premise.

The frequency is nonzero real, sources have actual compact support and
positive gap, the incident point lies in the enclosing ball, and the disk
radius satisfies T >= 2 and T >= 2R. Moving-gap convergence, finite incident
assembly and physical finite-stack Green identification remain further work.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `cf76378a9cbb1bcebe6951330a6bd594a8bb540a13bfd91e2d6d8a4ba5fc5a3e`. Independent log `lean/logs/SourceHerglotzWhole-root-audit.log`, SHA256 `9c6efeef17338dc6b72c71bc8c1686bd99c0b92575735658e4eabbc98a0cb534`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

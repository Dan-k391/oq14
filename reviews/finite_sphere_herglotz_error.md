# Actual finite-sphere inverse coherent Herglotz error

Frozen source: lean/FiniteSphereHerglotzError.lean.
SHA256: B54D459B2C8EE260F11D459DF23CFEB36FB60C4583FB4958B00A0620A03DC297.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all two reports standard-only. Log: lean/logs/FiniteSphereHerglotzError-final.log.
Independent audit pending.

The physical source is literally DynamicVolume.source of the actual
ParityMaterialField.solution; the trial is the actual finite ball-indicator
polarization source. Their admissibility and full L1 error are derived by
FiniteSpherePlaneSources. The actual whole-plane source/Herglotz coherent
bounds are instantiated with these sources, uniformly in an incident point
inside the enclosing ball, column index and complex coefficient bounded
by A0/a. Both actual coherent errors have explicit bounds equal to fixed
constants times CE(gamma*a)*a squared or CH(gamma*a)*a squared; their decay
was separately proved in SourceHerglotzScaling.

The final theorem invokes the actual FiniteSphereAsymptotics family
construction to discharge the inverse/source-error estimates. It constructs
the support data and all smallness/gap conditions from actual finite-ball
separation, enclosing geometry and height. No source response, field/flux
convergence, inverse identity or error estimate is a final premise.
Actual incident values, local differentiability, derivative/amplitude
bounds and weighted L2 forcing representation remain explicit input, as in
the underlying actual inverse family. This is an actual point-column
coherent error theorem for the literal parity material operator, not yet
the finite incident Gram interpolation construction or physical finite-stack
Green identification.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 2 reports use only standard foundations. Final source SHA256 `b54d459b2c8ee260f11d459df23cfeb36fb60c4583fb4958b00a0620a03dc297`. Independent log `lean/logs/FiniteSphereHerglotzError-root-audit.log`, SHA256 `7709dddb6374d6f7b940eacfe331611fe1914296e64ab7fe509587fd9c5e212f`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

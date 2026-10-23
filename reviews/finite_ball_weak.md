# Actual shrinking-ball inverse weak Maxwell equations

Frozen source: lean/FiniteBallWeak.lean.
SHA256: 1F76B1B7FE6DA824705A95A9C3DC2744901BE896F467814C4410042A37EC8DA4.
Author final pinned compiler/object PASS: exit 0, no warnings, two reports
using standard foundations only. Log: lean/logs/FiniteBallWeak-final.log.
Independent audit pending.

For finite balls of common radius rho*a in a fixed enclosing ball, nonnegative
contrast and nonzero gain scale b, the actual perturbation bound becomes less
than one for all sufficiently small positive a. The proof uses the actual
finite union volume bound and the existing genuine operator estimate; no
smallness or invertibility conclusion is supplied as a hypothesis. The literal
finite point-parity illumination datum and literal material inverse then satisfy
both dielectric Maxwell test equations. No incident PDE, material PDE, source
approximation, center separation or coefficient-amplitude bound is required
for this weak-equation conclusion. The finite-stack physical Green connection
and later coefficient/power construction remain separate.

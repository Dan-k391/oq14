# SpatialKernelAnalytic — actual spatial Green kernel analytic away from its source

Source: `lean/SpatialKernelAnalytic.lean`

SHA256: `5001CDB257AD2E0F15E393C84ADE2DE81D1CF0EF30A9A8CB7AE236EFFF585F33`

Evidence: `lean/logs/spatial-kernel-analytic-check.log`. Final compile
exited zero without warnings, created an importable object (116080 bytes),
and emitted twelve selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The existing pinned Green kernel proof has ContDiffAt at the outer
WithTop top, which is the analytic order omega. This is stronger than
C-infinity, whose notation is the coercion of the inner ENat top. The
kernel analyticity export uses the pinned ContDiffAt.analyticAt theorem;
it does not infer analyticity from mere C-infinity. The actual norm proof
at nonzero x uses norm-squared and the positive square-root inverse
function theorem, valid at the analytic order. Exponential, inverse, and
composition are already established in the existing physical kernel
proof at that same analytic order.

The new generic derivative lemmas preserve analytic order under the
actual real Frechet derivative and evaluation on a coordinate basis
vector. Local equality with the previously proved actual first and
second kernel derivative formulas then gives AnalyticAt for every literal
phiGradient and phiHessian entry. Complex-frequency kernels, their exact
real-frequency restrictions, and translated complex-frequency kernels
are all covered. Translation requires x distinct from the source point.

Self-review checked the crucial distinction between analytic omega and
inner C-infinity, the nonzero-source restriction, preservation of the
analytic order under Frechet differentiation, eventual derivative-formula
equality, real-frequency definitional restrictions, and the orientation
of source translation. No dependency versions or cached libraries were
changed. This proves kernel analyticity only; it does not prove
analyticity of arbitrary Helmholtz solutions, convolution integrals, or
continuation of Maxwell fields through material interfaces.

Root independently read the complete final source at the recorded hash
and passed all twelve exports. Source frozen.

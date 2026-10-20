# Actual truncated complex kernel is analytic in L2

Source: `lean/ComplexKernelAnalytic.lean`.

SHA256: `FF88BEF52D0BAB50970899A1158F7695D387DF95E4740B8BCC76CD6B2AD03F26`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0, no warnings). All eighteen theorem exports have matching axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final full-source audit passed at this exact hash. The source is frozen.

Actual complex derivatives of the cancellation numerators are computed: the transverse derivative is minus exp(z) z(z+1), and the radial derivative is exp(z) z(z-1). The literal cancellation formula identifies the physical remainder's parameter derivative, including its exact totalized zero value at the spatial origin. The derivative obeys a global bound of 2 exp(norm(k) norm(x)) norm(k) (norm(k) norm(x)+1)/(4 pi norm(x)). On norm(k) at most K and a spatial ball of radius R, this has a uniform constant times inverse radius.

The actual truncated physical remainder and its derivative are realized as global L2 classes using their proved local L2 membership. The local derivative majorant is the actual truncated inverse-radius function times an explicit constant, which is in L2. Applying `L2Parametric.hasDerivAt_toLp` proves actual L2 differentiation at every complex frequency. Entire complex differentiability then gives Banach-valued `AnalyticAt` at every frequency. No kernel holomorphy premise is assumed.

Almost-everywhere representative and support identities are exported, as is exact restriction of the truncated kernel to the real-frequency physical remainder. Bounded-linear convolution dependence is a separate transfer step. This file does not assert an analytic Fredholm inverse or outgoing PDE uniqueness.

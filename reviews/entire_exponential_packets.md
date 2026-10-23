# Constructive polynomial-exponential independence

Frozen source: lean/EntireExponentialPackets.lean.
SHA256: D3AAF6305D5935A129AA279E331E6A51961EA4F56DC18AF215852CB22203BDDA.
Author final pinned compiler/object PASS: exit 0, no warnings, four reports
using standard foundations only. Log: lean/logs/EntireExponentialPackets-final.log.
Independent audit pending.

The actual derivative is a complex-linear endomorphism of the submodule of
entire smooth functions. For the literal packet (a+b*z+c*z^2)*exp(zeta*z),
subtracting zeta times the identity differentiates its polynomial factor.
Three repetitions give zero, placing the packet in the actual third generalized
eigenspace. Distinct frequencies have independent generalized eigenspaces, so
a literal vanishing finite packet sum forces every polynomial coefficient to
vanish. Coefficients are recovered directly at 0,1,-1. No independence or
Fourier uniqueness conclusion is assumed. This is the algebraic analytic
bridge for the restricted scalar jet-interpolation argument; extension from
vanishing on a real interval and the two-dimensional jet map follow separately.

The pinned mathlib dependency Mathlib.LinearAlgebra.Eigenspace.Basic was built
locally without cleaning the root cache or changing configuration. Its build
log is lean/logs/EntireExponentialPackets-dependency.log, exit 0.

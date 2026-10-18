# Dynamic kernel integrability and mass estimates

`lean/DynamicIntegrability.lean` has five checked exports. For real k, the
actual dynamic dyadic remainder is measurable, vanishes at the conventionally
defined origin, and satisfies the proved bound
`|D_ij(k,x)| <= 14 k^2/(4 pi |x|)` when `|k||x|<=1`. Actual inverse-distance
and inverse-square integrability then gives local L1 and L2 membership on
the closed ball. The channel agent independently read and accepted this proof.
SHA256: `f9ecefa37a6fde22d08e3b08d69c073aba5b37adb2a74d22f8f86ca8feb01bec`.

`lean/KernelEstimates.lean` has four checked exports. Actual Haar radial
integration gives `integral_ball 1/r=(3/2) V_unit R^2` and
`integral_ball 1/r^2=3 V_unit R`, including R=0. Integral monotonicity then
gives the quadratic local mass bound for each actual remainder entry.
The counterexamples agent independently audited the proof; see
`kernel_estimates_independent.md`. SHA256:
`65ba57149ff9cf21cc9819ce7b8ae3a54546d6d4017f0d3137a2adcdc2e9501f`.

Both modules compile with only propext, Classical.choice and Quot.sound.
No custom axiom, admission, assumed kernel identity, or assumed integral
bound occurs. The estimates are entrywise, not operator-norm estimates.
The full outgoing distributional Hessian and volume operator identification
remain separate obligations.

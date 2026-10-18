# Actual three-dimensional kernel integrability

Source: `lean/KernelIntegrability.lean`. Ten exported theorems compiled
cleanly with only the standard three Lean/mathlib axioms.

The radial integrability transfer uses the actual measure-preserving
homeomorphism from punctured Euclidean three-space to the unit sphere
times positive radii. The sphere measure is finite; the radial measure
has the actual squared-radius density. Integrability transfers through
these maps and the source singleton is removed using its zero measure.
No formal polar-integration assertion is assumed.

Indicators of compact radial intervals prove integrability of inverse
distance and inverse squared distance on every finite closed ball.
The results include empty or zero-radius balls. Compact-set containment
then proves local integrability on all three-space. The actual outgoing
scalar kernel for real frequency has norm 1/(4 pi |x|), giving local L1
and L2 membership and measurability, with its total value at zero harmless
on the null singleton.

The channel agent independently read the whole file and checked the
polar-measure transfer, radial cancellation, singleton restoration,
scalar-kernel norm and compact-cover arguments. No defect was found.
Only three missing official pinned cache archives were fetched; compiler,
dependency revisions and the dependency lockfile were unchanged.

This is integrability of actual functions. No distributional delta source,
Newton Fourier identity, convolution derivative or scattering existence
theorem is asserted or used as a premise.

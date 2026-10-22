# Actual reflected Herglotz magnetic parity

Frozen source: lean/SphereMagneticParity.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all nine reports standard-only. Log: lean/logs/SphereMagneticParity-final.log.
Independent audit pending.

An actual continuous linear reflection agrees pointwise with the literal
reflection in SphereReactionKernel. The actual affine Frechet chain rule
and its derived coordinate action determine each partial derivative of the
literal electric reaction. Cyclic reflection signs derive the opposite
magnetic reflected parity, and curl(reaction)=I*k*magneticReaction holds
for the genuine sphere kernels at every real frequency and every point.

On the plane the exact electric and magnetic component selectors are
proved, and the normal complex cross product between any two columns of
the same parity vanishes pointwise (even with different source centers).
The actual magnetic reaction satisfies the derived uniform entryBound.
Neither a magnetic identity nor a parity/curl conclusion is assumed.

Opposite-parity/coherent whole-plane tails and physical finite-stack Green
identification remain separate constructions.
SHA256: 40CAE2FCB19B0938AECDCA20AE154F8471D1618113904E1001B99206978EC01A

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 9 reports use only standard foundations. Final source SHA256 `40cae2fcb19b0938aecdca20ae154f8471d1618113904e1001b99206978ec01a`. Independent log `lean/logs/SphereMagneticParity-root-audit.log`, SHA256 `9993d2a6a00d24a2988922b63d372a579525e22fa8de8128fe200ce5f602bea0`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
